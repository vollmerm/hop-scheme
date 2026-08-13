#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runtime.h"

/*
 * Garbage collector overview
 * --------------------------
 *
 * The runtime uses a simple semispace copying collector (Cheney's algorithm).
 * Every heap object lives in from-space until a collection happens. During
 * collection, reachable objects are copied into to-space, old objects are
 * turned into forwarding pointers, and the spaces are swapped.
 *
 * The interesting part is not the copying itself but root finding. This
 * runtime relies on a precise contract with the compiler:
 *
 *   1. Every allocation helper call is a GC safepoint.
 *   2. At a safepoint, every live Scheme value already lives in a known stack
 *      slot described by the current frame descriptor.
 *   3. Scratch registers are *not* roots.
 *
 * Because of that contract, the collector can walk frames precisely instead of
 * conservatively scanning raw stack memory.
 */
typedef uintptr_t hop_word;

enum {
    HOP_OBJ_FORWARD = 0,
    HOP_OBJ_BOX = 1,
    HOP_OBJ_PAIR = 2,
    HOP_OBJ_CLOSURE = 3,
    HOP_OBJ_VECTOR = 4,
    /*
     * A variadic closure uses the same pointer tag (HOP_CLOSURE_TAG) as an
     * ordinary closure -- only this header type byte distinguishes them --
     * and the same [header][code][env...] layout, with one extra trailing
     * word holding its fixed-argument count k (a plain integer, not a
     * GC-traced value). Keeping env slots at the same fixed offset for both
     * kinds means hop_closure_env, and every hot hop_call_N switch body
     * that reads it, never need to branch on variadic-ness at all.
     */
    HOP_OBJ_CLOSURE_VARIADIC = 5
};

#define HOP_HEADER_TYPE_MASK ((hop_word)0xff)
#define HOP_HEADER_AUX_SHIFT 8
#define HOP_DEFAULT_HEAP_BYTES (32 * 1024)
#define HOP_MIN_HEAP_BYTES 1024

typedef struct {
    uint8_t *from_space;
    uint8_t *to_space;
    size_t semispace_bytes;
    uint8_t *alloc_ptr;
    uint8_t *alloc_limit;
} hop_heap;

static hop_heap hop_runtime_heap = {0};
void *hop_gc_top_frame = NULL;
extern uint64_t hop_global_slot_count;
extern hop_value hop_global_slots[];

__attribute__((noreturn)) static void hop_panic(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(1);
}

static hop_word hop_make_header(hop_word type, hop_word aux) {
    return type | (aux << HOP_HEADER_AUX_SHIFT);
}

static hop_word hop_header_type(hop_word header) {
    return header & HOP_HEADER_TYPE_MASK;
}

static hop_word hop_header_aux(hop_word header) {
    return header >> HOP_HEADER_AUX_SHIFT;
}

static size_t hop_align_bytes(size_t bytes) {
    return (bytes + 15u) & ~((size_t)15u);
}

static size_t hop_parse_heap_size(void) {
    const char *text = getenv("HOP_HEAP_BYTES");
    char *end = NULL;
    unsigned long long parsed = 0;

    if (!text || *text == '\0') {
        return HOP_DEFAULT_HEAP_BYTES;
    }
    parsed = strtoull(text, &end, 10);
    if (*end != '\0' || parsed == 0) {
        hop_panic("invalid HOP_HEAP_BYTES");
    }
    if (parsed < HOP_MIN_HEAP_BYTES) {
        parsed = HOP_MIN_HEAP_BYTES;
    }
    return hop_align_bytes((size_t)parsed);
}

static void hop_init_heap(void) {
    size_t bytes;

    if (hop_runtime_heap.from_space) {
        return;
    }

    bytes = hop_parse_heap_size();
    hop_runtime_heap.from_space = (uint8_t *)malloc(bytes);
    hop_runtime_heap.to_space = (uint8_t *)malloc(bytes);
    if (!hop_runtime_heap.from_space || !hop_runtime_heap.to_space) {
        hop_panic("heap allocation failed");
    }
    hop_runtime_heap.semispace_bytes = bytes;
    hop_runtime_heap.alloc_ptr = hop_runtime_heap.from_space;
    hop_runtime_heap.alloc_limit = hop_runtime_heap.from_space + bytes;
}

static hop_value *hop_expect_pointer_tag(hop_value value, int64_t tag, const char *message) {
    if (!hop_has_tag(value, tag)) {
        hop_panic(message);
    }
    return (hop_value *)hop_untag_pointer(value);
}

static void hop_expect_object_type(hop_value *object, hop_word expected, const char *message) {
    if (hop_header_type((hop_word)object[0]) != expected) {
        hop_panic(message);
    }
}

static size_t hop_object_words(hop_value *object) {
    hop_word header = (hop_word)object[0];
    switch (hop_header_type(header)) {
    case HOP_OBJ_BOX:
        return 2;
    case HOP_OBJ_PAIR:
        return 3;
    case HOP_OBJ_CLOSURE:
        /* One extra trailing word beyond header+code+env slots holds the
         * closure's declared exact arity (see hop_closure_arity below) --
         * the same layout HOP_OBJ_CLOSURE_VARIADIC already uses for its
         * trailing k word. */
        return 3 + (size_t)hop_header_aux(header);
    case HOP_OBJ_CLOSURE_VARIADIC:
        return 3 + (size_t)hop_header_aux(header);
    case HOP_OBJ_VECTOR:
        return 1 + (size_t)hop_header_aux(header);
    case HOP_OBJ_FORWARD:
        return 2;
    default:
        hop_panic("unknown heap object type");
    }
}

static int hop_pointer_in_from_space(hop_value *ptr) {
    return ((uint8_t *)ptr >= hop_runtime_heap.from_space) &&
           ((uint8_t *)ptr < hop_runtime_heap.from_space + hop_runtime_heap.semispace_bytes);
}

static uint8_t *hop_gc_copy_alloc = NULL;
static uint8_t *hop_gc_copy_limit = NULL;

static hop_value hop_copy_value(hop_value value) {
    hop_value *old_object;
    hop_value *new_object;
    size_t words;
    int64_t tag;

    if (!hop_has_tag(value, HOP_PAIR_TAG) &&
        !hop_has_tag(value, HOP_BOX_TAG) &&
        !hop_has_tag(value, HOP_CLOSURE_TAG) &&
        !hop_has_tag(value, HOP_VECTOR_TAG)) {
        return value;
    }

    old_object = (hop_value *)hop_untag_pointer(value);
    if (!hop_pointer_in_from_space(old_object)) {
        return value;
    }

    tag = value & HOP_TAG_MASK;
    if (hop_header_type((hop_word)old_object[0]) == HOP_OBJ_FORWARD) {
        return hop_tag_pointer((void *)(uintptr_t)old_object[1], tag);
    }

    words = hop_object_words(old_object);
    if (hop_gc_copy_alloc + (words * sizeof(hop_value)) > hop_gc_copy_limit) {
        hop_panic("out of memory during garbage collection");
    }

    new_object = (hop_value *)hop_gc_copy_alloc;
    memcpy(new_object, old_object, words * sizeof(hop_value));
    hop_gc_copy_alloc += words * sizeof(hop_value);

    old_object[0] = (hop_value)hop_make_header(HOP_OBJ_FORWARD, 0);
    old_object[1] = (hop_value)(uintptr_t)new_object;
    return hop_tag_pointer(new_object, tag);
}

static void hop_copy_stack_roots(void) {
    void *frame = hop_gc_top_frame;

    /*
     * Each compiled frame links itself into hop_gc_top_frame and stores a
     * pointer to a tiny descriptor just above the standard x29/x30 frame
     * record. The descriptor tells us how many stack slots hold Scheme values
     * and how large the frame is, so we can rewrite exactly those slots.
     */
    while (frame) {
        void *prev = *(void **)((uint8_t *)frame - 16);
        const hop_gc_frame_desc *desc = *(const hop_gc_frame_desc **)((uint8_t *)frame - 8);
        hop_value *slots;
        uint64_t index;

        if (!desc) {
            hop_panic("missing GC frame descriptor");
        }

        slots = (hop_value *)((uint8_t *)frame - desc->stack_size);
        for (index = 0; index < desc->frame_slots; index += 1) {
            slots[index] = hop_copy_value(slots[index]);
        }
        frame = prev;
    }
}

static void hop_copy_temp_roots(hop_value *roots, size_t count) {
    size_t index;

    /*
     * Allocation helper arguments arrive in C registers. If a collection runs
     * before the new object is fully built, those incoming values are still
     * logically live even though they are not yet stored in the heap. We treat
     * them as an extra short-lived root set and rewrite them in place.
     */
    for (index = 0; index < count; index += 1) {
        roots[index] = hop_copy_value(roots[index]);
    }
}

static void hop_copy_global_roots(void) {
    uint64_t index;

    for (index = 0; index < hop_global_slot_count; index += 1) {
        hop_global_slots[index] = hop_copy_value(hop_global_slots[index]);
    }
}

static void hop_scan_copied_objects(void) {
    uint8_t *scan = hop_runtime_heap.to_space;

    /*
     * Cheney's algorithm uses two cursors:
     *   - hop_gc_copy_alloc: end of copied objects
     *   - scan: next copied object whose pointer fields still need rewriting
     *
     * That gives a breadth-first traversal without an explicit worklist.
     */
    while (scan < hop_gc_copy_alloc) {
        hop_value *object = (hop_value *)scan;
        hop_word header = (hop_word)object[0];
        hop_word type = hop_header_type(header);
        size_t words = hop_object_words(object);
        size_t index;

        switch (type) {
        case HOP_OBJ_BOX:
            object[1] = hop_copy_value(object[1]);
            break;
        case HOP_OBJ_PAIR:
            object[1] = hop_copy_value(object[1]);
            object[2] = hop_copy_value(object[2]);
            break;
        case HOP_OBJ_CLOSURE:
        case HOP_OBJ_CLOSURE_VARIADIC:
            /* Both kinds keep env slots at the same offset, for exactly
             * env_count words; a variadic closure's trailing k word is a
             * plain integer, not a pointer, and must not be traced. */
            for (index = 0; index < (size_t)hop_header_aux(header); index += 1) {
                object[2 + index] = hop_copy_value(object[2 + index]);
            }
            break;
        case HOP_OBJ_VECTOR:
            for (index = 0; index < (size_t)hop_header_aux(header); index += 1) {
                object[1 + index] = hop_copy_value(object[1 + index]);
            }
            break;
        default:
            hop_panic("unexpected copied object type");
        }

        scan += words * sizeof(hop_value);
    }
}

static void hop_collect(hop_value *temp_roots, size_t temp_root_count) {
    uint8_t *old_from_space = hop_runtime_heap.from_space;

    /* Start the new semispace empty and grow it by copying reachable objects. */
    hop_gc_copy_alloc = hop_runtime_heap.to_space;
    hop_gc_copy_limit = hop_runtime_heap.to_space + hop_runtime_heap.semispace_bytes;

    hop_copy_global_roots();
    hop_copy_stack_roots();
    hop_copy_temp_roots(temp_roots, temp_root_count);
    hop_scan_copied_objects();

    hop_runtime_heap.from_space = hop_runtime_heap.to_space;
    hop_runtime_heap.to_space = old_from_space;
    hop_runtime_heap.alloc_ptr = hop_gc_copy_alloc;
    hop_runtime_heap.alloc_limit = hop_runtime_heap.from_space + hop_runtime_heap.semispace_bytes;
}

static hop_value *hop_alloc_words(size_t words, hop_value *temp_roots, size_t temp_root_count) {
    size_t bytes = words * sizeof(hop_value);
    hop_value *object;

    hop_init_heap();

    /* Allocation is the only safepoint in this runtime. */
    if (hop_runtime_heap.alloc_ptr + bytes > hop_runtime_heap.alloc_limit) {
        hop_collect(temp_roots, temp_root_count);
    }
    if (hop_runtime_heap.alloc_ptr + bytes > hop_runtime_heap.alloc_limit) {
        hop_panic("heap exhausted");
    }

    object = (hop_value *)hop_runtime_heap.alloc_ptr;
    hop_runtime_heap.alloc_ptr += bytes;
    return object;
}

hop_value hop_alloc_box(hop_value value) {
    hop_value roots[1];
    hop_value *box;

    /* Preserve the incoming payload across a possible collection. */
    roots[0] = value;
    box = hop_alloc_words(2, roots, 1);
    box[0] = (hop_value)hop_make_header(HOP_OBJ_BOX, 0);
    box[1] = roots[0];
    return hop_tag_pointer(box, HOP_BOX_TAG);
}

hop_value hop_alloc_pair(hop_value car, hop_value cdr) {
    hop_value roots[2];
    hop_value *pair;

    /* The new pair is filled with post-GC versions of car/cdr if copying ran. */
    roots[0] = car;
    roots[1] = cdr;
    pair = hop_alloc_words(3, roots, 2);
    pair[0] = (hop_value)hop_make_header(HOP_OBJ_PAIR, 0);
    pair[1] = roots[0];
    pair[2] = roots[1];
    return hop_tag_pointer(pair, HOP_PAIR_TAG);
}

hop_value hop_car(hop_value pair_value) {
    hop_value *pair = hop_expect_pointer_tag(pair_value, HOP_PAIR_TAG, "car expected pair");
    hop_expect_object_type(pair, HOP_OBJ_PAIR, "car expected pair");
    return pair[1];
}

hop_value hop_cdr(hop_value pair_value) {
    hop_value *pair = hop_expect_pointer_tag(pair_value, HOP_PAIR_TAG, "cdr expected pair");
    hop_expect_object_type(pair, HOP_OBJ_PAIR, "cdr expected pair");
    return pair[2];
}

hop_value hop_alloc_vector(hop_value length_val, hop_value fill) {
    hop_value roots[2];
    hop_value *vector;
    int64_t length;
    size_t i;

    if (!hop_is_fixnum(length_val))
        hop_panic("make-vector: expected fixnum length");
    length = hop_decode_fixnum(length_val);
    if (length < 0)
        hop_panic("make-vector: negative length");

    roots[0] = length_val;
    roots[1] = fill;
    vector = hop_alloc_words((size_t)(1 + length), roots, 2);
    vector[0] = (hop_value)hop_make_header(HOP_OBJ_VECTOR, (hop_word)length);
    for (i = 0; i < (size_t)length; i += 1) {
        vector[1 + i] = roots[1];
    }
    return hop_tag_pointer(vector, HOP_VECTOR_TAG);
}

hop_value hop_vector_length(hop_value vec_value) {
    hop_value *vec = hop_expect_pointer_tag(vec_value, HOP_VECTOR_TAG, "vector-length expected vector");
    hop_expect_object_type(vec, HOP_OBJ_VECTOR, "vector-length expected vector");
    return hop_encode_fixnum((int64_t)hop_header_aux((hop_word)vec[0]));
}

hop_value hop_vector_ref(hop_value vec_value, hop_value index_val) {
    hop_value *vec;
    int64_t index, length;

    vec = hop_expect_pointer_tag(vec_value, HOP_VECTOR_TAG, "vector-ref expected vector");
    hop_expect_object_type(vec, HOP_OBJ_VECTOR, "vector-ref expected vector");
    length = (int64_t)hop_header_aux((hop_word)vec[0]);

    if (!hop_is_fixnum(index_val))
        hop_panic("vector-ref: expected fixnum index");
    index = hop_decode_fixnum(index_val);
    if (index < 0 || index >= length)
        hop_panic("vector-ref: index out of range");

    return vec[1 + (size_t)index];
}

hop_value hop_vector_set(hop_value vec_value, hop_value index_val, hop_value new_value) {
    hop_value *vec;
    int64_t index, length;

    vec = hop_expect_pointer_tag(vec_value, HOP_VECTOR_TAG, "vector-set! expected vector");
    hop_expect_object_type(vec, HOP_OBJ_VECTOR, "vector-set! expected vector");
    length = (int64_t)hop_header_aux((hop_word)vec[0]);

    if (!hop_is_fixnum(index_val))
        hop_panic("vector-set!: expected fixnum index");
    index = hop_decode_fixnum(index_val);
    if (index < 0 || index >= length)
        hop_panic("vector-set!: index out of range");

    vec[1 + (size_t)index] = new_value;
    return new_value;
}

hop_value hop_safe_add(hop_value a, hop_value b) {
    if (!hop_is_fixnum(a) || !hop_is_fixnum(b))
        hop_panic("safe-+: expected fixnums");
    return a + b;
}

hop_value hop_safe_sub(hop_value a, hop_value b) {
    if (!hop_is_fixnum(a) || !hop_is_fixnum(b))
        hop_panic("safe--: expected fixnums");
    return a - b;
}

hop_value hop_safe_mul(hop_value a, hop_value b) {
    if (!hop_is_fixnum(a) || !hop_is_fixnum(b))
        hop_panic("safe-*: expected fixnums");
    /* Both values are shifted left by HOP_FIXNUM_SHIFT. Multiplying them
       produces a result shifted by 2*shift, so we undo one shift to restore
       the correct fixnum encoding: result = val_a * val_b << shift. */
    return (a >> HOP_FIXNUM_SHIFT) * b;
}

hop_value hop_safe_eq(hop_value a, hop_value b) {
    if (!hop_is_fixnum(a) || !hop_is_fixnum(b))
        hop_panic("safe-=: expected fixnums");
    return (a == b) ? HOP_TRUE : HOP_FALSE;
}

hop_value hop_safe_lt(hop_value a, hop_value b) {
    if (!hop_is_fixnum(a) || !hop_is_fixnum(b))
        hop_panic("safe-<: expected fixnums");
    return (a < b) ? HOP_TRUE : HOP_FALSE;
}

hop_value hop_safe_gt(hop_value a, hop_value b) {
    if (!hop_is_fixnum(a) || !hop_is_fixnum(b))
        hop_panic("safe->: expected fixnums");
    return (a > b) ? HOP_TRUE : HOP_FALSE;
}

static hop_value *hop_alloc_closure_raw(void *code, int64_t env_count, int64_t arity) {
    hop_value *closure = hop_alloc_words(3 + (size_t)env_count, NULL, 0);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, (hop_word)env_count);
    closure[1] = (hop_value)(uintptr_t)code;
    closure[2 + env_count] = (hop_value)arity;
    return closure;
}

static hop_value *hop_as_closure(hop_value closure_value) {
    hop_value *closure =
        hop_expect_pointer_tag(closure_value, HOP_CLOSURE_TAG, "call expected closure");
    hop_word type = hop_header_type((hop_word)closure[0]);
    if (type != HOP_OBJ_CLOSURE && type != HOP_OBJ_CLOSURE_VARIADIC) {
        hop_panic("call expected closure");
    }
    return closure;
}

static void *hop_closure_code(hop_value *closure) {
    return (void *)(uintptr_t)closure[1];
}

static int64_t hop_closure_env_count(hop_value *closure) {
    return (int64_t)hop_header_aux((hop_word)closure[0]);
}

static hop_value *hop_closure_env(hop_value *closure) {
    return closure + 2;
}

/*
 * Every closure -- ordinary or variadic -- stores its declared, user-facing
 * exact/minimum fixed-argument count (captures excluded) in the single
 * trailing word just past its env slots. For an ordinary closure this is
 * the exact required argc; for a variadic closure it is the minimum (see
 * hop_closure_is_variadic below for which check applies).
 */
static int64_t hop_closure_arity(hop_value *closure) {
    return (int64_t)closure[2 + hop_closure_env_count(closure)];
}

static int hop_closure_is_variadic(hop_value *closure) {
    return hop_header_type((hop_word)closure[0]) == HOP_OBJ_CLOSURE_VARIADIC;
}

/* Valid only when hop_closure_is_variadic(closure) is true. */
static int64_t hop_closure_variadic_k(hop_value *closure) {
    return hop_closure_arity(closure);
}

hop_value hop_alloc_closure_0(void *code, int64_t arity) {
    return hop_tag_pointer(hop_alloc_closure_raw(code, 0, arity), HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_1(void *code, hop_value env0, int64_t arity) {
    hop_value roots[1];
    hop_value *closure;

    /* Code pointers are not GC-managed; only the captured Scheme values move. */
    roots[0] = env0;
    closure = hop_alloc_words(4, roots, 1);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, 1);
    closure[1] = (hop_value)(uintptr_t)code;
    hop_closure_env(closure)[0] = roots[0];
    closure[2 + 1] = (hop_value)arity;
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_2(void *code, hop_value env0, hop_value env1, int64_t arity) {
    hop_value roots[2];
    hop_value *closure;

    roots[0] = env0;
    roots[1] = env1;
    closure = hop_alloc_words(5, roots, 2);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, 2);
    closure[1] = (hop_value)(uintptr_t)code;
    hop_closure_env(closure)[0] = roots[0];
    hop_closure_env(closure)[1] = roots[1];
    closure[2 + 2] = (hop_value)arity;
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_3(void *code, hop_value env0, hop_value env1, hop_value env2, int64_t arity) {
    hop_value roots[3];
    hop_value *closure;

    roots[0] = env0;
    roots[1] = env1;
    roots[2] = env2;
    closure = hop_alloc_words(6, roots, 3);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, 3);
    closure[1] = (hop_value)(uintptr_t)code;
    hop_closure_env(closure)[0] = roots[0];
    hop_closure_env(closure)[1] = roots[1];
    hop_closure_env(closure)[2] = roots[2];
    closure[2 + 3] = (hop_value)arity;
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

#define HOP_MAX_CLOSURE_ENV 16
static hop_value hop_temp_closure_roots[HOP_MAX_CLOSURE_ENV];

hop_value hop_alloc_closure_n(void *code, int64_t count, hop_value *envs, int64_t arity) {
    hop_value *closure;
    int64_t i;

    if (count > HOP_MAX_CLOSURE_ENV) {
        hop_panic("too many closure captures");
    }
    /*
     * Copy the captures into a static root buffer before allocating.  If the
     * allocator triggers a collection, the collector updates every live root
     * slot in every compiled frame, and then also rewrites hop_temp_closure_roots
     * via hop_copy_temp_roots.  The envs array (in the outgoing-arg area of the
     * caller's frame) is NOT scanned, but we copied the values out before GC
     * can run, so post-GC values come from the static buffer.
     */
    for (i = 0; i < count; i++) {
        hop_temp_closure_roots[i] = envs[i];
    }
    closure = hop_alloc_words(3 + (size_t)count, hop_temp_closure_roots, (size_t)count);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, (hop_word)count);
    closure[1] = (hop_value)(uintptr_t)code;
    for (i = 0; i < count; i++) {
        hop_closure_env(closure)[i] = hop_temp_closure_roots[i];
    }
    closure[2 + count] = (hop_value)arity;
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

/*
 * Variadic closures are a new, unoptimized-for-speed path (ordinary
 * closures never route through here), so there is no small-count fast case
 * the way hop_alloc_closure_0..3 provide above -- always go through the
 * general captures-buffer path, mirroring hop_alloc_closure_n.
 */
hop_value hop_alloc_closure_variadic(void *code, int64_t k, int64_t count, hop_value *envs) {
    hop_value *closure;
    int64_t i;

    if (count > HOP_MAX_CLOSURE_ENV) {
        hop_panic("too many closure captures");
    }
    for (i = 0; i < count; i++) {
        hop_temp_closure_roots[i] = envs[i];
    }
    closure = hop_alloc_words(3 + (size_t)count, hop_temp_closure_roots, (size_t)count);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE_VARIADIC, (hop_word)count);
    closure[1] = (hop_value)(uintptr_t)code;
    for (i = 0; i < count; i++) {
        hop_closure_env(closure)[i] = hop_temp_closure_roots[i];
    }
    closure[2 + count] = (hop_value)k;
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

typedef hop_value (*hop_fun_0_0)(void);
typedef hop_value (*hop_fun_0_1)(hop_value);
typedef hop_value (*hop_fun_0_2)(hop_value, hop_value);
typedef hop_value (*hop_fun_0_3)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_0_4)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_0_5)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_0_6)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_0_7)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_0_8)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_0)(hop_value);
typedef hop_value (*hop_fun_1_1)(hop_value, hop_value);
typedef hop_value (*hop_fun_1_2)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_3)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_4)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_5)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_6)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_7)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_0)(hop_value, hop_value);
typedef hop_value (*hop_fun_2_1)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_2)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_3)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_4)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_5)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_6)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_0)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_1)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_2)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_3)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_4)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_5)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_4_0)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_4_1)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_4_2)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_4_3)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_4_4)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_5_0)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_5_1)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_5_2)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_5_3)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_6_0)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_6_1)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_6_2)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_7_0)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_7_1)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_8_0)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);

/*
 * Shared indirect-invocation primitive, reused by hop_call_N's variadic
 * branch below and by hop_apply. A variadic closure's underlying native
 * function has the exact same C shape as an ordinary (env_count, argc)-ary
 * function -- the trailing "argument" just happens to already be a
 * cons-list value -- so no new typedefs are needed here: this covers
 * exactly the same env_count+argc<=8 region the hop_fun_* typedefs above
 * already cover (the same ceiling hop_call_N already has), and panics
 * outside it exactly like their default: cases do.
 */
static hop_value hop_dispatch_flat_call(void *code, int64_t env_count,
                                        hop_value *env, hop_value *args, int64_t argc) {
    switch (argc) {
    case 0:
        switch (env_count) {
        case 0: return ((hop_fun_0_0)code)();
        case 1: return ((hop_fun_1_0)code)(env[0]);
        case 2: return ((hop_fun_2_0)code)(env[0], env[1]);
        case 3: return ((hop_fun_3_0)code)(env[0], env[1], env[2]);
        case 4: return ((hop_fun_4_0)code)(env[0], env[1], env[2], env[3]);
        case 5: return ((hop_fun_5_0)code)(env[0], env[1], env[2], env[3], env[4]);
        case 6: return ((hop_fun_6_0)code)(env[0], env[1], env[2], env[3], env[4], env[5]);
        case 7: return ((hop_fun_7_0)code)(env[0], env[1], env[2], env[3], env[4], env[5], env[6]);
        case 8: return ((hop_fun_8_0)code)(env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 1:
        switch (env_count) {
        case 0: return ((hop_fun_0_1)code)(args[0]);
        case 1: return ((hop_fun_1_1)code)(env[0], args[0]);
        case 2: return ((hop_fun_2_1)code)(env[0], env[1], args[0]);
        case 3: return ((hop_fun_3_1)code)(env[0], env[1], env[2], args[0]);
        case 4: return ((hop_fun_4_1)code)(env[0], env[1], env[2], env[3], args[0]);
        case 5: return ((hop_fun_5_1)code)(env[0], env[1], env[2], env[3], env[4], args[0]);
        case 6: return ((hop_fun_6_1)code)(env[0], env[1], env[2], env[3], env[4], env[5], args[0]);
        case 7: return ((hop_fun_7_1)code)(env[0], env[1], env[2], env[3], env[4], env[5], env[6], args[0]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 2:
        switch (env_count) {
        case 0: return ((hop_fun_0_2)code)(args[0], args[1]);
        case 1: return ((hop_fun_1_2)code)(env[0], args[0], args[1]);
        case 2: return ((hop_fun_2_2)code)(env[0], env[1], args[0], args[1]);
        case 3: return ((hop_fun_3_2)code)(env[0], env[1], env[2], args[0], args[1]);
        case 4: return ((hop_fun_4_2)code)(env[0], env[1], env[2], env[3], args[0], args[1]);
        case 5: return ((hop_fun_5_2)code)(env[0], env[1], env[2], env[3], env[4], args[0], args[1]);
        case 6: return ((hop_fun_6_2)code)(env[0], env[1], env[2], env[3], env[4], env[5], args[0], args[1]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 3:
        switch (env_count) {
        case 0: return ((hop_fun_0_3)code)(args[0], args[1], args[2]);
        case 1: return ((hop_fun_1_3)code)(env[0], args[0], args[1], args[2]);
        case 2: return ((hop_fun_2_3)code)(env[0], env[1], args[0], args[1], args[2]);
        case 3: return ((hop_fun_3_3)code)(env[0], env[1], env[2], args[0], args[1], args[2]);
        case 4: return ((hop_fun_4_3)code)(env[0], env[1], env[2], env[3], args[0], args[1], args[2]);
        case 5: return ((hop_fun_5_3)code)(env[0], env[1], env[2], env[3], env[4], args[0], args[1], args[2]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 4:
        switch (env_count) {
        case 0: return ((hop_fun_0_4)code)(args[0], args[1], args[2], args[3]);
        case 1: return ((hop_fun_1_4)code)(env[0], args[0], args[1], args[2], args[3]);
        case 2: return ((hop_fun_2_4)code)(env[0], env[1], args[0], args[1], args[2], args[3]);
        case 3: return ((hop_fun_3_4)code)(env[0], env[1], env[2], args[0], args[1], args[2], args[3]);
        case 4: return ((hop_fun_4_4)code)(env[0], env[1], env[2], env[3], args[0], args[1], args[2], args[3]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 5:
        switch (env_count) {
        case 0: return ((hop_fun_0_5)code)(args[0], args[1], args[2], args[3], args[4]);
        case 1: return ((hop_fun_1_5)code)(env[0], args[0], args[1], args[2], args[3], args[4]);
        case 2: return ((hop_fun_2_5)code)(env[0], env[1], args[0], args[1], args[2], args[3], args[4]);
        case 3: return ((hop_fun_3_5)code)(env[0], env[1], env[2], args[0], args[1], args[2], args[3], args[4]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 6:
        switch (env_count) {
        case 0: return ((hop_fun_0_6)code)(args[0], args[1], args[2], args[3], args[4], args[5]);
        case 1: return ((hop_fun_1_6)code)(env[0], args[0], args[1], args[2], args[3], args[4], args[5]);
        case 2: return ((hop_fun_2_6)code)(env[0], env[1], args[0], args[1], args[2], args[3], args[4], args[5]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 7:
        switch (env_count) {
        case 0: return ((hop_fun_0_7)code)(args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
        case 1: return ((hop_fun_1_7)code)(env[0], args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    case 8:
        switch (env_count) {
        case 0: return ((hop_fun_0_8)code)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
        default: hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
        }
    default:
        hop_panic("unsupported (env_count, argc) combination in hop_dispatch_flat_call");
    }
}

/*
 * Scratch buffer for building a variadic call's rest-list and (for
 * hop_apply) its fully-flattened argument list. Sized generously relative
 * to the existing HOP_MAX_CLOSURE_ENV=16 capture ceiling and the
 * env_count+argc<=8 dispatch ceiling above; exceeding it panics, mirroring
 * how hop_alloc_closure_n already panics past HOP_MAX_CLOSURE_ENV. Reused
 * (not held concurrently) by hop_invoke_variadic_closure and hop_apply --
 * both run to completion, including every allocation, before returning.
 */
#define HOP_MAX_VARIADIC_ARGS 64
static hop_value hop_temp_variadic_roots[HOP_MAX_VARIADIC_ARGS];

/*
 * Shared by every hop_call_N's variadic branch below. args[] holds exactly
 * the argc arguments the caller passed at this indirect call site (never
 * including captured env values -- those come from the closure's own env
 * slots, exactly as for an ordinary closure).
 */
static hop_value hop_invoke_variadic_closure(hop_value closure_value, hop_value *args, int64_t argc) {
    hop_value *closure = hop_as_closure(closure_value);
    int64_t k = hop_closure_variadic_k(closure);
    int64_t env_count;
    void *code;
    hop_value rest;
    hop_value fixed_and_rest[9];
    int64_t i;

    if (argc < k) {
        hop_panic("procedure called with too few arguments");
    }
    /* hop_dispatch_flat_call itself cannot dispatch a combined
     * env_count+argc beyond 8; check k here too so a large k can never
     * overrun the fixed-size fixed_and_rest buffer below. */
    if (k + 1 > 8) {
        hop_panic("procedure has too many fixed parameters for indirect variadic dispatch");
    }
    if (argc > HOP_MAX_VARIADIC_ARGS - 2) {
        hop_panic("too many arguments to variadic procedure");
    }

    /*
     * Root closure_value + every argument across the consing loop below:
     * each hop_alloc_words call is a GC safepoint, and this function's own
     * plain C stack frame -- unlike the compiler's own frames -- is
     * invisible to the precise collector's frame-descriptor walk. Every
     * allocation below roots the *entire* still-live window, and closure
     * is always re-derived from the rooted buffer afterward rather than
     * reusing a pointer computed before an allocation could have moved it.
     */
    hop_temp_variadic_roots[0] = closure_value;
    for (i = 0; i < argc; i++) {
        hop_temp_variadic_roots[1 + i] = args[i];
    }
    rest = HOP_NULL;
    hop_temp_variadic_roots[1 + argc] = rest;
    for (i = argc - 1; i >= k; i--) {
        hop_value *pair = hop_alloc_words(3, hop_temp_variadic_roots, (size_t)(argc + 2));
        pair[0] = (hop_value)hop_make_header(HOP_OBJ_PAIR, 0);
        pair[1] = hop_temp_variadic_roots[1 + i];
        pair[2] = hop_temp_variadic_roots[1 + argc];
        rest = hop_tag_pointer(pair, HOP_PAIR_TAG);
        hop_temp_variadic_roots[1 + argc] = rest;
    }

    closure = hop_as_closure(hop_temp_variadic_roots[0]);
    env_count = hop_closure_env_count(closure);
    code = hop_closure_code(closure);
    for (i = 0; i < k; i++) {
        fixed_and_rest[i] = hop_temp_variadic_roots[1 + i];
    }
    fixed_and_rest[k] = hop_temp_variadic_roots[1 + argc];
    return hop_dispatch_flat_call(code, env_count, hop_closure_env(closure), fixed_and_rest, k + 1);
}

/*
 * Ordinary (non-variadic) closures declare an exact required argument
 * count (see hop_closure_arity above). An indirect call site can never
 * prove this statically -- unlike (hop pass cfa)'s rewrite-known-calls,
 * which performs the equivalent check at compile time whenever the call
 * target *is* provably known -- so hop_call_N validates it here instead of
 * silently invoking the underlying function with the wrong number of
 * arguments (which would otherwise read garbage/uninitialized registers or
 * silently drop extra arguments).
 */
static void hop_check_ordinary_arity(hop_value *closure, int64_t argc) {
    if (hop_closure_arity(closure) != argc) {
        hop_panic("procedure called with wrong number of arguments");
    }
}

hop_value hop_call_0(hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        return hop_invoke_variadic_closure(closure_value, NULL, 0);
    }
    hop_check_ordinary_arity(closure, 0);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_0)hop_closure_code(closure))();
    case 1:
        return ((hop_fun_1_0)hop_closure_code(closure))(env[0]);
    case 2:
        return ((hop_fun_2_0)hop_closure_code(closure))(env[0], env[1]);
    case 3:
        return ((hop_fun_3_0)hop_closure_code(closure))(env[0], env[1], env[2]);
    case 4:
        return ((hop_fun_4_0)hop_closure_code(closure))(env[0], env[1], env[2], env[3]);
    case 5:
        return ((hop_fun_5_0)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4]);
    case 6:
        return ((hop_fun_6_0)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], env[5]);
    case 7:
        return ((hop_fun_7_0)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], env[5], env[6]);
    case 8:
        return ((hop_fun_8_0)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], env[5], env[6], env[7]);
    default:
        hop_panic("unsupported closure env count for hop_call_0");
    }
}

hop_value hop_call_1(hop_value arg0, hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[1] = {arg0};
        return hop_invoke_variadic_closure(closure_value, args, 1);
    }
    hop_check_ordinary_arity(closure, 1);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_1)hop_closure_code(closure))(arg0);
    case 1:
        return ((hop_fun_1_1)hop_closure_code(closure))(env[0], arg0);
    case 2:
        return ((hop_fun_2_1)hop_closure_code(closure))(env[0], env[1], arg0);
    case 3:
        return ((hop_fun_3_1)hop_closure_code(closure))(env[0], env[1], env[2], arg0);
    case 4:
        return ((hop_fun_4_1)hop_closure_code(closure))(env[0], env[1], env[2], env[3], arg0);
    case 5:
        return ((hop_fun_5_1)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], arg0);
    case 6:
        return ((hop_fun_6_1)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], env[5], arg0);
    case 7:
        return ((hop_fun_7_1)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], env[5], env[6], arg0);
    default:
        hop_panic("unsupported closure env count for hop_call_1");
    }
}

hop_value hop_call_2(hop_value arg0, hop_value arg1, hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[2] = {arg0, arg1};
        return hop_invoke_variadic_closure(closure_value, args, 2);
    }
    hop_check_ordinary_arity(closure, 2);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_2)hop_closure_code(closure))(arg0, arg1);
    case 1:
        return ((hop_fun_1_2)hop_closure_code(closure))(env[0], arg0, arg1);
    case 2:
        return ((hop_fun_2_2)hop_closure_code(closure))(env[0], env[1], arg0, arg1);
    case 3:
        return ((hop_fun_3_2)hop_closure_code(closure))(env[0], env[1], env[2], arg0, arg1);
    case 4:
        return ((hop_fun_4_2)hop_closure_code(closure))(env[0], env[1], env[2], env[3], arg0, arg1);
    case 5:
        return ((hop_fun_5_2)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], arg0, arg1);
    case 6:
        return ((hop_fun_6_2)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], env[5], arg0, arg1);
    default:
        hop_panic("unsupported closure env count for hop_call_2");
    }
}

hop_value hop_call_3(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[3] = {arg0, arg1, arg2};
        return hop_invoke_variadic_closure(closure_value, args, 3);
    }
    hop_check_ordinary_arity(closure, 3);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_3)hop_closure_code(closure))(arg0, arg1, arg2);
    case 1:
        return ((hop_fun_1_3)hop_closure_code(closure))(env[0], arg0, arg1, arg2);
    case 2:
        return ((hop_fun_2_3)hop_closure_code(closure))(env[0], env[1], arg0, arg1, arg2);
    case 3:
        return ((hop_fun_3_3)hop_closure_code(closure))(env[0], env[1], env[2], arg0, arg1, arg2);
    case 4:
        return ((hop_fun_4_3)hop_closure_code(closure))(env[0], env[1], env[2], env[3], arg0, arg1, arg2);
    case 5:
        return ((hop_fun_5_3)hop_closure_code(closure))(env[0], env[1], env[2], env[3], env[4], arg0, arg1, arg2);
    default:
        hop_panic("unsupported closure env count for hop_call_3");
    }
}

hop_value hop_call_4(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value arg3,
                     hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[4] = {arg0, arg1, arg2, arg3};
        return hop_invoke_variadic_closure(closure_value, args, 4);
    }
    hop_check_ordinary_arity(closure, 4);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_4)hop_closure_code(closure))(arg0, arg1, arg2, arg3);
    case 1:
        return ((hop_fun_1_4)hop_closure_code(closure))(env[0], arg0, arg1, arg2, arg3);
    case 2:
        return ((hop_fun_2_4)hop_closure_code(closure))(env[0], env[1], arg0, arg1, arg2, arg3);
    case 3:
        return ((hop_fun_3_4)hop_closure_code(closure))(env[0], env[1], env[2], arg0, arg1, arg2, arg3);
    case 4:
        return ((hop_fun_4_4)hop_closure_code(closure))(env[0], env[1], env[2], env[3], arg0, arg1, arg2, arg3);
    default:
        hop_panic("unsupported closure env count for hop_call_4");
    }
}

hop_value hop_call_5(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value arg3,
                     hop_value arg4,
                     hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[5] = {arg0, arg1, arg2, arg3, arg4};
        return hop_invoke_variadic_closure(closure_value, args, 5);
    }
    hop_check_ordinary_arity(closure, 5);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_5)hop_closure_code(closure))(arg0, arg1, arg2, arg3, arg4);
    case 1:
        return ((hop_fun_1_5)hop_closure_code(closure))(env[0], arg0, arg1, arg2, arg3, arg4);
    case 2:
        return ((hop_fun_2_5)hop_closure_code(closure))(env[0], env[1], arg0, arg1, arg2, arg3, arg4);
    case 3:
        return ((hop_fun_3_5)hop_closure_code(closure))(env[0], env[1], env[2], arg0, arg1, arg2, arg3, arg4);
    default:
        hop_panic("unsupported closure env count for hop_call_5");
    }
}

hop_value hop_call_6(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value arg3,
                     hop_value arg4,
                     hop_value arg5,
                     hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[6] = {arg0, arg1, arg2, arg3, arg4, arg5};
        return hop_invoke_variadic_closure(closure_value, args, 6);
    }
    hop_check_ordinary_arity(closure, 6);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_6)hop_closure_code(closure))(arg0, arg1, arg2, arg3, arg4, arg5);
    case 1:
        return ((hop_fun_1_6)hop_closure_code(closure))(env[0], arg0, arg1, arg2, arg3, arg4, arg5);
    case 2:
        return ((hop_fun_2_6)hop_closure_code(closure))(env[0], env[1], arg0, arg1, arg2, arg3, arg4, arg5);
    default:
        hop_panic("unsupported closure env count for hop_call_6");
    }
}

hop_value hop_call_7(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value arg3,
                     hop_value arg4,
                     hop_value arg5,
                     hop_value arg6,
                     hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[7] = {arg0, arg1, arg2, arg3, arg4, arg5, arg6};
        return hop_invoke_variadic_closure(closure_value, args, 7);
    }
    hop_check_ordinary_arity(closure, 7);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_7)hop_closure_code(closure))(arg0, arg1, arg2, arg3, arg4, arg5, arg6);
    case 1:
        return ((hop_fun_1_7)hop_closure_code(closure))(env[0], arg0, arg1, arg2, arg3, arg4, arg5, arg6);
    default:
        hop_panic("unsupported closure env count for hop_call_7");
    }
}

hop_value hop_call_8(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value arg3,
                     hop_value arg4,
                     hop_value arg5,
                     hop_value arg6,
                     hop_value arg7,
                     hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
    if (hop_closure_is_variadic(closure)) {
        hop_value args[8] = {arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7};
        return hop_invoke_variadic_closure(closure_value, args, 8);
    }
    hop_check_ordinary_arity(closure, 8);
    hop_value *env = hop_closure_env(closure);
    switch (hop_closure_env_count(closure)) {
    case 0:
        return ((hop_fun_0_8)hop_closure_code(closure))(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7);
    default:
        hop_panic("unsupported closure env count for hop_call_8");
    }
}

hop_value hop_tail_call_0(hop_value closure_value) {
    return hop_call_0(closure_value);
}

hop_value hop_tail_call_1(hop_value arg0, hop_value closure_value) {
    return hop_call_1(arg0, closure_value);
}

hop_value hop_tail_call_2(hop_value arg0, hop_value arg1, hop_value closure_value) {
    return hop_call_2(arg0, arg1, closure_value);
}

hop_value hop_tail_call_3(hop_value arg0,
                          hop_value arg1,
                          hop_value arg2,
                          hop_value closure_value) {
    return hop_call_3(arg0, arg1, arg2, closure_value);
}

hop_value hop_tail_call_4(hop_value arg0,
                          hop_value arg1,
                          hop_value arg2,
                          hop_value arg3,
                          hop_value closure_value) {
    return hop_call_4(arg0, arg1, arg2, arg3, closure_value);
}

hop_value hop_tail_call_5(hop_value arg0,
                          hop_value arg1,
                          hop_value arg2,
                          hop_value arg3,
                          hop_value arg4,
                          hop_value closure_value) {
    return hop_call_5(arg0, arg1, arg2, arg3, arg4, closure_value);
}

hop_value hop_tail_call_6(hop_value arg0,
                          hop_value arg1,
                          hop_value arg2,
                          hop_value arg3,
                          hop_value arg4,
                          hop_value arg5,
                          hop_value closure_value) {
    return hop_call_6(arg0, arg1, arg2, arg3, arg4, arg5, closure_value);
}

hop_value hop_tail_call_7(hop_value arg0,
                          hop_value arg1,
                          hop_value arg2,
                          hop_value arg3,
                          hop_value arg4,
                          hop_value arg5,
                          hop_value arg6,
                          hop_value closure_value) {
    return hop_call_7(arg0, arg1, arg2, arg3, arg4, arg5, arg6, closure_value);
}

hop_value hop_tail_call_8(hop_value arg0,
                          hop_value arg1,
                          hop_value arg2,
                          hop_value arg3,
                          hop_value arg4,
                          hop_value arg5,
                          hop_value arg6,
                          hop_value arg7,
                          hop_value closure_value) {
    return hop_call_8(arg0, arg1, arg2, arg3, arg4, arg5, arg6, arg7, closure_value);
}

/*
 * apply's spread argument count is only known once list_arg is walked here
 * at run time -- even when its target closure is statically known at the
 * call site, the compiler can never resolve apply to a fixed-argc direct
 * call, so it always lowers to this single fixed-signature entry point
 * (see (hop pass cfa) and (hop pass tac)). leading_list holds any leading
 * fixed arguments, already consed into an ordinary list by the compiler at
 * the call site; list_arg is apply's final, user-supplied argument and
 * must be a proper list.
 */
hop_value hop_apply(hop_value closure_value, hop_value leading_list, hop_value list_arg) {
    hop_value *closure;
    int64_t argc, k, env_count, i;
    void *code;
    hop_value cursor;
    hop_value rest;

    /*
     * Flatten leading_list ++ list_arg into the rooted scratch buffer.
     * Walking allocates nothing (hop_car/hop_cdr never call
     * hop_alloc_words), so no GC safepoint occurs during this loop and
     * nothing needs protecting yet.
     */
    hop_temp_variadic_roots[0] = closure_value;
    argc = 0;
    cursor = leading_list;
    while (cursor != HOP_NULL) {
        if (!hop_has_tag(cursor, HOP_PAIR_TAG)) {
            hop_panic("apply: internal leading-argument list is malformed");
        }
        if (argc > HOP_MAX_VARIADIC_ARGS - 3) {
            hop_panic("apply: too many spread arguments");
        }
        hop_temp_variadic_roots[1 + argc] = hop_car(cursor);
        argc += 1;
        cursor = hop_cdr(cursor);
    }
    cursor = list_arg;
    while (cursor != HOP_NULL) {
        if (!hop_has_tag(cursor, HOP_PAIR_TAG)) {
            hop_panic("apply: last argument is not a proper list");
        }
        if (argc > HOP_MAX_VARIADIC_ARGS - 3) {
            hop_panic("apply: too many spread arguments");
        }
        hop_temp_variadic_roots[1 + argc] = hop_car(cursor);
        argc += 1;
        cursor = hop_cdr(cursor);
    }

    closure = hop_as_closure(hop_temp_variadic_roots[0]);

    if (!hop_closure_is_variadic(closure)) {
        /* Every closure now carries its declared exact/minimum arity (see
         * hop_closure_arity), so validate it here exactly like hop_call_N
         * does for its own indirect call sites, instead of silently
         * invoking the underlying function with the wrong number of
         * arguments. */
        hop_check_ordinary_arity(closure, argc);
        env_count = hop_closure_env_count(closure);
        code = hop_closure_code(closure);
        return hop_dispatch_flat_call(code, env_count, hop_closure_env(closure),
                                      hop_temp_variadic_roots + 1, argc);
    }

    k = hop_closure_variadic_k(closure);
    if (argc < k) {
        hop_panic("apply: too few arguments for variadic procedure");
    }
    if (k + 1 > 8) {
        hop_panic("procedure has too many fixed parameters for indirect variadic dispatch");
    }

    rest = HOP_NULL;
    hop_temp_variadic_roots[1 + argc] = rest;
    for (i = argc - 1; i >= k; i--) {
        hop_value *pair = hop_alloc_words(3, hop_temp_variadic_roots, (size_t)(argc + 2));
        pair[0] = (hop_value)hop_make_header(HOP_OBJ_PAIR, 0);
        pair[1] = hop_temp_variadic_roots[1 + i];
        pair[2] = hop_temp_variadic_roots[1 + argc];
        rest = hop_tag_pointer(pair, HOP_PAIR_TAG);
        hop_temp_variadic_roots[1 + argc] = rest;
    }

    closure = hop_as_closure(hop_temp_variadic_roots[0]);
    env_count = hop_closure_env_count(closure);
    code = hop_closure_code(closure);
    {
        hop_value fixed_and_rest[9];
        for (i = 0; i < k; i++) {
            fixed_and_rest[i] = hop_temp_variadic_roots[1 + i];
        }
        fixed_and_rest[k] = hop_temp_variadic_roots[1 + argc];
        return hop_dispatch_flat_call(code, env_count, hop_closure_env(closure), fixed_and_rest, k + 1);
    }
}

const char *hop_symbol_name(hop_value value) {
    uint64_t index;

    if (!hop_has_tag(value, HOP_SYMBOL_TAG)) {
        hop_panic("hop_symbol_name expected symbol");
    }
    index = hop_decode_symbol(value);
    if (index >= hop_symbol_count) {
        hop_panic("symbol index out of range");
    }
    return hop_symbol_names[index];
}

hop_value hop_global_ref(uint64_t index) {
    if (index >= hop_global_slot_count) {
        hop_panic("global index out of range");
    }
    if (hop_global_slots[index] == HOP_UNINITIALIZED) {
        hop_panic("read of uninitialized global");
    }
    return hop_global_slots[index];
}

hop_value hop_global_set(uint64_t index, hop_value value) {
    if (index >= hop_global_slot_count) {
        hop_panic("global index out of range");
    }
    hop_global_slots[index] = value;
    return value;
}
