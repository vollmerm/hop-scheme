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
    HOP_OBJ_CLOSURE = 3
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
        return 2 + (size_t)hop_header_aux(header);
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
        !hop_has_tag(value, HOP_CLOSURE_TAG)) {
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
            for (index = 0; index < (size_t)hop_header_aux(header); index += 1) {
                object[2 + index] = hop_copy_value(object[2 + index]);
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

static hop_value *hop_alloc_closure_raw(void *code, int64_t env_count) {
    hop_value *closure = hop_alloc_words(2 + (size_t)env_count, NULL, 0);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, (hop_word)env_count);
    closure[1] = (hop_value)(uintptr_t)code;
    return closure;
}

static hop_value *hop_as_closure(hop_value closure_value) {
    hop_value *closure =
        hop_expect_pointer_tag(closure_value, HOP_CLOSURE_TAG, "call expected closure");
    hop_expect_object_type(closure, HOP_OBJ_CLOSURE, "call expected closure");
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

hop_value hop_alloc_closure_0(void *code) {
    return hop_tag_pointer(hop_alloc_closure_raw(code, 0), HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_1(void *code, hop_value env0) {
    hop_value roots[1];
    hop_value *closure;

    /* Code pointers are not GC-managed; only the captured Scheme values move. */
    roots[0] = env0;
    closure = hop_alloc_words(3, roots, 1);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, 1);
    closure[1] = (hop_value)(uintptr_t)code;
    hop_closure_env(closure)[0] = roots[0];
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_2(void *code, hop_value env0, hop_value env1) {
    hop_value roots[2];
    hop_value *closure;

    roots[0] = env0;
    roots[1] = env1;
    closure = hop_alloc_words(4, roots, 2);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, 2);
    closure[1] = (hop_value)(uintptr_t)code;
    hop_closure_env(closure)[0] = roots[0];
    hop_closure_env(closure)[1] = roots[1];
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_3(void *code, hop_value env0, hop_value env1, hop_value env2) {
    hop_value roots[3];
    hop_value *closure;

    roots[0] = env0;
    roots[1] = env1;
    roots[2] = env2;
    closure = hop_alloc_words(5, roots, 3);
    closure[0] = (hop_value)hop_make_header(HOP_OBJ_CLOSURE, 3);
    closure[1] = (hop_value)(uintptr_t)code;
    hop_closure_env(closure)[0] = roots[0];
    hop_closure_env(closure)[1] = roots[1];
    hop_closure_env(closure)[2] = roots[2];
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

typedef hop_value (*hop_fun_0_0)(void);
typedef hop_value (*hop_fun_0_1)(hop_value);
typedef hop_value (*hop_fun_0_2)(hop_value, hop_value);
typedef hop_value (*hop_fun_0_3)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_0)(hop_value);
typedef hop_value (*hop_fun_1_1)(hop_value, hop_value);
typedef hop_value (*hop_fun_1_2)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_1_3)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_0)(hop_value, hop_value);
typedef hop_value (*hop_fun_2_1)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_2)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_2_3)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_0)(hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_1)(hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_2)(hop_value, hop_value, hop_value, hop_value, hop_value);
typedef hop_value (*hop_fun_3_3)(hop_value, hop_value, hop_value, hop_value, hop_value, hop_value);

hop_value hop_call_0(hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
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
    default:
        hop_panic("unsupported closure env count for hop_call_0");
    }
}

hop_value hop_call_1(hop_value arg0, hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
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
    default:
        hop_panic("unsupported closure env count for hop_call_1");
    }
}

hop_value hop_call_2(hop_value arg0, hop_value arg1, hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
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
    default:
        hop_panic("unsupported closure env count for hop_call_2");
    }
}

hop_value hop_call_3(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value closure_value) {
    hop_value *closure = hop_as_closure(closure_value);
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
    default:
        hop_panic("unsupported closure env count for hop_call_3");
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
