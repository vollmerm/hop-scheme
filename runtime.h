#ifndef HOP_RUNTIME_H
#define HOP_RUNTIME_H

#include <stdint.h>

typedef int64_t hop_value;

typedef struct {
    uint64_t frame_slots;
    uint64_t stack_size;
} hop_gc_frame_desc;

/*
 * Runtime value representation
 * ----------------------------
 *
 * Every Scheme value is carried in a 64-bit hop_value. The runtime uses the
 * low three bits as a tag:
 *
 *   xxx...xxx000  fixnum immediate
 *   ptr......001  pair pointer
 *   ptr......010  box pointer
 *   ptr......011  closure pointer
 *
 * Fixnums are stored by shifting the signed integer left by
 * HOP_FIXNUM_SHIFT. Heap objects are allocated at aligned addresses, so their
 * low tag bits are available; hop_tag_pointer installs the object tag and
 * hop_untag_pointer removes it before dereferencing.
 *
 * Some values are represented as tagged immediates rather than pointers:
 *
 *   HOP_NULL   = ()
 *   HOP_FALSE  = #f
 *   HOP_TRUE   = #t
 *
 * Conditionals treat only HOP_FALSE as false. HOP_NULL and HOP_TRUE are both
 * truthy, and all tagged pointers and fixnums are truthy as well.
 */
#define HOP_FIXNUM_SHIFT 3
#define HOP_TAG_MASK 7

#define HOP_PAIR_TAG 1
#define HOP_BOX_TAG 2
#define HOP_CLOSURE_TAG 3

#define HOP_NULL 20
#define HOP_FALSE 36
#define HOP_TRUE 52
#define HOP_UNINITIALIZED 68

static inline hop_value hop_encode_fixnum(int64_t value) {
    return (hop_value)(value << HOP_FIXNUM_SHIFT);
}

static inline int64_t hop_decode_fixnum(hop_value value) {
    return value >> HOP_FIXNUM_SHIFT;
}

static inline int hop_is_fixnum(hop_value value) {
    return (value & HOP_TAG_MASK) == 0;
}

static inline int hop_has_tag(hop_value value, int64_t tag) {
    return (value & HOP_TAG_MASK) == tag;
}

static inline hop_value hop_tag_pointer(void *ptr, int64_t tag) {
    return (hop_value)((uintptr_t)ptr | (uintptr_t)tag);
}

static inline void *hop_untag_pointer(hop_value value) {
    return (void *)((uintptr_t)value & ~((uintptr_t)HOP_TAG_MASK));
}

extern void *hop_gc_top_frame;
extern uint64_t hop_global_slot_count;
extern hop_value hop_global_slots[];

hop_value hop_alloc_box(hop_value value);
hop_value hop_alloc_pair(hop_value car, hop_value cdr);
hop_value hop_car(hop_value pair_value);
hop_value hop_cdr(hop_value pair_value);
hop_value hop_alloc_closure_0(void *code);
hop_value hop_alloc_closure_1(void *code, hop_value env0);
hop_value hop_alloc_closure_2(void *code, hop_value env0, hop_value env1);
hop_value hop_alloc_closure_3(void *code, hop_value env0, hop_value env1, hop_value env2);
hop_value hop_alloc_closure_n(void *code, int64_t count, hop_value *envs);
hop_value hop_call_0(hop_value closure_value);
hop_value hop_call_1(hop_value arg0, hop_value closure_value);
hop_value hop_call_2(hop_value arg0, hop_value arg1, hop_value closure_value);
hop_value hop_call_3(hop_value arg0, hop_value arg1, hop_value arg2, hop_value closure_value);
hop_value hop_call_4(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value closure_value);
hop_value hop_call_5(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value closure_value);
hop_value hop_call_6(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value arg5, hop_value closure_value);
hop_value hop_call_7(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value arg5, hop_value arg6, hop_value closure_value);
hop_value hop_call_8(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value arg5, hop_value arg6, hop_value arg7, hop_value closure_value);
hop_value hop_tail_call_0(hop_value closure_value);
hop_value hop_tail_call_1(hop_value arg0, hop_value closure_value);
hop_value hop_tail_call_2(hop_value arg0, hop_value arg1, hop_value closure_value);
hop_value hop_tail_call_3(hop_value arg0, hop_value arg1, hop_value arg2, hop_value closure_value);
hop_value hop_tail_call_4(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value closure_value);
hop_value hop_tail_call_5(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value closure_value);
hop_value hop_tail_call_6(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value arg5, hop_value closure_value);
hop_value hop_tail_call_7(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value arg5, hop_value arg6, hop_value closure_value);
hop_value hop_tail_call_8(hop_value arg0, hop_value arg1, hop_value arg2, hop_value arg3, hop_value arg4, hop_value arg5, hop_value arg6, hop_value arg7, hop_value closure_value);
hop_value hop_global_ref(uint64_t index);
hop_value hop_global_set(uint64_t index, hop_value value);

hop_value hop_safe_add(hop_value a, hop_value b);
hop_value hop_safe_sub(hop_value a, hop_value b);
hop_value hop_safe_mul(hop_value a, hop_value b);
hop_value hop_safe_eq (hop_value a, hop_value b);
hop_value hop_safe_lt (hop_value a, hop_value b);
hop_value hop_safe_gt (hop_value a, hop_value b);

#endif
