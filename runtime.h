#ifndef HOP_RUNTIME_H
#define HOP_RUNTIME_H

#include <stdint.h>

typedef int64_t hop_value;

#define HOP_FIXNUM_SHIFT 3
#define HOP_TAG_MASK 7

#define HOP_PAIR_TAG 1
#define HOP_BOX_TAG 2
#define HOP_CLOSURE_TAG 3

#define HOP_NULL 20
#define HOP_FALSE 36
#define HOP_TRUE 52

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

#endif
