#ifndef HOP_RUNTIME_H
#define HOP_RUNTIME_H

#include <stdint.h>

typedef int64_t hop_value;

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
