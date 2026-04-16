#include <stdio.h>
#include <stdlib.h>
#include "runtime.h"

typedef struct {
    void *code;
    int64_t env_count;
    hop_value env[];
} hop_closure;

typedef struct {
    hop_value car;
    hop_value cdr;
} hop_pair;

__attribute__((noreturn)) static void hop_panic(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(1);
}

static void *hop_expect_pointer_tag(hop_value value, int64_t tag, const char *message) {
    if (!hop_has_tag(value, tag)) {
        hop_panic(message);
    }
    return hop_untag_pointer(value);
}

hop_value hop_alloc_box(hop_value value) {
    hop_value *box = (hop_value *)malloc(sizeof(hop_value));
    if (!box) {
        hop_panic("box allocation failed");
    }
    *box = value;
    return hop_tag_pointer(box, HOP_BOX_TAG);
}

hop_value hop_alloc_pair(hop_value car, hop_value cdr) {
    hop_pair *pair = (hop_pair *)malloc(sizeof(hop_pair));
    if (!pair) {
        hop_panic("pair allocation failed");
    }
    pair->car = car;
    pair->cdr = cdr;
    return hop_tag_pointer(pair, HOP_PAIR_TAG);
}

hop_value hop_car(hop_value pair_value) {
    hop_pair *pair =
        (hop_pair *)hop_expect_pointer_tag(pair_value, HOP_PAIR_TAG, "car expected pair");
    return pair->car;
}

hop_value hop_cdr(hop_value pair_value) {
    hop_pair *pair =
        (hop_pair *)hop_expect_pointer_tag(pair_value, HOP_PAIR_TAG, "cdr expected pair");
    return pair->cdr;
}

static hop_closure *hop_alloc_closure_raw(void *code, int64_t env_count) {
    hop_closure *closure =
        (hop_closure *)malloc(sizeof(hop_closure) + sizeof(hop_value) * env_count);
    if (!closure) {
        hop_panic("closure allocation failed");
    }
    closure->code = code;
    closure->env_count = env_count;
    return closure;
}

static hop_closure *hop_as_closure(hop_value closure_value) {
    return (hop_closure *)hop_expect_pointer_tag(closure_value,
                                                 HOP_CLOSURE_TAG,
                                                 "call expected closure");
}

hop_value hop_alloc_closure_0(void *code) {
    return hop_tag_pointer(hop_alloc_closure_raw(code, 0), HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_1(void *code, hop_value env0) {
    hop_closure *closure = hop_alloc_closure_raw(code, 1);
    closure->env[0] = env0;
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_2(void *code, hop_value env0, hop_value env1) {
    hop_closure *closure = hop_alloc_closure_raw(code, 2);
    closure->env[0] = env0;
    closure->env[1] = env1;
    return hop_tag_pointer(closure, HOP_CLOSURE_TAG);
}

hop_value hop_alloc_closure_3(void *code, hop_value env0, hop_value env1, hop_value env2) {
    hop_closure *closure = hop_alloc_closure_raw(code, 3);
    closure->env[0] = env0;
    closure->env[1] = env1;
    closure->env[2] = env2;
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
    hop_closure *closure = hop_as_closure(closure_value);
    switch (closure->env_count) {
    case 0:
        return ((hop_fun_0_0)closure->code)();
    case 1:
        return ((hop_fun_1_0)closure->code)(closure->env[0]);
    case 2:
        return ((hop_fun_2_0)closure->code)(closure->env[0], closure->env[1]);
    case 3:
        return ((hop_fun_3_0)closure->code)(closure->env[0], closure->env[1], closure->env[2]);
    default:
        hop_panic("unsupported closure env count for hop_call_0");
    }
}

hop_value hop_call_1(hop_value arg0, hop_value closure_value) {
    hop_closure *closure = hop_as_closure(closure_value);
    switch (closure->env_count) {
    case 0:
        return ((hop_fun_0_1)closure->code)(arg0);
    case 1:
        return ((hop_fun_1_1)closure->code)(closure->env[0], arg0);
    case 2:
        return ((hop_fun_2_1)closure->code)(closure->env[0], closure->env[1], arg0);
    case 3:
        return ((hop_fun_3_1)closure->code)(closure->env[0], closure->env[1], closure->env[2], arg0);
    default:
        hop_panic("unsupported closure env count for hop_call_1");
    }
}

hop_value hop_call_2(hop_value arg0, hop_value arg1, hop_value closure_value) {
    hop_closure *closure = hop_as_closure(closure_value);
    switch (closure->env_count) {
    case 0:
        return ((hop_fun_0_2)closure->code)(arg0, arg1);
    case 1:
        return ((hop_fun_1_2)closure->code)(closure->env[0], arg0, arg1);
    case 2:
        return ((hop_fun_2_2)closure->code)(closure->env[0], closure->env[1], arg0, arg1);
    case 3:
        return ((hop_fun_3_2)closure->code)(closure->env[0], closure->env[1], closure->env[2], arg0, arg1);
    default:
        hop_panic("unsupported closure env count for hop_call_2");
    }
}

hop_value hop_call_3(hop_value arg0,
                     hop_value arg1,
                     hop_value arg2,
                     hop_value closure_value) {
    hop_closure *closure = hop_as_closure(closure_value);
    switch (closure->env_count) {
    case 0:
        return ((hop_fun_0_3)closure->code)(arg0, arg1, arg2);
    case 1:
        return ((hop_fun_1_3)closure->code)(closure->env[0], arg0, arg1, arg2);
    case 2:
        return ((hop_fun_2_3)closure->code)(closure->env[0], closure->env[1], arg0, arg1, arg2);
    case 3:
        return ((hop_fun_3_3)closure->code)(closure->env[0], closure->env[1], closure->env[2], arg0, arg1, arg2);
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
