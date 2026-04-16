#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef int64_t hop_value;

typedef struct {
    void *code;
    int64_t env_count;
    hop_value env[];
} hop_closure;

__attribute__((noreturn)) static void hop_panic(const char *message) {
    fprintf(stderr, "%s\n", message);
    exit(1);
}

hop_value *hop_alloc_box(hop_value value) {
    hop_value *box = (hop_value *)malloc(sizeof(hop_value));
    if (!box) {
        hop_panic("box allocation failed");
    }
    *box = value;
    return box;
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

hop_closure *hop_alloc_closure_0(void *code) {
    return hop_alloc_closure_raw(code, 0);
}

hop_closure *hop_alloc_closure_1(void *code, hop_value env0) {
    hop_closure *closure = hop_alloc_closure_raw(code, 1);
    closure->env[0] = env0;
    return closure;
}

hop_closure *hop_alloc_closure_2(void *code, hop_value env0, hop_value env1) {
    hop_closure *closure = hop_alloc_closure_raw(code, 2);
    closure->env[0] = env0;
    closure->env[1] = env1;
    return closure;
}

hop_closure *hop_alloc_closure_3(void *code, hop_value env0, hop_value env1, hop_value env2) {
    hop_closure *closure = hop_alloc_closure_raw(code, 3);
    closure->env[0] = env0;
    closure->env[1] = env1;
    closure->env[2] = env2;
    return closure;
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

hop_value hop_call_0(hop_closure *closure) {
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

hop_value hop_call_1(hop_value arg0, hop_closure *closure) {
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

hop_value hop_call_2(hop_value arg0, hop_value arg1, hop_closure *closure) {
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

hop_value hop_call_3(hop_value arg0, hop_value arg1, hop_value arg2, hop_closure *closure) {
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

hop_value hop_tail_call_0(hop_closure *closure) {
    return hop_call_0(closure);
}

hop_value hop_tail_call_1(hop_value arg0, hop_closure *closure) {
    return hop_call_1(arg0, closure);
}

hop_value hop_tail_call_2(hop_value arg0, hop_value arg1, hop_closure *closure) {
    return hop_call_2(arg0, arg1, closure);
}

hop_value hop_tail_call_3(hop_value arg0, hop_value arg1, hop_value arg2, hop_closure *closure) {
    return hop_call_3(arg0, arg1, arg2, closure);
}
