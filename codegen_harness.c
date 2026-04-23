#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runtime.h"

extern hop_value scheme_entry(void);

static void hop_format_value(char *buffer, size_t size, hop_value value) {
    if (hop_is_fixnum(value)) {
        snprintf(buffer, size, "%lld", (long long)hop_decode_fixnum(value));
    } else if (value == HOP_TRUE) {
        snprintf(buffer, size, "#t");
    } else if (value == HOP_FALSE) {
        snprintf(buffer, size, "#f");
    } else if (value == HOP_NULL) {
        snprintf(buffer, size, "()");
    } else if (value == HOP_UNINITIALIZED) {
        snprintf(buffer, size, "#<uninitialized>");
    } else if (hop_has_tag(value, HOP_PAIR_TAG)) {
        snprintf(buffer, size, "#<pair>");
    } else if (hop_has_tag(value, HOP_BOX_TAG)) {
        snprintf(buffer, size, "#<box>");
    } else if (hop_has_tag(value, HOP_CLOSURE_TAG)) {
        snprintf(buffer, size, "#<closure>");
    } else {
        snprintf(buffer, size, "#<value:%lld>", (long long)value);
    }
}

int main(int argc, char **argv) {
    hop_value result = scheme_entry();
    char rendered[64];

    hop_format_value(rendered, sizeof(rendered), result);
    if (argc > 1) {
        if (strcmp(rendered, argv[1]) != 0) {
            fprintf(stderr, "expected %s but got %s\n", argv[1], rendered);
            return 1;
        }
    }
    printf("%s\n", rendered);
    return 0;
}
