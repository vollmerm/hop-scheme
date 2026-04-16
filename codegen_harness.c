#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern int64_t scheme_entry(void);

int main(int argc, char **argv) {
    int64_t result = scheme_entry();
    if (argc > 1) {
        int64_t expected = strtoll(argv[1], NULL, 10);
        if (result != expected) {
            fprintf(stderr, "expected %lld but got %lld\n",
                    (long long)expected,
                    (long long)result);
            return 1;
        }
    }
    printf("%lld\n", (long long)result);
    return 0;
}
