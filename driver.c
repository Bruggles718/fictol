#include <stdio.h>
#include <stdint.h>

extern int64_t test_entry();

int main() {
    int64_t result = test_entry();
    printf("%ld\n", result);
}