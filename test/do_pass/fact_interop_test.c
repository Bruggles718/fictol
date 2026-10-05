#include <stdio.h>
#include <stdint.h>

extern int fact(int);
extern int fact_tail(int);

extern int64_t summorial(int64_t);
extern int64_t summorial_tail(int64_t);

int main() {
    int result = fact(5);
    int result_tail = fact_tail(5);
    printf("result1: %d, result2: %d\n", result, result_tail);

    int64_t sum_res = summorial_tail(1000000);
    printf("sum_result: %ld\n", sum_res);
    return 0;
}