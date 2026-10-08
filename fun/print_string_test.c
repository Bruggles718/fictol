#include <stdio.h>
#include <stdint.h>

extern char* get_str_literal();

int main() {
    char* lit = get_str_literal();
    printf("%s", lit);
}