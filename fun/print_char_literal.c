#include <stdio.h>
#include <stdint.h>

extern char get_char_literal();

int main() {
    char lit = get_char_literal();
    printf("%c\n", lit);
}