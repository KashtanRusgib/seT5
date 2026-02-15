#include <stdio.h>
#include "include/ternary.h"

int main() {
    trit_word w;
    int_to_trit_word(100, w);
    printf("100 -> trit_word: ");
    for(int i=0; i<WORD_SIZE; i++) printf("%d ", w[i]);
    printf("\n");
    printf("trit_word_to_int: %d\n", trit_word_to_int(w));
    
    int_to_trit_word(10, w);
    printf("10 -> trit_word: ");
    for(int i=0; i<WORD_SIZE; i++) printf("%d ", w[i]);
    printf("\n");
    printf("trit_word_to_int: %d\n", trit_word_to_int(w));
    
    return 0;
}
