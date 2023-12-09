#include "mm.h"
 main(){
    mm_init();
    long*p = (long*)mm_malloc(8);
    free(p);
    p = (long*)mm_malloc(8);
}