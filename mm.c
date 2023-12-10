/*
 * mm.c
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
# define dbg_print_heap(...) print_heap(__VA_ARGS__)
#else
# define dbg_printf(...)
# define dbg_print_heap(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 
#define WSIZE 4 /*word size*/
#define DSIZE 8 
#define CHUNKSIZE  (1<<12)
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    
#define PUTW(p, val) (*(unsigned long *)(p) = (val))
/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 
/*Given free block ptr bp,  relative address of next and previous blocks in stack*/
#define GET_PREV(bp)  (*(int*)(bp) + stack_root) 
#define GET_NEXT(bp)  (*(int*)((char*)(bp) + WSIZE) + stack_root)
#define PUT_PREV(bp, pp)  (*(int*)(bp) = (char*)(pp) - stack_root) 
#define PUT_NEXT(bp, np)  (*(int*)((char*)(bp) + WSIZE) = (char*)(np) - stack_root)
#define GET_TOP(np) (*(int*)(stack_top + (unsigned int)(np)*WSIZE) + stack_root)
#define SET_TOP(bp, np) (*(int*)(stack_top + (unsigned int)(np)*WSIZE) = (char*)(bp) - stack_root)
/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void add_stack(void *bp);
static void delete_stack(void *bp);
static void print_heap();
static unsigned int get_index(unsigned int asize);
/* Global variables */
/*
 * Initialize: return -1 on error, 0 on success.
 */
static char *heap_listp = NULL; /* Pointer to first block*/ 
static char *stack_top = NULL; /* Pointer to first free block*/ 
static char *stack_root = NULL;
static unsigned int stack_size;
#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif
#define STACK_MIN (7)
#define STACK_MAX (10)
int mm_init(void) {
    /* Create the initial empty heap */
    stack_size = STACK_MAX + (1<<STACK_MIN);
    stack_root = mem_sbrk(0);
    if ((stack_top = mem_sbrk(stack_size*WSIZE)) == (void *)-1)//指针数组，存放各个栈顶的地址
        return -1;
    memset(stack_top, 0, stack_size*WSIZE);
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1) 
        return -1;
    PUT(heap_listp, PACK(0, 1));                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE),0);
    PUT(heap_listp + (2*WSIZE),0);
    PUT(heap_listp + (3*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (4*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));     /* Epilogue header */
    stack_root = heap_listp + WSIZE;
    heap_listp += (4*WSIZE);
     
#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    dbg_printf("malloc %d\n",size);   
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)                                          
        asize = 2*DSIZE;                                        
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
        place(bp, asize);      
        dbg_print_heap();           
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);                 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);   
    dbg_print_heap();              
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    dbg_printf("free %p\n",ptr);
    if (ptr == 0) 
        return;
    size_t size = GET_SIZE(HDRP(ptr));
    if (heap_listp == NULL){
        mm_init();
    }
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT_NEXT(ptr,NULL);
    PUT_PREV(ptr,NULL);
    coalesce(ptr);
    dbg_print_heap();
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    dbg_printf("realloc %d\n",size);
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(oldptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    mm_free(oldptr);
    dbg_print_heap();
    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    dbg_printf("calloc %d\n",size);
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    dbg_print_heap();
    return newptr;
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno) {
    int consist=0;
    for(char* i=heap_listp;GET_SIZE(HDRP(i))>0;i=NEXT_BLKP(i)){
        if(GET_ALLOC(HDRP(i))==1)consist=0;
        else if(consist==1){
            printf("EHAT DE HELL\n");
            exit(-1);
        }
        else consist=1;
        if(HDRP(i)!=FTRP(i)){
            printf("what de hell is that!");
            exit(-1);
        }
    }
    lineno = lineno; /* keep gcc happy */
}
/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if(size <= 2*DSIZE)size= 2*DSIZE;//显式空闲链表前后继
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        delete_stack(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        delete_stack(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        delete_stack(PREV_BLKP(bp));
        delete_stack(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
        rover = bp;
#endif
    add_stack(bp);
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   
    delete_stack(bp);
    if ((csize - asize) >= (2*DSIZE)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);

    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;
    unsigned int index = get_index(asize);
    for(unsigned int i=index;i<stack_size;i++){
        for (bp = GET_TOP(i); bp!=stack_root; bp = GET_PREV(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                return bp;
            }
        }
    }
    return NULL; /* No fit */
}
static void add_stack(void *bp){
    int index = get_index(GET_SIZE(HDRP(bp)));
    char* top_blk=GET_TOP(index);
    if(top_blk==stack_root){
        SET_TOP(bp,index);
        PUT_PREV(bp,top_blk);
        PUT_NEXT(bp, NULL);
    }
    else{
        PUT_NEXT(top_blk,bp);
        PUT_PREV(bp,top_blk);
        PUT_NEXT(bp,NULL);
        SET_TOP(bp,index);
    }
}
static void delete_stack(void *bp){
    int index = get_index(GET_SIZE(HDRP(bp)));
    char* top_blk=GET_TOP(index);
    if(bp==top_blk){
        char* prev_blk=GET_PREV(bp);
        SET_TOP(prev_blk,index);
        PUT_NEXT(prev_blk,NULL);
    }
    else{
        char* next_block=GET_NEXT(bp);
        char* prev_block=GET_PREV(bp);
        PUT_NEXT(prev_block,next_block);
        if(next_block)
            PUT_PREV(next_block,prev_block);   
    }
}
static void print_heap(){
    printf("***\n");
    for(char* i=heap_listp;GET_SIZE(HDRP(i))>0;i=NEXT_BLKP(i)){
        unsigned int alloc = GET_ALLOC(HDRP(i));
        unsigned int size = GET_SIZE(HDRP(i));
        char* next_blk=NEXT_BLKP(i);
        char* prev_blk=PREV_BLKP(i);
        printf("%p %u %u %p %p\n",i,alloc,size,prev_blk,next_blk);
    }
    printf("&&&\n");
    for(unsigned int i=0;i<stack_size;i++){
        printf("%u:",i);
        char* bp = GET_TOP(i);
        for (; bp!=stack_root; bp = GET_PREV(bp)) {
            unsigned int alloc = GET_ALLOC(HDRP(bp));
            unsigned int size = GET_SIZE(HDRP(bp));
            char* next_blk=GET_NEXT(bp);
            char* prev_blk=GET_PREV(bp);
            printf("%p %u %u %p %p\n",bp,alloc,size,prev_blk,next_blk);
        }
    }
    return NULL; /* No fit */
}
static unsigned int get_index(unsigned int asize){
    unsigned int max_size=1<<STACK_MIN;
    if(asize<=max_size)
        return asize-1;
    else{
        for(int i=0;i<STACK_MAX;i++){
            max_size<<=1;
            if(asize<=max_size){
                return (1<<STACK_MIN) + i;
            }
        }
        return (1<<STACK_MIN) + STACK_MAX - 1;
    }
}