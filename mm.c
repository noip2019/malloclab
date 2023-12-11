/*
 * mm.c
 * 使用了分离适配方法，1~(1<<STACK_MIN)单独分组，（1<<STACK_MIN)+1 ~ (1<<STACK_MAX)按2的幂分组，采用首次适配的策略
 * 由于大小不超过2^32,故使用WSIZE存储地址偏移
 * 去掉了已分配块的尾部
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
#define CHUNKSIZE  (1<<13)
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
#define GET_PREV_FREE(p) (GET(((char*)(p)-WSIZE)) & 0x2) //去尾部专用
#define SET_PREV_FREE(p) (GET(((char*)(p)-WSIZE)) |= 0x2) //去尾部专用
#define RM_PREV_FREE(p) (GET(((char*)(p)-WSIZE)) &= ~0x2) //去尾部专用
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 
/*Given free block ptr bp,  relative address of next and previous blocks in stack*/
#define GET_PREV(bp)  (*(int*)(bp) + stack_root) 
#define GET_NEXT(bp)  (*(int*)((char*)(bp) + WSIZE) + stack_root)
/*Given free block ptr bp,  set relative address of next and previous blocks in stack*/
#define PUT_PREV(bp, pp)  (*(int*)(bp) = (char*)(pp) - stack_root) 
#define PUT_NEXT(bp, np)  (*(int*)((char*)(bp) + WSIZE) = (char*)(np) - stack_root)
/*get and set the top block in stack with index np*/
#define GET_TOP(np) (*(int*)(stack_top + (unsigned int)(np)*WSIZE) + stack_root)
#define SET_TOP(bp, np) (*(int*)(stack_top + (unsigned int)(np)*WSIZE) = (char*)(bp) - stack_root)

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
/// @brief 在空闲块中放置分配块并分割
/// @param bp 空闲块
/// @param asize 分配块大小
static void place(void *bp, size_t asize);
/// @brief 发现适合一定大小的空闲块
/// @param asize 给定查找大小
/// @return 发现适合空闲块返回指针，否则返回空指针
static void *find_fit(size_t asize);
/// @brief 合并一个空闲块前后的空闲块
/// @param bp 待合并空闲块
/// @return 返回合并后的空闲块
static void *coalesce(void *bp);
/// @brief 将空闲块加入堆数组中
/// @param bp 待添加的空闲块
static void add_stack(void *bp);
/// @brief 从堆数组中删除空闲块
/// @param bp 待删除空闲块
static void delete_stack(void *bp);
/// @brief debug时用于输出堆中和栈数组中的块信息
static void print_heap();
/// @brief 获取asize对应的栈数组下标
/// @param asize 
/// @return 返回下标
static unsigned int get_index(unsigned int asize);
/* Global variables */
/*
 * Initialize: return -1 on error, 0 on success.
 */
static char *heap_listp = NULL; /* Pointer to first block*/ 
static char *stack_top = NULL; /* array of Pointer to first free block*/ 
static char *stack_root = NULL;/* 所有堆数组的首元素，作NULL使用*/
static unsigned int stack_size;/*堆数组的长度*/
#define STACK_MIN (7) /*精准分配的位数*/
#define STACK_MAX (10) /*按幂分配的位数*/
int mm_init(void) {
    /* Create the initial empty heap */
    stack_size = STACK_MAX + (1<<STACK_MIN);
    stack_root = mem_sbrk(0);
    if ((stack_top = mem_sbrk(stack_size*WSIZE)) == (void *)-1)
        return -1;
    memset(stack_top, 0, stack_size*WSIZE);//为栈数组分配空间，并全部初始化为stack_root
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
        asize = DSIZE * ((size + (WSIZE) + (DSIZE-1)) / DSIZE); 

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
    unsigned int prev_free = GET_PREV_FREE(ptr);
    if (heap_listp == NULL){
        mm_init();
    }
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    if(prev_free)
        SET_PREV_FREE(ptr);
    SET_PREV_FREE(NEXT_BLKP(ptr));
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
    unsigned int prev_alloc=1;
    for(char* i=heap_listp;GET_SIZE(HDRP(i))>0;i=NEXT_BLKP(i)){
        unsigned int alloc = GET_ALLOC(HDRP(i));
        if(prev_alloc==0 && alloc==0)
        {
            printf("fail coaleacing\n");
            exit(-1);
        }
        prev_alloc = alloc;
    }
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
    char* oldbp = mem_sbrk(0);
    int alloc=GET_ALLOC(HDRP(oldbp));
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    if(!alloc)
        SET_PREV_FREE(bp);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    SET_PREV_FREE(NEXT_BLKP(bp));
    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = !GET_PREV_FREE(bp);
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
    if ((csize - asize) >= (2*DSIZE)) { /*分配后还可分割*/
        PUT(HDRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        coalesce(bp);

    }
    else { /*分配后不可分割*/
        PUT(HDRP(bp), PACK(csize, 1));
        RM_PREV_FREE(NEXT_BLKP(bp));
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
                return bp;/*fit*/
            }
        }
    }
    return NULL; /* No fit */
}
static void add_stack(void *bp){
    int index = get_index(GET_SIZE(HDRP(bp)));
    char* top_blk=GET_TOP(index);
    if(top_blk==stack_root){/*如果待添加的栈是空的*/
        SET_TOP(bp,index);
        PUT_PREV(bp,top_blk);
        PUT_NEXT(bp, NULL);
    }
    else{/*如果待添加的栈非空*/
        PUT_NEXT(top_blk,bp);
        PUT_PREV(bp,top_blk);
        PUT_NEXT(bp,NULL);
        SET_TOP(bp,index);
    }
}
static void delete_stack(void *bp){
    int index = get_index(GET_SIZE(HDRP(bp)));
    char* top_blk=GET_TOP(index);
    if(bp==top_blk){/*如果待删除的块是栈顶*/
        char* prev_blk=GET_PREV(bp);
        SET_TOP(prev_blk,index);
        PUT_NEXT(prev_blk,NULL);
    }
    else{/*如果待删除的块不是栈顶*/
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
        unsigned int prev_alloc = GET_PREV_FREE(i)==0;
        char* next_blk=NEXT_BLKP(i);
        char* prev_blk=PREV_BLKP(i);
        printf("%p %u %u %u %p %p\n",i,alloc,size,prev_alloc,prev_blk,next_blk);
    }
    printf("&&&\n");
    for(unsigned int i=0;i<stack_size;i++){
        printf("%u:",i);
        char* bp = GET_TOP(i);
        for (; bp!=stack_root; bp = GET_PREV(bp)) {
            unsigned int alloc = GET_ALLOC(HDRP(bp));
            unsigned int size = GET_SIZE(HDRP(bp));
            unsigned int prev_alloc = GET_PREV_FREE(bp)==0;
            char* next_blk=GET_NEXT(bp);
            char* prev_blk=GET_PREV(bp);
            printf("%p %u %u %u %p %p\n",bp,alloc,size,prev_alloc,prev_blk,next_blk);
        }
    }
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