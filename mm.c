/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* bu username : eg. jappavoo */
    "gheyrich",
    /* full name : eg. jonathan appavoo */
    "Griffin Heyrich",
    /* email address : jappavoo@bu.edu */
    "gheyrich@bu.edu",
    "",
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//basic macros and constants
#define WSIZE 4 //word for header and footer size in bytes
#define DSIZE 8 //double word size for alignment
#define CHUNKSIZE (1<<12) //extend heap by this amount

#define MAX(x,y) ((x) > (y) ? (x): (y)) 

#define PACK(size, alloc) ((size)|(alloc)) //pack size and allocates bit into a word 

//read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) ((*unsigned int *)(p) = val)

//read size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

//given block ptr bp compute address of its header and footer
#define HDRP(bp) ((char*)(bp) - WSIZE)
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp) - DSIZE)

//given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((*char)(bp) + GET_SIZE(HDRP))
#define PREV_BLKP(bp) ((*char)(bp) + GET_SIZE(((chat *)(bp)- DSIZE)))


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    //create the intial empty heap 
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp,0); //alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); //prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); //prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); //epilogue header
    heap_listp += (2*WSIZE);

    //extend the heap with free block of CHUNCKSIZE bytes
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}


static void *extend_heap(size_t words){
    char *bp;
    size_t size;

//alloc an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words *WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    //initialize free block header anmd footer and the epilogue header
    PUT(HDRP(bp), PACK(size,0)); //free block header
    PUT(FTRP(bp), PACK(size,0)); //free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); //new epilogue header

    return coalesce(bp); //coalesce if the prev block was free 
}




/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














