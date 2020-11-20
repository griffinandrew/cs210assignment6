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

/* Basic constants and macros */ 
#define	WSIZE	4 /* Word and header/footer size (bytes) */ 
#define DSIZE	8 /* Double word size (bytes) */ 
#define CHUNKSIZE (1<<8) /* Extend heap by this amount (bytes) */ //6 with best gives 56 gives higher score //8 with best gives 57
//changing chunk size increases utility

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */ 
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */ 
#define GET(p)		(*(unsigned int *) (p)) 
#define PUT(p, val)	(*(unsigned int *) (p) = (val))

/* Read the size and allocated fields from address p */ 
#define GET_SIZE(p)	(GET (p) & ~0x7) 
#define GET_ALLOC(p)	(GET (p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */ 
#define HDRP(bp)	((char *) (bp) - WSIZE) 
#define FTRP(bp)	((char *) (bp) + GET_SIZE (HDRP (bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */ 
#define NEXT_BLKP(bp)	((char *) (bp) + GET_SIZE(((char *) (bp) - WSIZE))) 
#define PREV_BLKP(bp)	((char *) (bp) - GET_SIZE(((char *) (bp) - DSIZE)))

void *heap_listp;
//void *next_in_heap; // = heap_listp; //used for next fir
int count = 0; //for next fit

int mm_init(void);
static void *extend_heap(size_t words);
void mm_free(void *bp);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
//int mm_check(void);
//void check_blk(void *bp);
//static void show_block(void *bp);

int mm_init(void)
{
	/* Create the initial empty heap */ 
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1; 
	PUT(heap_listp, 0);				/* Alignment padding */ 
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));	/* Prologue header */ 
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));	/* Prologue footer */ 
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));	/* Epilogue header */ 
	heap_listp += (2*WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */ 
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
		return -1; 
	return 0;
}

static void *extend_heap(size_t words)
{
	char *bp; 
	size_t size;

	/* Allocate an even number of words to maintain alignment */ 
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
	if ((long) (bp = mem_sbrk(size)) == -1)
		return NULL;

	/* Initialize free block header/footer and the epilogue header */ 
	PUT(HDRP (bp), PACK(size, 0));			/* Free block header */ 
	PUT(FTRP (bp), PACK(size, 0));			/* Free block footer */ 
	PUT(HDRP (NEXT_BLKP(bp)), PACK(0, 1));		/* New epilogue header */

	/* Coalesce if the previous block was free */ 
	return coalesce(bp);
}

void mm_free(void *bp)
{
	size_t size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size, 0)); 
	PUT(FTRP(bp), PACK(size, 0)); 
	coalesce(bp);
}

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
	size_t size = GET_SIZE(HDRP(bp));

	if(prev_alloc && next_alloc) {			/* Case 1 */
		return bp;
	}

	else if (prev_alloc && ! next_alloc) {		/* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
		PUT(HDRP(bp), PACK(size, 0)); 
		PUT(FTRP(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) {		/* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
		PUT(FTRP(bp), PACK(size, 0)); 
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
		bp = PREV_BLKP(bp);
	}

	else {						/* Case 4 */ 
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); 
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp); 
	} 
	return bp;
}

void *mm_malloc(size_t size)
{
	size_t asize;		/* Adjusted block size */ 
	size_t extendsize;	/* Amount to extend heap if no fit */ 
	char *bp;

//	mm_check();

	/* Ignore spurious requests */ 
	if(size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */ 
	if(size <= DSIZE)
		asize = 2*DSIZE; 
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

	/* Search the free list for a fit */ 
	if((bp = find_fit(asize)) != NULL) {
		//count++;
		place (bp, asize); 
		return bp;
	}

	/* No fit found. Get more memory and place the block */ 
	extendsize = MAX(asize, CHUNKSIZE); 
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
		return NULL; 
	place (bp, asize);
	return bp;
}

static void *find_fit(size_t asize){ 
void *bp;
for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is firsts fit
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL; //not fit 

}
/*
void *bp;
int counter;
void *next_in_heap = heap_listp +count;
for (bp = next_in_heap; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is next
	counter++;
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
			next_in_heap = heap_listp + counter;
            return bp;
        }
    }




	return NULL;
}
*/
/*void *worst = NULL;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is worst fit 
		if(!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp))) >= asize){
			if(worst == NULL){
				worst = bp;
				//if(asize == GET_SIZE(HDRP(best))){
				//	return best;
				//}
			}
			if((worst != NULL) && (GET_SIZE(HDRP(bp))) < GET_SIZE(HDRP(worst))){
				worst = bp;
				//if(asize == GET_SIZE(HDRP(best))){
				//	return best;
				//}
			}

		}
	}
	if(worst!=NULL){
		return worst;
	}
*/

 /*   void *bp;
	void *best = NULL;
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is best fit 
		if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
			if(best == NULL){
				best = bp;
				if(asize == GET_SIZE(HDRP(best))){
					return best;
				}
			}
			if((best != NULL) && (GET_SIZE(HDRP(bp))) > GET_SIZE(HDRP(best))){
				best = bp;
				if(asize == GET_SIZE(HDRP(best))){
					return best;
				}
			}

		}
	}
	if(best!=NULL){
		return best;
	}
*/


	



    /*for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this is firsts fit
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL; //not fit 
	*/



static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else{
        PUT(HDRP(bp),PACK(csize, 1));
        PUT(FTRP(bp),PACK(csize, 1));
    }
}

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
	size_t old_size; //size is payload and header and footer
	size_t asize, next_size, csize;
    

	if(ptr == NULL){
		return mm_malloc(size);
	}

	if(size == 0){
		mm_free(ptr);
		return NULL;
	}
	

	old_size = GET_SIZE(HDRP(oldptr));
	next_size = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));
	//asize = old_size - size;
	//if(asize <= old_size){
	//	return ptr;
	//}
	//csize = size - old_size;
/*
	if(size < old_size){
		PUT(HDRP(oldptr), PACK(size,1));
		PUT(FTRP(oldptr), PACK(size,1));
		old_size = GET_SIZE(HDRP(oldptr));
		asize = old_size - size;
		PUT(HDRP(NEXT_BLKP(oldptr)), PACK(asize, 0));
		PUT(FTRP(NEXT_BLKP(oldptr)), PACK(asize, 0));
		mm_free(NEXT_BLKP(oldptr));
		return NEXT_BLKP(oldptr);
	}
	*/
/*
	else{
		//if (size > old_size){
			if( ((GET_ALLOC(HDRP(NEXT_BLKP(oldptr)))) == 0) 
			&& (old_size + next_size >= size) ){
				PUT(HDRP(oldptr), PACK(size,1));
				PUT(FTRP(oldptr), PACK(size,1));
				old_size = GET_SIZE(HDRP(oldptr));
				csize = size - old_size;
				PUT(HDRP(NEXT_BLKP(oldptr)), PACK(csize, 0));
				PUT(FTRP(NEXT_BLKP(oldptr)), PACK(csize, 0));
				mm_free(NEXT_BLKP(oldptr));
				return oldptr;
			}
			else{ //if(((GET_ALLOC(NEXT_BLKP(oldptr) == 0)) && (old_size + next_size < size)) || (GET_ALLOC(NEXT_BLKP(oldptr) != 0)))  {
				newptr = mm_malloc(size);
				if (newptr == NULL)
      				return NULL;
				old_size = GET_SIZE(HDRP(ptr)) -DSIZE;
				if(size < old_size)
				{
					size = old_size;
				}
				memcpy(newptr, oldptr, old_size); //-DSIZE
				mm_free(oldptr);
    			return newptr;
			}
			//newptr = mm_malloc(size);
			//if (newptr == NULL)
      		//	return NULL;
			//memcpy(newptr, oldptr, size);
			//mm_free(oldptr);
    	//	return newptr;
		//}
		//if()
		

	}


	//1. If new < old -> shrink it
	//2. If new > old and next block is free and old + next >= new, expand it
	//3. If new > old and next block is free but old + next < new, or next block is not free -> malloc another block, copy the content to the new block, free the current block


		//copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    	//if (size < copySize)
      		//copySize = size;

    	//memcpy(newptr, oldptr, copySize);
    	//mm_free(oldptr);
    	//return newptr;
	//if next block is free and sum is greater than new then just extend current block

*/

//else{
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
	
//	}
}



/*
int mm_check(void){
	void *bp, *p, *cp;
	void *heap_begin = mem_heap_lo();
	void *heap_end = mem_heap_hi();
	for(bp = heap_begin; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		check_blk(bp);
		//show_block(bp);
		if(*bp < (size_t)heap_begin || *bp > (size_t)heap_end){
			printf("Error pointer is out of bounds %p\n",bp);
		}
		if(GET_ALLOC(bp) == 0 && GET_ALLOC(NEXT_BLKP(bp)) == 0){
		printf("Error uncoalesced blocks %p, %p \n", bp, NEXT_BLKP(bp));
		}

	}

}

void check_blk(void *bp){
	//first check alignment 
	if((int)bp % DSIZE == 0){
		printf("error not aligned");
	}
	if(GET(FTRP(bp)) != GET(HDRP(bp))){
		printf("error header and footer do not match");
	}
}

static void show_block(void *bp){
	
	size_t hd_size = GET_SIZE(HDRP(bp));
	size_t ft_size = GET_SIZE(FTRP(bp));

	unsigned int hd_alloc = GET_ALLOC(HDRP(bp));
	unsigned int ft_alloc = GET_ALLOC(FTRP(bp));

	printf("header = %p\n", &hd_size);
	printf("footer = %p\n", &ft_size);
	printf("header aloocated = %p\n", &hd_alloc);
	printf("footer allocated = %p\n", &ft_alloc);
}
*/