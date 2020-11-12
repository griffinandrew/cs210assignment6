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
    "Griffin",
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
#define CHUNKSIZE (1<<24) /* Extend heap by this amount (bytes) */
// this means extending by 24 bytes is that right?
//i think i need to chane chunk size then to 24 was 12 
//wait but min size is sixteen bc header and footer and pointer space

//need 2 extra words for each block bc of next and prev
#define PSPACE 8 
  
//min size now is different with double alignment has to be 24
#define MIN_SIZE 16 //was 24 

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
#define HDRP(bp)	((void *) (bp) - WSIZE) 
#define FTRP(bp)	((void *) (bp) + GET_SIZE (HDRP (bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */ 
#define NEXT_BLKP(bp)	((void *) (bp) + GET_SIZE(((void *) (bp) - WSIZE))) 
#define PREV_BLKP(bp)	((void *) (bp) - GET_SIZE(((void *) (bp) - DSIZE)))

//for explicit list need more macros
//at least one for prev and next 

#define PREV_FREE(bp)  (*(void**)bp) //now need to intialize these feilds for explicit free list
#define NEXT_FREE(bp) (*(void**)(bp+DSIZE)) //is this 8 or 4? depends how i set up
//might need to change pointer type


void *heap_listp = 0;
void *free_listp = 0; //pointer to what will be first block

//i feel like i should add prev alloc to header value do i have to change pack? or need new func. 


int mm_init(void);
static void *extend_heap(size_t words);
void mm_free(void *bp);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void)
{

	/* Create the initial empty heap */ 
	if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
		return -1; 
	PUT(heap_listp, 0);				/* Alignment padding */ 
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));	/* Prologue header */ //4
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));	/* Prologue footer */ //8
	PUT(heap_listp + (3*WSIZE), PACK(0, 1));	/* Epilogue header */ //12, so min size is 24?
	heap_listp += (2*WSIZE); //points to first block in heap but i only care about free list 

	free_listp = 0; //points to nothing bc nothing on list yet i think? 
	//this means i need a way to traverse the free list, gotta write a helper oh zoinks
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */ 
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL) //shouldn't i only be extending by min size? 
		return -1; 
	return 0;
}

static void *extend_heap(size_t words)
{
	char *bp; 
	size_t size; //this looks pretty good dont think needs any changes

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
	size_t size = GET_SIZE(HDRP(bp)); //think this is mostly good too

	PUT(HDRP(bp), PACK(size, 0)); 
	PUT(FTRP(bp), PACK(size, 0)); 
	coalesce(bp);
}

static void *coalesce(void *bp) //this will def be different look at txt / lecture notes for procedure 
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
	size_t size = GET_SIZE(HDRP(bp));

	if(prev_alloc && next_alloc) {			/* Case 1 */
		return bp;
	}

	else if (prev_alloc && !next_alloc) {		/* Case 2 */
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

	/* Ignore spurious requests */ 
	if(size == 0)
		return NULL;

	/* Adjust block size to include overhead and alignment reqs. */ 
	if(size <= DSIZE)
		asize = 2*DSIZE; 
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //think this part is mostly good might need to change alignemt stuff bc new size

	/* Search the free list for a fit */ 
	if((bp = find_fit(asize)) != NULL) { //think this is fine
		place (bp, asize); 
		return bp;
	}

	/* No fit found. Get more memory and place the block */ 
	extendsize = MAX(asize, CHUNKSIZE); 
	if ((bp = extend_heap(extendsize/WSIZE)) == NULL) //look at max and how it relates to chunk / word
		return NULL; 
	place (bp, asize);
	return bp;
}

static void *find_fit(size_t asize){ //this is first fit, fine for now might want to use addressing or LIFO if can 
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
    return NULL; //not fit 
}

static void place(void *bp, size_t asize) //needs to change to account for pointers 
{
	size_t csize = GET_SIZE(HDRP(bp));

    if((csize - asize) >= (2*DSIZE)){ //this is splitting the block
        PUT(HDRP(bp), PACK(asize, 1)); //block header
        PUT(FTRP(bp), PACK(asize, 1)); //block footr
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



//helper functiin for travseing free list and policy for free or unfreed
//going to need helper functions to show free list and alloc list maybe to check the block and other stuff too


//function to add block to free list 
void fr_add(void* bp){
	NEXT_FREE(bp) = free_listp; //add to begining of list
	PREV_FREE(free_listp) = bp; //free list prev is now one added
	PREV_FREE(bp) = NULL; //new start of list prev will be null
	free_listp = bp; //this is new start
}

void fr_del(void *bp){ 
	//maybe like
	NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
	PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp); //this lets it skip
}