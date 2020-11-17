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
#define	WSIZE	 4 //sizeof(void *) /* Word and header/footer size (bytes) */ //void is 8 btyes on 64
#define DSIZE	2*WSIZE /* Double word size (bytes) */ 
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (bytes) */
// this means extending by 24 bytes is that right?
//i think i need to chane chunk size then to 24 was 12 
//wait but min size is sixteen bc header and footer and pointer space

//need 2 extra words for each block bc of next and prev
#define PSPACE 8 
  
//min size now is different with double alignment has to be 24
#define MIN_SIZE 16  //was 24
#define FREE_SIZE 16 //intial free list needs to have min size 

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */ 
#define PACK(size, alloc) ((size) | (alloc)) 

/* Read and write a word at address p */ 
#define GET(p)		(*(unsigned int *) (p)) 
#define PUT(p, val)	(*(unsigned int *) (p) = (val))

/* Read the size and allocated fields from address p */ 
#define GET_SIZE(p)	   (GET (p) & ~0x7) 
#define GET_ALLOC(p)	(GET (p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */ 
//#define HDRP(bp)	((void *) (bp) - WSIZE) 
//#define FTRP(bp)	((void *) (bp) + GET_SIZE (HDRP (bp)) - DSIZE)

#define HDRP(bp)	((void *) (bp) - WSIZE) 
#define FTRP(bp)	((void *) (bp) + GET_SIZE (HDRP (bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */ 
#define NEXT_BLKP(bp)	((void *) (bp) + GET_SIZE(((void *) (bp) - WSIZE))) 
#define PREV_BLKP(bp)	((void *) (bp) - GET_SIZE(((void *) (bp) - DSIZE)))

//#define NEXT_BLKP(bp)	((char *) (bp) + GET_SIZE(((void *) (bp) - WSIZE))) 
//#define PREV_BLKP(bp)	((char *) (bp) - GET_SIZE(((void *) (bp) - DSIZE)))


//for explicit list need more macros
//at least one for prev and next 

//#define PREV_FREE(bp)  (*(void**)bp) //now need to intialize these feilds for explicit free list
//#define NEXT_FREE(bp) (*(void**)(bp+DSIZE)) //is this 8 or 4? depends how i set up
//might need to change pointer type

#define PREV_FREE(bp) (*(void**)((void*)(bp))) //now need to intialize these feilds for explicit free list
#define NEXT_FREE(bp) (*(void**)((void*)(bp+DSIZE))) //is this 8 or 4? depends how i set up

//needed to put pointers into postion

static void *heap_listp = 0; //pointer to beginning of heap
static void *free_listp = 0; //pointer to what will be first block

//i feel like i should add prev alloc to header value do i have to change pack? or need new func. 

int mm_init(void);
static void *extend_heap(size_t words);
void mm_free(void *bp);
static void *coalesce(void *bp);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void fr_del(void *bp);
static void fr_add(void *bp);
static void show_block(void *bp);
void check_blk(void*bp);
int mm_check(void);

int mm_init(void)
{
	/* Create the initial empty heap */ //this word size might be wrong 
	if ((heap_listp = mem_sbrk(MIN_SIZE)) == NULL) //look if this should be 24 or 16 
		//print error message
		//printf("error in init\n");
		return -1; //expanation failed
	PUT(heap_listp, 0);				/* Alignment padding */ 
	//PUT(heap_listp , PACK(DSIZE, 1));	/* Prologue header */ //4
	
	PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); //need to init free list this is for pointer next 
	PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); //for prev
	
	//PUT(heap_listp + (3*WSIZE), PACK(0, 0));

	PUT(heap_listp + (3*WSIZE), PACK(0, 1));	/* Prologue footer */ //8
	//PUT(heap_listp + (4*WSIZE), PACK(0, 1));	/* Epilogue header */ //12, so min size is 24?
	heap_listp += (2*WSIZE); //points to first block in heap but i only care about free list 

	

	//points to nothing bc nothing on list yet i think? 
	//this means i need a way to traverse the free list, gotta write a helper oh zoinks
	/* Extend the empty heap with a free block of CHUNKSIZE bytes */ 
	
	if (extend_heap(CHUNKSIZE/WSIZE) == NULL) //shouldn't i only be extending by min size? 
		return -1; //this means failed

	free_listp = heap_listp+DSIZE; //d size for the heap extend we just did
	//tabby says when you intialize free list points to beinging of heap bc it is free makes sense
	//might need to set prev to null and next to bp 
	
	NEXT_FREE(free_listp) = NULL;
	PREV_FREE(free_listp) = NULL;
	return 0;
}

static void *extend_heap(size_t words)
{
	void *bp; 
	size_t size; //this looks pretty good dont think needs any changes

	/* Allocate an even number of words to maintain alignment */ 
	size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
	//size = ALIGN(words);
	if(size < MIN_SIZE){
		size = MIN_SIZE;
	}
	if ((bp = mem_sbrk(size)) == (void*)-1)
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

	if (bp == 0) { //need to insure that not freeing null
		return;
	}
	if(heap_listp == 0){
		mm_init();
	}

	size_t size = GET_SIZE(HDRP(bp)); //think this is mostly good too

	PUT(HDRP(bp), PACK(size, 0)); 
	PUT(FTRP(bp), PACK(size, 0)); 
	coalesce(bp);
}

static void *coalesce(void *bp) //this will def be different look at txt / lecture notes for procedure 
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp; 
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 
	size_t size = GET_SIZE(HDRP(bp));

	if(prev_alloc && next_alloc) {			/* Case 1 */
		fr_add(bp);
		return bp;
	}

	else if (prev_alloc && !next_alloc) {		/* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
		fr_del(NEXT_BLKP(bp));
		PUT(HDRP(bp), PACK(size, 0)); 
		PUT(FTRP(bp), PACK(size, 0));
	}

	else if (!prev_alloc && next_alloc) {		/* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))); 
		bp = PREV_BLKP(bp);
		fr_del(bp);
		PUT(HDRP(bp), PACK(size, 0)); //edited to make prev_blkp
		PUT(FTRP(bp), PACK(size, 0)); 
		
	}

	else {						/* Case 4 */ 
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		fr_del(NEXT_BLKP(bp));
		fr_del(PREV_BLKP(bp));
		bp = PREV_BLKP(bp); 
		PUT(HDRP(bp), PACK(size, 0)); 
		PUT(FTRP(bp), PACK(size, 0));
		
	} 
	fr_add(bp);
	return bp;
}

void *mm_malloc(size_t size)
{
	size_t asize;		/* Adjusted block size */ 
	size_t extendsize;	/* Amount to extend heap if no fit */ 
	void *bp;

	/* Ignore spurious requests */ 
	if(size == 0)
		return NULL;
	if(heap_listp ==0){
		mm_init();
	}

	/* Adjust block size to include overhead and alignment reqs. */ 
	if(size <= DSIZE)
		asize = 2*DSIZE; 
	else
		asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //think this part is mostly good might need to change alignemt stuff bc new size
	//asize = MAX(ALIGN(size) +DSIZE,MIN_SIZE);
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
    void *bp; //wait i need to change this to traverse free list 
	for (bp = free_listp; bp != NULL; bp = NEXT_FREE(bp)){ //this should be bp = freelistp
        if ((asize <= GET_SIZE(HDRP(bp))) && (!GET_ALLOC(HDRP(bp))) ){ //if size matches works
			return bp;
		}
    }

 /*   for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ //this should be bp = freelistp
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }
	*/
    return NULL; //not fit 
}

static void place(void *bp, size_t asize) //needs to change to account for pointers 
{
	size_t csize = GET_SIZE(HDRP(bp));
 //might need to change what it is checking
    if((csize - asize) >= (2*DSIZE)){ //this is splitting the block
        PUT(HDRP(bp), PACK(asize, 1)); //block header
        PUT(FTRP(bp), PACK(asize, 1)); //block footr
		fr_del(bp); //free block is added to heap and needs to be deleted from free 
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
		fr_add(bp);
		//coalesce(bp); //forgot to coalesce at end
    }
    else{
        PUT(HDRP(bp),PACK(csize, 1));
        PUT(FTRP(bp),PACK(csize, 1));
		fr_del(bp); ///free block is added to heap and needs to be deleted from free 
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
static void fr_add(void* bp){
	NEXT_FREE(bp) = free_listp; //add to begining of list
	PREV_FREE(free_listp) = bp; //free list prev is now one added
	PREV_FREE(bp) = NULL; //new start of list prev will be null
	free_listp = bp; //this is new start
}

static void fr_del(void *bp){ 
	//maybe like

	if(PREV_FREE(bp)){
		NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
		//PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp); //this lets it skip
	}
	else{
		free_listp = NEXT_FREE(bp);
		PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp);

	}
	/*if(PREV_FREE(bp) == NULL){ //if beginning of list free list pointer should point to the next block in list
		free_listp = NEXT_FREE(bp); 
	}
	else {
		
		NEXT_FREE(PREV_FREE(bp)) = NEXT_FREE(bp);
		PREV_FREE(NEXT_FREE(bp)) = PREV_FREE(bp); //this lets it skip
	}
	*/
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

int mm_check(void){
	char *bp, *p, *cp;
	void *heap_begin = mem_heap_lo();
	void *heap_end = mem_heap_hi();
	for(bp = heap_begin; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
		check_blk(bp);
		//show_block(bp);
		if(&bp < (size_t)heap_begin || &bp > (size_t)heap_end){
			printf("Error pointer is out of bounds %p\n",bp);
		}
		if(GET_ALLOC(bp) == 0 && GET_ALLOC(NEXT_BLKP(bp)) == 0){
		printf("Error uncoalesced blocks %p, %p \n", bp, NEXT_BLKP(bp));
		}
		if(GET_ALLOC(bp) == 0){
			for (cp = free_listp; ; cp = NEXT_BLKP(cp)){
				if(HDRP(bp) == HDRP(cp)){
					printf("in free list");
				}
			}
			printf("not in free list");
		}
		
	}
	for (p = free_listp; ; p = NEXT_BLKP(p)){
		if(GET_ALLOC(HDRP(p)) != 0){
			printf("error not free block");
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





//int main(){
//	mm_check();
//}