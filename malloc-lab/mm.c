/* mm-naive.c - 가장 빠르지만, 메모리는 가장 낭비하는 malloc
 * 이 단순한 방식에서 블록을 할당할 때 그냥 힙 끝(brk 포인터)을 늘리기만 한다.
 * 블록은 순수하게 데이터만 있고, 헤더나 푸터가 없다. 
 * 블록은 합쳐지거나 재사용되지 않는다.
 * realloc은 mm_malloc과 mm_free를 이용해 만들었다.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * 다른 무엇보다 먼저, 아래 구조체에 팀 정보를 적어라.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

#define WSIZE 4
#define ALIGNMENT 8
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN_BLOCK (2*DSIZE)

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

static void *extend_heap(size_t words);

static void *coalesce(void *bp);

static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 1 워드(4) 또는 더블 워드(8) 정렬, 반환하는 주소는 8의 배수여야 함. */

/* 가장 가까운 ALIGNMENT의 배수로 올림한다. */
/* 예: ALIGN(1)=8, ALIGN(8)=8, ALIGN(9)=16, ALIGN(13)=16 */
/* size_t 하나를 저장하는 데 필요한 크기를 8의 배수로 맞춘 값. 지금 환경(64비트)에서는 8. */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
 * mm_init - malloc 패키지를 초기화한다. 아무것도 안 하고 0(성공)만 반환
 */
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));

    heap_listp += (2 * WSIZE);

    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t asize;  // 조정한 블록 크기
    size_t extendsize;  // 맞는 블록이 없을 때 힙을 늘릴 크기
    char *bp;
    
    if (size == 0) return NULL;

    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // 안쪽 괄호를 빼면 != 가 = 보다 먼저 계산돼서 bp에 0이나 1이 들어간다.
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) return NULL;

    place(bp, asize);

    return bp;
}

/*
 * mm_free - 해제는 아무것도 하지 않는다
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - mm_malloc과 mm_free를 이용해 간단하게 구현했다.
 */
void *mm_realloc(void *bp, size_t size)
{
    void *oldbp = bp;
    void *newbp;
    size_t copySize;

    newbp = mm_malloc(size);
    if (newbp == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldbp - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newbp, oldbp, copySize);
    mm_free(oldbp);
    return newbp;
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 앞의 블록 할당 비트 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 뒤의 블록 할당 비트 저장
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록 크기 저장

    if (prev_alloc && next_alloc) { return bp;}

    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }

    return bp;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

    if((long)(bp = mem_sbrk(size)) == -1) return NULL;

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

static void *find_fit(size_t asize)
{
    void *bp = NEXT_BLKP(heap_listp);
    
    if (GET_SIZE(HDRP(bp)) == 0) return NULL;

    while (GET_SIZE(HDRP(bp)) != 0)
    {
        if (GET_ALLOC(HDRP(bp)) == 0 && GET_SIZE(HDRP(bp)) >= asize)
        {
            return bp;
        }
        else
        {
            bp = NEXT_BLKP(bp);
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize)
{
    // 현재 블록 크기 읽기
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= MIN_BLOCK)
    {
        size_t remain_size = csize - asize;

        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);  
        PUT(HDRP(bp), PACK(remain_size, 0));
        PUT(FTRP(bp), PACK(remain_size, 0));
    }

    else
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));  
    }
}