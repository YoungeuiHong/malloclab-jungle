/*
 * 🚀 Segregated Free List (분리 가용 리스트)
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include <sys/mman.h>
#include <errno.h>
#include "mm.h"
#include "memlib.h"

team_t team = {
    /* Team name */
    "Jungle Team 7",
    /* First member's full name */
    "Youngeui Hong",
    /* First member's email address */
    "my-email@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/***************************************** 상수 *******************************************/

#define MAX_POWER 50 // 2의 최대 몇 제곱까지 사이즈 클래스를 지원할지. 여기에서는 2^50까지의 사이즈 클래스를 지원함
#define TAKEN 1
#define FREE 0
#define WORD_SIZE 4
#define D_WORD_SIZE 8
#define CHUNK ((1 << 12) / WORD_SIZE)
#define STATUS_BIT_SIZE 3 // 할당된 블록과 할당되지 않은 블록을 구분하기 위해 사용되는 비트의 크기
#define HDR_FTR_SIZE 2    // 단위: word
#define HDR_SIZE 1        // 단위: word
#define FTR_SIZE 1        // 단위: word
#define PRED_FIELD_SIZE 1 // 단위: word
#define EPILOG_SIZE 2     // 단위: word
#define ALIGNMENT 8

/*************************************** 매크로 **********************************************/

/* 주소 p에 적힌 값을 읽어오기 */
#define GET_WORD(p) (*(unsigned int *)(p))

/* 주소 p에 새로운 값을 쓰기*/
#define PUT_WORD(p, val) (*(char **)(p) = (val))

/* size보다 크면서 가장 가까운 ALIGNMENT의 배수 찾기 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))

/* x보다 크면서 가장 가까운 짝수 찾기 */
#define EVENIZE(x) ((x + 1) & ~1)

/*
 * 블록 사이즈 가져오기
 * how? 16진수 0x7은 10진수로 7을 의미. 이를 이진수로 변환하면 0111이 되고 NOT 연산자 ~를 붙이면 1000이 됨. 주소값 p와 and 연산을 하면 비트의 마지막 세 자리를 0으로 바꿈
 */
#define GET_SIZE(p) (GET(p) & ~0x7)

/*
 * 블록의 할당 여부 가져오기
 * how? 마지막 자리를 제외하고 모두 0으로 바꿈. 할당이 되어 있다면 마지막 자리가 1로 반환되고, 할당이 안 되어 있다면 마지막 자리가 0으로 반환됨
 */
#define GET_STATUS(p) (GET(p) & 0x1)

/*
 * 블록 헤더의 주소 가져오기
 */
#define HDRP(bp) ((char *)(bp)-WSIZE)

/* 블록 푸터의 주소 가져오기 */
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 헤더와 푸터를 포함한 블록의 사이즈 가져오기 */
#define GET_TOTAL_SIZE(p) (GET_SIZE(p) + HDR_FTR_SIZE)

/* free_lists의 i번째 요소 가져오기 */
#define GET_FREE_LIST_PTR(i) (*(free_lists + i))

/* free_lists의 i번째 요소 값 설정하기 */
#define SET_FREE_LIST_PTR(i, ptr) (*(free_lists + i) = ptr)

/* 가용 블록의 predecessor, successor 주소값 셋팅 */
#define SET_PTR(p, ptr) (*(char **)(p) = (char *)(p))

/* 가용 블록 내에 predecessor 주소가 적힌 곳의 포인터 가져오기 */
#define GET_PTR_PRED_FIELD(header_ptr) ((char **)(header_ptr) + HDR_SIZE)

/* 가용 블록 내에 successor 주소가 적힌 곳의 포인터 가져오기 */
#define GET_PTR_SUCC_FIELD(header_ptr) ((char **)(header_ptr) + HDR_SIZE + PRED_FIELD_SIZE)

/* 가용 블록의 predecessor 메모리 공간에 저장된 주소값 가져오기 */
#define GET_PRED(bp) (*GET_PTR_PRED_FIELD(bp))

/* 가용 블록의 successor 메모리 공간에 저장된 주소값 가져오기 */
#define GET_SUCC(bp) (*(GET_PTR_SUCC_FIELD(bp)))

/* 이전 블록의 포인터 가져오기 */
#define PREV_BLOCK_IN_HEAP(header_p) ((char **)(header_p)-GET_TOTAL_SIZE((char **)(header_p)-FTR_SIZE))

/* 다음 블록의 포인터 가져오기 */
#define NEXT_BLOCK_IN_HEAP(header_p) (FTRP(header_p) + FTR_SIZE)

/************************************** 변수 선언부 *******************************************/

static char **free_lists;
static char **heap_ptr;

/************************************** 함수 선언부 *******************************************/

static size_t find_free_list_index(size_t words);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_free_block(size_t words);
static void alloc_free_block(void *bp, size_t words);
static void place_block_into_free_list(char **bp);
static void remove_block_from_free_list(char **bp);
static int round_up_power_2(int x);
void *mm_realloc_wrapped(void *ptr, size_t size, int buffer_size);
int mm_check();

/* 주어진 수 x보다 크거나 같은 2의 제곱 중에서 가장 작은 값을 찾는 함수*/
static int round_up_power_2(int x)
{
    if (x < 0)
        return 0;
    --x;
    x |= x >> 1;
    x |= x >> 2;
    x |= x >> 4;
    x |= x >> 8;
    x |= x >> 16;
    return x + 1;
}

/* mm_init - malloc 패키지 초기화하기 */
int mm_init(void)
{
    // MAX POWER만큼 segregated free list의 메모리 할당 받기
    if ((long)(free_lists = mem_sbrk(MAX_POWER * sizeof(char *))) == -1)
        return -1;

    // segregated free list 초기화
    for (int i = 0; i <= MAX_POWER; i++)
    {
        SET_FREE_LIST_PTR(i, NULL);
    }

    // 
    mem_sbrk(WORD_SIZE);
}