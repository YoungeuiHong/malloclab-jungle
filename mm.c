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
 * 블록의 크기와 할당 비트를 통합해서 header와 footer에 저장할 수 있는 값 만들기
 * Pack a size and allocated bit into a word
 */
#define PACK(size, alloc) ((size) | (alloc))

/*
 * 블록 헤더의 주소 가져오기
 */
#define HDRP(bp) ((char *)(bp)-WSIZE)

/* 블록 푸터의 주소 가져오기 */
#define FTRP(header_p) ((char **)(header_p) + GET_SIZE(header_p) + HDR_SIZE)

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

static void *extend_heap(size_t words);
static void place_block_into_free_list(char **bp);
static size_t find_free_list_index(size_t words);
static void alloc_free_block(void *bp, size_t words);
static void remove_block_from_free_list(char **bp);
static void *coalesce(void *bp);
static void *find_free_block(size_t words);


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

/* mm_init: malloc 패키지 초기화하기 */
int mm_init(void)
{
    // segregated free list를 위해 MAX_POWER * sizeof(char *) 만큼 힙 영역 확장하기
    if ((long)(free_lists = mem_sbrk(MAX_POWER * sizeof(char *))) == -1)
        return -1;

    // segregated free list 초기화
    for (int i = 0; i <= MAX_POWER; i++)
    {
        SET_FREE_LIST_PTR(i, NULL);
    }

    // 더블 워드 정렬 조건 충족을 위해 워드 사이즈만큼 힙 영역 확장
    mem_sbrk(WORD_SIZE);

    // 프롤로그 블록과 에필로그 블록을 위해 힙 영역 추가 확장
    if ((long)(heap_ptr = mem_sbrk(4 * WORD_SIZE)) == -1)
        return -1;

    PUT_WORD(heap_ptr, PACK(0, TAKEN));       // 프롤로그 헤더
    PUT_WORD(FTRP(heap_ptr), PACK(0, TAKEN)); // 프롤로그 푸터

    char **epilog = NEXT_BLOCK_IN_HEAP(heap_ptr); // 에필로그 헤더 포인터
    PUT_WORD(epilog, PACK(0, TAKEN));             // 에필로그 헤더
    PUT_WORD(FTRP(epilog), PACK(0, TAKEN));       // 에필로그 푸터

    heap_ptr = NEXT_BLOCK_IN_HEAP(heap_ptr); // heap 포인터를 프롤로그 블록 다음으로 이동시킴

    // CHUNK 사이즈만큼 힙 영역을 확장하기
    char **new_block;
    if ((new_block = extend_heap(CHUNK)) == NULL)
        return -1;

    // 힙 영역을 확장하여 새로 얻은 블록을 가용 리스트에 추가해주기
    place_block_into_free_list(new_block);

    return 0;
}

/* mm_malloc: 메모리 할당하기 */
void *mm_malloc(size_t size)
{
    if (size == 0)
        return NULL;

    // CHUNK 사이즈보다 작으면 가장 가까운 2의 제곱 사이즈로 만들기
    if (size <= CHUNK * WORD_SIZE)
        size = round_up_power_2(size);

    // 바이트 단위 사이즈를 워드 단위 사이즈로 변환하기
    size_t words = ALIGN(size) / WORD_SIZE;

    size_t extend_size;
    char **bp;

    // 2) 해당 가용 블록 리스트 내에 가용 블록이 있으면 할당한다.
    // 3) 가용 블록이 없으면 다음으로 큰 size class의 가용 블록 리스트로 이동하여 탐색한다.
    // 4) 모든 가용 블록 리스트를 탐색했는데도 가용 볼록이 없으면 힙 영역을 확장한다.

    // 할당하려는 사이즈에 적합한 블록이 있는지 찾았는데 없는 경우 힙 영역을 확장
    if ((bp = find_free_block(words)) == NULL)
    {
        extend_size = words > CHUNK ? words : CHUNK;
        if ((bp = extend_heap(extend_size)) == NULL)
            return NULL;

        // 새로 할당 받은 힙 영역에서 필요한 만큼 메모리 할당하고 나머지는 가용 리스트에 추가
        alloc_free_block(bp, words);

        return bp + HDR_SIZE;
    }

    remove_block_from_free_list(bp); // 사용하려는 블록을 가용 리스트에서 제거
    alloc_free_block(bp, words); // 가용 블록에서 필요한 만큼 메모리 할당하고, 남은 블록은 다시 가용 리스트에 추가

    return bp + HDR_SIZE;
}

/* mm_free: 메모리 반환하기 */
void mm_free(void *ptr)
{
    ptr -= WORD_SIZE; // 헤더 포인터

    // 헤더와 푸터의 할당 상태 정보를 free 상태로 수정
    size_t size = GET_SIZE(ptr);
    PUT_WORD(ptr, PACK(size, FREE));
    PUT_WORD(FTRP(ptr), PACK(size, FREE));

    // 해제된 블록의 전후로 가용 블록이 있다면 연결
    ptr = coalesce(ptr);

    // 연결된 블록을 가용 리스트에 추가
    place_block_into_free_list(ptr);
}

/*
extend_heap: 힙 영역 확장하기
- 힙 영역 확장에 성공하는 경우 새로운 블록의 헤더와 푸터 영역을 정의하고, 해당 블록의 포인터를 반환
- 힙 영역 확장에 실패하는 경우 NULL을 리턴
*/
static void *extend_heap(size_t words)
{
    char **bp;                                               // 힙 영역을 확장하여 새로 생긴 가용 블록을 가리키는 포인터
    char **end_pointer;                                      // 가용 블록의 끝을 가리키는 포인터
    size_t words_extend = EVENIZE(words);                    // 더블 워드 정렬
    size_t words_extend_total = words_extend + HDR_FTR_SIZE; // 헤더와 푸터 사이즈를 더한 총 블록 사이즈

    if ((long)(bp = mem_sbrk((words_extend_total)*WORD_SIZE)) == -1)
        return NULL;

    // 새로운 가용 블록의 헤더와 푸터에 값 셋팅
    PUT_WORD(bp, PACK(words_extend, FREE));
    PUT_WORD(FTRP(bp), PACK(words_extend, FREE));

    // 힙 영역 마지막에 에필로그 블록 추가
    bp -= EPILOG_SIZE;
    end_pointer = bp + words_extend_total;
    PUT_WORD(end_pointer, PACK(0, TAKEN));
    PUT_WORD(FTRP(end_pointer), PACK(0, TAKEN));

    return bp;
}

/* place_block_into_free_list: 블록 사이즈에 따라 적절한 위치에 새로운 가용 블록 추가하기 */
static void place_block_into_free_list(char **bp)
{
    size_t size = GET_SIZE(bp); // 새로 배치할 가용 블록의 사이즈

    if (size == 0)
        return;

    // 가용 블록에 적합한 size class의 가용 리스트 찾기
    int index = find_free_list_index(size);
    char **front_ptr = GET_FREE_LIST_PTR(index); // 해당 가용 리스트의 주소를 받아오기
    char **prev_ptr = NULL;

    // 만약 그 size class의 가용 리스트가 비어있다면
    if (front_ptr == NULL)
    {
        SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
        SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
        SET_FREE_LIST_PTR(index, bp); // 가용 리스트의 시작 지점으로 설정
        return;
    }

    // 만약 새로운 블록이 이 size class의 가용 리스트 내에서 가장 큰 사이즈라면 (가용 리스트는 내림차순으로 정렬되어 있음)
    if (size >= GET_SIZE(front_ptr))
    {
        SET_FREE_LIST_PTR(index, bp); // 가용 리스트의 시작 지점으로 설정
        SET_PTR(GET_PTR_PRED_FIELD(bp), NULL);
        SET_PTR(GET_PTR_SUCC_FIELD(bp), front_ptr);
        SET_PTR(GET_PTR_PRED_FIELD(front_ptr), bp);
        return;
    }

    // 내림차순으로 정렬된 가용 리스트에서 블록이 들어갈 지점 찾기
    while (front_ptr != NULL && GET_SIZE(front_ptr) > size)
    {
        prev_ptr = front_ptr;
        front_ptr = GET_SUCC(front_ptr);
    }

    if (front_ptr == NULL) // 가용 리스트의 끝에 도달한 경우
    {
        SET_PTR(GET_PTR_SUCC_FIELD(prev_ptr), bp);
        SET_PTR(GET_PTR_PRED_FIELD(bp), prev_ptr);
        SET_PTR(GET_PTR_SUCC_FIELD(bp), NULL);
        return;
    }
    else
    { // 가용 리스트의 중간에 집어넣는 경우
        SET_PTR(GET_PTR_SUCC_FIELD(prev_ptr), bp);
        SET_PTR(GET_PTR_PRED_FIELD(bp), prev_ptr);
        SET_PTR(GET_PTR_SUCC_FIELD(bp), front_ptr);
        SET_PTR(GET_PTR_PRED_FIELD(front_ptr), bp);
        return;
    }
}

/* find_free_list_index: 주어진 words 사이즈가 속하는 size class, 즉 가용 리스트 상의 인덱스를 찾는 함수 */
static size_t find_free_list_index(size_t words)
{
    int index = 0;

    while ((index <= MAX_POWER) && (words > 1))
    {
        words >>= 1; // words가 1보다 작거나 같아질 때까지 오른쪽으로 shift 연산
        index++;
    }

    return index;
}

/* find_free_block: 전체 Segregated Free List에서 주어진 words 사이즈에 적합한 가용 블록 찾기 */
static void *find_free_block(size_t words)
{
    char **bp;
    size_t index = find_free_list_index(words); // 주어진 words 사이즈보다 큰 size class 중 가장 작은 size class의 가용 리스트 찾기

    // 사용할 수 있는 가용 블록을 찾을 때까지 탐색
    while (index <= MAX_POWER)
    {
        // 현재 size class의 가용 리스트가 비어 있지 않고, 블록의 크기도 충분히 커서 메모리 할당이 가능한 경우
        if ((bp = GET_FREE_LIST_PTR(index)) != NULL && GET_SIZE(bp) >= words)
        {
            // 가용 리스트를 순회하며 사이즈가 가장 적합한 블록 찾기
            while (1)
            {
                if (GET_SIZE(bp) == words)
                    return bp;

                // 다음 블록이 없거나, 다음 불록이 필요한 사이즈보다 작으면 현재 블록을 리턴
                if (GET_SUCC(bp) == NULL || GET_SIZE(GET_SUCC(bp)) < words)
                    return bp;

                bp = GET_SUCC(bp);
            }
        }

        index++;
    }

    // 만약 모든 리스트를 탐색했는데도 사용할 수 있는 가용 블록이 없는 경우 NULL 리턴
    return NULL;
}

/*
alloc_free_block: 가용 블록에서 메모리 할당하기
*/
static void alloc_free_block(void *bp, size_t words)
{
    size_t bp_tot_size = GET_SIZE(bp) + HDR_FTR_SIZE;                      // 가용 블록의 사이즈 (= 페이로드 + 헤더 + 푸터)
    size_t needed_size = words;                                            // 할당 받아야 하는 사이즈
    size_t needed_tot_size = needed_size + HDR_FTR_SIZE;                   // 할당 받아야 하는 사이즈 (헤더, 푸터 포함)
    size_t left_block_size = bp_tot_size - needed_tot_size - HDR_FTR_SIZE; // 할당하고 남는 블록의 사이즈

    char **new_block_ptr; // 할당하고 남는 새로운 가용 블록의 포인터

    if ((int)left_block_size > 0) // 할당하고도 블록이 남는 경우
    {
        // 필요한 사이즈만큼 메모리 할당
        PUT_WORD(bp, PACK(needed_size, TAKEN));
        PUT_WORD(FTRP(bp), PACK(needed_size, TAKEN));

        // 새로운 가용 블록의 포인터
        new_block_ptr = (char **)(bp) + needed_tot_size;

        // 새로운 가용 블록의 헤더, 푸터 정보 셋팅
        PUT_WORD(new_block_ptr, PACK(left_block_size, FREE));
        PUT_WORD(FTRP(new_block_ptr), PACK(left_block_size, FREE));

        // 인접한 가용 블록이 있는 경우 연결
        new_block_ptr = coalesce(new_block_ptr);

        // 가용 리스트에 추가
        place_block_into_free_list(new_block_ptr);
    }
    else if (left_block_size == 0) // 필요한 만큼 할당하고 남는 블록이 2워드이면 쪼갤 수 없으므로 2워드를 추가하여 메모리를 할당함
    {
        PUT_WORD(bp, PACK(needed_tot_size, TAKEN));
        PUT_WORD(FTRP(bp), PACK(needed_tot_size, TAKEN));
    }
    else // 할당하려는 블록의 사이즈와 동일한 경우
    {
        PUT_WORD(bp, PACK(needed_size, TAKEN));
        PUT_WORD(FTRP(bp), PACK(needed_size, TAKEN));
    }
}

/* remove_block_from_free_list: 가용 리스트에서 블록 제거하기 */
static void remove_block_from_free_list(char **bp)
{
    char **prev_block = GET_PRED(bp);
    char **next_block = GET_SUCC(bp);
    int index;

    if (GET_SIZE(bp) == 0)
        return;
    
    if (prev_block == NULL) // 해당 size class 리스트의 맨 앞에 있는 가장 큰 블록인 경우
    {
        index = find_free_list_index(GET_SIZE(bp)); // 블록이 포함된 가용 리스트의 인덱스
        GET_FREE_LIST_PTR(index) = next_block; // 다음 블록을 가용 리스트의 첫 번째 블록으로 설정
        
    }
}