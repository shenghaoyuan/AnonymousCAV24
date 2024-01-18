#include<stdio.h>
#include <stdint.h>

#define ARRAY_LENGTH 40

struct test_md
{
    uint32_t data_start;
    uint32_t data_end;
    uint32_t len;
    uint32_t array[ARRAY_LENGTH];
};

uint32_t foo(struct test_md* ctx)
{
    uint32_t* array = ctx->array;
    uint32_t data_start = ctx->data_start;
    uint32_t data_end = ctx->data_end;
    uint32_t len = ctx->len;
    uint32_t index;
    uint32_t cumul = 0;


    for (index = 0U; index < len; index++) {
        if ((data_start + index) >= data_end)
            break;

        array[index] = 1U;
    }

    for (index = 0U; index < len; index++) {
        cumul += array[index];
    }
    return cumul;
}
