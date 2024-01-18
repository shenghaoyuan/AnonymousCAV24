#include<stdio.h>
#include <stdint.h>

#define ARRAY_LENGTH 40

struct test_md
{
    uint8_t* data_start;
    uint8_t* data_end; //llvm uses 8-bytes to represent this pointer, it should use 4-bytes.
    uint8_t array[ARRAY_LENGTH];
};

int foo(struct test_md* ctx)
{
    int index;
    int cumul = 0;


    for (index = 0; index < sizeof(ctx->array); index++) {
        if ((ctx->data_start + index) >= ctx->data_end)
            break;

        ctx->array[index] = 1;
    }

    for (index = 0; index < sizeof(ctx->array); index++) {
        cumul += ctx->array[index];
    }
    return cumul;
}
