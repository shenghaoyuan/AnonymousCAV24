#include<stdio.h>
#include<stdint.h>
#include<stdlib.h>
#include<stddef.h>

struct fletcher32_ctx {
  const unsigned short * data; // this pointer is 64-bit, so we must use bpf_share_ptr later ...
  uint32_t words;
};

uint32_t fletcher32(struct fletcher32_ctx *ctx)
{
    const uint16_t *data = ctx->data;
    size_t words = ctx->words;
    
    uint32_t sum1 = 0xffff, sum2 = 0xffff;

    while (words) {
        unsigned tlen = words > 359 ? 359 : words;
        words -= tlen;
        do {
            sum2 += sum1 += *data++;
        } while (--tlen);
        sum1 = (sum1 & 0xffff) + (sum1 >> 16);
        sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    }
    sum1 = (sum1 & 0xffff) + (sum1 >> 16);
    sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    return (sum2 << 16) | sum1;
}
