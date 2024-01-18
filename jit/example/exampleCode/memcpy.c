#include<stdio.h>
#include<stdint.h>

struct test_md
{
    char* src;
    char* dst;
    uint32_t len;
};

uint32_t memcpy_n(struct test_md * ctx)
{
  char* src = ctx->src;
  char* dst = ctx->dst;
  uint32_t len = ctx->len;
  for (uint32_t i = 0; i < len; i++) {
    dst[i] = src[i];
  }
  return 0;
}
