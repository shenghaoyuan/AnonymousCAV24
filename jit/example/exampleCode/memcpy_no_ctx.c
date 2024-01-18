#include<stdio.h>
#include<stdint.h>

uint32_t square(char* src, char* dst, uint32_t len)
{
  for (uint32_t i = 0; i < len; i++) {
    dst[i] = src[i];
  }
  return 0;
}
