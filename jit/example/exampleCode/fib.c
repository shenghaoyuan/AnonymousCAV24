#include<stdio.h>
#include<stdint.h>

uint32_t fib(uint32_t num)
{
    uint32_t t0 = 0, t1 = 1, next = 1;
    
    if (num == 0) {
      return 0;
    }
    else if (num == 1 || num == 2) {
      return 1;
    }
    else {
      for (uint32_t i = 3; i <=num; i++) {
        t0 = t1;
        t1 = next;
        next = t0 + t1;
      }
    
      return next;
    }
}
