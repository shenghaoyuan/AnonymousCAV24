#include<stdio.h>

struct test_md
{
    int size;
    int* arr;
};

void bubblesort(struct test_md * ctx) {
  int size = ctx->size;
  int * arr = ctx->arr;
  int i, j, tmp;
  for (i = 0;  i < size-1; i++) {
    for (j = 0; j < size - i-1; j++) {
      if (arr[j] > arr[j+1]) {
        tmp = arr[j];
        arr[j] = arr[j+1];
        arr[j+1] = tmp;
      }
    }
  }
}
