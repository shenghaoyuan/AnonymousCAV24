#include<stdio.h>
#include<stdint.h>
#include <inttypes.h>
#include <stdlib.h>
#include <stdbool.h>

#define MAX_INS_NUM 500

_Bool is_lddw_low (uint64_t ins) {
  return (ins & 255LLU) == 0x18;
}

int main(){
  uint32_t pre[11];
  uint64_t buffer;
  FILE *f_input, *f_output;
  _Bool flag;

  // llvm ebpf backend generates the following binary file + rBPF pre-process
  f_input = fopen("fletcher32_bpf.bin", "rb");
  f_output = fopen("fletcher32_bpf_int64.txt", "w+");
  
  if (f_input && f_output) {
    // skip the rBPF pre-process info: 11 bytes
    fread(pre, sizeof(pre), 1, f_input);
    
    fprintf(f_output, "[\n");
    if (fread(&buffer, sizeof(buffer), 1, f_input) == 1) {
      fprintf(f_output, "(Int64.repr 0x%016lx)", buffer);
      
      flag = is_lddw_low(buffer);
            
      while (fread(&buffer, sizeof(buffer), 1, f_input) == 1){
        // modify lddw_high: op -> 0x10
        if (flag) {
          buffer = buffer | 0x10;
          flag = false;
        }
        else {
          flag = is_lddw_low(buffer);
        }
        fprintf(f_output, ";\n(Int64.repr 0x%016lx)", buffer);
      }
    
      fprintf(f_output, "\n].\n");
    }
    else {
      printf("error: invalid input\n");
    }
    fclose (f_input);
    fclose (f_output);
  }
  else {
    printf("fail to open the file!\n");
  }
  return 0;
}
