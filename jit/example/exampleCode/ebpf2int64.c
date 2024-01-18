#include "ebpf_modifi.h"

int main(int argc, char *argv[]){
  char str[100];
  char obj[100];
  char out[100];
  uint32_t pre[PRE];
  uint64_t buffer;
  FILE *f_input, *f_output;
  _Bool flag;
  
  if (argc != 3) {
    printf("invaild argument%d: expect only two filenames `obj` and `output` \n", argc);
  }

  // llvm ebpf backend generates the following binary file + rBPF pre-process
  f_input = fopen(argv[1], "rb");
  f_output = fopen(argv[2], "w+");
  
  if (f_input && f_output) {
    // skip the rBPF pre-process info: 11 bytes
    fread(pre, sizeof(pre), 1, f_input);
    
    fprintf(f_output, "[\n");
    if (fread(&buffer, sizeof(buffer), 1, f_input) == 1) {
      fprintf(f_output, "(Int64.repr 0x%016lx)", buffer);
      
      flag = is_lddw_low(buffer);
      for (int i = 0; ; i++) {
        fread(&buffer, sizeof(buffer), 1, f_input);
        // modify lddw_high: op -> 0x10
        if (flag) {
          buffer = buffer | 0x10;
          flag = false;
        }
        else {
          flag = is_lddw_low(buffer);
        }
        fprintf(f_output, ";\n(Int64.repr 0x%016lx)", buffer);
        if (is_opcode_exit (buffer)) { break; }
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
