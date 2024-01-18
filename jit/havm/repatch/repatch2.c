/**
 * 1. deleting all lines before `struct memory_region *get_mem_region`
 * 2. deleting `\n\n`.
 * 2. deleting all `extern` lines
 * 3. adding `st` to all possible places
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 1000
#define CNT 1000

/* Function declaration */
void replaceAll(char *str, const char *oldWord, const char *newWord);


const char start_point[] = "struct memory_region *get_mem_region";


const char old_words[][200] = {
	"check_pc()",
	"  upd_pc(",
	"check_pc_incr()",
	"upd_reg(dst",
	"upd_reg(0U",
	"eval_reg(dst",
	"eval_reg(src",
	"upd_flag(",
	"eval_flag()",
	"check_mem(1U",
	"check_mem(2U",
	"upd_reg(1U",
	
	"eval_mrs_regions()",
	"void step_opcode_alu32(",
	"step_opcode_alu32(dst32",
	"void step_opcode_branch(",
	"step_opcode_branch(dst32",
	"void step_opcode_mem_ld_imm(",
	"step_opcode_mem_ld_imm(imm",
	"void step_opcode_mem_ld_reg(",
	
	"step_opcode_mem_ld_reg(addr",
	"void step_opcode_mem_st_imm(",
	"step_opcode_mem_st_imm(imm",
	"void step_opcode_mem_st_reg(",
	"step_opcode_mem_st_reg(src",
	"load_mem(1",
	"load_mem(2",
	"load_mem(4",
	"store_mem(addr_ptr",
	
	"unsigned char *check_mem_aux(",
	"return check_mem_aux(",
	"unsigned char *check_mem(",
	
	"void step(void)",
	"step();",
	"void bpf_interpreter_aux(",
	"bpf_interpreter_aux(fuel",	
	"unsigned int havm_interpreter(",
	"struct memory_region *get_mem_region(",
	"eval_reg(0",
	"eval_mrs_num()",
	"check_mem = check_mem_aux(",
	"check_mem_aux(mem_reg_num",
	
	"unsigned int get_dst(",
	"unsigned int get_src(",
	"int get_offset(",
	"int get_immediate(",
	"unsigned int get_src32(",
	"= get_src32(",
	"unsigned char get_opcode_ins(",
	"unsigned char get_opcode_alu32(",
	"unsigned char get_opcode_branch(",
	"unsigned char get_opcode_mem_ld_imm(",
	"unsigned char get_opcode_mem_ld_reg(",
	"unsigned char get_opcode_mem_st_imm(",
	"unsigned char get_opcode_mem_st_reg(",
	"unsigned char get_opcode_nat(",
	"unsigned int get_add(",
	"unsigned int get_sub(",
	"unsigned int get_addr_ofs(",
	"_Bool is_well_chunk_bool(",
	"unsigned char *check_mem_aux2(",
	"unsigned char *get_block_ptr",
	"unsigned int get_start_addr",
	"unsigned int get_block_size",
	"unsigned int get_block_perm",
	
	"unsigned long long *l",
	"eval_ins_len()",
	"eval_ins(",
	"exec_function(",
	"jit_call()"
	
	};

const char new_words[][200] = {
	"check_pc(st)",
	"  upd_pc(st, ",
	"check_pc_incr(st)",
	"upd_reg(st, dst",
	"upd_reg(st, 0U",
	"eval_reg(st, dst",
	"eval_reg(st, src",
	"upd_flag(st, ", 
	"eval_flag(st)",
	"check_mem(st, 1U",
	"check_mem(st, 2U",
	"upd_reg(st, 1U",
	
	"eval_mrs_regions(st)",
	"static __attribute__((always_inline)) inline void step_opcode_alu32(struct havm_state* st, ",
	"step_opcode_alu32(st, dst32",
	"static __attribute__((always_inline)) inline void step_opcode_branch(struct havm_state* st, ",
	"step_opcode_branch(st, dst32",
	"static __attribute__((always_inline)) inline void step_opcode_mem_ld_imm(struct havm_state* st, ",
	"step_opcode_mem_ld_imm(st, imm",
	"static __attribute__((always_inline)) inline void step_opcode_mem_ld_reg(struct havm_state* st, ",
	
	"step_opcode_mem_ld_reg(st, addr",
	"static __attribute__((always_inline)) inline void step_opcode_mem_st_imm(struct havm_state* st, ",
	"step_opcode_mem_st_imm(st, imm",
	"static __attribute__((always_inline)) inline void step_opcode_mem_st_reg(struct havm_state* st, ",
	"step_opcode_mem_st_reg(st, src",
	"load_mem(st, 1",
	"load_mem(st, 2",
	"load_mem(st, 4",
	"store_mem(st, addr_ptr",
	
	"static __attribute__((always_inline)) inline unsigned char *check_mem_aux(struct havm_state* st, ",
	"return check_mem_aux(st, ",
	"unsigned char *check_mem(struct havm_state* st, ",
	
	"static __attribute__((always_inline)) inline void step(struct havm_state* st)",
	"step(st); //print_havm_state(st);",
	"static __attribute__((always_inline)) inline void bpf_interpreter_aux(struct havm_state* st, ",
	"bpf_interpreter_aux(st, fuel",
	"unsigned int havm_interpreter(struct havm_state* st, ",
	"static __attribute__((always_inline)) inline struct memory_region *get_mem_region(",
	"eval_reg(st, 0",
	"eval_mrs_num(st)",
	"check_mem = check_mem_aux(st, ",
	"check_mem_aux(st, mem_reg_num",
	
	"static __attribute__((always_inline)) inline unsigned int get_dst(",
	"static __attribute__((always_inline)) inline unsigned int get_src(",	
	"static __attribute__((always_inline)) inline int get_offset(",
	"static __attribute__((always_inline)) inline int get_immediate(",
	"static __attribute__((always_inline)) inline unsigned int get_src32(struct havm_state* st, ",
	"= get_src32(st, ",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_ins(",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_alu32(",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_branch(",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_mem_ld_imm(",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_mem_ld_reg(",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_mem_st_imm(",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_mem_st_reg(",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_nat(",
	"static __attribute__((always_inline)) inline unsigned int get_add(",
	"static __attribute__((always_inline)) inline unsigned int get_sub(",
	"static __attribute__((always_inline)) inline unsigned int get_addr_ofs(",
	"static __attribute__((always_inline)) inline _Bool is_well_chunk_bool(",
	"static __attribute__((always_inline)) inline unsigned char *check_mem_aux2(",
	"static __attribute__((always_inline)) inline unsigned char *get_block_ptr",
	"static __attribute__((always_inline)) inline unsigned int get_start_addr",
	"static __attribute__((always_inline)) inline unsigned int get_block_size",
	"static __attribute__((always_inline)) inline unsigned int get_block_perm",
	
	"const unsigned long long *l",
	"eval_ins_len(st)",
	"eval_ins(st",
	"exec_function(st, ",
	"jit_call(st)"
	
	};
	


const char delete_lines[] ="extern ";

int main(int argc, char *argv[])
{
    /* File pointer to hold reference of input file */
    FILE * ptr_r;
    FILE * ptr_w;
    int counter = CNT;
    int index;
    int before_start_point;
    int two_blanks;
    
    char buffer[BUFFER_SIZE];



    /*  Open all required files */
  
    if (argc != 3) {
      printf("invaild argument%d: expect only two filenames `obj` and `output` \n", argc);
    }
  
    ptr_r = fopen(argv[1], "r");
    ptr_w = fopen(argv[2], "w+");

    /* fopen() return NULL if unable to open file in given mode. */
    if (ptr_r == NULL || ptr_w == NULL)
    {
        /* Unable to open file hence exit */
        printf("\nUnable to open file.\n");
        printf("Please check whether file exists and you have read/write privilege.\n");
        exit(EXIT_SUCCESS);
    }

    before_start_point = 0;
    two_blanks = 0;
    while ((fgets(buffer, BUFFER_SIZE, ptr_r)) != NULL)
    {  //printf("%d\n", CNT-counter);
    	//if ((counter --) == 0) { break; }
    	/* deleting all lines before `struct memory_region *get_mem_region` */
    	if (before_start_point == 0 && strstr(buffer, start_point) == NULL){
    	  /* we just skip this line and don't write it */
    	  continue;
    	}
    	else {
    	  before_start_point = 1;
    	}
    	
    	if (strcmp(buffer, "\n") == 0){
    	  if(two_blanks == 0){
    	    two_blanks = 1;
    	  }
    	  else {//two_blanks == 1
    	    //printf("skip\n");
    	    continue;
    	  }
    	}
    	else if(strcmp(buffer, "}\n") == 0) {
    	  /* we just skip this line and don't write it */
    	  two_blanks = 0;
    	}
    	
    	/* Delete all lines starting by `extern  ` */
    	if (strstr(buffer, delete_lines) != NULL){
    	  /* we just skip this line and don't write it */
    	  continue;
    	}
    	
    	if(strcmp(buffer,"\n") == 0) { fputs(buffer, ptr_w); continue; }
    
    	//printf("readline: %s\n", buffer);
        // Replace all occurrence of word from current line
        for (index = 0; index < sizeof(old_words)/200; index ++){
          replaceAll(buffer, old_words[index], new_words[index]);
        }

        // After replacing write it to temp file.
        fputs(buffer, ptr_w);
    }

    //printf("repatch2 done!\n");
    /* Close all files to release resource */
    fclose(ptr_r);
    fclose(ptr_w);

    return 0;
}



/**
 * Replace all occurrences of a given a word in string.
 */
void replaceAll(char *str, const char *oldWord, const char *newWord)
{
    char *pos, temp[BUFFER_SIZE];
    int index = 0;
    int owlen;

    owlen = strlen(oldWord);

    // Fix: If oldWord and newWord are same it goes to infinite loop
    if (!strcmp(oldWord, newWord)) {
        return;
    }

    if ((pos = strstr(str, oldWord)) == NULL) {return ;}
    /*
     * Repeat till all occurrences are replaced. 
     */
    //while ((pos = strstr(str, oldWord)) != NULL)
    //{
        // Backup current line
        strcpy(temp, str);

        // Index of current found word
        index = pos - str;

        // Terminate str after word found index
        str[index] = '\0';

        // Concatenate str with new word 
        strcat(str, newWord);
        
        // Concatenate str with remaining words after 
        // oldword found index.
        strcat(str, temp + index + owlen);
    //}
}
