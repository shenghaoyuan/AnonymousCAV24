/**
 * 1. deleting all lines before `_Bool ins_is_bpf_jump`
 * 2. deleting `\n\n`.
 * 2. deleting all `extern` lines
 * 3. adding `st` to all possible places
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BUFFER_SIZE 2000
#define CNT 2000

/* Function declaration */
void replaceAll(char *str, const char *oldWord, const char *newWord);


const char start_point[] = "_Bool ins_is_bpf_jump";


const char old_words[][200] = {
	"void jit_alu32_pre(void)",
	"= eval_load_regset(",
	"  upd_load_regset(",
	"  add_jited_bin(",
	"  upd_store_regset(",
	
	"void jit_call_save_add(",
	"  jit_call_save_add(",
	"void jit_call_save_imm(",
	"  jit_call_save_imm(",
	"= eval_input_ins(",
	
	"void jit_call_save_reg(",
	"  jit_call_save_reg(",
	"void mov_int_to_movwt(",
	"  mov_int_to_movwt(",
	"= eval_store_regset(",
	
	"void bpf_alu32_to_thumb_reg_comm(",
	"  bpf_alu32_to_thumb_reg_comm(",
	"void bpf_alu32_to_thumb_reg(",
	"  bpf_alu32_to_thumb_reg(",
	
	"void bpf_alu32_to_thumb_imm_comm(",
	"  bpf_alu32_to_thumb_imm_comm(",
	"void bpf_alu32_to_thumb_imm_shift_comm(",
	"  bpf_alu32_to_thumb_imm_shift_comm(",
	"void bpf_alu32_to_thumb_imm(",
	"  bpf_alu32_to_thumb_imm(",
	
	"_Bool jit_one(",
	"= jit_one(",
	"unsigned int jit_sequence(",
	"return jit_sequence(",
	"= jit_sequence(",
	
	"void jit_alu32_thumb_pc_add(",
	"  jit_alu32_thumb_pc_add(",
	"void jit_alu32_thumb_pc(",
	"  jit_alu32_thumb_pc(",
	
	"void jit_alu32_thumb_upd_store(",
	"  jit_alu32_thumb_upd_store(",
	"void jit_alu32_thumb_store(void)",
	"void jit_alu32_thumb_reset1(void)",
	"  jit_alu32_thumb_reset1()",
	
	"void jit_alu32_thumb_upd_reset(",
	"void jit_alu32_thumb_reset(void)",
	"  jit_alu32_thumb_upd_reset(",
	"void jit_alu32_post(void)",
	"jit_alu32_post()",
	
	"unsigned int jit_alu32_aux(",
	"reset_init_jittedthumb()",
	"jit_alu32_pre()",
	"jit_alu32_thumb_save()",
	"jit_alu32_thumb_load()",
	
	"jit_alu32_thumb_store()",
	"jit_alu32_thumb_reset()",
	"= jit_alu32_aux(",
	"return jit_alu32_aux(",
	"  add_key_value(",
	
	"unsigned int jit_list(",
	"= jit_list(",
	"void whole_compiler_aux(",
	"  whole_compiler_aux(",
	"void whole_compiler(void)",
	
	"int get_offset",
	"int get_immediate",
	"unsigned char get_opcode_ins",
	"unsigned char nat_to_opcode_alu32",
	"eval_input_len()",
	
	"  jit_list(",
	"  upd_IR11_jittedthumb(",
	"eval_use_IR11()",
	"eval_arm_ofs()",
	"void load_IR11(void)",
	"load_IR11()"
	};

const char new_words[][200] = {
	"static __attribute__((always_inline)) inline void jit_alu32_pre(struct jit_state* st)",
	"= eval_load_regset(st, ",
	"  upd_load_regset(st, ",
	"  add_jited_bin(st, ",
	"  upd_store_regset(st, ",
	
	"static __attribute__((always_inline)) inline void jit_call_save_add(struct jit_state* st, ",
	"  jit_call_save_add(st, ",
	"static __attribute__((always_inline)) inline void jit_call_save_imm(struct jit_state* st, ",
	"  jit_call_save_imm(st, ",
	"= eval_input_ins(st, ",
	
	"static __attribute__((always_inline)) inline void jit_call_save_reg(struct jit_state* st, ",
	"  jit_call_save_reg(st, ",
	"static __attribute__((always_inline)) inline void mov_int_to_movwt(struct jit_state* st, ",
	"  mov_int_to_movwt(st, ",
	"= eval_store_regset(st, ",
	
	"static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_reg_comm(struct jit_state* st,",
	"  bpf_alu32_to_thumb_reg_comm(st, ",
	"static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_reg(struct jit_state* st, ",
	"  bpf_alu32_to_thumb_reg(st, ",
	
	"static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_imm_comm(struct jit_state* st, ",
	"  bpf_alu32_to_thumb_imm_comm(st, ",
	"static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_imm_shift_comm(struct jit_state* st, ",
	"  bpf_alu32_to_thumb_imm_shift_comm(st, ",
	"static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_imm(struct jit_state* st, ",
	"  bpf_alu32_to_thumb_imm(st, ",
	
	"static __attribute__((always_inline)) inline _Bool jit_one(struct jit_state* st, ",
	"= jit_one(st, ",
	"static __attribute__((always_inline)) inline unsigned int jit_sequence(struct jit_state* st, ",
	"return jit_sequence(st, ",
	"= jit_sequence(st, ",
	
	"static __attribute__((always_inline)) inline void jit_alu32_thumb_pc_add(struct jit_state* st, ",
	"  jit_alu32_thumb_pc_add(st, ",
	"static __attribute__((always_inline)) inline void jit_alu32_thumb_pc(struct jit_state* st, ",
	"  jit_alu32_thumb_pc(st, ",
	
	"static __attribute__((always_inline)) inline void jit_alu32_thumb_upd_store(struct jit_state* st, ",
	"  jit_alu32_thumb_upd_store(st, ",
	"static __attribute__((always_inline)) inline void jit_alu32_thumb_store(struct jit_state* st)",
	"static __attribute__((always_inline)) inline void jit_alu32_thumb_reset1(struct jit_state* st)",
	"  jit_alu32_thumb_reset1(st)",
	
	"static __attribute__((always_inline)) inline void jit_alu32_thumb_upd_reset(struct jit_state* st, ",
	"static __attribute__((always_inline)) inline void jit_alu32_thumb_reset(struct jit_state* st)",
	"  jit_alu32_thumb_upd_reset(st, ",
	"static __attribute__((always_inline)) inline void jit_alu32_post(struct jit_state* st)",
	"jit_alu32_post(st)",
	
	"static __attribute__((always_inline)) inline unsigned int jit_alu32_aux(struct jit_state* st, ",
	"reset_init_jittedthumb(st)",
	"jit_alu32_pre(st)",
	"jit_alu32_thumb_save(st)",
	"jit_alu32_thumb_load(st)",
	
	"jit_alu32_thumb_store(st)",
	"jit_alu32_thumb_reset(st)",
	"= jit_alu32_aux(st, ",
	"return jit_alu32_aux(st, ",
	"  add_key_value(st, ",
	
	"static __attribute__((always_inline)) inline unsigned int jit_list(struct jit_state* st, ",
	"= jit_list(st, ",
	"static __attribute__((always_inline)) inline void whole_compiler_aux(struct jit_state* st, ",
	"  whole_compiler_aux(st, ",
	"void whole_compiler(struct jit_state* st)",
	
	"static __attribute__((always_inline)) inline int get_offset",
	"static __attribute__((always_inline)) inline int get_immediate",
	"static __attribute__((always_inline)) inline unsigned char get_opcode_ins",
	"static __attribute__((always_inline)) inline unsigned char nat_to_opcode_alu32",
	"eval_input_len(st)",
	
	"  jit_list(st, ",
	"  upd_IR11_jittedthumb(st, ",
	"eval_use_IR11(st)",
	"eval_arm_ofs(st)",
	"static __attribute__((always_inline)) inline void load_IR11(struct jit_state* st)",
	"load_IR11(st)"
	
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
