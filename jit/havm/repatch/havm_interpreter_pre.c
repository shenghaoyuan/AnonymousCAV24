#include "havm_interpreter.h"

static __attribute__((always_inline)) inline _Bool check_pc (struct havm_state* st) {
  return (*st).pc_loc < (*st).input_len;
}
static __attribute__((always_inline)) inline _Bool check_pc_incr(struct havm_state* st) {
  return (*st).pc_loc+1 < (*st).input_len;
}

static __attribute__((always_inline)) inline void upd_pc(struct havm_state* st, unsigned int pc) {
  (*st).pc_loc += pc;
  return ;
}


static __attribute__((always_inline)) inline unsigned int eval_reg(struct havm_state* st, unsigned int i){
  return (*st).regsmap[i];
}

static __attribute__((always_inline)) inline void upd_reg (struct havm_state* st, unsigned int i, unsigned int v){
  (*st).regsmap[i] = v;
  return ;
}

static __attribute__((always_inline)) inline unsigned eval_flag(struct havm_state* st){
  return (*st).bpf_flag;
}

static __attribute__((always_inline)) inline void upd_flag(struct havm_state* st, unsigned f){
  (*st).bpf_flag = f;
  return ;
}

static __attribute__((always_inline)) inline unsigned int eval_mrs_num(struct havm_state* st){
  return (*st).mrs_num;
}

static __attribute__((always_inline)) inline struct memory_region *eval_mrs_regions(struct havm_state* st){
  return (*st).mrs;
}

/*
void add_mem_region(struct havm_state* st, struct memory_region* mr){
  (*st).mrs[(*st).mem_num] = *mr;
  (*st).mem_num += 1;
  return ;
}

void add_mem_region_ctx(struct havm_state* st, struct memory_region* mr){
  (*st).mrs[0] = *mr;
  (*st).mem_num = 1;
  return ;
} */

static __attribute__((always_inline)) inline unsigned int load_mem(struct havm_state* st, unsigned int chunk, unsigned char* addr){
  /*if (addr == 0U) {
    (*st).bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
  else{*/
    switch (chunk) {
      case 1: return *(unsigned char *) addr;
      case 2: return *(unsigned short *) addr;
      case 4: return *(unsigned int *) addr;
      default: /*printf ("load:addr = %" PRIu64 "\n", v); (*st).bpf_flag = BPF_ILLEGAL_MEM;*/ return 0LLU;
    }
  //}
}

static __attribute__((always_inline)) inline void store_mem(struct havm_state* st, unsigned char* addr, unsigned int chunk, unsigned int v){
  /*if (addr == 0U) {
    (*st).bpf_flag = BPF_ILLEGAL_MEM; return ;
  }
  else{*/
    switch (chunk) {
      case 1: *(unsigned char *) addr = v; return ;
      case 2: *(unsigned short *) addr = v; return ;
      case 4: *(unsigned int *) addr = v; return ;
      default: /*printf ("store_imm:addr = %" PRIu64 "\n", addr); (*st).bpf_flag = BPF_ILLEGAL_MEM;*/ return ;
    }
  //}
}

static __attribute__((always_inline)) inline unsigned long long eval_ins(struct havm_state* st)
{
  return *((*st).input_ins + (*st).pc_loc);
}

static __attribute__((always_inline)) inline _Bool cmp_ptr32_nullM(unsigned char* addr){
   return (addr == 0);
}

static __attribute__((always_inline)) inline unsigned int get_dst(unsigned long long ins)
{
  return (unsigned int) ((ins & 4095LLU) >> 8LLU);
}

static __attribute__((always_inline)) inline unsigned int get_src(unsigned long long ins)
{
  return (unsigned int) ((ins & 65535LLU) >> 12LLU);
}

static __attribute__((always_inline)) inline struct memory_region *get_mem_region(unsigned int n, struct memory_region *mrs)
{
  return mrs + n;
}

static __attribute__((always_inline)) inline void jit_call(struct havm_state* st){
  //_magic_function is user-defined or compcert build-in
  // for user-defined, we swapped the order to make sure r0 is the start address of jitted_list while r1 is the start address of jit_state.
  unsigned int ofs;
  ofs = (*st).tp_kv[(*st).pc_loc].arm_ofs;
  _magic_function(ofs, st);
  (*st).pc_loc += (*st).tp_kv[(*st).pc_loc].alu32_ofs;
  return ;
}

static __attribute__((always_inline)) inline unsigned char *_bpf_get_call(int imm) {
  /* deleting `return NULL;` and adding your system APIs
  switch (imm) {
    default: return ...
  }
  */
  return NULL;
}

static __attribute__((always_inline)) inline unsigned int exec_function(struct havm_state* st, unsigned char * ptr){
  if (ptr == 0){
    (*st).bpf_flag = vBPF_ILLEGAL_CALL;
    return 0U;
  }
  else {
    /**do something e.g. print; */
    return 0U;
  }
}

/*******************below code are automatically generated by dx (after repatch) ***************************/
