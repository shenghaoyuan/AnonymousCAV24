#include "rbpf_jit_compiler.h"

static __attribute__((always_inline)) inline unsigned int eval_input_len(struct jit_state* st)
{
  return (*st).input_len;
}

static __attribute__((always_inline)) inline unsigned long long eval_input_ins(struct jit_state* st, unsigned int idx)
{ //print_jit_state(st);
  return *((*st).input_ins + idx);
}

static __attribute__((always_inline)) inline unsigned int get_dst(unsigned long long ins)
{
  return (unsigned int) ((ins & 4095LLU) >> 8LLU);
}

static __attribute__((always_inline)) inline unsigned int get_src(unsigned long long ins)
{
  return (unsigned int) ((ins & 65535LLU) >> 12LLU);
}

static __attribute__((always_inline)) inline unsigned int eval_arm_ofs(struct jit_state* st)
{
  return (*st).tp_bin_len;
}

static __attribute__((always_inline)) inline void add_key_value(struct jit_state* st, unsigned int pc, unsigned int ofs0, unsigned int ofs1){
  (*st).tp_kv[pc].arm_ofs = ofs0;
  (*st).tp_kv[pc].alu32_ofs = ofs1-1;
  return ;
}

static __attribute__((always_inline)) inline _Bool eval_use_IR11(struct jit_state* st){
  return (*st).use_IR11;
}

static __attribute__((always_inline)) inline void upd_IR11_jittedthumb(struct jit_state* st, _Bool f){
  (*st).use_IR11 = f;
  return ;
}

static __attribute__((always_inline)) inline void add_jited_bin(struct jit_state* st, unsigned int ins){
  //if ((*st).tp_bin_len < JITTED_LIST_MAX_LENGTH){
    (*st).tp_bin[(*st).tp_bin_len] = ins;
    (*st).tp_bin_len = (*st).tp_bin_len + 1U;
    return ; /*
  }
  else {
    // *((*st).flag) = vBPF_ILLEGAL_ARM_LEN;
    return ;
  } */
}

static __attribute__((always_inline)) inline _Bool eval_load_regset(struct jit_state* st, unsigned int r){
  return (*st).ld_set[r];
}

static __attribute__((always_inline)) inline _Bool eval_store_regset(struct jit_state* st, unsigned int r){
  return (*st).st_set[r];
}

static __attribute__((always_inline)) inline void upd_load_regset(struct jit_state* st, unsigned int r){
  (*st).ld_set[r] = 1; //set to true
  return ;
}

static __attribute__((always_inline)) inline void upd_store_regset(struct jit_state* st, unsigned int r){
  (*st).st_set[r] = 1;
  return ;
}

static __attribute__((always_inline)) inline void reset_init_jittedthumb(struct jit_state* st){
  (*st).use_IR11 = 0;
  for (unsigned int i = 0; i < 11; i ++) { (*st).ld_set[i]  = 0; (*st).st_set[i]  = 0; }
  return ;
}

// a recursion implementation of power2 to replace pow(2, _) from math.h because CompCert doesn't support math.h
static __attribute__((always_inline)) inline unsigned int power2(unsigned int width){
  if (width == 0U) {
    return 1U;
  }
  else {
    return 2U * power2(width - 1U);
  }
}

static __attribute__((always_inline)) inline unsigned int decode_thumb(unsigned int ins, unsigned int from, unsigned int size){
  return ( (ins >> from) & (power2(size) - 1U) );
}

static __attribute__((always_inline)) inline unsigned int encode_thumb(unsigned int v, unsigned int ins, unsigned int from, unsigned int size){
  unsigned int mask;
  mask = (power2(size) - 1U) << from;
  return ( ((v & (power2(size) - 1U)) << from) | (ins & (~mask)) );
}

static __attribute__((always_inline)) inline _Bool ins_is_bpf_alu32(unsigned long long ins){
  unsigned char op;
  op = (unsigned char) (ins & 255LLU);
  return (op == 4) || (op == 12) ||
  	 (op == 20) || (op == 28) ||
  	 (op == 36) || (op == 44) ||
  	 (op == 60) ||
  	 (op == 68) || (op == 76) ||
  	 (op == 84) || (op == 92) ||
  	 (op == 108) || (op == 124) ||
  	 (op == 132) ||
  	 (op == 164) || (op == 172) ||
  	 (op == 180) || (op == 188) ||
  	 (op == 204);
}
static __attribute__((always_inline)) inline _Bool ins_is_bpf_jump(unsigned long long ins){
  unsigned char op;
  op = (unsigned char) (ins & 255LLU);
  return (op == 5) ||
  	 (op == 21) || (op == 29) ||
  	 (op == 37) || (op == 45) ||
  	 (op == 53) || (op == 61) ||
  	 (op == 69) || (op == 77) ||
  	 (op == 85) || (op == 93) ||
  	 (op == 101) || (op == 109) ||
  	 (op == 117) || (op == 125) ||
  	 (op == 165) || (op == 173) ||
  	 (op == 181) || (op == 189) ||
  	 (op == 197) || (op == 205) ||
  	 (op == 213) || (op == 221);
  
}

/*******************below code are automatically generated by dx (after repatch) ***************************/

static __attribute__((always_inline)) inline int get_immediate(unsigned long long ins)
{
  return (int) (ins >> 32LLU);
}

static __attribute__((always_inline)) inline int get_offset(unsigned long long ins)
{
  return (int) (short) (ins << 32LLU >> 48LLU);
}

static __attribute__((always_inline)) inline unsigned char get_opcode_ins(unsigned long long ins)
{
  return (unsigned char) (ins & 255LLU);
}

unsigned int jit_alu32_thumb_mem_template_jit(unsigned short op, unsigned short rt, unsigned short rn, unsigned short imm12)
{
  unsigned int str_low;
  unsigned int str_high;
  str_low = encode_thumb(rn, op, 0U, 4U);
  str_high = encode_thumb(rt, imm12, 12U, 4U);
  return encode_thumb(str_high, str_low, 16U, 16U);
}

static __attribute__((always_inline)) inline void jit_alu32_pre(struct jit_state* st)
{
  unsigned int ins_rdn;
  unsigned int ins_rm;
  unsigned int ins;
  unsigned int ins32;
  ins_rdn = encode_thumb(4, 17920, 0U, 3U);
  ins_rm = encode_thumb(1, ins_rdn, 3U, 4U);
  ins = encode_thumb(1, ins_rm, 7U, 1U);
  ins32 = encode_thumb(ins, 48896, 16U, 16U);
  add_jited_bin(st, ins32);
  return;
}

static __attribute__((always_inline)) inline void jit_call_save_add(struct jit_state* st, unsigned int r)
{
  _Bool cond;
  unsigned int ldr_ins;
  unsigned int str_ins;
  cond = eval_load_regset(st, r);
  if (cond) {
    return;
  } else {
    ldr_ins = jit_alu32_thumb_mem_template_jit(63696, r, 12, r * 4);
    if (3 < r && r < 12) {
      str_ins = jit_alu32_thumb_mem_template_jit(63680, r, 13, r * 4);
      add_jited_bin(st, str_ins);
      add_jited_bin(st, ldr_ins);
      return;
    } else {
      add_jited_bin(st, ldr_ins);
      return;
    }
  }
}

static __attribute__((always_inline)) inline void jit_call_save_reg(struct jit_state* st, unsigned int dst, unsigned int src)
{
  jit_call_save_add(st, dst);
  upd_load_regset(st, dst);
  upd_store_regset(st, dst);
  jit_call_save_add(st, src);
  upd_load_regset(st, src);
  return;
}

static __attribute__((always_inline)) inline void jit_call_save_imm(struct jit_state* st, unsigned int dst)
{
  jit_call_save_add(st, dst);
  upd_load_regset(st, dst);
  upd_store_regset(st, dst);
  return;
}

static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_reg_comm(struct jit_state* st,unsigned short op, unsigned short dst, unsigned short src)
{
  unsigned int ins_lo;
  unsigned int ins_hi;
  unsigned int ins32;
  ins_lo = encode_thumb(dst, op, 0U, 4U);
  ins_hi = encode_thumb(dst, src, 8U, 4U);
  ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
  add_jited_bin(st, ins32);
  return;
}

static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_reg(struct jit_state* st, unsigned char op, unsigned short dst, unsigned short src)
{
  unsigned int d;
  unsigned short rdn;
  unsigned int ins_rdn;
  unsigned int ins_rm;
  unsigned int ins;
  unsigned int ins32;
  unsigned int ins_lo;
  unsigned int ins_hi0;
  unsigned int ins_hi;
  switch (op) {
    case 12:
      if (dst < 8) {
        d = 0;
      } else {
        d = 1;
      }
      if (dst < 8) {
        rdn = dst;
      } else {
        rdn = dst - 8;
      }
      ins_rdn = encode_thumb(rdn, 17408, 0U, 3U);
      ins_rm = encode_thumb(src, ins_rdn, 3U, 4U);
      ins = encode_thumb(d, ins_rm, 7U, 1U);
      ins32 = encode_thumb(ins, 48896, 16U, 16U);
      add_jited_bin(st, ins32);
      return;
    case 28:
      bpf_alu32_to_thumb_reg_comm(st, 60320, dst, src);
      return;
    case 44:
      ins_lo = encode_thumb(dst, 64256, 0U, 4U);
      ins_hi0 = encode_thumb(dst, src, 8U, 4U);
      ins_hi = encode_thumb(15, ins_hi0, 12U, 4U);
      ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
      add_jited_bin(st, ins32);
      return;
    case 76:
      bpf_alu32_to_thumb_reg_comm(st, 59968, dst, src);
      return;
    case 92:
      bpf_alu32_to_thumb_reg_comm(st, 59904, dst, src);
      return;
    case 108:
      ins_lo = encode_thumb(dst, 64000, 0U, 4U);
      ins_hi0 = encode_thumb(dst, src, 8U, 4U);
      ins_hi = encode_thumb(15, ins_hi0, 12U, 4U);
      ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
      add_jited_bin(st, ins32);
      return;
    case 124:
      ins_lo = encode_thumb(dst, 64032, 0U, 4U);
      ins_hi0 = encode_thumb(dst, src, 8U, 4U);
      ins_hi = encode_thumb(15, ins_hi0, 12U, 4U);
      ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
      add_jited_bin(st, ins32);
      return;
    case 172:
      bpf_alu32_to_thumb_reg_comm(st, 60032, dst, src);
      return;
    case 188:
      if (dst == src) {
        return;
      } else {
        if (dst < 8) {
          d = 0;
        } else {
          d = 1;
        }
        if (dst < 8) {
          rdn = dst;
        } else {
          rdn = dst - 8;
        }
        ins_rdn = encode_thumb(rdn, 17920, 0U, 3U);
        ins_rm = encode_thumb(src, ins_rdn, 3U, 4U);
        ins = encode_thumb(d, ins_rm, 7U, 1U);
        ins32 = encode_thumb(ins, 48896, 16U, 16U);
        add_jited_bin(st, ins32);
        return;
      }
    case 204:
      ins_lo = encode_thumb(dst, 64064, 0U, 4U);
      ins_hi0 = encode_thumb(dst, src, 8U, 4U);
      ins_hi = encode_thumb(15, ins_hi0, 12U, 4U);
      ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
      add_jited_bin(st, ins32);
      return;
    default:
      return;
    
  }
}

static __attribute__((always_inline)) inline void load_IR11(struct jit_state* st)
{
  _Bool f;
  unsigned int str;
  f = eval_use_IR11(st);
  if (f) {
    return;
  } else {
    upd_IR11_jittedthumb(st, 1);
    str = jit_alu32_thumb_mem_template_jit(63680, 11, 13, 44);
    add_jited_bin(st, str);
    return;
  }
}

static __attribute__((always_inline)) inline void mov_int_to_movwt(struct jit_state* st, unsigned int i, unsigned short r, unsigned short op)
{
  unsigned int lo_imm8;
  unsigned int lo_imm3;
  unsigned int lo_i;
  unsigned int lo_imm4;
  unsigned int movw_lo_0;
  unsigned int movw_lo;
  unsigned int movw_hi_0;
  unsigned int movw_hi;
  unsigned int ins32;
  load_IR11(st);
  lo_imm8 = decode_thumb(i, 0U, 8U);
  lo_imm3 = decode_thumb(i, 8U, 3U);
  lo_i = decode_thumb(i, 11U, 1U);
  lo_imm4 = decode_thumb(i, 12U, 4U);
  movw_lo_0 = encode_thumb(lo_imm4, op, 0U, 4U);
  movw_lo = encode_thumb(lo_i, movw_lo_0, 10U, 1U);
  movw_hi_0 = encode_thumb(r, lo_imm8, 8U, 4U);
  movw_hi = encode_thumb(lo_imm3, movw_hi_0, 12U, 3U);
  ins32 = encode_thumb(movw_hi, movw_lo, 16U, 16U);
  add_jited_bin(st, ins32);
  return;
}

static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_imm_comm(struct jit_state* st, unsigned short op, unsigned char alu_op, unsigned short dst, unsigned int imm32)
{
  unsigned int ins_lo;
  unsigned int ins_hi;
  unsigned int ins32;
  unsigned int lo_32;
  unsigned int hi_32;
  if (0U <= imm32 && imm32 <= 255U) {
    ins_lo = encode_thumb(dst, op, 0U, 4U);
    ins_hi = encode_thumb(dst, imm32, 8U, 4U);
    ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
    add_jited_bin(st, ins32);
    return;
  } else {
    lo_32 = decode_thumb(imm32, 0U, 16U);
    hi_32 = decode_thumb(imm32, 16U, 16U);
    mov_int_to_movwt(st, lo_32, 11, 62016);
    if (lo_32 == imm32) {
      bpf_alu32_to_thumb_reg(st, alu_op, dst, 11);
      return;
    } else {
      mov_int_to_movwt(st, hi_32, 11, 62144);
      bpf_alu32_to_thumb_reg(st, alu_op, dst, 11);
      return;
    }
  }
}

static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_imm_shift_comm(struct jit_state* st, unsigned short op, unsigned short dst, unsigned int imm32)
{
  unsigned int ins_lo;
  unsigned int ins_hi0;
  unsigned int ins_hi;
  unsigned int ins32;
  if (0U <= imm32 && imm32 < 32U) {
    ins_lo = encode_thumb(dst, op, 0U, 4U);
    ins_hi0 = encode_thumb(dst, 11, 8U, 4U);
    ins_hi = encode_thumb(15, ins_hi0, 12U, 4U);
    ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
    mov_int_to_movwt(st, imm32, 11, 62016);
    add_jited_bin(st, ins32);
    return;
  } else {
    return;
  }
}

static __attribute__((always_inline)) inline void bpf_alu32_to_thumb_imm(struct jit_state* st, unsigned char op, unsigned short dst, unsigned int imm32)
{
  unsigned int lo_32;
  unsigned int hi_32;
  unsigned int ins_lo;
  unsigned int ins_hi0;
  unsigned int ins_hi;
  unsigned int ins32;
  switch (op) {
    case 4:
      bpf_alu32_to_thumb_imm_comm(st, 61696, 12U, dst, imm32);
      return;
    case 20:
      bpf_alu32_to_thumb_imm_comm(st, 61856, 28U, dst, imm32);
      return;
    case 36:
      lo_32 = decode_thumb(imm32, 0U, 16U);
      hi_32 = decode_thumb(imm32, 16U, 16U);
      mov_int_to_movwt(st, lo_32, 11, 62016);
      if (lo_32 == imm32) {
        bpf_alu32_to_thumb_reg(st, 44U, dst, 11);
        return;
      } else {
        mov_int_to_movwt(st, hi_32, 11, 62144);
        bpf_alu32_to_thumb_reg(st, 44U, dst, 11);
        return;
      }
    case 52:
      if (imm32 == 0U) {
        return;
      } else {
        ins_lo = encode_thumb(dst, 64432, 0U, 4U);
        ins_hi0 = encode_thumb(dst, 61680, 8U, 4U);
        ins_hi = encode_thumb(11, ins_hi0, 0U, 4U);
        ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
        lo_32 = decode_thumb(imm32, 0U, 16U);
        hi_32 = decode_thumb(imm32, 16U, 16U);
        mov_int_to_movwt(st, lo_32, 11, 62016);
        if (lo_32 == imm32) {
          add_jited_bin(st, ins32);
          return;
        } else {
          mov_int_to_movwt(st, hi_32, 11, 62144);
          add_jited_bin(st, ins32);
          return;
        }
      }
    case 68:
      bpf_alu32_to_thumb_imm_comm(st, 61504, 76U, dst, imm32);
      return;
    case 84:
      bpf_alu32_to_thumb_imm_comm(st, 61440, 92U, dst, imm32);
      return;
    case 100:
      bpf_alu32_to_thumb_imm_shift_comm(st, 64000, dst, imm32);
      return;
    case 116:
      bpf_alu32_to_thumb_imm_shift_comm(st, 64032, dst, imm32);
      return;
    case 132:
      ins_lo = encode_thumb(11, 61888, 0U, 4U);
      ins_hi = encode_thumb(dst, 0, 8U, 4U);
      ins32 = encode_thumb(ins_hi, ins_lo, 16U, 16U);
      lo_32 = decode_thumb(imm32, 0U, 16U);
      hi_32 = decode_thumb(imm32, 16U, 16U);
      mov_int_to_movwt(st, lo_32, 11, 62016);
      if (lo_32 == imm32) {
        add_jited_bin(st, ins32);
        return;
      } else {
        mov_int_to_movwt(st, hi_32, 11, 62144);
        add_jited_bin(st, ins32);
        return;
      }
    case 164:
      bpf_alu32_to_thumb_imm_comm(st, 61568, 172U, dst, imm32);
      return;
    case 180:
      lo_32 = decode_thumb(imm32, 0U, 16U);
      hi_32 = decode_thumb(imm32, 16U, 16U);
      mov_int_to_movwt(st, lo_32, dst, 62016);
      if (lo_32 == imm32) {
        return;
      } else {
        mov_int_to_movwt(st, hi_32, dst, 62144);
        return;
      }
    case 196:
      bpf_alu32_to_thumb_imm_shift_comm(st, 64064, dst, imm32);
      return;
    default:
      return;
    
  }
}

static __attribute__((always_inline)) inline unsigned char nat_to_opcode_alu32(unsigned char op)
{
  if ((op & 7U) == 4U) {
    if (0U == (op & 8U)) {
      return 4U;
    } else {
      return 12U;
    }
  } else {
    return 0U;
  }
}

static __attribute__((always_inline)) inline unsigned char nat_to_opcode_alu32_reg(unsigned char op)
{
  return op;
}

static __attribute__((always_inline)) inline unsigned char nat_to_opcode_alu32_imm(unsigned char op)
{
  return op;
}

static __attribute__((always_inline)) inline _Bool jit_one(struct jit_state* st, unsigned long long ins)
{
  unsigned char op;
  unsigned char opc;
  unsigned int dst;
  int imm32;
  unsigned char opr;
  unsigned int src;
  unsigned char opi;
  op = get_opcode_ins(ins);
  opc = nat_to_opcode_alu32(op);
  dst = get_dst(ins);
  imm32 = get_immediate(ins);
  switch (opc) {
    case 12:
      opr = nat_to_opcode_alu32_reg(op);
      src = get_src(ins);
      jit_call_save_reg(st, dst, src);
      bpf_alu32_to_thumb_reg(st, opr, dst, src);
      return 1;
    case 4:
      opi = nat_to_opcode_alu32_imm(op);
      jit_call_save_imm(st, dst);
      bpf_alu32_to_thumb_imm(st, opi, dst, imm32);
      return 1;
    default:
      return 0;
    
  }
}

static __attribute__((always_inline)) inline unsigned int jit_sequence(struct jit_state* st, unsigned int fuel, unsigned int pc, unsigned int counter)
{
  unsigned int n;
  unsigned long long ins64;
  _Bool cond;
  if (fuel == 0U) {
    return counter;
  } else {
    n = fuel - 1U;
    ins64 = eval_input_ins(st, pc);
    cond = jit_one(st, ins64);
    if (cond) {
      return jit_sequence(st, n, pc + 1U, counter + 1U);
    } else {
      return counter;
    }
  }
}

static __attribute__((always_inline)) inline void jit_alu32_thumb_upd_store(struct jit_state* st, unsigned int r)
{
  _Bool cond;
  unsigned int ins32;
  cond = eval_store_regset(st, r);
  if (cond) {
    ins32 = jit_alu32_thumb_mem_template_jit(63680, r, 12, r * 4);
    add_jited_bin(st, ins32);
    return;
  } else {
    return;
  }
}

static __attribute__((always_inline)) inline void jit_alu32_thumb_store(struct jit_state* st)
{
  jit_alu32_thumb_upd_store(st, 0U);
  jit_alu32_thumb_upd_store(st, 1U);
  jit_alu32_thumb_upd_store(st, 2U);
  jit_alu32_thumb_upd_store(st, 3U);
  jit_alu32_thumb_upd_store(st, 4U);
  jit_alu32_thumb_upd_store(st, 5U);
  jit_alu32_thumb_upd_store(st, 6U);
  jit_alu32_thumb_upd_store(st, 7U);
  jit_alu32_thumb_upd_store(st, 8U);
  jit_alu32_thumb_upd_store(st, 9U);
  jit_alu32_thumb_upd_store(st, 10U);
  return;
}

static __attribute__((always_inline)) inline void jit_alu32_thumb_upd_reset(struct jit_state* st, unsigned int r)
{
  _Bool cond;
  unsigned int ins32;
  cond = eval_load_regset(st, r);
  if (cond) {
    ins32 = jit_alu32_thumb_mem_template_jit(63696, r, 13, r * 4);
    add_jited_bin(st, ins32);
    return;
  } else {
    return;
  }
}

static __attribute__((always_inline)) inline void jit_alu32_thumb_reset1(struct jit_state* st)
{
  jit_alu32_thumb_upd_reset(st, 4U);
  jit_alu32_thumb_upd_reset(st, 5U);
  jit_alu32_thumb_upd_reset(st, 6U);
  jit_alu32_thumb_upd_reset(st, 7U);
  jit_alu32_thumb_upd_reset(st, 8U);
  jit_alu32_thumb_upd_reset(st, 9U);
  jit_alu32_thumb_upd_reset(st, 10U);
  return;
}

static __attribute__((always_inline)) inline void jit_alu32_thumb_reset(struct jit_state* st)
{
  _Bool f;
  unsigned int l_ldr;
  f = eval_use_IR11(st);
  if (f) {
    l_ldr = jit_alu32_thumb_mem_template_jit(63696, 11, 13, 44);
    add_jited_bin(st, l_ldr);
  }
  jit_alu32_thumb_reset1(st);
  return;
}

static __attribute__((always_inline)) inline void jit_alu32_post(struct jit_state* st)
{
  unsigned int l_ldr;
  unsigned int ins_rm;
  unsigned int ins32;
  l_ldr = jit_alu32_thumb_mem_template_jit(63696, 13, 13, 0);
  ins_rm = encode_thumb(14, 18176, 3U, 4U);
  ins32 = encode_thumb(ins_rm, 48896, 16U, 16U);
  add_jited_bin(st, l_ldr);
  add_jited_bin(st, ins32);
  return;
}

static __attribute__((always_inline)) inline unsigned int jit_alu32_aux(struct jit_state* st, unsigned int fuel, unsigned int pc, unsigned int counter)
{
  unsigned int n;
  jit_alu32_pre(st);
  n = jit_sequence(st, fuel, pc, counter);
  jit_alu32_thumb_store(st);
  jit_alu32_thumb_reset(st);
  jit_alu32_post(st);
  return n;
}

static __attribute__((always_inline)) inline unsigned int jit_list(struct jit_state* st, unsigned int fuel, unsigned int pc)
{
  reset_init_jittedthumb(st);
  return jit_alu32_aux(st, fuel, pc, 0U);
}

static __attribute__((always_inline)) inline void whole_compiler_aux(struct jit_state* st, unsigned int fuel, unsigned int pc)
{
  unsigned int n;
  unsigned int len;
  unsigned long long ins64;
  _Bool b;
  unsigned int arm_ofs;
  unsigned int sz;
  int ofs;
  unsigned int next_pc;
  unsigned long long next_ins;
  if (fuel == 0U) {
    return;
  } else {
    n = fuel - 1U;
    len = eval_input_len(st);
    if (len == pc) {
      return;
    } else {
      ins64 = eval_input_ins(st, pc);
      b = ins_is_bpf_alu32(ins64);
      if (b) {
        arm_ofs = eval_arm_ofs(st);
        sz = jit_list(st, len - pc, pc);
        add_key_value(st, pc, arm_ofs, sz);
        whole_compiler_aux(st, n, pc + sz);
        return;
      } else {
        b = ins_is_bpf_jump(ins64);
        if (b) {
          ofs = get_offset(ins64);
          next_pc = pc + ofs + 1U;
          next_ins = eval_input_ins(st, next_pc);
          b = ins_is_bpf_alu32(next_ins);
          if (b) {
            arm_ofs = eval_arm_ofs(st);
            sz = jit_list(st, len - next_pc, next_pc);
            add_key_value(st, next_pc, arm_ofs, sz);
            whole_compiler_aux(st, n, pc + 1U);
            return;
          } else {
            whole_compiler_aux(st, n, pc + 1U);
            return;
          }
        } else {
          whole_compiler_aux(st, n, pc + 1U);
          return;
        }
      }
    }
  }
}

void whole_compiler(struct jit_state* st)
{
  unsigned int len;
  len = eval_input_len(st);
  whole_compiler_aux(st, len, 0U);
  return;
}

