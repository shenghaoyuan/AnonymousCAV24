
val negb : bool -> bool

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val div2 : int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val coq_land : int -> int -> int
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val div2 : int -> int

  val div2_up : int -> int

  val size : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val testbit : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int

  val eq_dec : int -> int -> bool
 end

module N :
 sig
  val succ_double : int -> int

  val double : int -> int

  val succ_pos : int -> int

  val sub : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val pos_div_eucl : int -> int -> int * int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val testbit : int -> int -> bool
 end

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val pred : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val eqb : int -> int -> bool

  val to_nat : int -> int

  val of_nat : int -> int

  val of_N : int -> int

  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : int -> int -> int * int

  val div_eucl : int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val quotrem : int -> int -> int * int

  val quot : int -> int -> int

  val rem : int -> int -> int

  val odd : int -> bool

  val div2 : int -> int

  val log2 : int -> int

  val testbit : int -> int -> bool

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val eq_dec : int -> int -> bool
 end

val z_lt_dec : int -> int -> bool

val z_le_dec : int -> int -> bool

val z_le_gt_dec : int -> int -> bool

val nth_error : 'a1 list -> int -> 'a1 option

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val shift_nat : int -> int -> int

val shift_pos : int -> int -> int

val two_power_nat : int -> int

val two_power_pos : int -> int

val two_p : int -> int

val zeq : int -> int -> bool

val zlt : int -> int -> bool

val zle : int -> int -> bool

val proj_sumbool : bool -> bool

val p_mod_two_p : int -> int -> int

val zshiftin : bool -> int -> int

val zzero_ext : int -> int -> int

val zsign_ext : int -> int -> int

val z_one_bits : int -> int -> int -> int list

val p_is_power2 : int -> bool

val z_is_power2 : int -> int option

val zsize : int -> int

type comparison0 =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : int
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : int

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  type int = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int -> int -> int

  val sign_ext : int -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int -> int -> int -> bool

  val size : int -> int

  val unsigned_bitfield_extract : int -> int -> int -> int

  val signed_bitfield_extract : int -> int -> int -> int

  val bitfield_insert : int -> int -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : int
 end

module Int :
 sig
  val wordsize : int

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  val intval : int -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val zero_ext : int -> int -> int

  val sign_ext : int -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int -> int -> int -> bool

  val size : int -> int

  val unsigned_bitfield_extract : int -> int -> int -> int

  val signed_bitfield_extract : int -> int -> int -> int

  val bitfield_insert : int -> int -> int -> int -> int
 end

module Wordsize_64 :
 sig
  val wordsize : int
 end

module Int64 :
 sig
  val wordsize : int

  val modulus : int

  val intval : int -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val repr : int -> int

  val coq_and : int -> int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int
 end

type ident = int

type typ =
| Tint
| Tfloat
| Tlong
| Tsingle
| Tany32
| Tany64

type rettype =
| Tret of typ
| Tint8signed
| Tint8unsigned
| Tint16signed
| Tint16unsigned
| Tvoid

type calling_convention = { cc_vararg : int option; cc_unproto : bool;
                            cc_structret : bool }

type signature = { sig_args : typ list; sig_res : rettype;
                   sig_cc : calling_convention }

type ireg =
| IR0
| IR1
| IR2
| IR3
| IR4
| IR5
| IR6
| IR7
| IR8
| IR9
| IR10
| IR11
| IR12
| IR13
| IR14

val encode_arm32 : int -> int -> int -> int -> int

val decode_arm32 : int -> int -> int -> int

type signedness =
| Signed
| Unsigned

val int64_to_sint32 : int -> int

val get_dst : int -> int

val get_src : int -> int

val get_opcode : int -> int

val get_offset : int -> int

val get_immediate : int -> int

type 'a set = 'a list

val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set

val set_mem : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> bool

type breg =
| R0
| R1
| R2
| R3
| R4
| R5
| R6
| R7
| R8
| R9
| R10

type listset = breg set

val z_of_breg : breg -> int

val breg_eq : breg -> breg -> bool

val int_of_breg : breg -> int

type off = int

type imm = int

type aluOp =
| ADD
| SUB
| MUL
| DIV
| OR
| AND
| LSH
| RSH
| NEG
| MOD
| XOR
| MOV
| ARSH

type cmpOp =
| EQ
| NE
| SET
| GT of signedness
| GE of signedness
| LT of signedness
| LE of signedness

type sizeOp =
| Byte
| HalfWord
| Word

type instruction =
| Pload of sizeOp * breg * breg * off
| Pstore of sizeOp * breg * (breg, imm) sum * off
| Palu32 of aluOp * breg * (breg, imm) sum
| Pjmp of off
| Pjmpcmp of cmpOp * breg * (breg, imm) sum * off
| Pcall of ident * signature
| Pret

type code = int list

type bpf_code = instruction list

type bin_code = int list

val get_instruction_alu32_imm : breg -> imm -> int -> instruction option

val get_instruction_alu32_reg : breg -> breg -> int -> instruction option

val get_instruction_ldx : breg -> breg -> off -> int -> instruction option

val get_instruction_st : breg -> off -> int -> int -> instruction option

val get_instruction_stx : breg -> breg -> off -> int -> instruction option

val get_instruction_branch_imm :
  breg -> off -> imm -> int -> instruction option

val get_instruction_branch_reg :
  breg -> breg -> off -> int -> instruction option

val z_to_breg : int -> breg option

val int64_to_dst_breg : int -> breg option

val int64_to_src_breg : int -> breg option

val decode_ind : int -> instruction option

val find_instr : int -> code -> instruction option

val is_alu32 : instruction -> bool

val get_alu32_list : code -> int -> int -> bpf_code option

val analyzer_aux : code -> int -> int -> (int * bpf_code) list option

val analyzer : code -> (int * bpf_code) list option

val rbpf_arm_callee_save : listset

val reg_ireg_eqb : breg -> ireg -> bool

val ireg_of_breg : breg -> ireg

val z_of_ireg : ireg -> int

val int_of_ireg : ireg -> int

val nOP_OP : int

val aDD_R_OP : int

val aDD_I_OP : int

val aND_R_OP : int

val aND_I_OP : int

val aSR_R_OP : int

val eOR_R_OP : int

val eOR_I_OP : int

val lSL_R_OP : int

val lSR_R_OP : int

val mOVW_OP : int

val mOVT_OP : int

val mOV_R_OP : int

val mUL_OP : int

val oRR_R_OP : int

val oRR_I_OP : int

val sUB_R_OP : int

val sUB_I_OP : int

val rSB_I_OP : int

val uDIV_LO_OP : int

val uDIV_HI_OP : int

val bX_OP : int

val lDR_I_OP : int

val sTR_I_OP : int

val insert : listset -> breg -> listset

val sort_listset : listset -> listset

val jit_alu32_thumb_mem_template_jit : int -> int -> int -> int -> int

val jit_alu32_pre : bin_code

val jit_call_save_add : breg -> listset -> bin_code

val jit_call_save_reg :
  breg -> breg -> listset -> listset -> (bin_code * listset) * listset

val jit_call_save_imm :
  breg -> listset -> listset -> (bin_code * listset) * listset

val bpf_alu32_to_thumb_reg_comm : int -> breg -> ireg -> int

val bpf_alu32_to_thumb_reg : aluOp -> breg -> ireg -> bin_code option

val mov_int_to_movwt : int -> ireg -> int -> int

val bpf_alu32_to_thumb_imm_comm :
  int -> aluOp -> breg -> int -> bin_code option

val bpf_alu32_to_thumb_imm_shift_comm : int -> breg -> int -> bin_code option

val bpf_alu32_to_thumb_imm : aluOp -> breg -> int -> bin_code option

val jit_one :
  aluOp -> breg -> (breg, imm) sum -> listset -> listset ->
  ((bin_code * listset) * listset) option

val jit_sequence :
  bpf_code -> listset -> listset -> ((bin_code * listset) * listset) option

val jit_alu32_thumb_pc_add : int -> bin_code option

val jit_alu32_thumb_pc : int -> bin_code option

val jit_alu32_thumb_store : listset -> bin_code

val jit_alu32_thumb_reset1 : listset -> bin_code

val jit_alu32_thumb_reset : listset -> bin_code

val jit_alu32_post : bin_code

val jit_alu32_aux : bpf_code -> bin_code option

val jit_alu32 : bpf_code -> bin_code option

val combiner_aux :
  (int * bpf_code) list -> int -> (int * (int * bin_code)) list option

val combiner : (int * bpf_code) list -> (int * (int * bin_code)) list option

val concat_bin : (int * (int * bin_code)) list -> (int * int) list * bin_code

val whole_compiler : code -> ((int * int) list * bin_code) option

val test_bitswap_int64 : int list

val bitswap_ibpf_main : ((int * int) list * bin_code) option
