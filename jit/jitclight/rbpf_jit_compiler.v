From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.12".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "arm".
  Definition model := "armv7a".
  Definition abi := "eabi".
  Definition bitsize := 32.
  Definition big_endian := false.
  Definition source_file := "rbpf_jit_compiler.c".
  Definition normalized := false.
End Info.

Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_dmb : ident := $"__builtin_dmb".
Definition ___builtin_dsb : ident := $"__builtin_dsb".
Definition ___builtin_execbin : ident := $"__builtin_execbin".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_isb : ident := $"__builtin_isb".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _add_jited_bin : ident := $"add_jited_bin".
Definition _add_key_value : ident := $"add_key_value".
Definition _alu32_ofs : ident := $"alu32_ofs".
Definition _alu_op : ident := $"alu_op".
Definition _arm_ofs : ident := $"arm_ofs".
Definition _b : ident := $"b".
Definition _bpf_alu32_to_thumb_imm : ident := $"bpf_alu32_to_thumb_imm".
Definition _bpf_alu32_to_thumb_imm_comm : ident := $"bpf_alu32_to_thumb_imm_comm".
Definition _bpf_alu32_to_thumb_imm_shift_comm : ident := $"bpf_alu32_to_thumb_imm_shift_comm".
Definition _bpf_alu32_to_thumb_reg : ident := $"bpf_alu32_to_thumb_reg".
Definition _bpf_alu32_to_thumb_reg_comm : ident := $"bpf_alu32_to_thumb_reg_comm".
Definition _cond : ident := $"cond".
Definition _counter : ident := $"counter".
Definition _d : ident := $"d".
Definition _decode_thumb : ident := $"decode_thumb".
Definition _dst : ident := $"dst".
Definition _encode_thumb : ident := $"encode_thumb".
Definition _eval_arm_ofs : ident := $"eval_arm_ofs".
Definition _eval_input_ins : ident := $"eval_input_ins".
Definition _eval_input_len : ident := $"eval_input_len".
Definition _eval_load_regset : ident := $"eval_load_regset".
Definition _eval_store_regset : ident := $"eval_store_regset".
Definition _eval_use_IR11 : ident := $"eval_use_IR11".
Definition _f : ident := $"f".
Definition _from : ident := $"from".
Definition _fuel : ident := $"fuel".
Definition _get_dst : ident := $"get_dst".
Definition _get_immediate : ident := $"get_immediate".
Definition _get_offset : ident := $"get_offset".
Definition _get_opcode_ins : ident := $"get_opcode_ins".
Definition _get_src : ident := $"get_src".
Definition _hi_32 : ident := $"hi_32".
Definition _i : ident := $"i".
Definition _idx : ident := $"idx".
Definition _imm12 : ident := $"imm12".
Definition _imm32 : ident := $"imm32".
Definition _input_ins : ident := $"input_ins".
Definition _input_len : ident := $"input_len".
Definition _ins : ident := $"ins".
Definition _ins32 : ident := $"ins32".
Definition _ins64 : ident := $"ins64".
Definition _ins_hi : ident := $"ins_hi".
Definition _ins_hi0 : ident := $"ins_hi0".
Definition _ins_is_bpf_alu32 : ident := $"ins_is_bpf_alu32".
Definition _ins_is_bpf_jump : ident := $"ins_is_bpf_jump".
Definition _ins_lo : ident := $"ins_lo".
Definition _ins_rdn : ident := $"ins_rdn".
Definition _ins_rm : ident := $"ins_rm".
Definition _jit_alu32_aux : ident := $"jit_alu32_aux".
Definition _jit_alu32_post : ident := $"jit_alu32_post".
Definition _jit_alu32_pre : ident := $"jit_alu32_pre".
Definition _jit_alu32_thumb_mem_template_jit : ident := $"jit_alu32_thumb_mem_template_jit".
Definition _jit_alu32_thumb_reset : ident := $"jit_alu32_thumb_reset".
Definition _jit_alu32_thumb_reset1 : ident := $"jit_alu32_thumb_reset1".
Definition _jit_alu32_thumb_store : ident := $"jit_alu32_thumb_store".
Definition _jit_alu32_thumb_upd_reset : ident := $"jit_alu32_thumb_upd_reset".
Definition _jit_alu32_thumb_upd_store : ident := $"jit_alu32_thumb_upd_store".
Definition _jit_call_save_add : ident := $"jit_call_save_add".
Definition _jit_call_save_imm : ident := $"jit_call_save_imm".
Definition _jit_call_save_reg : ident := $"jit_call_save_reg".
Definition _jit_list : ident := $"jit_list".
Definition _jit_one : ident := $"jit_one".
Definition _jit_sequence : ident := $"jit_sequence".
Definition _jit_state : ident := $"jit_state".
Definition _key_value2 : ident := $"key_value2".
Definition _l_ldr : ident := $"l_ldr".
Definition _ld_set : ident := $"ld_set".
Definition _ldr_ins : ident := $"ldr_ins".
Definition _len : ident := $"len".
Definition _lo_32 : ident := $"lo_32".
Definition _lo_i : ident := $"lo_i".
Definition _lo_imm3 : ident := $"lo_imm3".
Definition _lo_imm4 : ident := $"lo_imm4".
Definition _lo_imm8 : ident := $"lo_imm8".
Definition _load_IR11 : ident := $"load_IR11".
Definition _main : ident := $"main".
Definition _mask : ident := $"mask".
Definition _mov_int_to_movwt : ident := $"mov_int_to_movwt".
Definition _movw_hi : ident := $"movw_hi".
Definition _movw_hi_0 : ident := $"movw_hi_0".
Definition _movw_lo : ident := $"movw_lo".
Definition _movw_lo_0 : ident := $"movw_lo_0".
Definition _n : ident := $"n".
Definition _nat_to_opcode_alu32 : ident := $"nat_to_opcode_alu32".
Definition _nat_to_opcode_alu32_imm : ident := $"nat_to_opcode_alu32_imm".
Definition _nat_to_opcode_alu32_reg : ident := $"nat_to_opcode_alu32_reg".
Definition _next_ins : ident := $"next_ins".
Definition _next_pc : ident := $"next_pc".
Definition _ofs : ident := $"ofs".
Definition _ofs0 : ident := $"ofs0".
Definition _ofs1 : ident := $"ofs1".
Definition _op : ident := $"op".
Definition _opc : ident := $"opc".
Definition _opi : ident := $"opi".
Definition _opr : ident := $"opr".
Definition _pc : ident := $"pc".
Definition _power2 : ident := $"power2".
Definition _r : ident := $"r".
Definition _rdn : ident := $"rdn".
Definition _reset_init_jittedthumb : ident := $"reset_init_jittedthumb".
Definition _rn : ident := $"rn".
Definition _rt : ident := $"rt".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _st : ident := $"st".
Definition _st_set : ident := $"st_set".
Definition _str : ident := $"str".
Definition _str_high : ident := $"str_high".
Definition _str_ins : ident := $"str_ins".
Definition _str_low : ident := $"str_low".
Definition _sz : ident := $"sz".
Definition _tp_bin : ident := $"tp_bin".
Definition _tp_bin_len : ident := $"tp_bin_len".
Definition _tp_kv : ident := $"tp_kv".
Definition _upd_IR11_jittedthumb : ident := $"upd_IR11_jittedthumb".
Definition _upd_load_regset : ident := $"upd_load_regset".
Definition _upd_store_regset : ident := $"upd_store_regset".
Definition _use_IR11 : ident := $"use_IR11".
Definition _v : ident := $"v".
Definition _whole_compiler : ident := $"whole_compiler".
Definition _whole_compiler_aux : ident := $"whole_compiler_aux".
Definition _width : ident := $"width".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_eval_input_len := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                   (Tstruct _jit_state noattr)) _input_len tuint)))
|}.

Definition f_eval_input_ins := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_idx, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                       (Tstruct _jit_state noattr)) _input_ins (tptr tulong))
                   (Etempvar _idx tuint) (tptr tulong)) tulong)))
|}.

Definition f_get_dst := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr
                   (Ebinop Oand (Etempvar _ins tulong)
                     (Econst_long (Int64.repr 4095) tulong) tulong)
                   (Econst_long (Int64.repr 8) tulong) tulong) tuint)))
|}.

Definition f_get_src := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr
                   (Ebinop Oand (Etempvar _ins tulong)
                     (Econst_long (Int64.repr 65535) tulong) tulong)
                   (Econst_long (Int64.repr 12) tulong) tulong) tuint)))
|}.

Definition f_eval_arm_ofs := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                   (Tstruct _jit_state noattr)) _tp_bin_len tuint)))
|}.

Definition f_add_key_value := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_pc, tuint) ::
                (_ofs0, tuint) :: (_ofs1, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
              (Tstruct _jit_state noattr)) _tp_kv
            (tptr (Tstruct _key_value2 noattr))) (Etempvar _pc tuint)
          (tptr (Tstruct _key_value2 noattr))) (Tstruct _key_value2 noattr))
      _arm_ofs tuint) (Etempvar _ofs0 tuint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                (Tstruct _jit_state noattr)) _tp_kv
              (tptr (Tstruct _key_value2 noattr))) (Etempvar _pc tuint)
            (tptr (Tstruct _key_value2 noattr)))
          (Tstruct _key_value2 noattr)) _alu32_ofs tuint)
      (Etempvar _ofs1 tuint))
    (Sreturn None)))
|}.

Definition f_eval_use_IR11 := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                   (Tstruct _jit_state noattr)) _use_IR11 tbool)))
|}.

Definition f_upd_IR11_jittedthumb := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_f, tbool) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
        (Tstruct _jit_state noattr)) _use_IR11 tbool) (Etempvar _f tbool))
  (Sreturn None))
|}.

Definition f_add_jited_bin := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_ins, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
            (Tstruct _jit_state noattr)) _tp_bin (tptr tuint))
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
            (Tstruct _jit_state noattr)) _tp_bin_len tuint) (tptr tuint))
      tuint) (Etempvar _ins tuint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
          (Tstruct _jit_state noattr)) _tp_bin_len tuint)
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
            (Tstruct _jit_state noattr)) _tp_bin_len tuint)
        (Econst_int (Int.repr 1) tuint) tuint))
    (Sreturn None)))
|}.

Definition f_eval_load_regset := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_r, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                       (Tstruct _jit_state noattr)) _ld_set
                     (tarray tbool 11)) (Etempvar _r tuint) (tptr tbool))
                 tbool)))
|}.

Definition f_eval_store_regset := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_r, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                       (Tstruct _jit_state noattr)) _st_set
                     (tarray tbool 11)) (Etempvar _r tuint) (tptr tbool))
                 tbool)))
|}.

Definition f_upd_load_regset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_r, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
            (Tstruct _jit_state noattr)) _ld_set (tarray tbool 11))
        (Etempvar _r tuint) (tptr tbool)) tbool)
    (Econst_int (Int.repr 1) tint))
  (Sreturn None))
|}.

Definition f_upd_store_regset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_r, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
            (Tstruct _jit_state noattr)) _st_set (tarray tbool 11))
        (Etempvar _r tuint) (tptr tbool)) tbool)
    (Econst_int (Int.repr 1) tint))
  (Sreturn None))
|}.

Definition f_reset_init_jittedthumb := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
        (Tstruct _jit_state noattr)) _use_IR11 tbool)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _i (Econst_int (Int.repr 0) tint))
      (Sloop
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tuint)
                         (Econst_int (Int.repr 11) tint) tint)
            Sskip
            Sbreak)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                      (Tstruct _jit_state noattr)) _ld_set (tarray tbool 11))
                  (Etempvar _i tuint) (tptr tbool)) tbool)
              (Econst_int (Int.repr 0) tint))
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef (Etempvar _st (tptr (Tstruct _jit_state noattr)))
                      (Tstruct _jit_state noattr)) _st_set (tarray tbool 11))
                  (Etempvar _i tuint) (tptr tbool)) tbool)
              (Econst_int (Int.repr 0) tint))))
        (Sset _i
          (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint)
            tuint))))
    (Sreturn None)))
|}.

Definition f_power2 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_width, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _width tuint)
               (Econst_int (Int.repr 0) tuint) tint)
  (Sreturn (Some (Econst_int (Int.repr 1) tuint)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _power2 (Tfunction (Tcons tuint Tnil) tuint cc_default))
      ((Ebinop Osub (Etempvar _width tuint) (Econst_int (Int.repr 1) tuint)
         tuint) :: nil))
    (Sreturn (Some (Ebinop Omul (Econst_int (Int.repr 2) tuint)
                     (Etempvar _t'1 tuint) tuint)))))
|}.

Definition f_decode_thumb := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tuint) :: (_from, tuint) :: (_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _power2 (Tfunction (Tcons tuint Tnil) tuint cc_default))
    ((Etempvar _size tuint) :: nil))
  (Sreturn (Some (Ebinop Oand
                   (Ebinop Oshr (Etempvar _ins tuint) (Etempvar _from tuint)
                     tuint)
                   (Ebinop Osub (Etempvar _t'1 tuint)
                     (Econst_int (Int.repr 1) tuint) tuint) tuint))))
|}.

Definition f_encode_thumb := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_v, tuint) :: (_ins, tuint) :: (_from, tuint) ::
                (_size, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_mask, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _power2 (Tfunction (Tcons tuint Tnil) tuint cc_default))
      ((Etempvar _size tuint) :: nil))
    (Sset _mask
      (Ebinop Oshl
        (Ebinop Osub (Etempvar _t'1 tuint) (Econst_int (Int.repr 1) tuint)
          tuint) (Etempvar _from tuint) tuint)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _power2 (Tfunction (Tcons tuint Tnil) tuint cc_default))
      ((Etempvar _size tuint) :: nil))
    (Sreturn (Some (Ebinop Oor
                     (Ebinop Oshl
                       (Ebinop Oand (Etempvar _v tuint)
                         (Ebinop Osub (Etempvar _t'2 tuint)
                           (Econst_int (Int.repr 1) tuint) tuint) tuint)
                       (Etempvar _from tuint) tuint)
                     (Ebinop Oand (Etempvar _ins tuint)
                       (Eunop Onotint (Etempvar _mask tuint) tuint) tuint)
                     tuint)))))
|}.

Definition f_ins_is_bpf_alu32 := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_op, tuchar) :: (_t'18, tint) :: (_t'17, tint) ::
               (_t'16, tint) :: (_t'15, tint) :: (_t'14, tint) ::
               (_t'13, tint) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _op
    (Ecast
      (Ecast
        (Ebinop Oand (Etempvar _ins tulong)
          (Econst_long (Int64.repr 255) tulong) tulong) tuchar) tuchar))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sifthenelse (Ebinop Oeq
                                                     (Etempvar _op tuchar)
                                                     (Econst_int (Int.repr 4) tint)
                                                     tint)
                                        (Sset _t'1
                                          (Econst_int (Int.repr 1) tint))
                                        (Sset _t'1
                                          (Ecast
                                            (Ebinop Oeq (Etempvar _op tuchar)
                                              (Econst_int (Int.repr 12) tint)
                                              tint) tbool)))
                                      (Sifthenelse (Etempvar _t'1 tint)
                                        (Sset _t'2
                                          (Econst_int (Int.repr 1) tint))
                                        (Sset _t'2
                                          (Ecast
                                            (Ebinop Oeq (Etempvar _op tuchar)
                                              (Econst_int (Int.repr 20) tint)
                                              tint) tbool))))
                                    (Sifthenelse (Etempvar _t'2 tint)
                                      (Sset _t'3
                                        (Econst_int (Int.repr 1) tint))
                                      (Sset _t'3
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _op tuchar)
                                            (Econst_int (Int.repr 28) tint)
                                            tint) tbool))))
                                  (Sifthenelse (Etempvar _t'3 tint)
                                    (Sset _t'4
                                      (Econst_int (Int.repr 1) tint))
                                    (Sset _t'4
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _op tuchar)
                                          (Econst_int (Int.repr 36) tint)
                                          tint) tbool))))
                                (Sifthenelse (Etempvar _t'4 tint)
                                  (Sset _t'5 (Econst_int (Int.repr 1) tint))
                                  (Sset _t'5
                                    (Ecast
                                      (Ebinop Oeq (Etempvar _op tuchar)
                                        (Econst_int (Int.repr 44) tint) tint)
                                      tbool))))
                              (Sifthenelse (Etempvar _t'5 tint)
                                (Sset _t'6 (Econst_int (Int.repr 1) tint))
                                (Sset _t'6
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _op tuchar)
                                      (Econst_int (Int.repr 60) tint) tint)
                                    tbool))))
                            (Sifthenelse (Etempvar _t'6 tint)
                              (Sset _t'7 (Econst_int (Int.repr 1) tint))
                              (Sset _t'7
                                (Ecast
                                  (Ebinop Oeq (Etempvar _op tuchar)
                                    (Econst_int (Int.repr 68) tint) tint)
                                  tbool))))
                          (Sifthenelse (Etempvar _t'7 tint)
                            (Sset _t'8 (Econst_int (Int.repr 1) tint))
                            (Sset _t'8
                              (Ecast
                                (Ebinop Oeq (Etempvar _op tuchar)
                                  (Econst_int (Int.repr 76) tint) tint)
                                tbool))))
                        (Sifthenelse (Etempvar _t'8 tint)
                          (Sset _t'9 (Econst_int (Int.repr 1) tint))
                          (Sset _t'9
                            (Ecast
                              (Ebinop Oeq (Etempvar _op tuchar)
                                (Econst_int (Int.repr 84) tint) tint) tbool))))
                      (Sifthenelse (Etempvar _t'9 tint)
                        (Sset _t'10 (Econst_int (Int.repr 1) tint))
                        (Sset _t'10
                          (Ecast
                            (Ebinop Oeq (Etempvar _op tuchar)
                              (Econst_int (Int.repr 92) tint) tint) tbool))))
                    (Sifthenelse (Etempvar _t'10 tint)
                      (Sset _t'11 (Econst_int (Int.repr 1) tint))
                      (Sset _t'11
                        (Ecast
                          (Ebinop Oeq (Etempvar _op tuchar)
                            (Econst_int (Int.repr 108) tint) tint) tbool))))
                  (Sifthenelse (Etempvar _t'11 tint)
                    (Sset _t'12 (Econst_int (Int.repr 1) tint))
                    (Sset _t'12
                      (Ecast
                        (Ebinop Oeq (Etempvar _op tuchar)
                          (Econst_int (Int.repr 124) tint) tint) tbool))))
                (Sifthenelse (Etempvar _t'12 tint)
                  (Sset _t'13 (Econst_int (Int.repr 1) tint))
                  (Sset _t'13
                    (Ecast
                      (Ebinop Oeq (Etempvar _op tuchar)
                        (Econst_int (Int.repr 132) tint) tint) tbool))))
              (Sifthenelse (Etempvar _t'13 tint)
                (Sset _t'14 (Econst_int (Int.repr 1) tint))
                (Sset _t'14
                  (Ecast
                    (Ebinop Oeq (Etempvar _op tuchar)
                      (Econst_int (Int.repr 164) tint) tint) tbool))))
            (Sifthenelse (Etempvar _t'14 tint)
              (Sset _t'15 (Econst_int (Int.repr 1) tint))
              (Sset _t'15
                (Ecast
                  (Ebinop Oeq (Etempvar _op tuchar)
                    (Econst_int (Int.repr 172) tint) tint) tbool))))
          (Sifthenelse (Etempvar _t'15 tint)
            (Sset _t'16 (Econst_int (Int.repr 1) tint))
            (Sset _t'16
              (Ecast
                (Ebinop Oeq (Etempvar _op tuchar)
                  (Econst_int (Int.repr 180) tint) tint) tbool))))
        (Sifthenelse (Etempvar _t'16 tint)
          (Sset _t'17 (Econst_int (Int.repr 1) tint))
          (Sset _t'17
            (Ecast
              (Ebinop Oeq (Etempvar _op tuchar)
                (Econst_int (Int.repr 188) tint) tint) tbool))))
      (Sifthenelse (Etempvar _t'17 tint)
        (Sset _t'18 (Econst_int (Int.repr 1) tint))
        (Sset _t'18
          (Ecast
            (Ebinop Oeq (Etempvar _op tuchar)
              (Econst_int (Int.repr 204) tint) tint) tbool))))
    (Sreturn (Some (Etempvar _t'18 tint)))))
|}.

Definition f_ins_is_bpf_jump := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_op, tuchar) :: (_t'22, tint) :: (_t'21, tint) ::
               (_t'20, tint) :: (_t'19, tint) :: (_t'18, tint) ::
               (_t'17, tint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _op
    (Ecast
      (Ecast
        (Ebinop Oand (Etempvar _ins tulong)
          (Econst_long (Int64.repr 255) tulong) tulong) tuchar) tuchar))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sifthenelse (Ebinop Oeq
                                                             (Etempvar _op tuchar)
                                                             (Econst_int (Int.repr 5) tint)
                                                             tint)
                                                (Sset _t'1
                                                  (Econst_int (Int.repr 1) tint))
                                                (Sset _t'1
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Etempvar _op tuchar)
                                                      (Econst_int (Int.repr 21) tint)
                                                      tint) tbool)))
                                              (Sifthenelse (Etempvar _t'1 tint)
                                                (Sset _t'2
                                                  (Econst_int (Int.repr 1) tint))
                                                (Sset _t'2
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Etempvar _op tuchar)
                                                      (Econst_int (Int.repr 29) tint)
                                                      tint) tbool))))
                                            (Sifthenelse (Etempvar _t'2 tint)
                                              (Sset _t'3
                                                (Econst_int (Int.repr 1) tint))
                                              (Sset _t'3
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _op tuchar)
                                                    (Econst_int (Int.repr 37) tint)
                                                    tint) tbool))))
                                          (Sifthenelse (Etempvar _t'3 tint)
                                            (Sset _t'4
                                              (Econst_int (Int.repr 1) tint))
                                            (Sset _t'4
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _op tuchar)
                                                  (Econst_int (Int.repr 45) tint)
                                                  tint) tbool))))
                                        (Sifthenelse (Etempvar _t'4 tint)
                                          (Sset _t'5
                                            (Econst_int (Int.repr 1) tint))
                                          (Sset _t'5
                                            (Ecast
                                              (Ebinop Oeq
                                                (Etempvar _op tuchar)
                                                (Econst_int (Int.repr 53) tint)
                                                tint) tbool))))
                                      (Sifthenelse (Etempvar _t'5 tint)
                                        (Sset _t'6
                                          (Econst_int (Int.repr 1) tint))
                                        (Sset _t'6
                                          (Ecast
                                            (Ebinop Oeq (Etempvar _op tuchar)
                                              (Econst_int (Int.repr 61) tint)
                                              tint) tbool))))
                                    (Sifthenelse (Etempvar _t'6 tint)
                                      (Sset _t'7
                                        (Econst_int (Int.repr 1) tint))
                                      (Sset _t'7
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _op tuchar)
                                            (Econst_int (Int.repr 69) tint)
                                            tint) tbool))))
                                  (Sifthenelse (Etempvar _t'7 tint)
                                    (Sset _t'8
                                      (Econst_int (Int.repr 1) tint))
                                    (Sset _t'8
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _op tuchar)
                                          (Econst_int (Int.repr 77) tint)
                                          tint) tbool))))
                                (Sifthenelse (Etempvar _t'8 tint)
                                  (Sset _t'9 (Econst_int (Int.repr 1) tint))
                                  (Sset _t'9
                                    (Ecast
                                      (Ebinop Oeq (Etempvar _op tuchar)
                                        (Econst_int (Int.repr 85) tint) tint)
                                      tbool))))
                              (Sifthenelse (Etempvar _t'9 tint)
                                (Sset _t'10 (Econst_int (Int.repr 1) tint))
                                (Sset _t'10
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _op tuchar)
                                      (Econst_int (Int.repr 93) tint) tint)
                                    tbool))))
                            (Sifthenelse (Etempvar _t'10 tint)
                              (Sset _t'11 (Econst_int (Int.repr 1) tint))
                              (Sset _t'11
                                (Ecast
                                  (Ebinop Oeq (Etempvar _op tuchar)
                                    (Econst_int (Int.repr 101) tint) tint)
                                  tbool))))
                          (Sifthenelse (Etempvar _t'11 tint)
                            (Sset _t'12 (Econst_int (Int.repr 1) tint))
                            (Sset _t'12
                              (Ecast
                                (Ebinop Oeq (Etempvar _op tuchar)
                                  (Econst_int (Int.repr 109) tint) tint)
                                tbool))))
                        (Sifthenelse (Etempvar _t'12 tint)
                          (Sset _t'13 (Econst_int (Int.repr 1) tint))
                          (Sset _t'13
                            (Ecast
                              (Ebinop Oeq (Etempvar _op tuchar)
                                (Econst_int (Int.repr 117) tint) tint) tbool))))
                      (Sifthenelse (Etempvar _t'13 tint)
                        (Sset _t'14 (Econst_int (Int.repr 1) tint))
                        (Sset _t'14
                          (Ecast
                            (Ebinop Oeq (Etempvar _op tuchar)
                              (Econst_int (Int.repr 125) tint) tint) tbool))))
                    (Sifthenelse (Etempvar _t'14 tint)
                      (Sset _t'15 (Econst_int (Int.repr 1) tint))
                      (Sset _t'15
                        (Ecast
                          (Ebinop Oeq (Etempvar _op tuchar)
                            (Econst_int (Int.repr 165) tint) tint) tbool))))
                  (Sifthenelse (Etempvar _t'15 tint)
                    (Sset _t'16 (Econst_int (Int.repr 1) tint))
                    (Sset _t'16
                      (Ecast
                        (Ebinop Oeq (Etempvar _op tuchar)
                          (Econst_int (Int.repr 173) tint) tint) tbool))))
                (Sifthenelse (Etempvar _t'16 tint)
                  (Sset _t'17 (Econst_int (Int.repr 1) tint))
                  (Sset _t'17
                    (Ecast
                      (Ebinop Oeq (Etempvar _op tuchar)
                        (Econst_int (Int.repr 181) tint) tint) tbool))))
              (Sifthenelse (Etempvar _t'17 tint)
                (Sset _t'18 (Econst_int (Int.repr 1) tint))
                (Sset _t'18
                  (Ecast
                    (Ebinop Oeq (Etempvar _op tuchar)
                      (Econst_int (Int.repr 189) tint) tint) tbool))))
            (Sifthenelse (Etempvar _t'18 tint)
              (Sset _t'19 (Econst_int (Int.repr 1) tint))
              (Sset _t'19
                (Ecast
                  (Ebinop Oeq (Etempvar _op tuchar)
                    (Econst_int (Int.repr 197) tint) tint) tbool))))
          (Sifthenelse (Etempvar _t'19 tint)
            (Sset _t'20 (Econst_int (Int.repr 1) tint))
            (Sset _t'20
              (Ecast
                (Ebinop Oeq (Etempvar _op tuchar)
                  (Econst_int (Int.repr 205) tint) tint) tbool))))
        (Sifthenelse (Etempvar _t'20 tint)
          (Sset _t'21 (Econst_int (Int.repr 1) tint))
          (Sset _t'21
            (Ecast
              (Ebinop Oeq (Etempvar _op tuchar)
                (Econst_int (Int.repr 213) tint) tint) tbool))))
      (Sifthenelse (Etempvar _t'21 tint)
        (Sset _t'22 (Econst_int (Int.repr 1) tint))
        (Sset _t'22
          (Ecast
            (Ebinop Oeq (Etempvar _op tuchar)
              (Econst_int (Int.repr 221) tint) tint) tbool))))
    (Sreturn (Some (Etempvar _t'22 tint)))))
|}.

Definition f_get_immediate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oshr (Etempvar _ins tulong)
                   (Econst_long (Int64.repr 32) tulong) tulong) tint)))
|}.

Definition f_get_offset := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ecast
                   (Ebinop Oshr
                     (Ebinop Oshl (Etempvar _ins tulong)
                       (Econst_long (Int64.repr 32) tulong) tulong)
                     (Econst_long (Int64.repr 48) tulong) tulong) tshort)
                 tint)))
|}.

Definition f_get_opcode_ins := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _ins tulong)
                   (Econst_long (Int64.repr 255) tulong) tulong) tuchar)))
|}.

Definition f_jit_alu32_thumb_mem_template_jit := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_op, tushort) :: (_rt, tushort) :: (_rn, tushort) ::
                (_imm12, tushort) :: nil);
  fn_vars := nil;
  fn_temps := ((_str_low, tuint) :: (_str_high, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _encode_thumb (Tfunction
                            (Tcons tuint
                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                            tuint cc_default))
      ((Etempvar _rn tushort) :: (Etempvar _op tushort) ::
       (Econst_int (Int.repr 0) tuint) :: (Econst_int (Int.repr 4) tuint) ::
       nil))
    (Sset _str_low (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _encode_thumb (Tfunction
                              (Tcons tuint
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil)))) tuint
                              cc_default))
        ((Etempvar _rt tushort) :: (Etempvar _imm12 tushort) ::
         (Econst_int (Int.repr 12) tuint) ::
         (Econst_int (Int.repr 4) tuint) :: nil))
      (Sset _str_high (Etempvar _t'2 tuint)))
    (Ssequence
      (Scall (Some _t'3)
        (Evar _encode_thumb (Tfunction
                              (Tcons tuint
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil)))) tuint
                              cc_default))
        ((Etempvar _str_high tuint) :: (Etempvar _str_low tuint) ::
         (Econst_int (Int.repr 16) tuint) ::
         (Econst_int (Int.repr 16) tuint) :: nil))
      (Sreturn (Some (Etempvar _t'3 tuint))))))
|}.

Definition f_jit_alu32_pre := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ins_rdn, tuint) :: (_ins_rm, tuint) :: (_ins, tuint) ::
               (_ins32, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _encode_thumb (Tfunction
                            (Tcons tuint
                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                            tuint cc_default))
      ((Econst_int (Int.repr 4) tint) ::
       (Econst_int (Int.repr 17920) tint) ::
       (Econst_int (Int.repr 0) tuint) :: (Econst_int (Int.repr 3) tuint) ::
       nil))
    (Sset _ins_rdn (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _encode_thumb (Tfunction
                              (Tcons tuint
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil)))) tuint
                              cc_default))
        ((Econst_int (Int.repr 1) tint) :: (Etempvar _ins_rdn tuint) ::
         (Econst_int (Int.repr 3) tuint) ::
         (Econst_int (Int.repr 4) tuint) :: nil))
      (Sset _ins_rm (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _encode_thumb (Tfunction
                                (Tcons tuint
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tuint Tnil)))) tuint
                                cc_default))
          ((Econst_int (Int.repr 1) tint) :: (Etempvar _ins_rm tuint) ::
           (Econst_int (Int.repr 7) tuint) ::
           (Econst_int (Int.repr 1) tuint) :: nil))
        (Sset _ins (Etempvar _t'3 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _encode_thumb (Tfunction
                                  (Tcons tuint
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tuint Tnil))))
                                  tuint cc_default))
            ((Etempvar _ins tuint) :: (Econst_int (Int.repr 48896) tint) ::
             (Econst_int (Int.repr 16) tuint) ::
             (Econst_int (Int.repr 16) tuint) :: nil))
          (Sset _ins32 (Etempvar _t'4 tuint)))
        (Ssequence
          (Scall None
            (Evar _add_jited_bin (Tfunction
                                   (Tcons (tptr (Tstruct _jit_state noattr))
                                     (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Etempvar _ins32 tuint) :: nil))
          (Sreturn None))))))
|}.

Definition f_jit_call_save_add := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_r, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_cond, tbool) :: (_ldr_ins, tuint) :: (_str_ins, tuint) ::
               (_t'4, tint) :: (_t'3, tuint) :: (_t'2, tuint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_load_regset (Tfunction
                                (Tcons (tptr (Tstruct _jit_state noattr))
                                  (Tcons tuint Tnil)) tbool cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Etempvar _r tuint) :: nil))
    (Sset _cond (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _cond tbool)
    (Sreturn None)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _jit_alu32_thumb_mem_template_jit (Tfunction
                                                    (Tcons tushort
                                                      (Tcons tushort
                                                        (Tcons tushort
                                                          (Tcons tushort
                                                            Tnil)))) tuint
                                                    cc_default))
          ((Econst_int (Int.repr 63696) tint) :: (Etempvar _r tuint) ::
           (Econst_int (Int.repr 12) tint) ::
           (Ebinop Omul (Etempvar _r tuint) (Econst_int (Int.repr 4) tint)
             tuint) :: nil))
        (Sset _ldr_ins (Etempvar _t'2 tuint)))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 3) tint)
                       (Etempvar _r tuint) tint)
          (Sset _t'4
            (Ecast
              (Ebinop Olt (Etempvar _r tuint) (Econst_int (Int.repr 12) tint)
                tint) tbool))
          (Sset _t'4 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'4 tint)
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _jit_alu32_thumb_mem_template_jit (Tfunction
                                                          (Tcons tushort
                                                            (Tcons tushort
                                                              (Tcons tushort
                                                                (Tcons
                                                                  tushort
                                                                  Tnil))))
                                                          tuint cc_default))
                ((Econst_int (Int.repr 63680) tint) :: (Etempvar _r tuint) ::
                 (Econst_int (Int.repr 13) tint) ::
                 (Ebinop Omul (Etempvar _r tuint)
                   (Econst_int (Int.repr 4) tint) tuint) :: nil))
              (Sset _str_ins (Etempvar _t'3 tuint)))
            (Ssequence
              (Scall None
                (Evar _add_jited_bin (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _jit_state noattr))
                                         (Tcons tuint Tnil)) tvoid
                                       cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Etempvar _str_ins tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _add_jited_bin (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _jit_state noattr))
                                           (Tcons tuint Tnil)) tvoid
                                         cc_default))
                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                   (Etempvar _ldr_ins tuint) :: nil))
                (Sreturn None))))
          (Ssequence
            (Scall None
              (Evar _add_jited_bin (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _jit_state noattr))
                                       (Tcons tuint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
               (Etempvar _ldr_ins tuint) :: nil))
            (Sreturn None)))))))
|}.

Definition f_jit_call_save_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_dst, tuint) ::
                (_src, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _jit_call_save_add (Tfunction
                               (Tcons (tptr (Tstruct _jit_state noattr))
                                 (Tcons tuint Tnil)) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
     (Etempvar _dst tuint) :: nil))
  (Ssequence
    (Scall None
      (Evar _upd_load_regset (Tfunction
                               (Tcons (tptr (Tstruct _jit_state noattr))
                                 (Tcons tuint Tnil)) tvoid cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Etempvar _dst tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _upd_store_regset (Tfunction
                                  (Tcons (tptr (Tstruct _jit_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
         (Etempvar _dst tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar _jit_call_save_add (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _jit_state noattr))
                                       (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Etempvar _src tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _upd_load_regset (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _jit_state noattr))
                                       (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Etempvar _src tuint) :: nil))
          (Sreturn None))))))
|}.

Definition f_jit_call_save_imm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_dst, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _jit_call_save_add (Tfunction
                               (Tcons (tptr (Tstruct _jit_state noattr))
                                 (Tcons tuint Tnil)) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
     (Etempvar _dst tuint) :: nil))
  (Ssequence
    (Scall None
      (Evar _upd_load_regset (Tfunction
                               (Tcons (tptr (Tstruct _jit_state noattr))
                                 (Tcons tuint Tnil)) tvoid cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Etempvar _dst tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _upd_store_regset (Tfunction
                                  (Tcons (tptr (Tstruct _jit_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
         (Etempvar _dst tuint) :: nil))
      (Sreturn None))))
|}.

Definition f_bpf_alu32_to_thumb_reg_comm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_op, tushort) :: (_dst, tushort) :: (_src, tushort) :: nil);
  fn_vars := nil;
  fn_temps := ((_ins_lo, tuint) :: (_ins_hi, tuint) :: (_ins32, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _encode_thumb (Tfunction
                            (Tcons tuint
                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                            tuint cc_default))
      ((Etempvar _dst tushort) :: (Etempvar _op tushort) ::
       (Econst_int (Int.repr 0) tuint) :: (Econst_int (Int.repr 4) tuint) ::
       nil))
    (Sset _ins_lo (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _encode_thumb (Tfunction
                              (Tcons tuint
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil)))) tuint
                              cc_default))
        ((Etempvar _dst tushort) :: (Etempvar _src tushort) ::
         (Econst_int (Int.repr 8) tuint) ::
         (Econst_int (Int.repr 4) tuint) :: nil))
      (Sset _ins_hi (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _encode_thumb (Tfunction
                                (Tcons tuint
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tuint Tnil)))) tuint
                                cc_default))
          ((Etempvar _ins_hi tuint) :: (Etempvar _ins_lo tuint) ::
           (Econst_int (Int.repr 16) tuint) ::
           (Econst_int (Int.repr 16) tuint) :: nil))
        (Sset _ins32 (Etempvar _t'3 tuint)))
      (Ssequence
        (Scall None
          (Evar _add_jited_bin (Tfunction
                                 (Tcons (tptr (Tstruct _jit_state noattr))
                                   (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Etempvar _ins32 tuint) :: nil))
        (Sreturn None)))))
|}.

Definition f_bpf_alu32_to_thumb_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_op, tuchar) ::
                (_dst, tushort) :: (_src, tushort) :: nil);
  fn_vars := nil;
  fn_temps := ((_d, tuint) :: (_rdn, tushort) :: (_ins_rdn, tuint) ::
               (_ins_rm, tuint) :: (_ins, tuint) :: (_ins32, tuint) ::
               (_ins_lo, tuint) :: (_ins_hi0, tuint) :: (_ins_hi, tuint) ::
               (_t'24, tuint) :: (_t'23, tuint) :: (_t'22, tuint) ::
               (_t'21, tuint) :: (_t'20, tuint) :: (_t'19, tuint) ::
               (_t'18, tuint) :: (_t'17, tuint) :: (_t'16, tuint) ::
               (_t'15, tuint) :: (_t'14, tuint) :: (_t'13, tuint) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 12)
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _dst tushort)
                     (Econst_int (Int.repr 8) tint) tint)
        (Sset _d (Econst_int (Int.repr 0) tint))
        (Sset _d (Econst_int (Int.repr 1) tint)))
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _dst tushort)
                       (Econst_int (Int.repr 8) tint) tint)
          (Sset _rdn (Ecast (Etempvar _dst tushort) tushort))
          (Sset _rdn
            (Ecast
              (Ebinop Osub (Etempvar _dst tushort)
                (Econst_int (Int.repr 8) tint) tint) tushort)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _encode_thumb (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil))))
                                    tuint cc_default))
              ((Etempvar _rdn tushort) ::
               (Econst_int (Int.repr 17408) tint) ::
               (Econst_int (Int.repr 0) tuint) ::
               (Econst_int (Int.repr 3) tuint) :: nil))
            (Sset _ins_rdn (Etempvar _t'1 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _encode_thumb (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tuint Tnil))))
                                      tuint cc_default))
                ((Etempvar _src tushort) :: (Etempvar _ins_rdn tuint) ::
                 (Econst_int (Int.repr 3) tuint) ::
                 (Econst_int (Int.repr 4) tuint) :: nil))
              (Sset _ins_rm (Etempvar _t'2 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _encode_thumb (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint
                                            (Tcons tuint (Tcons tuint Tnil))))
                                        tuint cc_default))
                  ((Etempvar _d tuint) :: (Etempvar _ins_rm tuint) ::
                   (Econst_int (Int.repr 7) tuint) ::
                   (Econst_int (Int.repr 1) tuint) :: nil))
                (Sset _ins (Etempvar _t'3 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _encode_thumb (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint Tnil)))) tuint
                                          cc_default))
                    ((Etempvar _ins tuint) ::
                     (Econst_int (Int.repr 48896) tint) ::
                     (Econst_int (Int.repr 16) tuint) ::
                     (Econst_int (Int.repr 16) tuint) :: nil))
                  (Sset _ins32 (Etempvar _t'4 tuint)))
                (Ssequence
                  (Scall None
                    (Evar _add_jited_bin (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _jit_state noattr))
                                             (Tcons tuint Tnil)) tvoid
                                           cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Etempvar _ins32 tuint) :: nil))
                  (Sreturn None))))))))
    (LScons (Some 28)
      (Ssequence
        (Scall None
          (Evar _bpf_alu32_to_thumb_reg_comm (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _jit_state noattr))
                                                 (Tcons tushort
                                                   (Tcons tushort
                                                     (Tcons tushort Tnil))))
                                               tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Econst_int (Int.repr 60320) tint) :: (Etempvar _dst tushort) ::
           (Etempvar _src tushort) :: nil))
        (Sreturn None))
      (LScons (Some 44)
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _encode_thumb (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil))))
                                    tuint cc_default))
              ((Etempvar _dst tushort) ::
               (Econst_int (Int.repr 64256) tint) ::
               (Econst_int (Int.repr 0) tuint) ::
               (Econst_int (Int.repr 4) tuint) :: nil))
            (Sset _ins_lo (Etempvar _t'5 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _encode_thumb (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tuint Tnil))))
                                      tuint cc_default))
                ((Etempvar _dst tushort) :: (Etempvar _src tushort) ::
                 (Econst_int (Int.repr 8) tuint) ::
                 (Econst_int (Int.repr 4) tuint) :: nil))
              (Sset _ins_hi0 (Etempvar _t'6 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _encode_thumb (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint
                                            (Tcons tuint (Tcons tuint Tnil))))
                                        tuint cc_default))
                  ((Econst_int (Int.repr 15) tint) ::
                   (Etempvar _ins_hi0 tuint) ::
                   (Econst_int (Int.repr 12) tuint) ::
                   (Econst_int (Int.repr 4) tuint) :: nil))
                (Sset _ins_hi (Etempvar _t'7 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'8)
                    (Evar _encode_thumb (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint Tnil)))) tuint
                                          cc_default))
                    ((Etempvar _ins_hi tuint) :: (Etempvar _ins_lo tuint) ::
                     (Econst_int (Int.repr 16) tuint) ::
                     (Econst_int (Int.repr 16) tuint) :: nil))
                  (Sset _ins32 (Etempvar _t'8 tuint)))
                (Ssequence
                  (Scall None
                    (Evar _add_jited_bin (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _jit_state noattr))
                                             (Tcons tuint Tnil)) tvoid
                                           cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Etempvar _ins32 tuint) :: nil))
                  (Sreturn None))))))
        (LScons (Some 76)
          (Ssequence
            (Scall None
              (Evar _bpf_alu32_to_thumb_reg_comm (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _jit_state noattr))
                                                     (Tcons tushort
                                                       (Tcons tushort
                                                         (Tcons tushort Tnil))))
                                                   tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
               (Econst_int (Int.repr 59968) tint) ::
               (Etempvar _dst tushort) :: (Etempvar _src tushort) :: nil))
            (Sreturn None))
          (LScons (Some 92)
            (Ssequence
              (Scall None
                (Evar _bpf_alu32_to_thumb_reg_comm (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _jit_state noattr))
                                                       (Tcons tushort
                                                         (Tcons tushort
                                                           (Tcons tushort
                                                             Tnil)))) tvoid
                                                     cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Econst_int (Int.repr 59904) tint) ::
                 (Etempvar _dst tushort) :: (Etempvar _src tushort) :: nil))
              (Sreturn None))
            (LScons (Some 108)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'9)
                    (Evar _encode_thumb (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint Tnil)))) tuint
                                          cc_default))
                    ((Etempvar _dst tushort) ::
                     (Econst_int (Int.repr 64000) tint) ::
                     (Econst_int (Int.repr 0) tuint) ::
                     (Econst_int (Int.repr 4) tuint) :: nil))
                  (Sset _ins_lo (Etempvar _t'9 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'10)
                      (Evar _encode_thumb (Tfunction
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint Tnil)))) tuint
                                            cc_default))
                      ((Etempvar _dst tushort) :: (Etempvar _src tushort) ::
                       (Econst_int (Int.repr 8) tuint) ::
                       (Econst_int (Int.repr 4) tuint) :: nil))
                    (Sset _ins_hi0 (Etempvar _t'10 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'11)
                        (Evar _encode_thumb (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil))))
                                              tuint cc_default))
                        ((Econst_int (Int.repr 15) tint) ::
                         (Etempvar _ins_hi0 tuint) ::
                         (Econst_int (Int.repr 12) tuint) ::
                         (Econst_int (Int.repr 4) tuint) :: nil))
                      (Sset _ins_hi (Etempvar _t'11 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'12)
                          (Evar _encode_thumb (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tuint Tnil))))
                                                tuint cc_default))
                          ((Etempvar _ins_hi tuint) ::
                           (Etempvar _ins_lo tuint) ::
                           (Econst_int (Int.repr 16) tuint) ::
                           (Econst_int (Int.repr 16) tuint) :: nil))
                        (Sset _ins32 (Etempvar _t'12 tuint)))
                      (Ssequence
                        (Scall None
                          (Evar _add_jited_bin (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _jit_state noattr))
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
                          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                           (Etempvar _ins32 tuint) :: nil))
                        (Sreturn None))))))
              (LScons (Some 124)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'13)
                      (Evar _encode_thumb (Tfunction
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint Tnil)))) tuint
                                            cc_default))
                      ((Etempvar _dst tushort) ::
                       (Econst_int (Int.repr 64032) tint) ::
                       (Econst_int (Int.repr 0) tuint) ::
                       (Econst_int (Int.repr 4) tuint) :: nil))
                    (Sset _ins_lo (Etempvar _t'13 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'14)
                        (Evar _encode_thumb (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil))))
                                              tuint cc_default))
                        ((Etempvar _dst tushort) ::
                         (Etempvar _src tushort) ::
                         (Econst_int (Int.repr 8) tuint) ::
                         (Econst_int (Int.repr 4) tuint) :: nil))
                      (Sset _ins_hi0 (Etempvar _t'14 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'15)
                          (Evar _encode_thumb (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tuint Tnil))))
                                                tuint cc_default))
                          ((Econst_int (Int.repr 15) tint) ::
                           (Etempvar _ins_hi0 tuint) ::
                           (Econst_int (Int.repr 12) tuint) ::
                           (Econst_int (Int.repr 4) tuint) :: nil))
                        (Sset _ins_hi (Etempvar _t'15 tuint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'16)
                            (Evar _encode_thumb (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil))))
                                                  tuint cc_default))
                            ((Etempvar _ins_hi tuint) ::
                             (Etempvar _ins_lo tuint) ::
                             (Econst_int (Int.repr 16) tuint) ::
                             (Econst_int (Int.repr 16) tuint) :: nil))
                          (Sset _ins32 (Etempvar _t'16 tuint)))
                        (Ssequence
                          (Scall None
                            (Evar _add_jited_bin (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _jit_state noattr))
                                                     (Tcons tuint Tnil))
                                                   tvoid cc_default))
                            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                             (Etempvar _ins32 tuint) :: nil))
                          (Sreturn None))))))
                (LScons (Some 172)
                  (Ssequence
                    (Scall None
                      (Evar _bpf_alu32_to_thumb_reg_comm (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _jit_state noattr))
                                                             (Tcons tushort
                                                               (Tcons tushort
                                                                 (Tcons
                                                                   tushort
                                                                   Tnil))))
                                                           tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Econst_int (Int.repr 60032) tint) ::
                       (Etempvar _dst tushort) :: (Etempvar _src tushort) ::
                       nil))
                    (Sreturn None))
                  (LScons (Some 188)
                    (Sifthenelse (Ebinop Oeq (Etempvar _dst tushort)
                                   (Etempvar _src tushort) tint)
                      (Sreturn None)
                      (Ssequence
                        (Sifthenelse (Ebinop Olt (Etempvar _dst tushort)
                                       (Econst_int (Int.repr 8) tint) tint)
                          (Sset _d (Econst_int (Int.repr 0) tint))
                          (Sset _d (Econst_int (Int.repr 1) tint)))
                        (Ssequence
                          (Sifthenelse (Ebinop Olt (Etempvar _dst tushort)
                                         (Econst_int (Int.repr 8) tint) tint)
                            (Sset _rdn
                              (Ecast (Etempvar _dst tushort) tushort))
                            (Sset _rdn
                              (Ecast
                                (Ebinop Osub (Etempvar _dst tushort)
                                  (Econst_int (Int.repr 8) tint) tint)
                                tushort)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'17)
                                (Evar _encode_thumb (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuint
                                                              Tnil)))) tuint
                                                      cc_default))
                                ((Etempvar _rdn tushort) ::
                                 (Econst_int (Int.repr 17920) tint) ::
                                 (Econst_int (Int.repr 0) tuint) ::
                                 (Econst_int (Int.repr 3) tuint) :: nil))
                              (Sset _ins_rdn (Etempvar _t'17 tuint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'18)
                                  (Evar _encode_thumb (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuint
                                                              (Tcons tuint
                                                                Tnil))))
                                                        tuint cc_default))
                                  ((Etempvar _src tushort) ::
                                   (Etempvar _ins_rdn tuint) ::
                                   (Econst_int (Int.repr 3) tuint) ::
                                   (Econst_int (Int.repr 4) tuint) :: nil))
                                (Sset _ins_rm (Etempvar _t'18 tuint)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'19)
                                    (Evar _encode_thumb (Tfunction
                                                          (Tcons tuint
                                                            (Tcons tuint
                                                              (Tcons tuint
                                                                (Tcons tuint
                                                                  Tnil))))
                                                          tuint cc_default))
                                    ((Etempvar _d tuint) ::
                                     (Etempvar _ins_rm tuint) ::
                                     (Econst_int (Int.repr 7) tuint) ::
                                     (Econst_int (Int.repr 1) tuint) :: nil))
                                  (Sset _ins (Etempvar _t'19 tuint)))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'20)
                                      (Evar _encode_thumb (Tfunction
                                                            (Tcons tuint
                                                              (Tcons tuint
                                                                (Tcons tuint
                                                                  (Tcons
                                                                    tuint
                                                                    Tnil))))
                                                            tuint cc_default))
                                      ((Etempvar _ins tuint) ::
                                       (Econst_int (Int.repr 48896) tint) ::
                                       (Econst_int (Int.repr 16) tuint) ::
                                       (Econst_int (Int.repr 16) tuint) ::
                                       nil))
                                    (Sset _ins32 (Etempvar _t'20 tuint)))
                                  (Ssequence
                                    (Scall None
                                      (Evar _add_jited_bin (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _jit_state noattr))
                                                               (Tcons tuint
                                                                 Tnil)) tvoid
                                                             cc_default))
                                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                       (Etempvar _ins32 tuint) :: nil))
                                    (Sreturn None)))))))))
                    (LScons (Some 204)
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'21)
                            (Evar _encode_thumb (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil))))
                                                  tuint cc_default))
                            ((Etempvar _dst tushort) ::
                             (Econst_int (Int.repr 64064) tint) ::
                             (Econst_int (Int.repr 0) tuint) ::
                             (Econst_int (Int.repr 4) tuint) :: nil))
                          (Sset _ins_lo (Etempvar _t'21 tuint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'22)
                              (Evar _encode_thumb (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil))))
                                                    tuint cc_default))
                              ((Etempvar _dst tushort) ::
                               (Etempvar _src tushort) ::
                               (Econst_int (Int.repr 8) tuint) ::
                               (Econst_int (Int.repr 4) tuint) :: nil))
                            (Sset _ins_hi0 (Etempvar _t'22 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'23)
                                (Evar _encode_thumb (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuint
                                                              Tnil)))) tuint
                                                      cc_default))
                                ((Econst_int (Int.repr 15) tint) ::
                                 (Etempvar _ins_hi0 tuint) ::
                                 (Econst_int (Int.repr 12) tuint) ::
                                 (Econst_int (Int.repr 4) tuint) :: nil))
                              (Sset _ins_hi (Etempvar _t'23 tuint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'24)
                                  (Evar _encode_thumb (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuint
                                                              (Tcons tuint
                                                                Tnil))))
                                                        tuint cc_default))
                                  ((Etempvar _ins_hi tuint) ::
                                   (Etempvar _ins_lo tuint) ::
                                   (Econst_int (Int.repr 16) tuint) ::
                                   (Econst_int (Int.repr 16) tuint) :: nil))
                                (Sset _ins32 (Etempvar _t'24 tuint)))
                              (Ssequence
                                (Scall None
                                  (Evar _add_jited_bin (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _jit_state noattr))
                                                           (Tcons tuint Tnil))
                                                         tvoid cc_default))
                                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                   (Etempvar _ins32 tuint) :: nil))
                                (Sreturn None))))))
                      (LScons None (Sreturn None) LSnil))))))))))))
|}.

Definition f_load_IR11 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_f, tbool) :: (_str, tuint) :: (_t'2, tuint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_use_IR11 (Tfunction
                             (Tcons (tptr (Tstruct _jit_state noattr)) Tnil)
                             tbool cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
    (Sset _f (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _f tbool)
    (Sreturn None)
    (Ssequence
      (Scall None
        (Evar _upd_IR11_jittedthumb (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _jit_state noattr))
                                        (Tcons tbool Tnil)) tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
         (Econst_int (Int.repr 1) tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _jit_alu32_thumb_mem_template_jit (Tfunction
                                                      (Tcons tushort
                                                        (Tcons tushort
                                                          (Tcons tushort
                                                            (Tcons tushort
                                                              Tnil)))) tuint
                                                      cc_default))
            ((Econst_int (Int.repr 63680) tint) ::
             (Econst_int (Int.repr 11) tint) ::
             (Econst_int (Int.repr 13) tint) ::
             (Econst_int (Int.repr 44) tint) :: nil))
          (Sset _str (Etempvar _t'2 tuint)))
        (Ssequence
          (Scall None
            (Evar _add_jited_bin (Tfunction
                                   (Tcons (tptr (Tstruct _jit_state noattr))
                                     (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Etempvar _str tuint) :: nil))
          (Sreturn None))))))
|}.

Definition f_mov_int_to_movwt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_i, tuint) ::
                (_r, tushort) :: (_op, tushort) :: nil);
  fn_vars := nil;
  fn_temps := ((_lo_imm8, tuint) :: (_lo_imm3, tuint) :: (_lo_i, tuint) ::
               (_lo_imm4, tuint) :: (_movw_lo_0, tuint) ::
               (_movw_lo, tuint) :: (_movw_hi_0, tuint) ::
               (_movw_hi, tuint) :: (_ins32, tuint) :: (_t'9, tuint) ::
               (_t'8, tuint) :: (_t'7, tuint) :: (_t'6, tuint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _load_IR11 (Tfunction
                       (Tcons (tptr (Tstruct _jit_state noattr)) Tnil) tvoid
                       cc_default))
    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _decode_thumb (Tfunction
                              (Tcons tuint (Tcons tuint (Tcons tuint Tnil)))
                              tuint cc_default))
        ((Etempvar _i tuint) :: (Econst_int (Int.repr 0) tuint) ::
         (Econst_int (Int.repr 8) tuint) :: nil))
      (Sset _lo_imm8 (Etempvar _t'1 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _decode_thumb (Tfunction
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil))) tuint
                                cc_default))
          ((Etempvar _i tuint) :: (Econst_int (Int.repr 8) tuint) ::
           (Econst_int (Int.repr 3) tuint) :: nil))
        (Sset _lo_imm3 (Etempvar _t'2 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _decode_thumb (Tfunction
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tuint Tnil))) tuint
                                  cc_default))
            ((Etempvar _i tuint) :: (Econst_int (Int.repr 11) tuint) ::
             (Econst_int (Int.repr 1) tuint) :: nil))
          (Sset _lo_i (Etempvar _t'3 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _decode_thumb (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tuint Tnil))) tuint
                                    cc_default))
              ((Etempvar _i tuint) :: (Econst_int (Int.repr 12) tuint) ::
               (Econst_int (Int.repr 4) tuint) :: nil))
            (Sset _lo_imm4 (Etempvar _t'4 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _encode_thumb (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tuint Tnil))))
                                      tuint cc_default))
                ((Etempvar _lo_imm4 tuint) :: (Etempvar _op tushort) ::
                 (Econst_int (Int.repr 0) tuint) ::
                 (Econst_int (Int.repr 4) tuint) :: nil))
              (Sset _movw_lo_0 (Etempvar _t'5 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'6)
                  (Evar _encode_thumb (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint
                                            (Tcons tuint (Tcons tuint Tnil))))
                                        tuint cc_default))
                  ((Etempvar _lo_i tuint) :: (Etempvar _movw_lo_0 tuint) ::
                   (Econst_int (Int.repr 10) tuint) ::
                   (Econst_int (Int.repr 1) tuint) :: nil))
                (Sset _movw_lo (Etempvar _t'6 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _encode_thumb (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint Tnil)))) tuint
                                          cc_default))
                    ((Etempvar _r tushort) :: (Etempvar _lo_imm8 tuint) ::
                     (Econst_int (Int.repr 8) tuint) ::
                     (Econst_int (Int.repr 4) tuint) :: nil))
                  (Sset _movw_hi_0 (Etempvar _t'7 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _encode_thumb (Tfunction
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint Tnil)))) tuint
                                            cc_default))
                      ((Etempvar _lo_imm3 tuint) ::
                       (Etempvar _movw_hi_0 tuint) ::
                       (Econst_int (Int.repr 12) tuint) ::
                       (Econst_int (Int.repr 3) tuint) :: nil))
                    (Sset _movw_hi (Etempvar _t'8 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _encode_thumb (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil))))
                                              tuint cc_default))
                        ((Etempvar _movw_hi tuint) ::
                         (Etempvar _movw_lo tuint) ::
                         (Econst_int (Int.repr 16) tuint) ::
                         (Econst_int (Int.repr 16) tuint) :: nil))
                      (Sset _ins32 (Etempvar _t'9 tuint)))
                    (Ssequence
                      (Scall None
                        (Evar _add_jited_bin (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _jit_state noattr))
                                                 (Tcons tuint Tnil)) tvoid
                                               cc_default))
                        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                         (Etempvar _ins32 tuint) :: nil))
                      (Sreturn None))))))))))))
|}.

Definition f_bpf_alu32_to_thumb_imm_comm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_op, tushort) :: (_alu_op, tuchar) :: (_dst, tushort) ::
                (_imm32, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ins_lo, tuint) :: (_ins_hi, tuint) :: (_ins32, tuint) ::
               (_lo_32, tuint) :: (_hi_32, tuint) :: (_t'6, tint) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tuint)
                 (Etempvar _imm32 tuint) tint)
    (Sset _t'6
      (Ecast
        (Ebinop Ole (Etempvar _imm32 tuint) (Econst_int (Int.repr 255) tuint)
          tint) tbool))
    (Sset _t'6 (Econst_int (Int.repr 0) tint)))
  (Sifthenelse (Etempvar _t'6 tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _encode_thumb (Tfunction
                                (Tcons tuint
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tuint Tnil)))) tuint
                                cc_default))
          ((Etempvar _dst tushort) :: (Etempvar _op tushort) ::
           (Econst_int (Int.repr 0) tuint) ::
           (Econst_int (Int.repr 4) tuint) :: nil))
        (Sset _ins_lo (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _encode_thumb (Tfunction
                                  (Tcons tuint
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tuint Tnil))))
                                  tuint cc_default))
            ((Etempvar _dst tushort) :: (Etempvar _imm32 tuint) ::
             (Econst_int (Int.repr 8) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: nil))
          (Sset _ins_hi (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _encode_thumb (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil))))
                                    tuint cc_default))
              ((Etempvar _ins_hi tuint) :: (Etempvar _ins_lo tuint) ::
               (Econst_int (Int.repr 16) tuint) ::
               (Econst_int (Int.repr 16) tuint) :: nil))
            (Sset _ins32 (Etempvar _t'3 tuint)))
          (Ssequence
            (Scall None
              (Evar _add_jited_bin (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _jit_state noattr))
                                       (Tcons tuint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
               (Etempvar _ins32 tuint) :: nil))
            (Sreturn None)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _decode_thumb (Tfunction
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil))) tuint
                                cc_default))
          ((Etempvar _imm32 tuint) :: (Econst_int (Int.repr 0) tuint) ::
           (Econst_int (Int.repr 16) tuint) :: nil))
        (Sset _lo_32 (Etempvar _t'4 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'5)
            (Evar _decode_thumb (Tfunction
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tuint Tnil))) tuint
                                  cc_default))
            ((Etempvar _imm32 tuint) :: (Econst_int (Int.repr 16) tuint) ::
             (Econst_int (Int.repr 16) tuint) :: nil))
          (Sset _hi_32 (Etempvar _t'5 tuint)))
        (Ssequence
          (Scall None
            (Evar _mov_int_to_movwt (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _jit_state noattr))
                                        (Tcons tuint
                                          (Tcons tushort
                                            (Tcons tushort Tnil)))) tvoid
                                      cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Etempvar _lo_32 tuint) :: (Econst_int (Int.repr 11) tint) ::
             (Econst_int (Int.repr 62016) tint) :: nil))
          (Sifthenelse (Ebinop Oeq (Etempvar _lo_32 tuint)
                         (Etempvar _imm32 tuint) tint)
            (Ssequence
              (Scall None
                (Evar _bpf_alu32_to_thumb_reg (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _jit_state noattr))
                                                  (Tcons tuchar
                                                    (Tcons tushort
                                                      (Tcons tushort Tnil))))
                                                tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Etempvar _alu_op tuchar) :: (Etempvar _dst tushort) ::
                 (Econst_int (Int.repr 11) tint) :: nil))
              (Sreturn None))
            (Ssequence
              (Scall None
                (Evar _mov_int_to_movwt (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _jit_state noattr))
                                            (Tcons tuint
                                              (Tcons tushort
                                                (Tcons tushort Tnil)))) tvoid
                                          cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Etempvar _hi_32 tuint) ::
                 (Econst_int (Int.repr 11) tint) ::
                 (Econst_int (Int.repr 62144) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _bpf_alu32_to_thumb_reg (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _jit_state noattr))
                                                    (Tcons tuchar
                                                      (Tcons tushort
                                                        (Tcons tushort Tnil))))
                                                  tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                   (Etempvar _alu_op tuchar) :: (Etempvar _dst tushort) ::
                   (Econst_int (Int.repr 11) tint) :: nil))
                (Sreturn None)))))))))
|}.

Definition f_bpf_alu32_to_thumb_imm_shift_comm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_op, tushort) :: (_dst, tushort) :: (_imm32, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ins_lo, tuint) :: (_ins_hi0, tuint) :: (_ins_hi, tuint) ::
               (_ins32, tuint) :: (_t'5, tint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 0) tuint)
                 (Etempvar _imm32 tuint) tint)
    (Sset _t'5
      (Ecast
        (Ebinop Olt (Etempvar _imm32 tuint) (Econst_int (Int.repr 32) tuint)
          tint) tbool))
    (Sset _t'5 (Econst_int (Int.repr 0) tint)))
  (Sifthenelse (Etempvar _t'5 tint)
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _encode_thumb (Tfunction
                                (Tcons tuint
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tuint Tnil)))) tuint
                                cc_default))
          ((Etempvar _dst tushort) :: (Etempvar _op tushort) ::
           (Econst_int (Int.repr 0) tuint) ::
           (Econst_int (Int.repr 4) tuint) :: nil))
        (Sset _ins_lo (Etempvar _t'1 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _encode_thumb (Tfunction
                                  (Tcons tuint
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tuint Tnil))))
                                  tuint cc_default))
            ((Etempvar _dst tushort) :: (Econst_int (Int.repr 11) tint) ::
             (Econst_int (Int.repr 8) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: nil))
          (Sset _ins_hi0 (Etempvar _t'2 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _encode_thumb (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil))))
                                    tuint cc_default))
              ((Econst_int (Int.repr 15) tint) ::
               (Etempvar _ins_hi0 tuint) ::
               (Econst_int (Int.repr 12) tuint) ::
               (Econst_int (Int.repr 4) tuint) :: nil))
            (Sset _ins_hi (Etempvar _t'3 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _encode_thumb (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint
                                          (Tcons tuint (Tcons tuint Tnil))))
                                      tuint cc_default))
                ((Etempvar _ins_hi tuint) :: (Etempvar _ins_lo tuint) ::
                 (Econst_int (Int.repr 16) tuint) ::
                 (Econst_int (Int.repr 16) tuint) :: nil))
              (Sset _ins32 (Etempvar _t'4 tuint)))
            (Ssequence
              (Scall None
                (Evar _mov_int_to_movwt (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _jit_state noattr))
                                            (Tcons tuint
                                              (Tcons tushort
                                                (Tcons tushort Tnil)))) tvoid
                                          cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Etempvar _imm32 tuint) ::
                 (Econst_int (Int.repr 11) tint) ::
                 (Econst_int (Int.repr 62016) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _add_jited_bin (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _jit_state noattr))
                                           (Tcons tuint Tnil)) tvoid
                                         cc_default))
                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                   (Etempvar _ins32 tuint) :: nil))
                (Sreturn None)))))))
    (Sreturn None)))
|}.

Definition f_bpf_alu32_to_thumb_imm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_op, tuchar) ::
                (_dst, tushort) :: (_imm32, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_lo_32, tuint) :: (_hi_32, tuint) :: (_ins_lo, tuint) ::
               (_ins_hi0, tuint) :: (_ins_hi, tuint) :: (_ins32, tuint) ::
               (_t'15, tuint) :: (_t'14, tuint) :: (_t'13, tuint) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, tuint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tuint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Sswitch (Etempvar _op tuchar)
  (LScons (Some 4)
    (Ssequence
      (Scall None
        (Evar _bpf_alu32_to_thumb_imm_comm (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _jit_state noattr))
                                               (Tcons tushort
                                                 (Tcons tuchar
                                                   (Tcons tushort
                                                     (Tcons tuint Tnil)))))
                                             tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
         (Econst_int (Int.repr 61696) tint) ::
         (Econst_int (Int.repr 12) tuint) :: (Etempvar _dst tushort) ::
         (Etempvar _imm32 tuint) :: nil))
      (Sreturn None))
    (LScons (Some 20)
      (Ssequence
        (Scall None
          (Evar _bpf_alu32_to_thumb_imm_comm (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _jit_state noattr))
                                                 (Tcons tushort
                                                   (Tcons tuchar
                                                     (Tcons tushort
                                                       (Tcons tuint Tnil)))))
                                               tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Econst_int (Int.repr 61856) tint) ::
           (Econst_int (Int.repr 28) tuint) :: (Etempvar _dst tushort) ::
           (Etempvar _imm32 tuint) :: nil))
        (Sreturn None))
      (LScons (Some 36)
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _decode_thumb (Tfunction
                                    (Tcons tuint
                                      (Tcons tuint (Tcons tuint Tnil))) tuint
                                    cc_default))
              ((Etempvar _imm32 tuint) :: (Econst_int (Int.repr 0) tuint) ::
               (Econst_int (Int.repr 16) tuint) :: nil))
            (Sset _lo_32 (Etempvar _t'1 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _decode_thumb (Tfunction
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil)))
                                      tuint cc_default))
                ((Etempvar _imm32 tuint) ::
                 (Econst_int (Int.repr 16) tuint) ::
                 (Econst_int (Int.repr 16) tuint) :: nil))
              (Sset _hi_32 (Etempvar _t'2 tuint)))
            (Ssequence
              (Scall None
                (Evar _mov_int_to_movwt (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _jit_state noattr))
                                            (Tcons tuint
                                              (Tcons tushort
                                                (Tcons tushort Tnil)))) tvoid
                                          cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Etempvar _lo_32 tuint) ::
                 (Econst_int (Int.repr 11) tint) ::
                 (Econst_int (Int.repr 62016) tint) :: nil))
              (Sifthenelse (Ebinop Oeq (Etempvar _lo_32 tuint)
                             (Etempvar _imm32 tuint) tint)
                (Ssequence
                  (Scall None
                    (Evar _bpf_alu32_to_thumb_reg (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _jit_state noattr))
                                                      (Tcons tuchar
                                                        (Tcons tushort
                                                          (Tcons tushort
                                                            Tnil)))) tvoid
                                                    cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Econst_int (Int.repr 44) tuint) ::
                     (Etempvar _dst tushort) ::
                     (Econst_int (Int.repr 11) tint) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Scall None
                    (Evar _mov_int_to_movwt (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _jit_state noattr))
                                                (Tcons tuint
                                                  (Tcons tushort
                                                    (Tcons tushort Tnil))))
                                              tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Etempvar _hi_32 tuint) ::
                     (Econst_int (Int.repr 11) tint) ::
                     (Econst_int (Int.repr 62144) tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _bpf_alu32_to_thumb_reg (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _jit_state noattr))
                                                        (Tcons tuchar
                                                          (Tcons tushort
                                                            (Tcons tushort
                                                              Tnil)))) tvoid
                                                      cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Econst_int (Int.repr 44) tuint) ::
                       (Etempvar _dst tushort) ::
                       (Econst_int (Int.repr 11) tint) :: nil))
                    (Sreturn None)))))))
        (LScons (Some 52)
          (Sifthenelse (Ebinop Oeq (Etempvar _imm32 tuint)
                         (Econst_int (Int.repr 0) tuint) tint)
            (Sreturn None)
            (Ssequence
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _encode_thumb (Tfunction
                                        (Tcons tuint
                                          (Tcons tuint
                                            (Tcons tuint (Tcons tuint Tnil))))
                                        tuint cc_default))
                  ((Etempvar _dst tushort) ::
                   (Econst_int (Int.repr 64432) tint) ::
                   (Econst_int (Int.repr 0) tuint) ::
                   (Econst_int (Int.repr 4) tuint) :: nil))
                (Sset _ins_lo (Etempvar _t'3 tuint)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _encode_thumb (Tfunction
                                          (Tcons tuint
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint Tnil)))) tuint
                                          cc_default))
                    ((Etempvar _dst tushort) ::
                     (Econst_int (Int.repr 61680) tint) ::
                     (Econst_int (Int.repr 8) tuint) ::
                     (Econst_int (Int.repr 4) tuint) :: nil))
                  (Sset _ins_hi0 (Etempvar _t'4 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _encode_thumb (Tfunction
                                            (Tcons tuint
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint Tnil)))) tuint
                                            cc_default))
                      ((Econst_int (Int.repr 11) tint) ::
                       (Etempvar _ins_hi0 tuint) ::
                       (Econst_int (Int.repr 0) tuint) ::
                       (Econst_int (Int.repr 4) tuint) :: nil))
                    (Sset _ins_hi (Etempvar _t'5 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'6)
                        (Evar _encode_thumb (Tfunction
                                              (Tcons tuint
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil))))
                                              tuint cc_default))
                        ((Etempvar _ins_hi tuint) ::
                         (Etempvar _ins_lo tuint) ::
                         (Econst_int (Int.repr 16) tuint) ::
                         (Econst_int (Int.repr 16) tuint) :: nil))
                      (Sset _ins32 (Etempvar _t'6 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'7)
                          (Evar _decode_thumb (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint Tnil)))
                                                tuint cc_default))
                          ((Etempvar _imm32 tuint) ::
                           (Econst_int (Int.repr 0) tuint) ::
                           (Econst_int (Int.repr 16) tuint) :: nil))
                        (Sset _lo_32 (Etempvar _t'7 tuint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'8)
                            (Evar _decode_thumb (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tuint Tnil)))
                                                  tuint cc_default))
                            ((Etempvar _imm32 tuint) ::
                             (Econst_int (Int.repr 16) tuint) ::
                             (Econst_int (Int.repr 16) tuint) :: nil))
                          (Sset _hi_32 (Etempvar _t'8 tuint)))
                        (Ssequence
                          (Scall None
                            (Evar _mov_int_to_movwt (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _jit_state noattr))
                                                        (Tcons tuint
                                                          (Tcons tushort
                                                            (Tcons tushort
                                                              Tnil)))) tvoid
                                                      cc_default))
                            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                             (Etempvar _lo_32 tuint) ::
                             (Econst_int (Int.repr 11) tint) ::
                             (Econst_int (Int.repr 62016) tint) :: nil))
                          (Sifthenelse (Ebinop Oeq (Etempvar _lo_32 tuint)
                                         (Etempvar _imm32 tuint) tint)
                            (Ssequence
                              (Scall None
                                (Evar _add_jited_bin (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _jit_state noattr))
                                                         (Tcons tuint Tnil))
                                                       tvoid cc_default))
                                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                 (Etempvar _ins32 tuint) :: nil))
                              (Sreturn None))
                            (Ssequence
                              (Scall None
                                (Evar _mov_int_to_movwt (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _jit_state noattr))
                                                            (Tcons tuint
                                                              (Tcons tushort
                                                                (Tcons
                                                                  tushort
                                                                  Tnil))))
                                                          tvoid cc_default))
                                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                 (Etempvar _hi_32 tuint) ::
                                 (Econst_int (Int.repr 11) tint) ::
                                 (Econst_int (Int.repr 62144) tint) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _add_jited_bin (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _jit_state noattr))
                                                           (Tcons tuint Tnil))
                                                         tvoid cc_default))
                                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                   (Etempvar _ins32 tuint) :: nil))
                                (Sreturn None))))))))))))
          (LScons (Some 68)
            (Ssequence
              (Scall None
                (Evar _bpf_alu32_to_thumb_imm_comm (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _jit_state noattr))
                                                       (Tcons tushort
                                                         (Tcons tuchar
                                                           (Tcons tushort
                                                             (Tcons tuint
                                                               Tnil)))))
                                                     tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Econst_int (Int.repr 61504) tint) ::
                 (Econst_int (Int.repr 76) tuint) ::
                 (Etempvar _dst tushort) :: (Etempvar _imm32 tuint) :: nil))
              (Sreturn None))
            (LScons (Some 84)
              (Ssequence
                (Scall None
                  (Evar _bpf_alu32_to_thumb_imm_comm (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _jit_state noattr))
                                                         (Tcons tushort
                                                           (Tcons tuchar
                                                             (Tcons tushort
                                                               (Tcons tuint
                                                                 Tnil)))))
                                                       tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                   (Econst_int (Int.repr 61440) tint) ::
                   (Econst_int (Int.repr 92) tuint) ::
                   (Etempvar _dst tushort) :: (Etempvar _imm32 tuint) :: nil))
                (Sreturn None))
              (LScons (Some 100)
                (Ssequence
                  (Scall None
                    (Evar _bpf_alu32_to_thumb_imm_shift_comm (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _jit_state noattr))
                                                                 (Tcons
                                                                   tushort
                                                                   (Tcons
                                                                    tushort
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))))
                                                               tvoid
                                                               cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Econst_int (Int.repr 64000) tint) ::
                     (Etempvar _dst tushort) :: (Etempvar _imm32 tuint) ::
                     nil))
                  (Sreturn None))
                (LScons (Some 116)
                  (Ssequence
                    (Scall None
                      (Evar _bpf_alu32_to_thumb_imm_shift_comm (Tfunction
                                                                 (Tcons
                                                                   (tptr (Tstruct _jit_state noattr))
                                                                   (Tcons
                                                                    tushort
                                                                    (Tcons
                                                                    tushort
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil))))
                                                                 tvoid
                                                                 cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Econst_int (Int.repr 64032) tint) ::
                       (Etempvar _dst tushort) :: (Etempvar _imm32 tuint) ::
                       nil))
                    (Sreturn None))
                  (LScons (Some 132)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _encode_thumb (Tfunction
                                                (Tcons tuint
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tuint Tnil))))
                                                tuint cc_default))
                          ((Econst_int (Int.repr 11) tint) ::
                           (Econst_int (Int.repr 61888) tint) ::
                           (Econst_int (Int.repr 0) tuint) ::
                           (Econst_int (Int.repr 4) tuint) :: nil))
                        (Sset _ins_lo (Etempvar _t'9 tuint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'10)
                            (Evar _encode_thumb (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil))))
                                                  tuint cc_default))
                            ((Etempvar _dst tushort) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Econst_int (Int.repr 8) tuint) ::
                             (Econst_int (Int.repr 4) tuint) :: nil))
                          (Sset _ins_hi (Etempvar _t'10 tuint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'11)
                              (Evar _encode_thumb (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil))))
                                                    tuint cc_default))
                              ((Etempvar _ins_hi tuint) ::
                               (Etempvar _ins_lo tuint) ::
                               (Econst_int (Int.repr 16) tuint) ::
                               (Econst_int (Int.repr 16) tuint) :: nil))
                            (Sset _ins32 (Etempvar _t'11 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'12)
                                (Evar _decode_thumb (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil)))
                                                      tuint cc_default))
                                ((Etempvar _imm32 tuint) ::
                                 (Econst_int (Int.repr 0) tuint) ::
                                 (Econst_int (Int.repr 16) tuint) :: nil))
                              (Sset _lo_32 (Etempvar _t'12 tuint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'13)
                                  (Evar _decode_thumb (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuint
                                                              Tnil))) tuint
                                                        cc_default))
                                  ((Etempvar _imm32 tuint) ::
                                   (Econst_int (Int.repr 16) tuint) ::
                                   (Econst_int (Int.repr 16) tuint) :: nil))
                                (Sset _hi_32 (Etempvar _t'13 tuint)))
                              (Ssequence
                                (Scall None
                                  (Evar _mov_int_to_movwt (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _jit_state noattr))
                                                              (Tcons tuint
                                                                (Tcons
                                                                  tushort
                                                                  (Tcons
                                                                    tushort
                                                                    Tnil))))
                                                            tvoid cc_default))
                                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                   (Etempvar _lo_32 tuint) ::
                                   (Econst_int (Int.repr 11) tint) ::
                                   (Econst_int (Int.repr 62016) tint) :: nil))
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _lo_32 tuint)
                                               (Etempvar _imm32 tuint) tint)
                                  (Ssequence
                                    (Scall None
                                      (Evar _add_jited_bin (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _jit_state noattr))
                                                               (Tcons tuint
                                                                 Tnil)) tvoid
                                                             cc_default))
                                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                       (Etempvar _ins32 tuint) :: nil))
                                    (Sreturn None))
                                  (Ssequence
                                    (Scall None
                                      (Evar _mov_int_to_movwt (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _jit_state noattr))
                                                                  (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tushort
                                                                    (Tcons
                                                                    tushort
                                                                    Tnil))))
                                                                tvoid
                                                                cc_default))
                                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                       (Etempvar _hi_32 tuint) ::
                                       (Econst_int (Int.repr 11) tint) ::
                                       (Econst_int (Int.repr 62144) tint) ::
                                       nil))
                                    (Ssequence
                                      (Scall None
                                        (Evar _add_jited_bin (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _jit_state noattr))
                                                                 (Tcons tuint
                                                                   Tnil))
                                                               tvoid
                                                               cc_default))
                                        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                         (Etempvar _ins32 tuint) :: nil))
                                      (Sreturn None))))))))))
                    (LScons (Some 164)
                      (Ssequence
                        (Scall None
                          (Evar _bpf_alu32_to_thumb_imm_comm (Tfunction
                                                               (Tcons
                                                                 (tptr (Tstruct _jit_state noattr))
                                                                 (Tcons
                                                                   tushort
                                                                   (Tcons
                                                                    tuchar
                                                                    (Tcons
                                                                    tushort
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))))
                                                               tvoid
                                                               cc_default))
                          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                           (Econst_int (Int.repr 61568) tint) ::
                           (Econst_int (Int.repr 172) tuint) ::
                           (Etempvar _dst tushort) ::
                           (Etempvar _imm32 tuint) :: nil))
                        (Sreturn None))
                      (LScons (Some 180)
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'14)
                              (Evar _decode_thumb (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil)))
                                                    tuint cc_default))
                              ((Etempvar _imm32 tuint) ::
                               (Econst_int (Int.repr 0) tuint) ::
                               (Econst_int (Int.repr 16) tuint) :: nil))
                            (Sset _lo_32 (Etempvar _t'14 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'15)
                                (Evar _decode_thumb (Tfunction
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil)))
                                                      tuint cc_default))
                                ((Etempvar _imm32 tuint) ::
                                 (Econst_int (Int.repr 16) tuint) ::
                                 (Econst_int (Int.repr 16) tuint) :: nil))
                              (Sset _hi_32 (Etempvar _t'15 tuint)))
                            (Ssequence
                              (Scall None
                                (Evar _mov_int_to_movwt (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _jit_state noattr))
                                                            (Tcons tuint
                                                              (Tcons tushort
                                                                (Tcons
                                                                  tushort
                                                                  Tnil))))
                                                          tvoid cc_default))
                                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                 (Etempvar _lo_32 tuint) ::
                                 (Etempvar _dst tushort) ::
                                 (Econst_int (Int.repr 62016) tint) :: nil))
                              (Sifthenelse (Ebinop Oeq
                                             (Etempvar _lo_32 tuint)
                                             (Etempvar _imm32 tuint) tint)
                                (Sreturn None)
                                (Ssequence
                                  (Scall None
                                    (Evar _mov_int_to_movwt (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _jit_state noattr))
                                                                (Tcons tuint
                                                                  (Tcons
                                                                    tushort
                                                                    (Tcons
                                                                    tushort
                                                                    Tnil))))
                                                              tvoid
                                                              cc_default))
                                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                     (Etempvar _hi_32 tuint) ::
                                     (Etempvar _dst tushort) ::
                                     (Econst_int (Int.repr 62144) tint) ::
                                     nil))
                                  (Sreturn None))))))
                        (LScons (Some 196)
                          (Ssequence
                            (Scall None
                              (Evar _bpf_alu32_to_thumb_imm_shift_comm 
                              (Tfunction
                                (Tcons (tptr (Tstruct _jit_state noattr))
                                  (Tcons tushort
                                    (Tcons tushort (Tcons tuint Tnil))))
                                tvoid cc_default))
                              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                               (Econst_int (Int.repr 64064) tint) ::
                               (Etempvar _dst tushort) ::
                               (Etempvar _imm32 tuint) :: nil))
                            (Sreturn None))
                          (LScons None (Sreturn None) LSnil))))))))))))))
|}.

Definition f_nat_to_opcode_alu32 := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Oeq
               (Ebinop Oand (Etempvar _op tuchar)
                 (Econst_int (Int.repr 7) tuint) tuint)
               (Econst_int (Int.repr 4) tuint) tint)
  (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tuint)
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 8) tuint) tuint) tint)
    (Sreturn (Some (Econst_int (Int.repr 4) tuint)))
    (Sreturn (Some (Econst_int (Int.repr 12) tuint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tuint))))
|}.

Definition f_nat_to_opcode_alu32_reg := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Etempvar _op tuchar)))
|}.

Definition f_nat_to_opcode_alu32_imm := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Etempvar _op tuchar)))
|}.

Definition f_jit_one := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_op, tuchar) :: (_opc, tuchar) :: (_dst, tuint) ::
               (_imm32, tint) :: (_opr, tuchar) :: (_src, tuint) ::
               (_opi, tuchar) :: (_t'7, tuchar) :: (_t'6, tuint) ::
               (_t'5, tuchar) :: (_t'4, tint) :: (_t'3, tuint) ::
               (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_ins (Tfunction (Tcons tulong Tnil) tuchar cc_default))
      ((Etempvar _ins tulong) :: nil))
    (Sset _op (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _nat_to_opcode_alu32 (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
        ((Etempvar _op tuchar) :: nil))
      (Sset _opc (Ecast (Etempvar _t'2 tuchar) tuchar)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint cc_default))
          ((Etempvar _ins tulong) :: nil))
        (Sset _dst (Etempvar _t'3 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_immediate (Tfunction (Tcons tulong Tnil) tint
                                   cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _imm32 (Etempvar _t'4 tint)))
        (Sswitch (Etempvar _opc tuchar)
          (LScons (Some 12)
            (Ssequence
              (Ssequence
                (Scall (Some _t'5)
                  (Evar _nat_to_opcode_alu32_reg (Tfunction
                                                   (Tcons tuchar Tnil) tuchar
                                                   cc_default))
                  ((Etempvar _op tuchar) :: nil))
                (Sset _opr (Ecast (Etempvar _t'5 tuchar) tuchar)))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _get_src (Tfunction (Tcons tulong Tnil) tuint
                                     cc_default))
                    ((Etempvar _ins tulong) :: nil))
                  (Sset _src (Etempvar _t'6 tuint)))
                (Ssequence
                  (Scall None
                    (Evar _jit_call_save_reg (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _jit_state noattr))
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil))) tvoid
                                               cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Etempvar _dst tuint) :: (Etempvar _src tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _bpf_alu32_to_thumb_reg (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _jit_state noattr))
                                                        (Tcons tuchar
                                                          (Tcons tushort
                                                            (Tcons tushort
                                                              Tnil)))) tvoid
                                                      cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Etempvar _opr tuchar) :: (Etempvar _dst tuint) ::
                       (Etempvar _src tuint) :: nil))
                    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
            (LScons (Some 4)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _nat_to_opcode_alu32_imm (Tfunction
                                                     (Tcons tuchar Tnil)
                                                     tuchar cc_default))
                    ((Etempvar _op tuchar) :: nil))
                  (Sset _opi (Ecast (Etempvar _t'7 tuchar) tuchar)))
                (Ssequence
                  (Scall None
                    (Evar _jit_call_save_imm (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _jit_state noattr))
                                                 (Tcons tuint Tnil)) tvoid
                                               cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Etempvar _dst tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _bpf_alu32_to_thumb_imm (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _jit_state noattr))
                                                        (Tcons tuchar
                                                          (Tcons tushort
                                                            (Tcons tuint
                                                              Tnil)))) tvoid
                                                      cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Etempvar _opi tuchar) :: (Etempvar _dst tuint) ::
                       (Etempvar _imm32 tint) :: nil))
                    (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
              (LScons None
                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                LSnil))))))))
|}.

Definition f_jit_sequence := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_fuel, tuint) :: (_pc, tuint) :: (_counter, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_ins64, tulong) :: (_cond, tbool) ::
               (_t'3, tuint) :: (_t'2, tbool) :: (_t'1, tulong) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _fuel tuint)
               (Econst_int (Int.repr 0) tuint) tint)
  (Sreturn (Some (Etempvar _counter tuint)))
  (Ssequence
    (Sset _n
      (Ebinop Osub (Etempvar _fuel tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _eval_input_ins (Tfunction
                                  (Tcons (tptr (Tstruct _jit_state noattr))
                                    (Tcons tuint Tnil)) tulong cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Etempvar _pc tuint) :: nil))
        (Sset _ins64 (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _jit_one (Tfunction
                             (Tcons (tptr (Tstruct _jit_state noattr))
                               (Tcons tulong Tnil)) tbool cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Etempvar _ins64 tulong) :: nil))
          (Sset _cond (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sifthenelse (Etempvar _cond tbool)
          (Ssequence
            (Scall (Some _t'3)
              (Evar _jit_sequence (Tfunction
                                    (Tcons (tptr (Tstruct _jit_state noattr))
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil))))
                                    tuint cc_default))
              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
               (Etempvar _n tuint) ::
               (Ebinop Oadd (Etempvar _pc tuint)
                 (Econst_int (Int.repr 1) tuint) tuint) ::
               (Ebinop Oadd (Etempvar _counter tuint)
                 (Econst_int (Int.repr 1) tuint) tuint) :: nil))
            (Sreturn (Some (Etempvar _t'3 tuint))))
          (Sreturn (Some (Etempvar _counter tuint))))))))
|}.

Definition f_jit_alu32_thumb_upd_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_r, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_cond, tbool) :: (_ins32, tuint) :: (_t'2, tuint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_store_regset (Tfunction
                                 (Tcons (tptr (Tstruct _jit_state noattr))
                                   (Tcons tuint Tnil)) tbool cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Etempvar _r tuint) :: nil))
    (Sset _cond (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _cond tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _jit_alu32_thumb_mem_template_jit (Tfunction
                                                    (Tcons tushort
                                                      (Tcons tushort
                                                        (Tcons tushort
                                                          (Tcons tushort
                                                            Tnil)))) tuint
                                                    cc_default))
          ((Econst_int (Int.repr 63680) tint) :: (Etempvar _r tuint) ::
           (Econst_int (Int.repr 12) tint) ::
           (Ebinop Omul (Etempvar _r tuint) (Econst_int (Int.repr 4) tint)
             tuint) :: nil))
        (Sset _ins32 (Etempvar _t'2 tuint)))
      (Ssequence
        (Scall None
          (Evar _add_jited_bin (Tfunction
                                 (Tcons (tptr (Tstruct _jit_state noattr))
                                   (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Etempvar _ins32 tuint) :: nil))
        (Sreturn None)))
    (Sreturn None)))
|}.

Definition f_jit_alu32_thumb_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _jit_alu32_thumb_upd_store (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _jit_state noattr))
                                         (Tcons tuint Tnil)) tvoid
                                       cc_default))
    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
     (Econst_int (Int.repr 0) tuint) :: nil))
  (Ssequence
    (Scall None
      (Evar _jit_alu32_thumb_upd_store (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _jit_state noattr))
                                           (Tcons tuint Tnil)) tvoid
                                         cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Econst_int (Int.repr 1) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _jit_alu32_thumb_upd_store (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _jit_state noattr))
                                             (Tcons tuint Tnil)) tvoid
                                           cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
         (Econst_int (Int.repr 2) tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar _jit_alu32_thumb_upd_store (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _jit_state noattr))
                                               (Tcons tuint Tnil)) tvoid
                                             cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Econst_int (Int.repr 3) tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _jit_alu32_thumb_upd_store (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _jit_state noattr))
                                                 (Tcons tuint Tnil)) tvoid
                                               cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Econst_int (Int.repr 4) tuint) :: nil))
          (Ssequence
            (Scall None
              (Evar _jit_alu32_thumb_upd_store (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _jit_state noattr))
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
               (Econst_int (Int.repr 5) tuint) :: nil))
            (Ssequence
              (Scall None
                (Evar _jit_alu32_thumb_upd_store (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _jit_state noattr))
                                                     (Tcons tuint Tnil))
                                                   tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Econst_int (Int.repr 6) tuint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _jit_alu32_thumb_upd_store (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _jit_state noattr))
                                                       (Tcons tuint Tnil))
                                                     tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                   (Econst_int (Int.repr 7) tuint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _jit_alu32_thumb_upd_store (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _jit_state noattr))
                                                         (Tcons tuint Tnil))
                                                       tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     (Econst_int (Int.repr 8) tuint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _jit_alu32_thumb_upd_store (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _jit_state noattr))
                                                           (Tcons tuint Tnil))
                                                         tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Econst_int (Int.repr 9) tuint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _jit_alu32_thumb_upd_store (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _jit_state noattr))
                                                             (Tcons tuint
                                                               Tnil)) tvoid
                                                           cc_default))
                        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                         (Econst_int (Int.repr 10) tuint) :: nil))
                      (Sreturn None))))))))))))
|}.

Definition f_jit_alu32_thumb_upd_reset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: (_r, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_cond, tbool) :: (_ins32, tuint) :: (_t'2, tuint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_load_regset (Tfunction
                                (Tcons (tptr (Tstruct _jit_state noattr))
                                  (Tcons tuint Tnil)) tbool cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Etempvar _r tuint) :: nil))
    (Sset _cond (Ecast (Etempvar _t'1 tbool) tbool)))
  (Sifthenelse (Etempvar _cond tbool)
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _jit_alu32_thumb_mem_template_jit (Tfunction
                                                    (Tcons tushort
                                                      (Tcons tushort
                                                        (Tcons tushort
                                                          (Tcons tushort
                                                            Tnil)))) tuint
                                                    cc_default))
          ((Econst_int (Int.repr 63696) tint) :: (Etempvar _r tuint) ::
           (Econst_int (Int.repr 13) tint) ::
           (Ebinop Omul (Etempvar _r tuint) (Econst_int (Int.repr 4) tint)
             tuint) :: nil))
        (Sset _ins32 (Etempvar _t'2 tuint)))
      (Ssequence
        (Scall None
          (Evar _add_jited_bin (Tfunction
                                 (Tcons (tptr (Tstruct _jit_state noattr))
                                   (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Etempvar _ins32 tuint) :: nil))
        (Sreturn None)))
    (Sreturn None)))
|}.

Definition f_jit_alu32_thumb_reset1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _jit_alu32_thumb_upd_reset (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _jit_state noattr))
                                         (Tcons tuint Tnil)) tvoid
                                       cc_default))
    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
     (Econst_int (Int.repr 4) tuint) :: nil))
  (Ssequence
    (Scall None
      (Evar _jit_alu32_thumb_upd_reset (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _jit_state noattr))
                                           (Tcons tuint Tnil)) tvoid
                                         cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Econst_int (Int.repr 5) tuint) :: nil))
    (Ssequence
      (Scall None
        (Evar _jit_alu32_thumb_upd_reset (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _jit_state noattr))
                                             (Tcons tuint Tnil)) tvoid
                                           cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
         (Econst_int (Int.repr 6) tuint) :: nil))
      (Ssequence
        (Scall None
          (Evar _jit_alu32_thumb_upd_reset (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _jit_state noattr))
                                               (Tcons tuint Tnil)) tvoid
                                             cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Econst_int (Int.repr 7) tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _jit_alu32_thumb_upd_reset (Tfunction
                                               (Tcons
                                                 (tptr (Tstruct _jit_state noattr))
                                                 (Tcons tuint Tnil)) tvoid
                                               cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Econst_int (Int.repr 8) tuint) :: nil))
          (Ssequence
            (Scall None
              (Evar _jit_alu32_thumb_upd_reset (Tfunction
                                                 (Tcons
                                                   (tptr (Tstruct _jit_state noattr))
                                                   (Tcons tuint Tnil)) tvoid
                                                 cc_default))
              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
               (Econst_int (Int.repr 9) tuint) :: nil))
            (Ssequence
              (Scall None
                (Evar _jit_alu32_thumb_upd_reset (Tfunction
                                                   (Tcons
                                                     (tptr (Tstruct _jit_state noattr))
                                                     (Tcons tuint Tnil))
                                                   tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                 (Econst_int (Int.repr 10) tuint) :: nil))
              (Sreturn None))))))))
|}.

Definition f_jit_alu32_thumb_reset := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_f, tbool) :: (_l_ldr, tuint) :: (_t'2, tuint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_use_IR11 (Tfunction
                             (Tcons (tptr (Tstruct _jit_state noattr)) Tnil)
                             tbool cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
    (Sset _f (Ecast (Etempvar _t'1 tbool) tbool)))
  (Ssequence
    (Sifthenelse (Etempvar _f tbool)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _jit_alu32_thumb_mem_template_jit (Tfunction
                                                      (Tcons tushort
                                                        (Tcons tushort
                                                          (Tcons tushort
                                                            (Tcons tushort
                                                              Tnil)))) tuint
                                                      cc_default))
            ((Econst_int (Int.repr 63696) tint) ::
             (Econst_int (Int.repr 11) tint) ::
             (Econst_int (Int.repr 13) tint) ::
             (Econst_int (Int.repr 44) tint) :: nil))
          (Sset _l_ldr (Etempvar _t'2 tuint)))
        (Scall None
          (Evar _add_jited_bin (Tfunction
                                 (Tcons (tptr (Tstruct _jit_state noattr))
                                   (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Etempvar _l_ldr tuint) :: nil)))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _jit_alu32_thumb_reset1 (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _jit_state noattr))
                                          Tnil) tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
      (Sreturn None))))
|}.

Definition f_jit_alu32_post := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_l_ldr, tuint) :: (_ins_rm, tuint) :: (_ins32, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _jit_alu32_thumb_mem_template_jit (Tfunction
                                                (Tcons tushort
                                                  (Tcons tushort
                                                    (Tcons tushort
                                                      (Tcons tushort Tnil))))
                                                tuint cc_default))
      ((Econst_int (Int.repr 63696) tint) ::
       (Econst_int (Int.repr 13) tint) :: (Econst_int (Int.repr 13) tint) ::
       (Econst_int (Int.repr 0) tint) :: nil))
    (Sset _l_ldr (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _encode_thumb (Tfunction
                              (Tcons tuint
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil)))) tuint
                              cc_default))
        ((Econst_int (Int.repr 14) tint) ::
         (Econst_int (Int.repr 18176) tint) ::
         (Econst_int (Int.repr 3) tuint) ::
         (Econst_int (Int.repr 4) tuint) :: nil))
      (Sset _ins_rm (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _encode_thumb (Tfunction
                                (Tcons tuint
                                  (Tcons tuint
                                    (Tcons tuint (Tcons tuint Tnil)))) tuint
                                cc_default))
          ((Etempvar _ins_rm tuint) :: (Econst_int (Int.repr 48896) tint) ::
           (Econst_int (Int.repr 16) tuint) ::
           (Econst_int (Int.repr 16) tuint) :: nil))
        (Sset _ins32 (Etempvar _t'3 tuint)))
      (Ssequence
        (Scall None
          (Evar _add_jited_bin (Tfunction
                                 (Tcons (tptr (Tstruct _jit_state noattr))
                                   (Tcons tuint Tnil)) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
           (Etempvar _l_ldr tuint) :: nil))
        (Ssequence
          (Scall None
            (Evar _add_jited_bin (Tfunction
                                   (Tcons (tptr (Tstruct _jit_state noattr))
                                     (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
             (Etempvar _ins32 tuint) :: nil))
          (Sreturn None))))))
|}.

Definition f_jit_alu32_aux := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_fuel, tuint) :: (_pc, tuint) :: (_counter, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _jit_alu32_pre (Tfunction
                           (Tcons (tptr (Tstruct _jit_state noattr)) Tnil)
                           tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _jit_sequence (Tfunction
                              (Tcons (tptr (Tstruct _jit_state noattr))
                                (Tcons tuint
                                  (Tcons tuint (Tcons tuint Tnil)))) tuint
                              cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
         (Etempvar _fuel tuint) :: (Etempvar _pc tuint) ::
         (Etempvar _counter tuint) :: nil))
      (Sset _n (Etempvar _t'1 tuint)))
    (Ssequence
      (Scall None
        (Evar _jit_alu32_thumb_store (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _jit_state noattr))
                                         Tnil) tvoid cc_default))
        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
      (Ssequence
        (Scall None
          (Evar _jit_alu32_thumb_reset (Tfunction
                                         (Tcons
                                           (tptr (Tstruct _jit_state noattr))
                                           Tnil) tvoid cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
        (Ssequence
          (Scall None
            (Evar _jit_alu32_post (Tfunction
                                    (Tcons (tptr (Tstruct _jit_state noattr))
                                      Tnil) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
          (Sreturn (Some (Etempvar _n tuint))))))))
|}.

Definition f_jit_list := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_fuel, tuint) :: (_pc, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _reset_init_jittedthumb (Tfunction
                                    (Tcons (tptr (Tstruct _jit_state noattr))
                                      Tnil) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _jit_alu32_aux (Tfunction
                             (Tcons (tptr (Tstruct _jit_state noattr))
                               (Tcons tuint (Tcons tuint (Tcons tuint Tnil))))
                             tuint cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Etempvar _fuel tuint) :: (Etempvar _pc tuint) ::
       (Econst_int (Int.repr 0) tuint) :: nil))
    (Sreturn (Some (Etempvar _t'1 tuint)))))
|}.

Definition f_whole_compiler_aux := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) ::
                (_fuel, tuint) :: (_pc, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) :: (_len, tuint) :: (_ins64, tulong) ::
               (_b, tbool) :: (_arm_ofs, tuint) :: (_sz, tuint) ::
               (_ofs, tint) :: (_next_pc, tuint) :: (_next_ins, tulong) ::
               (_t'11, tuint) :: (_t'10, tuint) :: (_t'9, tbool) ::
               (_t'8, tulong) :: (_t'7, tint) :: (_t'6, tbool) ::
               (_t'5, tuint) :: (_t'4, tuint) :: (_t'3, tbool) ::
               (_t'2, tulong) :: (_t'1, tuint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _fuel tuint)
               (Econst_int (Int.repr 0) tuint) tint)
  (Sreturn None)
  (Ssequence
    (Sset _n
      (Ebinop Osub (Etempvar _fuel tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _eval_input_len (Tfunction
                                  (Tcons (tptr (Tstruct _jit_state noattr))
                                    Tnil) tuint cc_default))
          ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
        (Sset _len (Etempvar _t'1 tuint)))
      (Sifthenelse (Ebinop Oeq (Etempvar _len tuint) (Etempvar _pc tuint)
                     tint)
        (Sreturn None)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _eval_input_ins (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _jit_state noattr))
                                        (Tcons tuint Tnil)) tulong
                                      cc_default))
              ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
               (Etempvar _pc tuint) :: nil))
            (Sset _ins64 (Etempvar _t'2 tulong)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _ins_is_bpf_alu32 (Tfunction (Tcons tulong Tnil) tbool
                                          cc_default))
                ((Etempvar _ins64 tulong) :: nil))
              (Sset _b (Ecast (Etempvar _t'3 tbool) tbool)))
            (Sifthenelse (Etempvar _b tbool)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _eval_arm_ofs (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _jit_state noattr))
                                            Tnil) tuint cc_default))
                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                     nil))
                  (Sset _arm_ofs (Etempvar _t'4 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'5)
                      (Evar _jit_list (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _jit_state noattr))
                                          (Tcons tuint (Tcons tuint Tnil)))
                                        tuint cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Ebinop Osub (Etempvar _len tuint)
                         (Etempvar _pc tuint) tuint) ::
                       (Etempvar _pc tuint) :: nil))
                    (Sset _sz (Etempvar _t'5 tuint)))
                  (Ssequence
                    (Scall None
                      (Evar _add_key_value (Tfunction
                                             (Tcons
                                               (tptr (Tstruct _jit_state noattr))
                                               (Tcons tuint
                                                 (Tcons tuint
                                                   (Tcons tuint Tnil))))
                                             tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Etempvar _pc tuint) :: (Etempvar _arm_ofs tuint) ::
                       (Etempvar _sz tuint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _whole_compiler_aux (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _jit_state noattr))
                                                      (Tcons tuint
                                                        (Tcons tuint Tnil)))
                                                    tvoid cc_default))
                        ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                         (Etempvar _n tuint) ::
                         (Ebinop Oadd (Etempvar _pc tuint)
                           (Etempvar _sz tuint) tuint) :: nil))
                      (Sreturn None)))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _ins_is_bpf_jump (Tfunction (Tcons tulong Tnil)
                                             tbool cc_default))
                    ((Etempvar _ins64 tulong) :: nil))
                  (Sset _b (Ecast (Etempvar _t'6 tbool) tbool)))
                (Sifthenelse (Etempvar _b tbool)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'7)
                        (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                            cc_default))
                        ((Etempvar _ins64 tulong) :: nil))
                      (Sset _ofs (Etempvar _t'7 tint)))
                    (Ssequence
                      (Sset _next_pc
                        (Ebinop Oadd
                          (Ebinop Oadd (Etempvar _pc tuint)
                            (Etempvar _ofs tint) tuint)
                          (Econst_int (Int.repr 1) tuint) tuint))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'8)
                            (Evar _eval_input_ins (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _jit_state noattr))
                                                      (Tcons tuint Tnil))
                                                    tulong cc_default))
                            ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                             (Etempvar _next_pc tuint) :: nil))
                          (Sset _next_ins (Etempvar _t'8 tulong)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'9)
                              (Evar _ins_is_bpf_alu32 (Tfunction
                                                        (Tcons tulong Tnil)
                                                        tbool cc_default))
                              ((Etempvar _next_ins tulong) :: nil))
                            (Sset _b (Ecast (Etempvar _t'9 tbool) tbool)))
                          (Sifthenelse (Etempvar _b tbool)
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'10)
                                  (Evar _eval_arm_ofs (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _jit_state noattr))
                                                          Tnil) tuint
                                                        cc_default))
                                  ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                   nil))
                                (Sset _arm_ofs (Etempvar _t'10 tuint)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'11)
                                    (Evar _jit_list (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _jit_state noattr))
                                                        (Tcons tuint
                                                          (Tcons tuint Tnil)))
                                                      tuint cc_default))
                                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                     (Ebinop Osub (Etempvar _len tuint)
                                       (Etempvar _next_pc tuint) tuint) ::
                                     (Etempvar _next_pc tuint) :: nil))
                                  (Sset _sz (Etempvar _t'11 tuint)))
                                (Ssequence
                                  (Scall None
                                    (Evar _add_key_value (Tfunction
                                                           (Tcons
                                                             (tptr (Tstruct _jit_state noattr))
                                                             (Tcons tuint
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   Tnil))))
                                                           tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                     (Etempvar _next_pc tuint) ::
                                     (Etempvar _arm_ofs tuint) ::
                                     (Etempvar _sz tuint) :: nil))
                                  (Ssequence
                                    (Scall None
                                      (Evar _whole_compiler_aux (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _jit_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuint
                                                                    Tnil)))
                                                                  tvoid
                                                                  cc_default))
                                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                       (Etempvar _n tuint) ::
                                       (Ebinop Oadd (Etempvar _pc tuint)
                                         (Econst_int (Int.repr 1) tuint)
                                         tuint) :: nil))
                                    (Sreturn None)))))
                            (Ssequence
                              (Scall None
                                (Evar _whole_compiler_aux (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _jit_state noattr))
                                                              (Tcons tuint
                                                                (Tcons tuint
                                                                  Tnil)))
                                                            tvoid cc_default))
                                ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                                 (Etempvar _n tuint) ::
                                 (Ebinop Oadd (Etempvar _pc tuint)
                                   (Econst_int (Int.repr 1) tuint) tuint) ::
                                 nil))
                              (Sreturn None)))))))
                  (Ssequence
                    (Scall None
                      (Evar _whole_compiler_aux (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _jit_state noattr))
                                                    (Tcons tuint
                                                      (Tcons tuint Tnil)))
                                                  tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
                       (Etempvar _n tuint) ::
                       (Ebinop Oadd (Etempvar _pc tuint)
                         (Econst_int (Int.repr 1) tuint) tuint) :: nil))
                    (Sreturn None)))))))))))
|}.

Definition f_whole_compiler := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _jit_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_len, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_input_len (Tfunction
                              (Tcons (tptr (Tstruct _jit_state noattr)) Tnil)
                              tuint cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) :: nil))
    (Sset _len (Etempvar _t'1 tuint)))
  (Ssequence
    (Scall None
      (Evar _whole_compiler_aux (Tfunction
                                  (Tcons (tptr (Tstruct _jit_state noattr))
                                    (Tcons tuint (Tcons tuint Tnil))) tvoid
                                  cc_default))
      ((Etempvar _st (tptr (Tstruct _jit_state noattr))) ::
       (Etempvar _len tuint) :: (Econst_int (Int.repr 0) tuint) :: nil))
    (Sreturn None)))
|}.

Definition composites : list composite_definition :=
(Composite _key_value2 Struct
   (Member_plain _arm_ofs tuint :: Member_plain _alu32_ofs tuint :: nil)
   noattr ::
 Composite _jit_state Struct
   (Member_plain _input_len tuint :: Member_plain _input_ins (tptr tulong) ::
    Member_plain _tp_kv (tptr (Tstruct _key_value2 noattr)) ::
    Member_plain _use_IR11 tbool :: Member_plain _ld_set (tarray tbool 11) ::
    Member_plain _st_set (tarray tbool 11) ::
    Member_plain _tp_bin_len tuint :: Member_plain _tp_bin (tptr tuint) ::
    nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tuchar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tuchar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tuchar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons tint (Tcons tint Tnil)) tint
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons (tptr tushort) Tnil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_dmb,
   Gfun(External (EF_builtin "__builtin_dmb"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_dsb,
   Gfun(External (EF_builtin "__builtin_dsb"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_isb,
   Gfun(External (EF_builtin "__builtin_isb"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_execbin,
   Gfun(External (EF_builtin "__builtin_execbin"
                   (mksignature nil AST.Tint
                     {|cc_vararg:=(Some 0); cc_unproto:=false; cc_structret:=false|}))
     Tnil tuint
     {|cc_vararg:=(Some 0); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_eval_input_len, Gfun(Internal f_eval_input_len)) ::
 (_eval_input_ins, Gfun(Internal f_eval_input_ins)) ::
 (_get_dst, Gfun(Internal f_get_dst)) ::
 (_get_src, Gfun(Internal f_get_src)) ::
 (_eval_arm_ofs, Gfun(Internal f_eval_arm_ofs)) ::
 (_add_key_value, Gfun(Internal f_add_key_value)) ::
 (_eval_use_IR11, Gfun(Internal f_eval_use_IR11)) ::
 (_upd_IR11_jittedthumb, Gfun(Internal f_upd_IR11_jittedthumb)) ::
 (_add_jited_bin, Gfun(Internal f_add_jited_bin)) ::
 (_eval_load_regset, Gfun(Internal f_eval_load_regset)) ::
 (_eval_store_regset, Gfun(Internal f_eval_store_regset)) ::
 (_upd_load_regset, Gfun(Internal f_upd_load_regset)) ::
 (_upd_store_regset, Gfun(Internal f_upd_store_regset)) ::
 (_reset_init_jittedthumb, Gfun(Internal f_reset_init_jittedthumb)) ::
 (_power2, Gfun(Internal f_power2)) ::
 (_decode_thumb, Gfun(Internal f_decode_thumb)) ::
 (_encode_thumb, Gfun(Internal f_encode_thumb)) ::
 (_ins_is_bpf_alu32, Gfun(Internal f_ins_is_bpf_alu32)) ::
 (_ins_is_bpf_jump, Gfun(Internal f_ins_is_bpf_jump)) ::
 (_get_immediate, Gfun(Internal f_get_immediate)) ::
 (_get_offset, Gfun(Internal f_get_offset)) ::
 (_get_opcode_ins, Gfun(Internal f_get_opcode_ins)) ::
 (_jit_alu32_thumb_mem_template_jit, Gfun(Internal f_jit_alu32_thumb_mem_template_jit)) ::
 (_jit_alu32_pre, Gfun(Internal f_jit_alu32_pre)) ::
 (_jit_call_save_add, Gfun(Internal f_jit_call_save_add)) ::
 (_jit_call_save_reg, Gfun(Internal f_jit_call_save_reg)) ::
 (_jit_call_save_imm, Gfun(Internal f_jit_call_save_imm)) ::
 (_bpf_alu32_to_thumb_reg_comm, Gfun(Internal f_bpf_alu32_to_thumb_reg_comm)) ::
 (_bpf_alu32_to_thumb_reg, Gfun(Internal f_bpf_alu32_to_thumb_reg)) ::
 (_load_IR11, Gfun(Internal f_load_IR11)) ::
 (_mov_int_to_movwt, Gfun(Internal f_mov_int_to_movwt)) ::
 (_bpf_alu32_to_thumb_imm_comm, Gfun(Internal f_bpf_alu32_to_thumb_imm_comm)) ::
 (_bpf_alu32_to_thumb_imm_shift_comm, Gfun(Internal f_bpf_alu32_to_thumb_imm_shift_comm)) ::
 (_bpf_alu32_to_thumb_imm, Gfun(Internal f_bpf_alu32_to_thumb_imm)) ::
 (_nat_to_opcode_alu32, Gfun(Internal f_nat_to_opcode_alu32)) ::
 (_nat_to_opcode_alu32_reg, Gfun(Internal f_nat_to_opcode_alu32_reg)) ::
 (_nat_to_opcode_alu32_imm, Gfun(Internal f_nat_to_opcode_alu32_imm)) ::
 (_jit_one, Gfun(Internal f_jit_one)) ::
 (_jit_sequence, Gfun(Internal f_jit_sequence)) ::
 (_jit_alu32_thumb_upd_store, Gfun(Internal f_jit_alu32_thumb_upd_store)) ::
 (_jit_alu32_thumb_store, Gfun(Internal f_jit_alu32_thumb_store)) ::
 (_jit_alu32_thumb_upd_reset, Gfun(Internal f_jit_alu32_thumb_upd_reset)) ::
 (_jit_alu32_thumb_reset1, Gfun(Internal f_jit_alu32_thumb_reset1)) ::
 (_jit_alu32_thumb_reset, Gfun(Internal f_jit_alu32_thumb_reset)) ::
 (_jit_alu32_post, Gfun(Internal f_jit_alu32_post)) ::
 (_jit_alu32_aux, Gfun(Internal f_jit_alu32_aux)) ::
 (_jit_list, Gfun(Internal f_jit_list)) ::
 (_whole_compiler_aux, Gfun(Internal f_whole_compiler_aux)) ::
 (_whole_compiler, Gfun(Internal f_whole_compiler)) :: nil).

Definition public_idents : list ident :=
(_whole_compiler :: _jit_alu32_thumb_mem_template_jit :: ___builtin_debug ::
 ___builtin_execbin :: ___builtin_isb :: ___builtin_dsb :: ___builtin_dmb ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


