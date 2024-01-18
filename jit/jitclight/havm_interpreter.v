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
  Definition source_file := "havm_interpreter.c".
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
Definition __bpf_get_call : ident := $"_bpf_get_call".
Definition __magic_function : ident := $"_magic_function".
Definition _addr : ident := $"addr".
Definition _addr_ptr : ident := $"addr_ptr".
Definition _alu32_ofs : ident := $"alu32_ofs".
Definition _arm_ofs : ident := $"arm_ofs".
Definition _b0 : ident := $"b0".
Definition _b1 : ident := $"b1".
Definition _block_perm : ident := $"block_perm".
Definition _block_ptr : ident := $"block_ptr".
Definition _block_size : ident := $"block_size".
Definition _bpf_flag : ident := $"bpf_flag".
Definition _bpf_interpreter_aux : ident := $"bpf_interpreter_aux".
Definition _check_mem : ident := $"check_mem".
Definition _check_mem_aux : ident := $"check_mem_aux".
Definition _check_mem_aux2 : ident := $"check_mem_aux2".
Definition _check_pc : ident := $"check_pc".
Definition _check_pc_incr : ident := $"check_pc_incr".
Definition _check_ptr : ident := $"check_ptr".
Definition _chunk : ident := $"chunk".
Definition _cmp_ptr32_nullM : ident := $"cmp_ptr32_nullM".
Definition _ctx_ptr : ident := $"ctx_ptr".
Definition _cur_mr : ident := $"cur_mr".
Definition _dst : ident := $"dst".
Definition _dst32 : ident := $"dst32".
Definition _eval_flag : ident := $"eval_flag".
Definition _eval_ins : ident := $"eval_ins".
Definition _eval_mrs_num : ident := $"eval_mrs_num".
Definition _eval_mrs_regions : ident := $"eval_mrs_regions".
Definition _eval_reg : ident := $"eval_reg".
Definition _exec_function : ident := $"exec_function".
Definition _f : ident := $"f".
Definition _f_ptr : ident := $"f_ptr".
Definition _fuel : ident := $"fuel".
Definition _fuel0 : ident := $"fuel0".
Definition _get_add : ident := $"get_add".
Definition _get_addr_ofs : ident := $"get_addr_ofs".
Definition _get_block_perm : ident := $"get_block_perm".
Definition _get_block_size : ident := $"get_block_size".
Definition _get_dst : ident := $"get_dst".
Definition _get_immediate : ident := $"get_immediate".
Definition _get_mem_region : ident := $"get_mem_region".
Definition _get_offset : ident := $"get_offset".
Definition _get_opcode_branch : ident := $"get_opcode_branch".
Definition _get_opcode_ins : ident := $"get_opcode_ins".
Definition _get_opcode_mem_ld_reg : ident := $"get_opcode_mem_ld_reg".
Definition _get_opcode_mem_st_imm : ident := $"get_opcode_mem_st_imm".
Definition _get_opcode_mem_st_reg : ident := $"get_opcode_mem_st_reg".
Definition _get_opcode_nat : ident := $"get_opcode_nat".
Definition _get_src : ident := $"get_src".
Definition _get_src32 : ident := $"get_src32".
Definition _get_start_addr : ident := $"get_start_addr".
Definition _get_sub : ident := $"get_sub".
Definition _havm_interpreter : ident := $"havm_interpreter".
Definition _havm_state : ident := $"havm_state".
Definition _hi_ofs : ident := $"hi_ofs".
Definition _i : ident := $"i".
Definition _imm : ident := $"imm".
Definition _input_ins : ident := $"input_ins".
Definition _input_len : ident := $"input_len".
Definition _ins : ident := $"ins".
Definition _is_null : ident := $"is_null".
Definition _jit_call : ident := $"jit_call".
Definition _key_value2 : ident := $"key_value2".
Definition _lo_ofs : ident := $"lo_ofs".
Definition _load_mem : ident := $"load_mem".
Definition _main : ident := $"main".
Definition _mem_reg_num : ident := $"mem_reg_num".
Definition _memory_region : ident := $"memory_region".
Definition _mr : ident := $"mr".
Definition _mr_perm : ident := $"mr_perm".
Definition _mrs : ident := $"mrs".
Definition _mrs_num : ident := $"mrs_num".
Definition _n : ident := $"n".
Definition _num : ident := $"num".
Definition _ofs : ident := $"ofs".
Definition _op : ident := $"op".
Definition _opc : ident := $"opc".
Definition _opcode_jmp : ident := $"opcode_jmp".
Definition _opcode_ld : ident := $"opcode_ld".
Definition _opcode_st : ident := $"opcode_st".
Definition _pc : ident := $"pc".
Definition _pc_loc : ident := $"pc_loc".
Definition _perm : ident := $"perm".
Definition _ptr : ident := $"ptr".
Definition _regsmap : ident := $"regsmap".
Definition _res : ident := $"res".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _src32 : ident := $"src32".
Definition _st : ident := $"st".
Definition _start : ident := $"start".
Definition _start_addr : ident := $"start_addr".
Definition _step : ident := $"step".
Definition _step_opcode_branch : ident := $"step_opcode_branch".
Definition _step_opcode_mem_ld_reg : ident := $"step_opcode_mem_ld_reg".
Definition _step_opcode_mem_st_imm : ident := $"step_opcode_mem_st_imm".
Definition _step_opcode_mem_st_reg : ident := $"step_opcode_mem_st_reg".
Definition _store_mem : ident := $"store_mem".
Definition _tp_bin : ident := $"tp_bin".
Definition _tp_bin_len : ident := $"tp_bin_len".
Definition _tp_kv : ident := $"tp_kv".
Definition _upd_flag : ident := $"upd_flag".
Definition _upd_pc : ident := $"upd_pc".
Definition _upd_reg : ident := $"upd_reg".
Definition _v : ident := $"v".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
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
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_check_pc := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Olt
                 (Efield
                   (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                     (Tstruct _havm_state noattr)) _pc_loc tuint)
                 (Efield
                   (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                     (Tstruct _havm_state noattr)) _input_len tuint) tint)))
|}.

Definition f_check_pc_incr := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Olt
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                       (Tstruct _havm_state noattr)) _pc_loc tuint)
                   (Econst_int (Int.repr 1) tint) tuint)
                 (Efield
                   (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                     (Tstruct _havm_state noattr)) _input_len tuint) tint)))
|}.

Definition f_upd_pc := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: (_pc, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
        (Tstruct _havm_state noattr)) _pc_loc tuint)
    (Ebinop Oadd
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
          (Tstruct _havm_state noattr)) _pc_loc tuint) (Etempvar _pc tuint)
      tuint))
  (Sreturn None))
|}.

Definition f_eval_reg := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: (_i, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                       (Tstruct _havm_state noattr)) _regsmap
                     (tarray tuint 11)) (Etempvar _i tuint) (tptr tuint))
                 tuint)))
|}.

Definition f_upd_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: (_i, tuint) ::
                (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
            (Tstruct _havm_state noattr)) _regsmap (tarray tuint 11))
        (Etempvar _i tuint) (tptr tuint)) tuint) (Etempvar _v tuint))
  (Sreturn None))
|}.

Definition f_eval_flag := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                   (Tstruct _havm_state noattr)) _bpf_flag tuint)))
|}.

Definition f_upd_flag := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: (_f, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
        (Tstruct _havm_state noattr)) _bpf_flag tuint) (Etempvar _f tuint))
  (Sreturn None))
|}.

Definition f_eval_mrs_num := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                   (Tstruct _havm_state noattr)) _mrs_num tuint)))
|}.

Definition f_eval_mrs_regions := {|
  fn_return := (tptr (Tstruct _memory_region noattr));
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                   (Tstruct _havm_state noattr)) _mrs
                 (tptr (Tstruct _memory_region noattr)))))
|}.

Definition f_load_mem := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_chunk, tuint) :: (_addr, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _chunk tuint)
  (LScons (Some 1)
    (Sreturn (Some (Ederef
                     (Ecast (Etempvar _addr (tptr tuchar)) (tptr tuchar))
                     tuchar)))
    (LScons (Some 2)
      (Sreturn (Some (Ederef
                       (Ecast (Etempvar _addr (tptr tuchar)) (tptr tushort))
                       tushort)))
      (LScons (Some 4)
        (Sreturn (Some (Ederef
                         (Ecast (Etempvar _addr (tptr tuchar)) (tptr tuint))
                         tuint)))
        (LScons None
          (Sreturn (Some (Econst_long (Int64.repr 0) tulong)))
          LSnil)))))
|}.

Definition f_store_mem := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_addr, (tptr tuchar)) :: (_chunk, tuint) :: (_v, tuint) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Etempvar _chunk tuint)
  (LScons (Some 1)
    (Ssequence
      (Sassign
        (Ederef (Ecast (Etempvar _addr (tptr tuchar)) (tptr tuchar)) tuchar)
        (Etempvar _v tuint))
      (Sreturn None))
    (LScons (Some 2)
      (Ssequence
        (Sassign
          (Ederef (Ecast (Etempvar _addr (tptr tuchar)) (tptr tushort))
            tushort) (Etempvar _v tuint))
        (Sreturn None))
      (LScons (Some 4)
        (Ssequence
          (Sassign
            (Ederef (Ecast (Etempvar _addr (tptr tuchar)) (tptr tuint))
              tuint) (Etempvar _v tuint))
          (Sreturn None))
        (LScons None (Sreturn None) LSnil)))))
|}.

Definition f_eval_ins := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ederef
                 (Ebinop Oadd
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                       (Tstruct _havm_state noattr)) _input_ins
                     (tptr tulong))
                   (Efield
                     (Ederef
                       (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                       (Tstruct _havm_state noattr)) _pc_loc tuint)
                   (tptr tulong)) tulong)))
|}.

Definition f_cmp_ptr32_nullM := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_addr, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oeq (Etempvar _addr (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)))
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

Definition f_get_mem_region := {|
  fn_return := (tptr (Tstruct _memory_region noattr));
  fn_callconv := cc_default;
  fn_params := ((_n, tuint) ::
                (_mrs, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd
                 (Etempvar _mrs (tptr (Tstruct _memory_region noattr)))
                 (Etempvar _n tuint) (tptr (Tstruct _memory_region noattr)))))
|}.

Definition f_jit_call := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ofs, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _ofs
    (Efield
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
              (Tstruct _havm_state noattr)) _tp_kv
            (tptr (Tstruct _key_value2 noattr)))
          (Efield
            (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
              (Tstruct _havm_state noattr)) _pc_loc tuint)
          (tptr (Tstruct _key_value2 noattr))) (Tstruct _key_value2 noattr))
      _arm_ofs tuint))
  (Ssequence
    (Scall None
      (Evar __magic_function (Tfunction
                               (Tcons tuint
                                 (Tcons (tptr (Tstruct _havm_state noattr))
                                   Tnil)) tvoid cc_default))
      ((Ebinop Omul (Econst_int (Int.repr 4) tint) (Etempvar _ofs tuint)
         tuint) :: (Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
            (Tstruct _havm_state noattr)) _pc_loc tuint)
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
              (Tstruct _havm_state noattr)) _pc_loc tuint)
          (Efield
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                    (Tstruct _havm_state noattr)) _tp_kv
                  (tptr (Tstruct _key_value2 noattr)))
                (Efield
                  (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
                    (Tstruct _havm_state noattr)) _pc_loc tuint)
                (tptr (Tstruct _key_value2 noattr)))
              (Tstruct _key_value2 noattr)) _alu32_ofs tuint) tuint))
      (Sreturn None))))
|}.

Definition f__bpf_get_call := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_imm, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
|}.

Definition f_exec_function := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_ptr, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _ptr (tptr tuchar))
               (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _st (tptr (Tstruct _havm_state noattr)))
          (Tstruct _havm_state noattr)) _bpf_flag tuint)
      (Econst_int (Int.repr 5) tint))
    (Sreturn (Some (Econst_int (Int.repr 0) tuint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tuint))))
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

Definition f_get_src32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: (_x, tuchar) ::
                (_ins, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_imm, tint) :: (_src, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tint) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tuint)
               (Ebinop Oand (Etempvar _x tuchar)
                 (Econst_int (Int.repr 8) tuint) tuint) tint)
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _get_immediate (Tfunction (Tcons tulong Tnil) tint cc_default))
        ((Etempvar _ins tulong) :: nil))
      (Sset _imm (Etempvar _t'1 tint)))
    (Sreturn (Some (Etempvar _imm tint))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _get_src (Tfunction (Tcons tulong Tnil) tuint cc_default))
        ((Etempvar _ins tulong) :: nil))
      (Sset _src (Etempvar _t'2 tuint)))
    (Ssequence
      (Scall (Some _t'3)
        (Evar _eval_reg (Tfunction
                          (Tcons (tptr (Tstruct _havm_state noattr))
                            (Tcons tuint Tnil)) tuint cc_default))
        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
         (Etempvar _src tuint) :: nil))
      (Sreturn (Some (Etempvar _t'3 tuint))))))
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

Definition f_get_opcode_branch := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 240) tint) tint) tuchar)))
|}.

Definition f_get_opcode_mem_ld_reg := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 255) tint) tint) tuchar)))
|}.

Definition f_get_opcode_mem_st_imm := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 255) tint) tint) tuchar)))
|}.

Definition f_get_opcode_mem_st_reg := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 255) tint) tint) tuchar)))
|}.

Definition f_get_opcode_nat := {|
  fn_return := tuchar;
  fn_callconv := cc_default;
  fn_params := ((_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oand (Etempvar _op tuchar)
                   (Econst_int (Int.repr 7) tint) tint) tuchar)))
|}.

Definition f_get_add := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: (_y, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _x tuint) (Etempvar _y tuint) tuint)))
|}.

Definition f_get_sub := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: (_y, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Osub (Etempvar _x tuint) (Etempvar _y tuint) tuint)))
|}.

Definition f_get_addr_ofs := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_x, tuint) :: (_ofs, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oadd (Etempvar _x tuint) (Etempvar _ofs tint) tuint)))
|}.

Definition f_get_start_addr := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_mr, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef
                   (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
                   (Tstruct _memory_region noattr)) _start_addr tuint)))
|}.

Definition f_get_block_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_mr, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef
                   (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
                   (Tstruct _memory_region noattr)) _block_size tuint)))
|}.

Definition f_get_block_perm := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_mr, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Efield
                 (Ederef
                   (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
                   (Tstruct _memory_region noattr)) _block_perm tuint)))
|}.

Definition f_check_mem_aux2 := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_mr, (tptr (Tstruct _memory_region noattr))) ::
                (_perm, tuint) :: (_addr, tuint) :: (_chunk, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_start, tuint) :: (_size, tuint) :: (_mr_perm, tuint) ::
               (_lo_ofs, tuint) :: (_hi_ofs, tuint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_start_addr (Tfunction
                              (Tcons (tptr (Tstruct _memory_region noattr))
                                Tnil) tuint cc_default))
      ((Etempvar _mr (tptr (Tstruct _memory_region noattr))) :: nil))
    (Sset _start (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _get_block_size (Tfunction
                                (Tcons (tptr (Tstruct _memory_region noattr))
                                  Tnil) tuint cc_default))
        ((Etempvar _mr (tptr (Tstruct _memory_region noattr))) :: nil))
      (Sset _size (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_block_perm (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _memory_region noattr))
                                    Tnil) tuint cc_default))
          ((Etempvar _mr (tptr (Tstruct _memory_region noattr))) :: nil))
        (Sset _mr_perm (Etempvar _t'3 tuint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_sub (Tfunction (Tcons tuint (Tcons tuint Tnil)) tuint
                             cc_default))
            ((Etempvar _addr tuint) :: (Etempvar _start tuint) :: nil))
          (Sset _lo_ofs (Etempvar _t'4 tuint)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _get_add (Tfunction (Tcons tuint (Tcons tuint Tnil))
                               tuint cc_default))
              ((Etempvar _lo_ofs tuint) :: (Etempvar _chunk tuint) :: nil))
            (Sset _hi_ofs (Etempvar _t'5 tuint)))
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Ole (Etempvar _hi_ofs tuint)
                             (Etempvar _size tuint) tint)
                (Sifthenelse (Ebinop Ole (Etempvar _lo_ofs tuint)
                               (Ebinop Osub
                                 (Econst_int (Int.repr (-1)) tuint)
                                 (Etempvar _chunk tuint) tuint) tint)
                  (Ssequence
                    (Sset _t'6
                      (Ecast
                        (Ebinop Oeq (Econst_int (Int.repr 0) tuint)
                          (Ebinop Omod (Etempvar _lo_ofs tuint)
                            (Etempvar _chunk tuint) tuint) tint) tbool))
                    (Sset _t'6 (Ecast (Etempvar _t'6 tint) tbool)))
                  (Sset _t'6 (Ecast (Econst_int (Int.repr 0) tint) tbool)))
                (Sset _t'6 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'6 tint)
                (Sset _t'7
                  (Ecast
                    (Ebinop Oge (Etempvar _mr_perm tuint)
                      (Etempvar _perm tuint) tint) tbool))
                (Sset _t'7 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'7 tint)
              (Sreturn (Some (Ebinop Oadd
                               (Efield
                                 (Ederef
                                   (Etempvar _mr (tptr (Tstruct _memory_region noattr)))
                                   (Tstruct _memory_region noattr))
                                 _block_ptr (tptr tuchar))
                               (Etempvar _lo_ofs tuint) (tptr tuchar))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_check_mem_aux := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_num, tuint) :: (_perm, tuint) :: (_chunk, tuint) ::
                (_addr, tuint) ::
                (_mrs, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tuint) ::
               (_cur_mr, (tptr (Tstruct _memory_region noattr))) ::
               (_check_ptr, (tptr tuchar)) :: (_is_null, tbool) ::
               (_t'4, (tptr tuchar)) :: (_t'3, tbool) ::
               (_t'2, (tptr tuchar)) ::
               (_t'1, (tptr (Tstruct _memory_region noattr))) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _num tuint)
               (Econst_int (Int.repr 0) tuint) tint)
  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
  (Ssequence
    (Sset _n
      (Ebinop Osub (Etempvar _num tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _get_mem_region (Tfunction
                                  (Tcons tuint
                                    (Tcons
                                      (tptr (Tstruct _memory_region noattr))
                                      Tnil))
                                  (tptr (Tstruct _memory_region noattr))
                                  cc_default))
          ((Etempvar _n tuint) ::
           (Etempvar _mrs (tptr (Tstruct _memory_region noattr))) :: nil))
        (Sset _cur_mr (Etempvar _t'1 (tptr (Tstruct _memory_region noattr)))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_mem_aux2 (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _memory_region noattr))
                                      (Tcons tuint
                                        (Tcons tuint (Tcons tuint Tnil))))
                                    (tptr tuchar) cc_default))
            ((Etempvar _cur_mr (tptr (Tstruct _memory_region noattr))) ::
             (Etempvar _perm tuint) :: (Etempvar _addr tuint) ::
             (Etempvar _chunk tuint) :: nil))
          (Sset _check_ptr (Etempvar _t'2 (tptr tuchar))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                       tbool cc_default))
              ((Etempvar _check_ptr (tptr tuchar)) :: nil))
            (Sset _is_null (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sifthenelse (Etempvar _is_null tbool)
            (Ssequence
              (Scall (Some _t'4)
                (Evar _check_mem_aux (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _havm_state noattr))
                                         (Tcons tuint
                                           (Tcons tuint
                                             (Tcons tuint
                                               (Tcons tuint
                                                 (Tcons
                                                   (tptr (Tstruct _memory_region noattr))
                                                   Tnil)))))) (tptr tuchar)
                                       cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Etempvar _n tuint) :: (Etempvar _perm tuint) ::
                 (Etempvar _chunk tuint) :: (Etempvar _addr tuint) ::
                 (Etempvar _mrs (tptr (Tstruct _memory_region noattr))) ::
                 nil))
              (Sreturn (Some (Etempvar _t'4 (tptr tuchar)))))
            (Sreturn (Some (Etempvar _check_ptr (tptr tuchar))))))))))
|}.

Definition f_check_mem := {|
  fn_return := (tptr tuchar);
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_perm, tuint) :: (_chunk, tuint) :: (_addr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_mem_reg_num, tuint) ::
               (_mrs, (tptr (Tstruct _memory_region noattr))) ::
               (_check_ptr, (tptr tuchar)) :: (_is_null, tbool) ::
               (_t'4, tbool) :: (_t'3, (tptr tuchar)) ::
               (_t'2, (tptr (Tstruct _memory_region noattr))) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_mrs_num (Tfunction
                            (Tcons (tptr (Tstruct _havm_state noattr)) Tnil)
                            tuint cc_default))
      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
    (Sset _mem_reg_num (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _eval_mrs_regions (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    Tnil)
                                  (tptr (Tstruct _memory_region noattr))
                                  cc_default))
        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
      (Sset _mrs (Etempvar _t'2 (tptr (Tstruct _memory_region noattr)))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _check_mem_aux (Tfunction
                                 (Tcons (tptr (Tstruct _havm_state noattr))
                                   (Tcons tuint
                                     (Tcons tuint
                                       (Tcons tuint
                                         (Tcons tuint
                                           (Tcons
                                             (tptr (Tstruct _memory_region noattr))
                                             Tnil)))))) (tptr tuchar)
                                 cc_default))
          ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
           (Etempvar _mem_reg_num tuint) :: (Etempvar _perm tuint) ::
           (Etempvar _chunk tuint) :: (Etempvar _addr tuint) ::
           (Etempvar _mrs (tptr (Tstruct _memory_region noattr))) :: nil))
        (Sset _check_ptr (Etempvar _t'3 (tptr tuchar))))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                     tbool cc_default))
            ((Etempvar _check_ptr (tptr tuchar)) :: nil))
          (Sset _is_null (Ecast (Etempvar _t'4 tbool) tbool)))
        (Sifthenelse (Etempvar _is_null tbool)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          (Sreturn (Some (Etempvar _check_ptr (tptr tuchar)))))))))
|}.

Definition f_step_opcode_branch := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_dst32, tuint) :: (_src32, tuint) :: (_ofs, tuint) ::
                (_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_jmp, tuchar) :: (_f_ptr, (tptr tuchar)) ::
               (_is_null, tbool) :: (_res, tuint) :: (_t'4, tuint) ::
               (_t'3, tbool) :: (_t'2, (tptr tuchar)) :: (_t'1, tuchar) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_branch (Tfunction (Tcons tuchar Tnil) tuchar
                                 cc_default)) ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_jmp (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_jmp tuchar)
    (LScons (Some 0)
      (Sifthenelse (Ebinop Oeq (Etempvar _op tuchar)
                     (Econst_int (Int.repr 5) tint) tint)
        (Ssequence
          (Scall None
            (Evar _upd_pc (Tfunction
                            (Tcons (tptr (Tstruct _havm_state noattr))
                              (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
             (Etempvar _ofs tuint) :: nil))
          (Sreturn None))
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _havm_state noattr))
                                (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
             (Econst_int (Int.repr 2) tuint) :: nil))
          (Sreturn None)))
      (LScons (Some 16)
        (Sifthenelse (Ebinop Oeq (Etempvar _dst32 tuint)
                       (Etempvar _src32 tuint) tint)
          (Ssequence
            (Scall None
              (Evar _upd_pc (Tfunction
                              (Tcons (tptr (Tstruct _havm_state noattr))
                                (Tcons tuint Tnil)) tvoid cc_default))
              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
               (Etempvar _ofs tuint) :: nil))
            (Sreturn None))
          (Sreturn None))
        (LScons (Some 32)
          (Sifthenelse (Ebinop Ogt (Etempvar _dst32 tuint)
                         (Etempvar _src32 tuint) tint)
            (Ssequence
              (Scall None
                (Evar _upd_pc (Tfunction
                                (Tcons (tptr (Tstruct _havm_state noattr))
                                  (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Etempvar _ofs tuint) :: nil))
              (Sreturn None))
            (Sreturn None))
          (LScons (Some 48)
            (Sifthenelse (Ebinop Oge (Etempvar _dst32 tuint)
                           (Etempvar _src32 tuint) tint)
              (Ssequence
                (Scall None
                  (Evar _upd_pc (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Etempvar _ofs tuint) :: nil))
                (Sreturn None))
              (Sreturn None))
            (LScons (Some 160)
              (Sifthenelse (Ebinop Olt (Etempvar _dst32 tuint)
                             (Etempvar _src32 tuint) tint)
                (Ssequence
                  (Scall None
                    (Evar _upd_pc (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _havm_state noattr))
                                      (Tcons tuint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Etempvar _ofs tuint) :: nil))
                  (Sreturn None))
                (Sreturn None))
              (LScons (Some 176)
                (Sifthenelse (Ebinop Ole (Etempvar _dst32 tuint)
                               (Etempvar _src32 tuint) tint)
                  (Ssequence
                    (Scall None
                      (Evar _upd_pc (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _havm_state noattr))
                                        (Tcons tuint Tnil)) tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                       (Etempvar _ofs tuint) :: nil))
                    (Sreturn None))
                  (Sreturn None))
                (LScons (Some 64)
                  (Sifthenelse (Ebinop One
                                 (Ebinop Oand (Etempvar _dst32 tuint)
                                   (Etempvar _src32 tuint) tuint)
                                 (Econst_int (Int.repr 0) tuint) tint)
                    (Ssequence
                      (Scall None
                        (Evar _upd_pc (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _havm_state noattr))
                                          (Tcons tuint Tnil)) tvoid
                                        cc_default))
                        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                         (Etempvar _ofs tuint) :: nil))
                      (Sreturn None))
                    (Sreturn None))
                  (LScons (Some 80)
                    (Sifthenelse (Ebinop One (Etempvar _dst32 tuint)
                                   (Etempvar _src32 tuint) tint)
                      (Ssequence
                        (Scall None
                          (Evar _upd_pc (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _havm_state noattr))
                                            (Tcons tuint Tnil)) tvoid
                                          cc_default))
                          ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                           (Etempvar _ofs tuint) :: nil))
                        (Sreturn None))
                      (Sreturn None))
                    (LScons (Some 96)
                      (Sifthenelse (Ebinop Ogt
                                     (Ecast (Etempvar _dst32 tuint) tint)
                                     (Ecast (Etempvar _src32 tuint) tint)
                                     tint)
                        (Ssequence
                          (Scall None
                            (Evar _upd_pc (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _havm_state noattr))
                                              (Tcons tuint Tnil)) tvoid
                                            cc_default))
                            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                             (Etempvar _ofs tuint) :: nil))
                          (Sreturn None))
                        (Sreturn None))
                      (LScons (Some 112)
                        (Sifthenelse (Ebinop Oge
                                       (Ecast (Etempvar _dst32 tuint) tint)
                                       (Ecast (Etempvar _src32 tuint) tint)
                                       tint)
                          (Ssequence
                            (Scall None
                              (Evar _upd_pc (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _havm_state noattr))
                                                (Tcons tuint Tnil)) tvoid
                                              cc_default))
                              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                               (Etempvar _ofs tuint) :: nil))
                            (Sreturn None))
                          (Sreturn None))
                        (LScons (Some 192)
                          (Sifthenelse (Ebinop Olt
                                         (Ecast (Etempvar _dst32 tuint) tint)
                                         (Ecast (Etempvar _src32 tuint) tint)
                                         tint)
                            (Ssequence
                              (Scall None
                                (Evar _upd_pc (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _havm_state noattr))
                                                  (Tcons tuint Tnil)) tvoid
                                                cc_default))
                                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                 (Etempvar _ofs tuint) :: nil))
                              (Sreturn None))
                            (Sreturn None))
                          (LScons (Some 208)
                            (Sifthenelse (Ebinop Ole
                                           (Ecast (Etempvar _dst32 tuint)
                                             tint)
                                           (Ecast (Etempvar _src32 tuint)
                                             tint) tint)
                              (Ssequence
                                (Scall None
                                  (Evar _upd_pc (Tfunction
                                                  (Tcons
                                                    (tptr (Tstruct _havm_state noattr))
                                                    (Tcons tuint Tnil)) tvoid
                                                  cc_default))
                                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                   (Etempvar _ofs tuint) :: nil))
                                (Sreturn None))
                              (Sreturn None))
                            (LScons (Some 128)
                              (Sifthenelse (Ebinop Oeq (Etempvar _op tuchar)
                                             (Econst_int (Int.repr 133) tint)
                                             tint)
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'2)
                                      (Evar __bpf_get_call (Tfunction
                                                             (Tcons tint
                                                               Tnil)
                                                             (tptr tuchar)
                                                             cc_default))
                                      ((Ecast (Etempvar _src32 tuint) tint) ::
                                       nil))
                                    (Sset _f_ptr
                                      (Etempvar _t'2 (tptr tuchar))))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'3)
                                        (Evar _cmp_ptr32_nullM (Tfunction
                                                                 (Tcons
                                                                   (tptr tuchar)
                                                                   Tnil)
                                                                 tbool
                                                                 cc_default))
                                        ((Etempvar _f_ptr (tptr tuchar)) ::
                                         nil))
                                      (Sset _is_null
                                        (Ecast (Etempvar _t'3 tbool) tbool)))
                                    (Sifthenelse (Etempvar _is_null tbool)
                                      (Ssequence
                                        (Scall None
                                          (Evar _upd_flag (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _havm_state noattr))
                                                              (Tcons tuint
                                                                Tnil)) tvoid
                                                            cc_default))
                                          ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                           (Econst_int (Int.repr 5) tuint) ::
                                           nil))
                                        (Sreturn None))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'4)
                                            (Evar _exec_function (Tfunction
                                                                   (Tcons
                                                                    (tptr (Tstruct _havm_state noattr))
                                                                    (Tcons
                                                                    (tptr tuchar)
                                                                    Tnil))
                                                                   tuint
                                                                   cc_default))
                                            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                             (Etempvar _f_ptr (tptr tuchar)) ::
                                             nil))
                                          (Sset _res (Etempvar _t'4 tuint)))
                                        (Ssequence
                                          (Scall None
                                            (Evar _upd_reg (Tfunction
                                                             (Tcons
                                                               (tptr (Tstruct _havm_state noattr))
                                                               (Tcons tuint
                                                                 (Tcons tuint
                                                                   Tnil)))
                                                             tvoid
                                                             cc_default))
                                            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                             (Econst_int (Int.repr 0) tuint) ::
                                             (Etempvar _res tuint) :: nil))
                                          (Sreturn None))))))
                                (Ssequence
                                  (Scall None
                                    (Evar _upd_flag (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _havm_state noattr))
                                                        (Tcons tuint Tnil))
                                                      tvoid cc_default))
                                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                     (Econst_int (Int.repr 2) tuint) :: nil))
                                  (Sreturn None)))
                              (LScons (Some 144)
                                (Sifthenelse (Ebinop Oeq
                                               (Etempvar _op tuchar)
                                               (Econst_int (Int.repr 149) tint)
                                               tint)
                                  (Ssequence
                                    (Scall None
                                      (Evar _upd_flag (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _havm_state noattr))
                                                          (Tcons tuint Tnil))
                                                        tvoid cc_default))
                                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                       (Econst_int (Int.repr 1) tuint) ::
                                       nil))
                                    (Sreturn None))
                                  (Ssequence
                                    (Scall None
                                      (Evar _upd_flag (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _havm_state noattr))
                                                          (Tcons tuint Tnil))
                                                        tvoid cc_default))
                                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                       (Econst_int (Int.repr 2) tuint) ::
                                       nil))
                                    (Sreturn None)))
                                (LScons None
                                  (Ssequence
                                    (Scall None
                                      (Evar _upd_flag (Tfunction
                                                        (Tcons
                                                          (tptr (Tstruct _havm_state noattr))
                                                          (Tcons tuint Tnil))
                                                        tvoid cc_default))
                                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                       (Econst_int (Int.repr 2) tuint) ::
                                       nil))
                                    (Sreturn None))
                                  LSnil)))))))))))))))))
|}.

Definition f_step_opcode_mem_ld_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_addr, tuint) :: (_dst, tuint) :: (_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_ld, tuchar) :: (_addr_ptr, (tptr tuchar)) ::
               (_is_null, tbool) :: (_v, tuint) :: (_t'10, tuint) ::
               (_t'9, tbool) :: (_t'8, (tptr tuchar)) :: (_t'7, tuint) ::
               (_t'6, tbool) :: (_t'5, (tptr tuchar)) :: (_t'4, tuint) ::
               (_t'3, tbool) :: (_t'2, (tptr tuchar)) :: (_t'1, tuchar) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_mem_ld_reg (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
      ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_ld (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_ld tuchar)
    (LScons (Some 97)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_mem (Tfunction
                               (Tcons (tptr (Tstruct _havm_state noattr))
                                 (Tcons tuint
                                   (Tcons tuint (Tcons tuint Tnil))))
                               (tptr tuchar) cc_default))
            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
             (Econst_int (Int.repr 1) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: (Etempvar _addr tuint) ::
             nil))
          (Sset _addr_ptr (Etempvar _t'2 (tptr tuchar))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                       tbool cc_default))
              ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
            (Sset _is_null (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sifthenelse (Etempvar _is_null tbool)
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 3) tuint) :: nil))
              (Sreturn None))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _load_mem (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _havm_state noattr))
                                      (Tcons tuint
                                        (Tcons (tptr tuchar) Tnil))) tuint
                                    cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Econst_int (Int.repr 4) tuint) ::
                   (Etempvar _addr_ptr (tptr tuchar)) :: nil))
                (Sset _v (Etempvar _t'4 tuint)))
              (Ssequence
                (Scall None
                  (Evar _upd_reg (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     (Tcons tuint (Tcons tuint Tnil))) tvoid
                                   cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Etempvar _dst tuint) :: (Etempvar _v tuint) :: nil))
                (Sreturn None))))))
      (LScons (Some 105)
        (Ssequence
          (Ssequence
            (Scall (Some _t'5)
              (Evar _check_mem (Tfunction
                                 (Tcons (tptr (Tstruct _havm_state noattr))
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tuint Tnil))))
                                 (tptr tuchar) cc_default))
              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
               (Econst_int (Int.repr 1) tuint) ::
               (Econst_int (Int.repr 2) tuint) :: (Etempvar _addr tuint) ::
               nil))
            (Sset _addr_ptr (Etempvar _t'5 (tptr tuchar))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                         tbool cc_default))
                ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
              (Sset _is_null (Ecast (Etempvar _t'6 tbool) tbool)))
            (Sifthenelse (Etempvar _is_null tbool)
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _havm_state noattr))
                                      (Tcons tuint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Econst_int (Int.repr 3) tuint) :: nil))
                (Sreturn None))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'7)
                    (Evar _load_mem (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _havm_state noattr))
                                        (Tcons tuint
                                          (Tcons (tptr tuchar) Tnil))) tuint
                                      cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Econst_int (Int.repr 2) tuint) ::
                     (Etempvar _addr_ptr (tptr tuchar)) :: nil))
                  (Sset _v (Etempvar _t'7 tuint)))
                (Ssequence
                  (Scall None
                    (Evar _upd_reg (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _havm_state noattr))
                                       (Tcons tuint (Tcons tuint Tnil)))
                                     tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Etempvar _dst tuint) :: (Etempvar _v tuint) :: nil))
                  (Sreturn None))))))
        (LScons (Some 113)
          (Ssequence
            (Ssequence
              (Scall (Some _t'8)
                (Evar _check_mem (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))))
                                   (tptr tuchar) cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 1) tuint) ::
                 (Econst_int (Int.repr 1) tuint) :: (Etempvar _addr tuint) ::
                 nil))
              (Sset _addr_ptr (Etempvar _t'8 (tptr tuchar))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'9)
                  (Evar _cmp_ptr32_nullM (Tfunction
                                           (Tcons (tptr tuchar) Tnil) tbool
                                           cc_default))
                  ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
                (Sset _is_null (Ecast (Etempvar _t'9 tbool) tbool)))
              (Sifthenelse (Etempvar _is_null tbool)
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _havm_state noattr))
                                        (Tcons tuint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Econst_int (Int.repr 3) tuint) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'10)
                      (Evar _load_mem (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _havm_state noattr))
                                          (Tcons tuint
                                            (Tcons (tptr tuchar) Tnil)))
                                        tuint cc_default))
                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                       (Econst_int (Int.repr 1) tuint) ::
                       (Etempvar _addr_ptr (tptr tuchar)) :: nil))
                    (Sset _v (Etempvar _t'10 tuint)))
                  (Ssequence
                    (Scall None
                      (Evar _upd_reg (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _havm_state noattr))
                                         (Tcons tuint (Tcons tuint Tnil)))
                                       tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                       (Etempvar _dst tuint) :: (Etempvar _v tuint) :: nil))
                    (Sreturn None))))))
          (LScons None
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) :: nil))
              (Sreturn None))
            LSnil))))))
|}.

Definition f_step_opcode_mem_st_imm := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: (_imm, tint) ::
                (_addr, tuint) :: (_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_st, tuchar) :: (_addr_ptr, (tptr tuchar)) ::
               (_is_null, tbool) :: (_t'7, tbool) :: (_t'6, (tptr tuchar)) ::
               (_t'5, tbool) :: (_t'4, (tptr tuchar)) :: (_t'3, tbool) ::
               (_t'2, (tptr tuchar)) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_mem_st_imm (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
      ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_st (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_st tuchar)
    (LScons (Some 98)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_mem (Tfunction
                               (Tcons (tptr (Tstruct _havm_state noattr))
                                 (Tcons tuint
                                   (Tcons tuint (Tcons tuint Tnil))))
                               (tptr tuchar) cc_default))
            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
             (Econst_int (Int.repr 2) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: (Etempvar _addr tuint) ::
             nil))
          (Sset _addr_ptr (Etempvar _t'2 (tptr tuchar))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                       tbool cc_default))
              ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
            (Sset _is_null (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sifthenelse (Etempvar _is_null tbool)
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 3) tuint) :: nil))
              (Sreturn None))
            (Ssequence
              (Scall None
                (Evar _store_mem (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     (Tcons (tptr tuchar)
                                       (Tcons tuint (Tcons tuint Tnil))))
                                   tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Etempvar _addr_ptr (tptr tuchar)) ::
                 (Econst_int (Int.repr 4) tuint) ::
                 (Ecast (Etempvar _imm tint) tuint) :: nil))
              (Sreturn None)))))
      (LScons (Some 106)
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _check_mem (Tfunction
                                 (Tcons (tptr (Tstruct _havm_state noattr))
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tuint Tnil))))
                                 (tptr tuchar) cc_default))
              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
               (Econst_int (Int.repr 2) tuint) ::
               (Econst_int (Int.repr 2) tuint) :: (Etempvar _addr tuint) ::
               nil))
            (Sset _addr_ptr (Etempvar _t'4 (tptr tuchar))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                         tbool cc_default))
                ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
              (Sset _is_null (Ecast (Etempvar _t'5 tbool) tbool)))
            (Sifthenelse (Etempvar _is_null tbool)
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _havm_state noattr))
                                      (Tcons tuint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Econst_int (Int.repr 3) tuint) :: nil))
                (Sreturn None))
              (Ssequence
                (Scall None
                  (Evar _store_mem (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _havm_state noattr))
                                       (Tcons (tptr tuchar)
                                         (Tcons tuint (Tcons tuint Tnil))))
                                     tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Etempvar _addr_ptr (tptr tuchar)) ::
                   (Econst_int (Int.repr 2) tuint) ::
                   (Ecast (Etempvar _imm tint) tuint) :: nil))
                (Sreturn None)))))
        (LScons (Some 114)
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _check_mem (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))))
                                   (tptr tuchar) cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) ::
                 (Econst_int (Int.repr 1) tuint) :: (Etempvar _addr tuint) ::
                 nil))
              (Sset _addr_ptr (Etempvar _t'6 (tptr tuchar))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _cmp_ptr32_nullM (Tfunction
                                           (Tcons (tptr tuchar) Tnil) tbool
                                           cc_default))
                  ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
                (Sset _is_null (Ecast (Etempvar _t'7 tbool) tbool)))
              (Sifthenelse (Etempvar _is_null tbool)
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _havm_state noattr))
                                        (Tcons tuint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Econst_int (Int.repr 3) tuint) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Scall None
                    (Evar _store_mem (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _havm_state noattr))
                                         (Tcons (tptr tuchar)
                                           (Tcons tuint (Tcons tuint Tnil))))
                                       tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Etempvar _addr_ptr (tptr tuchar)) ::
                     (Econst_int (Int.repr 1) tuint) ::
                     (Ecast (Etempvar _imm tint) tuint) :: nil))
                  (Sreturn None)))))
          (LScons None
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) :: nil))
              (Sreturn None))
            LSnil))))))
|}.

Definition f_step_opcode_mem_st_reg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_src32, tuint) :: (_addr, tuint) :: (_op, tuchar) :: nil);
  fn_vars := nil;
  fn_temps := ((_opcode_st, tuchar) :: (_addr_ptr, (tptr tuchar)) ::
               (_is_null, tbool) :: (_t'7, tbool) :: (_t'6, (tptr tuchar)) ::
               (_t'5, tbool) :: (_t'4, (tptr tuchar)) :: (_t'3, tbool) ::
               (_t'2, (tptr tuchar)) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _get_opcode_mem_st_reg (Tfunction (Tcons tuchar Tnil) tuchar
                                     cc_default))
      ((Etempvar _op tuchar) :: nil))
    (Sset _opcode_st (Ecast (Etempvar _t'1 tuchar) tuchar)))
  (Sswitch (Etempvar _opcode_st tuchar)
    (LScons (Some 99)
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _check_mem (Tfunction
                               (Tcons (tptr (Tstruct _havm_state noattr))
                                 (Tcons tuint
                                   (Tcons tuint (Tcons tuint Tnil))))
                               (tptr tuchar) cc_default))
            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
             (Econst_int (Int.repr 2) tuint) ::
             (Econst_int (Int.repr 4) tuint) :: (Etempvar _addr tuint) ::
             nil))
          (Sset _addr_ptr (Etempvar _t'2 (tptr tuchar))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                       tbool cc_default))
              ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
            (Sset _is_null (Ecast (Etempvar _t'3 tbool) tbool)))
          (Sifthenelse (Etempvar _is_null tbool)
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 3) tuint) :: nil))
              (Sreturn None))
            (Ssequence
              (Scall None
                (Evar _store_mem (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     (Tcons (tptr tuchar)
                                       (Tcons tuint (Tcons tuint Tnil))))
                                   tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Etempvar _addr_ptr (tptr tuchar)) ::
                 (Econst_int (Int.repr 4) tuint) ::
                 (Etempvar _src32 tuint) :: nil))
              (Sreturn None)))))
      (LScons (Some 107)
        (Ssequence
          (Ssequence
            (Scall (Some _t'4)
              (Evar _check_mem (Tfunction
                                 (Tcons (tptr (Tstruct _havm_state noattr))
                                   (Tcons tuint
                                     (Tcons tuint (Tcons tuint Tnil))))
                                 (tptr tuchar) cc_default))
              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
               (Econst_int (Int.repr 2) tuint) ::
               (Econst_int (Int.repr 2) tuint) :: (Etempvar _addr tuint) ::
               nil))
            (Sset _addr_ptr (Etempvar _t'4 (tptr tuchar))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _cmp_ptr32_nullM (Tfunction (Tcons (tptr tuchar) Tnil)
                                         tbool cc_default))
                ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
              (Sset _is_null (Ecast (Etempvar _t'5 tbool) tbool)))
            (Sifthenelse (Etempvar _is_null tbool)
              (Ssequence
                (Scall None
                  (Evar _upd_flag (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _havm_state noattr))
                                      (Tcons tuint Tnil)) tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Econst_int (Int.repr 3) tuint) :: nil))
                (Sreturn None))
              (Ssequence
                (Scall None
                  (Evar _store_mem (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _havm_state noattr))
                                       (Tcons (tptr tuchar)
                                         (Tcons tuint (Tcons tuint Tnil))))
                                     tvoid cc_default))
                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                   (Etempvar _addr_ptr (tptr tuchar)) ::
                   (Econst_int (Int.repr 2) tuint) ::
                   (Etempvar _src32 tuint) :: nil))
                (Sreturn None)))))
        (LScons (Some 115)
          (Ssequence
            (Ssequence
              (Scall (Some _t'6)
                (Evar _check_mem (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     (Tcons tuint
                                       (Tcons tuint (Tcons tuint Tnil))))
                                   (tptr tuchar) cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) ::
                 (Econst_int (Int.repr 1) tuint) :: (Etempvar _addr tuint) ::
                 nil))
              (Sset _addr_ptr (Etempvar _t'6 (tptr tuchar))))
            (Ssequence
              (Ssequence
                (Scall (Some _t'7)
                  (Evar _cmp_ptr32_nullM (Tfunction
                                           (Tcons (tptr tuchar) Tnil) tbool
                                           cc_default))
                  ((Etempvar _addr_ptr (tptr tuchar)) :: nil))
                (Sset _is_null (Ecast (Etempvar _t'7 tbool) tbool)))
              (Sifthenelse (Etempvar _is_null tbool)
                (Ssequence
                  (Scall None
                    (Evar _upd_flag (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _havm_state noattr))
                                        (Tcons tuint Tnil)) tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Econst_int (Int.repr 3) tuint) :: nil))
                  (Sreturn None))
                (Ssequence
                  (Scall None
                    (Evar _store_mem (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _havm_state noattr))
                                         (Tcons (tptr tuchar)
                                           (Tcons tuint (Tcons tuint Tnil))))
                                       tvoid cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Etempvar _addr_ptr (tptr tuchar)) ::
                     (Econst_int (Int.repr 1) tuint) ::
                     (Etempvar _src32 tuint) :: nil))
                  (Sreturn None)))))
          (LScons None
            (Ssequence
              (Scall None
                (Evar _upd_flag (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    (Tcons tuint Tnil)) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                 (Econst_int (Int.repr 2) tuint) :: nil))
              (Sreturn None))
            LSnil))))))
|}.

Definition f_step := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ins, tulong) :: (_op, tuchar) :: (_opc, tuchar) ::
               (_dst, tuint) :: (_dst32, tuint) :: (_ofs, tint) ::
               (_src32, tuint) :: (_src, tuint) :: (_addr, tuint) ::
               (_imm, tint) :: (_t'20, tuint) :: (_t'19, tint) ::
               (_t'18, tuint) :: (_t'17, tuint) :: (_t'16, tuint) ::
               (_t'15, tuint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tuint) :: (_t'11, tuint) :: (_t'10, tint) ::
               (_t'9, tuint) :: (_t'8, tuint) :: (_t'7, tuint) ::
               (_t'6, tint) :: (_t'5, tuint) :: (_t'4, tuint) ::
               (_t'3, tuchar) :: (_t'2, tuchar) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _eval_ins (Tfunction
                        (Tcons (tptr (Tstruct _havm_state noattr)) Tnil)
                        tulong cc_default))
      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
    (Sset _ins (Etempvar _t'1 tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _get_opcode_ins (Tfunction (Tcons tulong Tnil) tuchar
                                cc_default)) ((Etempvar _ins tulong) :: nil))
      (Sset _op (Ecast (Etempvar _t'2 tuchar) tuchar)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _get_opcode_nat (Tfunction (Tcons tuchar Tnil) tuchar
                                  cc_default))
          ((Etempvar _op tuchar) :: nil))
        (Sset _opc (Ecast (Etempvar _t'3 tuchar) tuchar)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _get_dst (Tfunction (Tcons tulong Tnil) tuint cc_default))
            ((Etempvar _ins tulong) :: nil))
          (Sset _dst (Etempvar _t'4 tuint)))
        (Sswitch (Etempvar _opc tuchar)
          (LScons (Some 4)
            (Ssequence
              (Scall None
                (Evar _jit_call (Tfunction
                                  (Tcons (tptr (Tstruct _havm_state noattr))
                                    Tnil) tvoid cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
              (Sreturn None))
            (LScons (Some 5)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'5)
                    (Evar _eval_reg (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _havm_state noattr))
                                        (Tcons tuint Tnil)) tuint cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     (Etempvar _dst tuint) :: nil))
                  (Sset _dst32 (Etempvar _t'5 tuint)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'6)
                      (Evar _get_offset (Tfunction (Tcons tulong Tnil) tint
                                          cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _ofs (Etempvar _t'6 tint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'7)
                        (Evar _get_src32 (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _havm_state noattr))
                                             (Tcons tuchar
                                               (Tcons tulong Tnil))) tuint
                                           cc_default))
                        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                         (Etempvar _op tuchar) :: (Etempvar _ins tulong) ::
                         nil))
                      (Sset _src32 (Etempvar _t'7 tuint)))
                    (Ssequence
                      (Scall None
                        (Evar _step_opcode_branch (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _havm_state noattr))
                                                      (Tcons tuint
                                                        (Tcons tuint
                                                          (Tcons tuint
                                                            (Tcons tuchar
                                                              Tnil))))) tvoid
                                                    cc_default))
                        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                         (Etempvar _dst32 tuint) ::
                         (Etempvar _src32 tuint) ::
                         (Ecast (Etempvar _ofs tint) tuint) ::
                         (Etempvar _op tuchar) :: nil))
                      (Sreturn None)))))
              (LScons (Some 1)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'8)
                      (Evar _get_src (Tfunction (Tcons tulong Tnil) tuint
                                       cc_default))
                      ((Etempvar _ins tulong) :: nil))
                    (Sset _src (Etempvar _t'8 tuint)))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'9)
                        (Evar _eval_reg (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _havm_state noattr))
                                            (Tcons tuint Tnil)) tuint
                                          cc_default))
                        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                         (Etempvar _src tuint) :: nil))
                      (Sset _src32 (Etempvar _t'9 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'10)
                          (Evar _get_offset (Tfunction (Tcons tulong Tnil)
                                              tint cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _ofs (Etempvar _t'10 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'11)
                            (Evar _get_addr_ofs (Tfunction
                                                  (Tcons tuint
                                                    (Tcons tint Tnil)) tuint
                                                  cc_default))
                            ((Etempvar _src32 tuint) ::
                             (Etempvar _ofs tint) :: nil))
                          (Sset _addr (Etempvar _t'11 tuint)))
                        (Ssequence
                          (Scall None
                            (Evar _step_opcode_mem_ld_reg (Tfunction
                                                            (Tcons
                                                              (tptr (Tstruct _havm_state noattr))
                                                              (Tcons tuint
                                                                (Tcons tuint
                                                                  (Tcons
                                                                    tuchar
                                                                    Tnil))))
                                                            tvoid cc_default))
                            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                             (Etempvar _addr tuint) ::
                             (Etempvar _dst tuint) ::
                             (Etempvar _op tuchar) :: nil))
                          (Sreturn None))))))
                (LScons (Some 2)
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'12)
                        (Evar _eval_reg (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _havm_state noattr))
                                            (Tcons tuint Tnil)) tuint
                                          cc_default))
                        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                         (Etempvar _dst tuint) :: nil))
                      (Sset _dst32 (Etempvar _t'12 tuint)))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'13)
                          (Evar _get_offset (Tfunction (Tcons tulong Tnil)
                                              tint cc_default))
                          ((Etempvar _ins tulong) :: nil))
                        (Sset _ofs (Etempvar _t'13 tint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'14)
                            (Evar _get_immediate (Tfunction
                                                   (Tcons tulong Tnil) tint
                                                   cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _imm (Etempvar _t'14 tint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'15)
                              (Evar _get_addr_ofs (Tfunction
                                                    (Tcons tuint
                                                      (Tcons tint Tnil))
                                                    tuint cc_default))
                              ((Etempvar _dst32 tuint) ::
                               (Etempvar _ofs tint) :: nil))
                            (Sset _addr (Etempvar _t'15 tuint)))
                          (Ssequence
                            (Scall None
                              (Evar _step_opcode_mem_st_imm (Tfunction
                                                              (Tcons
                                                                (tptr (Tstruct _havm_state noattr))
                                                                (Tcons tint
                                                                  (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil))))
                                                              tvoid
                                                              cc_default))
                              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                               (Etempvar _imm tint) ::
                               (Etempvar _addr tuint) ::
                               (Etempvar _op tuchar) :: nil))
                            (Sreturn None))))))
                  (LScons (Some 3)
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'16)
                          (Evar _eval_reg (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _havm_state noattr))
                                              (Tcons tuint Tnil)) tuint
                                            cc_default))
                          ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                           (Etempvar _dst tuint) :: nil))
                        (Sset _dst32 (Etempvar _t'16 tuint)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'17)
                            (Evar _get_src (Tfunction (Tcons tulong Tnil)
                                             tuint cc_default))
                            ((Etempvar _ins tulong) :: nil))
                          (Sset _src (Etempvar _t'17 tuint)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'18)
                              (Evar _eval_reg (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _havm_state noattr))
                                                  (Tcons tuint Tnil)) tuint
                                                cc_default))
                              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                               (Etempvar _src tuint) :: nil))
                            (Sset _src32 (Etempvar _t'18 tuint)))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'19)
                                (Evar _get_offset (Tfunction
                                                    (Tcons tulong Tnil) tint
                                                    cc_default))
                                ((Etempvar _ins tulong) :: nil))
                              (Sset _ofs (Etempvar _t'19 tint)))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'20)
                                  (Evar _get_addr_ofs (Tfunction
                                                        (Tcons tuint
                                                          (Tcons tint Tnil))
                                                        tuint cc_default))
                                  ((Etempvar _dst32 tuint) ::
                                   (Etempvar _ofs tint) :: nil))
                                (Sset _addr (Etempvar _t'20 tuint)))
                              (Ssequence
                                (Scall None
                                  (Evar _step_opcode_mem_st_reg (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _havm_state noattr))
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuint
                                                                    (Tcons
                                                                    tuchar
                                                                    Tnil))))
                                                                  tvoid
                                                                  cc_default))
                                  ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                                   (Etempvar _src32 tuint) ::
                                   (Etempvar _addr tuint) ::
                                   (Etempvar _op tuchar) :: nil))
                                (Sreturn None)))))))
                    (LScons None
                      (Ssequence
                        (Scall None
                          (Evar _upd_flag (Tfunction
                                            (Tcons
                                              (tptr (Tstruct _havm_state noattr))
                                              (Tcons tuint Tnil)) tvoid
                                            cc_default))
                          ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                           (Econst_int (Int.repr 2) tuint) :: nil))
                        (Sreturn None))
                      LSnil)))))))))))
|}.

Definition f_bpf_interpreter_aux := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_fuel, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_fuel0, tuint) :: (_b0, tbool) :: (_f, tuint) ::
               (_b1, tbool) :: (_t'3, tbool) :: (_t'2, tuint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Sifthenelse (Ebinop Oeq (Etempvar _fuel tuint)
               (Econst_int (Int.repr 0) tuint) tint)
  (Ssequence
    (Scall None
      (Evar _upd_flag (Tfunction
                        (Tcons (tptr (Tstruct _havm_state noattr))
                          (Tcons tuint Tnil)) tvoid cc_default))
      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
       (Econst_int (Int.repr 6) tuint) :: nil))
    (Sreturn None))
  (Ssequence
    (Sset _fuel0
      (Ebinop Osub (Etempvar _fuel tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _check_pc (Tfunction
                            (Tcons (tptr (Tstruct _havm_state noattr)) Tnil)
                            tbool cc_default))
          ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
        (Sset _b0 (Ecast (Etempvar _t'1 tbool) tbool)))
      (Sifthenelse (Etempvar _b0 tbool)
        (Ssequence
          (Scall None
            (Evar _step (Tfunction
                          (Tcons (tptr (Tstruct _havm_state noattr)) Tnil)
                          tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _eval_flag (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     Tnil) tuint cc_default))
                ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
              (Sset _f (Etempvar _t'2 tuint)))
            (Sifthenelse (Ebinop Oeq (Etempvar _f tuint)
                           (Econst_int (Int.repr 0) tuint) tint)
              (Ssequence
                (Ssequence
                  (Scall (Some _t'3)
                    (Evar _check_pc_incr (Tfunction
                                           (Tcons
                                             (tptr (Tstruct _havm_state noattr))
                                             Tnil) tbool cc_default))
                    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                     nil))
                  (Sset _b1 (Ecast (Etempvar _t'3 tbool) tbool)))
                (Sifthenelse (Etempvar _b1 tbool)
                  (Ssequence
                    (Scall None
                      (Evar _upd_pc (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _havm_state noattr))
                                        (Tcons tuint Tnil)) tvoid cc_default))
                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                       (Econst_int (Int.repr 1) tuint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _bpf_interpreter_aux (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _havm_state noattr))
                                                       (Tcons tuint Tnil))
                                                     tvoid cc_default))
                        ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                         (Etempvar _fuel0 tuint) :: nil))
                      (Sreturn None)))
                  (Ssequence
                    (Scall None
                      (Evar _upd_flag (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _havm_state noattr))
                                          (Tcons tuint Tnil)) tvoid
                                        cc_default))
                      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
                       (Econst_int (Int.repr 6) tuint) :: nil))
                    (Sreturn None))))
              (Sreturn None))))
        (Ssequence
          (Scall None
            (Evar _upd_flag (Tfunction
                              (Tcons (tptr (Tstruct _havm_state noattr))
                                (Tcons tuint Tnil)) tvoid cc_default))
            ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
             (Econst_int (Int.repr 6) tuint) :: nil))
          (Sreturn None))))))
|}.

Definition f_havm_interpreter := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_st, (tptr (Tstruct _havm_state noattr))) ::
                (_fuel, tuint) :: (_ctx_ptr, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_f, tuint) :: (_res, tuint) :: (_t'2, tuint) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _upd_reg (Tfunction
                     (Tcons (tptr (Tstruct _havm_state noattr))
                       (Tcons tuint (Tcons tuint Tnil))) tvoid cc_default))
    ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
     (Econst_int (Int.repr 1) tuint) :: (Etempvar _ctx_ptr tuint) :: nil))
  (Ssequence
    (Scall None
      (Evar _bpf_interpreter_aux (Tfunction
                                   (Tcons (tptr (Tstruct _havm_state noattr))
                                     (Tcons tuint Tnil)) tvoid cc_default))
      ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
       (Etempvar _fuel tuint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _eval_flag (Tfunction
                             (Tcons (tptr (Tstruct _havm_state noattr)) Tnil)
                             tuint cc_default))
          ((Etempvar _st (tptr (Tstruct _havm_state noattr))) :: nil))
        (Sset _f (Etempvar _t'1 tuint)))
      (Sifthenelse (Ebinop Oeq (Etempvar _f tuint)
                     (Econst_int (Int.repr 1) tuint) tint)
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _eval_reg (Tfunction
                                (Tcons (tptr (Tstruct _havm_state noattr))
                                  (Tcons tuint Tnil)) tuint cc_default))
              ((Etempvar _st (tptr (Tstruct _havm_state noattr))) ::
               (Econst_int (Int.repr 0) tuint) :: nil))
            (Sset _res (Etempvar _t'2 tuint)))
          (Sreturn (Some (Etempvar _res tuint))))
        (Sreturn (Some (Econst_int (Int.repr 0) tuint)))))))
|}.

Definition composites : list composite_definition :=
(Composite _key_value2 Struct
   (Member_plain _arm_ofs tuint :: Member_plain _alu32_ofs tuint :: nil)
   noattr ::
 Composite _memory_region Struct
   (Member_plain _start_addr tuint :: Member_plain _block_size tuint ::
    Member_plain _block_perm tuint ::
    Member_plain _block_ptr (tptr tuchar) :: nil)
   noattr ::
 Composite _havm_state Struct
   (Member_plain _regsmap (tarray tuint 11) :: Member_plain _pc_loc tuint ::
    Member_plain _bpf_flag tuint :: Member_plain _mrs_num tuint ::
    Member_plain _mrs (tptr (Tstruct _memory_region noattr)) ::
    Member_plain _input_len tuint :: Member_plain _input_ins (tptr tulong) ::
    Member_plain _tp_kv (tptr (Tstruct _key_value2 noattr)) ::
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
 (__magic_function,
   Gfun(External (EF_external "_magic_function"
                   (mksignature (AST.Tint :: AST.Tint :: nil) AST.Tvoid
                     cc_default))
     (Tcons tuint (Tcons (tptr (Tstruct _havm_state noattr)) Tnil)) tvoid
     cc_default)) :: (_check_pc, Gfun(Internal f_check_pc)) ::
 (_check_pc_incr, Gfun(Internal f_check_pc_incr)) ::
 (_upd_pc, Gfun(Internal f_upd_pc)) ::
 (_eval_reg, Gfun(Internal f_eval_reg)) ::
 (_upd_reg, Gfun(Internal f_upd_reg)) ::
 (_eval_flag, Gfun(Internal f_eval_flag)) ::
 (_upd_flag, Gfun(Internal f_upd_flag)) ::
 (_eval_mrs_num, Gfun(Internal f_eval_mrs_num)) ::
 (_eval_mrs_regions, Gfun(Internal f_eval_mrs_regions)) ::
 (_load_mem, Gfun(Internal f_load_mem)) ::
 (_store_mem, Gfun(Internal f_store_mem)) ::
 (_eval_ins, Gfun(Internal f_eval_ins)) ::
 (_cmp_ptr32_nullM, Gfun(Internal f_cmp_ptr32_nullM)) ::
 (_get_dst, Gfun(Internal f_get_dst)) ::
 (_get_src, Gfun(Internal f_get_src)) ::
 (_get_mem_region, Gfun(Internal f_get_mem_region)) ::
 (_jit_call, Gfun(Internal f_jit_call)) ::
 (__bpf_get_call, Gfun(Internal f__bpf_get_call)) ::
 (_exec_function, Gfun(Internal f_exec_function)) ::
 (_get_offset, Gfun(Internal f_get_offset)) ::
 (_get_immediate, Gfun(Internal f_get_immediate)) ::
 (_get_src32, Gfun(Internal f_get_src32)) ::
 (_get_opcode_ins, Gfun(Internal f_get_opcode_ins)) ::
 (_get_opcode_branch, Gfun(Internal f_get_opcode_branch)) ::
 (_get_opcode_mem_ld_reg, Gfun(Internal f_get_opcode_mem_ld_reg)) ::
 (_get_opcode_mem_st_imm, Gfun(Internal f_get_opcode_mem_st_imm)) ::
 (_get_opcode_mem_st_reg, Gfun(Internal f_get_opcode_mem_st_reg)) ::
 (_get_opcode_nat, Gfun(Internal f_get_opcode_nat)) ::
 (_get_add, Gfun(Internal f_get_add)) ::
 (_get_sub, Gfun(Internal f_get_sub)) ::
 (_get_addr_ofs, Gfun(Internal f_get_addr_ofs)) ::
 (_get_start_addr, Gfun(Internal f_get_start_addr)) ::
 (_get_block_size, Gfun(Internal f_get_block_size)) ::
 (_get_block_perm, Gfun(Internal f_get_block_perm)) ::
 (_check_mem_aux2, Gfun(Internal f_check_mem_aux2)) ::
 (_check_mem_aux, Gfun(Internal f_check_mem_aux)) ::
 (_check_mem, Gfun(Internal f_check_mem)) ::
 (_step_opcode_branch, Gfun(Internal f_step_opcode_branch)) ::
 (_step_opcode_mem_ld_reg, Gfun(Internal f_step_opcode_mem_ld_reg)) ::
 (_step_opcode_mem_st_imm, Gfun(Internal f_step_opcode_mem_st_imm)) ::
 (_step_opcode_mem_st_reg, Gfun(Internal f_step_opcode_mem_st_reg)) ::
 (_step, Gfun(Internal f_step)) ::
 (_bpf_interpreter_aux, Gfun(Internal f_bpf_interpreter_aux)) ::
 (_havm_interpreter, Gfun(Internal f_havm_interpreter)) :: nil).

Definition public_idents : list ident :=
(_havm_interpreter :: _check_mem :: __magic_function :: ___builtin_debug ::
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


