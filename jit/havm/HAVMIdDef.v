From compcert.common Require AST.
From dx Require Import IRtoC.
From Coq Require Import ZArith String.
Import UserIdentNotations.
Open Scope string.

Definition havm_state_id: AST.ident := $"havm_state".
Definition pc_loc_id:     AST.ident := $"pc_loc".
Definition regs_st_id:    AST.ident := $"regs_st".
Definition flag_id:       AST.ident := $"flag".
Definition mrs_num_id:    AST.ident := $"mrs_num".
Definition bpf_mrs_id:    AST.ident := $"bpf_mrs".
Definition mem_region_id: AST.ident := $"memory_region".
Definition input_len_id:  AST.ident := $"input_len".
Definition input_ins_id:  AST.ident := $"input_ins".
Definition tp_kv_id:      AST.ident := $"tp_kv".
Definition tp_bin_len_id: AST.ident := $"tp_bin_len".
Definition tp_bin_id:     AST.ident := $"tp_bin".
Definition start_addr_id: AST.ident := $"start_addr".
Definition size_id:       AST.ident := $"block_size".
Definition perm_id:       AST.ident := $"block_perm".
Definition block_ptr_id:  AST.ident := $"block_ptr".
Definition mem_regions_id:AST.ident := $"memory_regions".
Definition bpf_ctx_id:    AST.ident := $"bpf_ctx".
Definition bpf_stk_id:    AST.ident := $"bpf_stk".
Definition content_id:    AST.ident := $"content".
Close Scope string.