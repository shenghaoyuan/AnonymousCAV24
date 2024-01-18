From compcert.common Require AST.
From dx Require Import IRtoC.
From Coq Require Import ZArith String.
Import UserIdentNotations.
Open Scope string.

Definition arm_ofs_id:          AST.ident := $"arm_ofs".
Definition alu32_ofs_id:        AST.ident := $"alu32_ofs".
Definition key_value2_id:       AST.ident := $"key_value2".

Definition ld_set_id:           AST.ident := $"ld_set".
Definition st_set_id:           AST.ident := $"st_set".
Definition jit_state_id:        AST.ident := $"jit_state".
Close Scope string.