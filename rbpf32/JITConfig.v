From compcert.lib Require Import Integers.
From compcert.common Require Import AST Values Memory.
From compcert.arm Require Import AsmSyntax.

From bpf.comm Require Import JITCall.
From bpf.rbpf32 Require Import TSSyntax.

From Coq Require Import ZArith Lia List ListSet.

Open Scope Z_scope.
Import ListNotations.

(* Definition callee_save *)
Definition rbpf_arm_callee_save: listset := [R4; R5; R6; R7; R8; R9; R10]. (*
Definition arm_callee_save: list ireg := [IR4; IR5; IR6; IR7; IR8; IR9; IR10; IR11]. *)

(**r st_blk layout:
  [4*i, 4*i+4) <==> Ri,
  [44, 48) <==> PC
  [48, 52) <==> flag * later
 *)

Definition copy_to (rs: regset) (st_blk: block) (m: mem): option mem :=
  match Mem.store Mint32 m st_blk   0   (rs#R0) with
  | None => None
  | Some m0 =>
  match Mem.store Mint32 m0 st_blk  4   (rs#R1) with
  | None => None
  | Some m1 =>
  match Mem.store Mint32 m1 st_blk  8   (rs#R2) with
  | None => None
  | Some m2 =>
  match Mem.store Mint32 m2 st_blk  12  (rs#R3) with
  | None => None
  | Some m3 =>
  match Mem.store Mint32 m3 st_blk  16  (rs#R4) with
  | None => None
  | Some m4 =>
  match Mem.store Mint32 m4 st_blk  20  (rs#R5) with
  | None => None
  | Some m5 =>
  match Mem.store Mint32 m5 st_blk  24  (rs#R6) with
  | None => None
  | Some m6 =>
  match Mem.store Mint32 m6 st_blk  28  (rs#R7) with
  | None => None
  | Some m7 =>
  match Mem.store Mint32 m7 st_blk  32  (rs#R8) with
  | None => None
  | Some m8 =>
  match Mem.store Mint32 m8 st_blk  36  (rs#R9) with
  | None => None
  | Some m9 =>
  match Mem.store Mint32 m9 st_blk  40  (rs#R10) with
  | None => None
  | Some m10 => Mem.store Mint32 m10 st_blk 44 (rs#BPC)
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end.

Definition copy_from (rs: regset) (st_blk: block) (m: mem): option regset :=
  match Mem.load Mint32 m st_blk 0 with
  | None => None
  | Some v0 =>
  match Mem.load Mint32 m st_blk 4 with
  | None => None
  | Some v1 =>
  match Mem.load Mint32 m st_blk 8  with
  | None => None
  | Some v2 =>
  match Mem.load Mint32 m st_blk 12 with
  | None => None
  | Some v3 =>
  match Mem.load Mint32 m st_blk 16 with
  | None => None
  | Some v4 =>
  match Mem.load Mint32 m st_blk 20 with
  | None => None
  | Some v5 =>
  match Mem.load Mint32 m st_blk 24 with
  | None => None
  | Some v6 =>
  match Mem.load Mint32 m st_blk 28 with
  | None => None
  | Some v7 =>
  match Mem.load Mint32 m st_blk 32 with
  | None => None
  | Some v8 =>
  match Mem.load Mint32 m st_blk 36 with
  | None => None
  | Some v9 =>
  match Mem.load Mint32 m st_blk 40 with
  | None => None
  | Some v10 =>
  match Mem.load Mint32 m st_blk 44 with
  | None => None
  | Some vpc =>
    Some (rs
          #R0 <- v0
          #R1 <- v1
          #R2 <- v2
          #R3 <- v3
          #R4 <- v4
          #R5 <- v5
          #R6 <- v6
          #R7 <- v7
          #R8 <- v8
          #R9 <- v9
          #R10 <- v10
          #BPC <- vpc)
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end
  end.