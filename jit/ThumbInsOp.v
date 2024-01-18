From compcert Require Import Integers.
From Coq Require Import ZArith.
Open Scope Z_scope.


(**
  This module is used for defining the initial value of each ARM32 instruction.
*)


Definition COND_EQ	:=	Int.repr 0x0.	(* == *)
Definition COND_NE	:=	Int.repr 0x1.	(* != *)
Definition COND_CS	:=	Int.repr 0x2.	(* Unsigned >= *)
Definition COND_CC	:=	Int.repr 0x3.	(* Unsigned < *)
Definition COND_MI	:=	Int.repr 0x4.	(* < 0 *)
Definition COND_PL	:=	Int.repr 0x5.	(* >= 0 *)
Definition COND_VS	:=	Int.repr 0x6.	(* Signed Overflow *)
Definition COND_VC	:=	Int.repr 0x7.	(* No Signed Overflow *)
Definition COND_HI	:=	Int.repr 0x8.	(* Unsigned > *)
Definition COND_LS	:=	Int.repr 0x9.	(* Unsigned <= *)
Definition COND_GE	:=	Int.repr 0xa.	(* Signed >= *)
Definition COND_LT	:=	Int.repr 0xb.	(* Signed < *)
Definition COND_GT	:=	Int.repr 0xc.	(* Signed > *)
Definition COND_LE	:=	Int.repr 0xd.	(* Signed <= *)
Definition COND_AL	:=	Int.repr 0xe.	(* All *)


(** NB: the following declared instrutions is the final selected THUMB/THUMB2 ISA while our deocde supports more instructions *)

(**r - encoding T1
NOP
 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------
|1 0 1 1|1 1 1 1|0 0 0 0|0 0 0 0|
 -------------------------------- *)

Definition NOP_OP: int := Int.repr 0xbf00.

(** * ALU *)

(**r - encoding T2
ADD Rdn, Rm (Rdn = D:Rdn)
 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------
|0 1 0 0 0 1|0 0|D|  Rm   |Rdn  |
 -------------------------------- *)
Definition ADD_R_OP: int := Int.repr 0x4400.

(** - encoding T3
ADD Rd, Rn, #imm12 (= i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|0|1 0 0 0|S|  Rn   |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition ADD_I_OP: int := Int.repr 0xf100.

(**r - encoding T2
AND Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 0 1|0 1|0 0 0 0|S|  Rn   |   |0|0 0 0|  Rd   |0 0|typ|  Rm   |
 --------------------------------    -------------------------------- *)
Definition AND_R_OP: int := Int.repr 0xea00.

(**r - encoding T1
AND Rd, Rn, #imm12 (= i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|0|0 0 0 0|S|  Rn   |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition AND_I_OP: int := Int.repr 0xf000.

(**r - encoding T2
ASR Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 1|0 1 0|0|1 0|S|  Rn   |   |1 1 1 1|  Rd   |0|0 0 0|  Rm   |
 --------------------------------    -------------------------------- *)
Definition ASR_R_OP: int := Int.repr 0xfa40.


(**r - encoding T2
CMP Rn, Rm (Rn = N:Rn)
 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------
|0 1 0 0 0 1|0 1|N|   Rm  |  Rn |
 -------------------------------- *)
Definition CMP_R_OP: int := Int.repr 0x4500.

(**r - encoding T2
CMP Rn, #imm12 (= i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|0|1 1 0 1|1|  Rn   |   |0| imm3|1 1 1 1|  imm8         |
 --------------------------------    -------------------------------- *)
Definition CMP_I_OP: int := Int.repr 0xf1b0.


(**r - encoding T2
EOR Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 0 1|0 1|0 1 0 0|S|  Rn   |   |0|0 0 0|  Rd   |0 0|typ|  Rm   |
 --------------------------------    -------------------------------- *)
Definition EOR_R_OP: int := Int.repr 0xea80.

(**r - encoding T1
EOR Rd, Rn, #imm12 (= i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|0|0 1 0 0|S|  Rn   |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition EOR_I_OP: int := Int.repr 0xf080.

(**r - encoding T2
LSL Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 1|0 1 0|0|0 0|S|  Rn   |   |1 1 1 1|  Rd   |0|0 0 0|  Rm   |
 --------------------------------    -------------------------------- *)
Definition LSL_R_OP: int := Int.repr 0xfa00.

(**r - encoding T2
LSR Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 1|0 1 0|0|0 1|S|  Rn   |   |1 1 1 1|  Rd   |0|0 0 0|  Rm   |
 --------------------------------    -------------------------------- *)
Definition LSR_R_OP: int := Int.repr 0xfa20.

(**r - encoding T3
MOVW Rd, #imm16 (= imm4:i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|1 0|0|1|0 0| imm4  |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition MOVW_OP: int := Int.repr 0xf240.

(**r - encoding T1
MOVT Rd, #imm16 (= imm4:i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|1 0|1|1|0|0| imm4  |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition MOVT_OP: int := Int.repr 0xf2c0.


(**r - encoding T1
MOV Rd, Rm (Rd = D:Rd)
 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------
|0 1 0 0 0 1|1 0|D|  Rm   | Rd  |
 -------------------------------- *)
Definition MOV_R_OP: int := Int.repr 0x4600.

(**r - encoding T2
MUL Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 1|0 1 1 0|0 0 0|  Rn   |   |1 1 1 1|  Rd   |0 0 0 0|  Rm   |
 --------------------------------    -------------------------------- *)
Definition MUL_OP: int := Int.repr 0xfb00.

(**r - encoding T2
ORR Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 0 1|0 1|0 0 1 0|S|  Rn   |   |0|0 0 0|  Rd   |0 0|typ|  Rm   |
 --------------------------------    -------------------------------- *)
Definition ORR_R_OP: int := Int.repr 0xea40.

(**r - encoding T1
ORR Rd, Rn, #imm12 (= i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|0|0 0 1 0|S|  Rn   |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition ORR_I_OP: int := Int.repr 0xf040.

(**r - encoding T2
SUB Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 0 1|0 1|1 1 0 1|S|  Rn   |   |0|0 0 0|  Rd   |0 0|typ|  Rm   |
 --------------------------------    -------------------------------- *)
Definition SUB_R_OP: int := Int.repr 0xeba0.

(**r - encoding T3
SUB Rd, Rn, #imm12 (= i:imm3:imm8)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|0|1 1 0 1|S|  Rn   |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition SUB_I_OP: int := Int.repr 0xf1a0.

(**r - encoding T2
RSB Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 0 1|0 1|1 1 1 0|S|  Rn   |   |0|0 0 0|  Rd   |0 0|typ|  Rm   |
 --------------------------------    -------------------------------- *)
Definition RSB_R_OP: int := Int.repr 0xebc0.

(**r - encoding T2
RSB Rd, Rn, #0

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|i|0|1 1 1 0|S|  Rn   |   |0| imm3|  Rd   |  imm8         |
 --------------------------------    -------------------------------- *)
Definition RSB_I_OP: int := Int.repr 0xf1c0.

(**r - encoding T1
UDIV Rd, Rn, Rm

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 1|0 1 1 1 0 1|1|  Rn   |   |1 1 1 1|   Rd  |1 1 1 1|  Rm   |
 --------------------------------    -------------------------------- *)
Definition UDIV_LO_OP: int := Int.repr 0xfbb0.
Definition UDIV_HI_OP: int := Int.repr 0xf0f0.


(** * Branch *)

(**r - encoding T1
BX Rm
 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------
|0 1 0 0 0 1|1 1|0|   Rm  |0 0 0|
 -------------------------------- *)
Definition BX_OP: int := Int.repr 0x4700.

(**r a special value to tell the JIT compiler the current binary should add a offset that jumps to the reset stage, because this value means there is an exception we capture! *)
(**r - encoding T1
B label ( = imm8:'0' )
 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------
|1 1 0 1|  cond |     imm8      |
 -------------------------------- *) (*
Definition B_OP := Int.repr 0xd000. *)

(**r - encoding T3
B #imm32 (= S:J2:J1:imm6:imm11)

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 0|S|  cond |   imm6    |   |1 0|J10J2|       imm11         |
 --------------------------------    -------------------------------- *)
Definition B_OP_LOW := Int.repr 0xf000.
Definition B_OP_HI  := Int.repr 0x8000.

Definition BNE_0  := Int.repr 0xf040.
Definition BGE_0  := Int.repr 0xf280.
Definition BLT_0  := Int.repr 0xf2c0.


(** * MEMORY *)

(**r - encoding T3
LDR Rt, Rn, #imm12

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 1|0 0|0|1|1 0|1|  Rn   |   |   Rt  |         imm12         |
 --------------------------------    -------------------------------- *)
Definition LDR_I_OP: int := Int.repr 0xf8d0.

(**r - encoding T3
STR Rt, Rn, #imm12

 1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0     1 1 1 1 1 1 0 0 0 0 0 0 0 0 0 0
 5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0     5 4 3 2 1 0 9 8 7 6 5 4 3 2 1 0
 --------------------------------    --------------------------------
|1 1 1 1 1|0 0|0|1|1 0|0|  Rn   |   |   Rt  |         imm12         |
 --------------------------------    -------------------------------- *)
Definition STR_I_OP: int := Int.repr 0xf8c0.

Close Scope Z_scope.
