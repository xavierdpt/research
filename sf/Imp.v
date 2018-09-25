Require Import Coq.Arith.Arith.
Require Import Maps.

Module ANum.

Inductive aexp : Type :=
ANum : nat -> aexp
.

Inductive bexp : Type :=
BEq : aexp -> aexp -> bexp
.

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n:nat), aevalR (ANum n) n
.

Definition state := total_map nat.

Inductive com : Type :=
| CSkip : com
.

Inductive


End ANum.