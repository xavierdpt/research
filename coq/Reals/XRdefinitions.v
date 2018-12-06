Declare ML Module "r_syntax_plugin".
Require Export ZArith_base.

Parameter R : Set.

Delimit Scope XR_scope with R.
Bind Scope XR_scope with R.
Local Open Scope XR_scope.

Parameter R0 : R.
Parameter R1 : R.
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.
Parameter Rlt : R -> R -> Prop.
Parameter up : R -> Z.

Infix "+" := Rplus : XR_scope.
Infix "*" := Rmult : XR_scope.
Notation "- x" := (Ropp x) : XR_scope.
Notation "/ x" := (Rinv x) : XR_scope.

Infix "<" := Rlt : XR_scope.

Definition R2 := R1 + R1.
Definition R3 := R2 + R1.
Definition R4 := R2 + R2.
Definition R5 := R3 + R2.
Definition R6 := R3 + R3.
Definition R7 := R4 + R3.
Definition R8 := R4 + R4.
Definition R9 := R3 + R3 + R3.
Definition R10 := R5 + R5.
Definition R12 := R6 + R6.
Definition R14 := R7 + R7.
Definition R16 := R8 + R8.
Definition R18 := R9 + R9.
Definition R20 := R10 + R10.

(* Definition Rgt (r1 r2:R) : Prop := r2 < r1. *)
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
(* Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2. *)
Definition Rminus (r1 r2:R) : R := r1 + - r2.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.

Infix "-" := Rminus : XR_scope.
Infix "/" := Rdiv   : XR_scope.

Infix "<=" := Rle : XR_scope.
(* Infix ">=" := Rge : XR_scope.
Infix ">"  := Rgt : XR_scope. *)

Notation "x <= y <= z" := (x <= y /\ y <= z) : XR_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : XR_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : XR_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : XR_scope.

Fixpoint IPR_2 (p:positive) : R :=
  match p with
  | xH => R1 + R1
  | xO p => (R1 + R1) * IPR_2 p
  | xI p => (R1 + R1) * (R1 + IPR_2 p)
  end.

Definition IPR (p:positive) : R :=
  match p with
  | xH => R1
  | xO p => IPR_2 p
  | xI p => R1 + IPR_2 p
  end.
Arguments IPR p%positive : simpl never.

Definition IZR (z:Z) : R :=
  match z with
  | Z0 => R0
  | Zpos n => IPR n
  | Zneg n => - IPR n
  end.
Arguments IZR z%Z : simpl never.
