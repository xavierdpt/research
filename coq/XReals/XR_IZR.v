Require Export ZArith_base.
Require Import XR_R.
Require Import XR_R0.
Require Import XR_Ropp.
Require Import XR_INR.

Local Open Scope R_scope.

Definition IZR (z:Z) : R :=
  match z with
  | Z0 => R0
  | Zpos n => INR (Pos.to_nat n)
  | Zneg n => - INR (Pos.to_nat n)
  end.
Arguments IZR z%Z.
