Require Import XR_R0.
Require Import XR_Rlt.
Require Import XR_Rmin.
Require Import XR_Rmin_Rgt_r.

Local Open Scope R_scope.

Lemma Rmin_pos : forall x y:R, R0 < x -> R0 < y -> R0 < Rmin x y.
Proof.
  intros x y hx hy.
  apply Rmin_Rgt_r.
  split.
  { exact hx. }
  { exact hy. }
Qed.
