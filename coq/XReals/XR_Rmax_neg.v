Require Import XR_R.
Require Import XR_R0.
Require Import XR_Rlt.
Require Import XR_Rmax.
Require Import XR_Rmax_Rlt.

Local Open Scope R_scope.

Lemma Rmax_neg : forall x y:R, x < R0 -> y < R0 -> Rmax x y < R0.
Proof.
  intros x y hx hy.
  apply Rmax_Rlt.
  split.
  { exact hx. }
  { exact hy. }
Qed.
