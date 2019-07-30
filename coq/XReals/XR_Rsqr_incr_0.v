Require Import XR_Rsqr.
Require Import XR_Rtotal_order.
Require Import XR_Rlt_irrefl.
Require Import XR_Rle_lt_trans.
Require Import XR_Rmult_le_0_lt_compat.

Local Open Scope R_scope.

Lemma Rsqr_incr_0 : forall x y:R,
  Rsqr x <= Rsqr y ->
  R0 <= x ->
  R0 <= y ->
  x <= y.
Proof.
  intros x y.
  intros h hx hy.
  destruct (Rtotal_order x y) as [ hto | [ hto | hto ] ].
  {
    left.
    exact hto.
  }
  {
    right.
    exact hto.
  }
  {
    exfalso.
    apply Rlt_irrefl with (Rsqr x).
    apply Rle_lt_trans with (Rsqr y).
    { exact h. }
    {
      unfold Rsqr.
      apply Rmult_le_0_lt_compat.
      { exact hy. }
      { exact hy. }
      { exact hto. }
      { exact hto. }
    }
  }
Qed.
