Require Import XR_Rlt_irrefl.
Require Import XR_Rlt_le_trans.
Require Import XR_Rsqr.
Require Import XR_Rtotal_order.
Require Import XR_Rmult_le_0_lt_compat.

Local Open Scope R_scope.

Lemma Rsqr_incr_0_var : forall x y:R, Rsqr x <= Rsqr y -> R0 <= y -> x <= y.
Proof.
  intros x y h hy.
  destruct (Rtotal_order x y) as [ hx | [ hx | hx ] ].
  {
    left.
    exact hx.
  }
  {
    right.
    exact hx.
  }
  {
    exfalso.
    apply Rlt_irrefl with (Rsqr y).
    apply Rlt_le_trans with (Rsqr x).
    {
      unfold Rsqr.
      apply Rmult_le_0_lt_compat.
      { exact hy. }
      { exact hy. }
      { exact hx. }
      { exact hx. }
    }
    { exact h. }
  }
Qed.
