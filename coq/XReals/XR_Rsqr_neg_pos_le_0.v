Require Import XR_Rsqr.
Require Import XR_Ropp_le_cancel.
Require Import XR_Rsqr_incr_0_var.
Require Import XR_Rsqr_neg.

Local Open Scope R_scope.

Lemma Rsqr_neg_pos_le_0 : forall x y:R, Rsqr x <= Rsqr y -> R0 <= y -> - y <= x.
Proof.
  intros x y h hy.
  apply Ropp_le_cancel.
  rewrite Ropp_involutive.
  apply Rsqr_incr_0_var.
  {
    rewrite <- Rsqr_neg.
    exact h.
  }
  { exact hy. }
Qed.
