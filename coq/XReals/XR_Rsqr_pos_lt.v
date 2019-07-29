Require Import XR_R.
Require Import XR_R0.
Require Import XR_Rsqr.
Require Import XR_Rlt.
Require Import XR_Rdichotomy.
Require Import XR_Ropp_involutive.
Require Import XR_Ropp_mult_distr_l.
Require Import XR_Ropp_mult_distr_r.
Require Import XR_Rmult_lt_0_compat.
Require Import XR_Ropp_0.
Require Import XR_Ropp_lt_contravar.

Local Open Scope R_scope.

Lemma Rsqr_pos_lt : forall x:R, x <> R0 -> R0 < Rsqr x.
Proof.
  intros x h.
  unfold Rsqr.
  assert (h' := h).
  apply Rdichotomy in h'.
  destruct h' as [ hl | hr ].
  {
    rewrite <- Ropp_involutive with (x*x).
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    apply Rmult_lt_0_compat.
    {
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact hl.
    }
    {
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact hl.
    }
  }
  {
    apply Rmult_lt_0_compat.
    { exact hr. }
    { exact hr. }
  }
Qed.