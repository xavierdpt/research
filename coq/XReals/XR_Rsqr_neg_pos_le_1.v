Require Import XR_Rsqr.
Require Import XR_Ropp_0.
Require Import XR_Rle_or_lt.
Require Import XR_Rsqr_incr_1.
Require Import XR_Rsqr_neg.
Require Import XR_Ropp_le_cancel.

Local Open Scope R_scope.

Lemma Rsqr_neg_pos_le_1 :
  forall x y:R, - y <= x -> x <= y -> R0 <= y -> Rsqr x <= Rsqr y.
Proof.
  intros x y.
  intros hyx hxy hy.
  destruct (Rle_or_lt R0 x) as [ hx | hx ].
  {
    apply Rsqr_incr_1.
    { exact hxy. }
    { exact hx. }
  }
  {
    rewrite (Rsqr_neg x).
    apply Rsqr_incr_1.
    {
      apply Ropp_le_cancel.
      rewrite Ropp_involutive.
      exact hyx.
    }
    {
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      left.
      exact hx.
    }
  }
Qed.
