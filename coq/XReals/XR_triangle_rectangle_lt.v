Require Import XR_Rabs.
Require Import XR_Rsqr.
Require Import XR_Rsqr_lt_abs_0.
Require Import XR_plus_lt_is_lt.
Require Import XR_Rle_0_sqr.

Local Open Scope R_scope.

Lemma triangle_rectangle_lt :
  forall x y z:R,
    Rsqr x + Rsqr y < Rsqr z -> Rabs x < Rabs z /\ Rabs y < Rabs z.
Proof.
  intros x y z.
  intro h.
  split.
  {
    apply Rsqr_lt_abs_0.
    apply plus_lt_is_lt with (Rsqr y).
    { apply Rle_0_sqr. }
    { exact h. }
  }
  {
    apply Rsqr_lt_abs_0.
    apply plus_lt_is_lt with (Rsqr x).
    { apply Rle_0_sqr. }
    {
      rewrite Rplus_comm.
      exact h.
    }
  }
Qed.
