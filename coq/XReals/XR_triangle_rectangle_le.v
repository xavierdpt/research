Require Import XR_Rabs.
Require Import XR_Rsqr_le_abs_0.
Require Import XR_plus_le_is_le.
Require Import XR_Rle_0_sqr.

Local Open Scope R_scope.

Lemma triangle_rectangle_le : forall x y z:R,
    Rsqr x + Rsqr y <= Rsqr z -> Rabs x <= Rabs z /\ Rabs y <= Rabs z.
Proof.
  intros x y z h.
  split.
  {
    apply Rsqr_le_abs_0.
    apply plus_le_is_le with (Rsqr y).
    { apply Rle_0_sqr. }
    { exact h. }
    }
  {
    apply Rsqr_le_abs_0.
    apply plus_le_is_le with (Rsqr x).
    { apply Rle_0_sqr. }
    {
      rewrite Rplus_comm.
      exact h.
    }
  }
Qed.
