Require Import XR_Rsqr.
Require Import XR_plus_le_is_le.
Require Import XR_Rle_0_sqr.
Require Import XR_Rsqr_neg_pos_le_0.
Require Import XR_Rsqr_incr_0_var.

Local Open Scope R_scope.

Lemma triangle_rectangle :
  forall x y z:R,
    R0 <= z -> Rsqr x + Rsqr y <= Rsqr z -> - z <= x <= z /\ - z <= y <= z.
Proof.
  intros x y z hz h.

  assert (hxz : Rsqr x <= Rsqr z).
  {
    apply plus_le_is_le with (Rsqr y).
    { apply Rle_0_sqr. }
    { exact h. }
  }

  assert (hyz : Rsqr y <= Rsqr z).
  {
    apply plus_le_is_le with (Rsqr x).
    { apply Rle_0_sqr. }
    {
      rewrite Rplus_comm.
      exact h.
    }
  }

  split.
  {
    split.
    {
      apply Rsqr_neg_pos_le_0.
      { exact hxz. }
      { exact hz. }
    }
    {
      apply Rsqr_incr_0_var.
      { exact hxz. }
      { exact hz. }
    }
  }
  {
    split.
    {
      apply Rsqr_neg_pos_le_0.
      { exact hyz. }
      { exact hz. }
    }
    {
      apply Rsqr_incr_0_var.
      { exact hyz. }
      { exact hz. }
    }
  }
Qed.
