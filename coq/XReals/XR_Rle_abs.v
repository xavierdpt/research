Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rle.
Require Import XR_Ropp_0.
Require Import XR_Rle_trans.
Require Import XR_Ropp_le_contravar.

Local Open Scope R_scope.

Lemma Rle_abs : forall x:R, x <= Rabs x.
Proof.
  intro x.
  unfold Rabs.
  destruct (Rcase_abs x) as [ h | h].
  {
    apply Rle_trans with R0.
    {
      left.
      exact h.
    }
    {
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      left.
      exact h.
    }
  }
  {
    right.
    reflexivity.
  }
Qed.
