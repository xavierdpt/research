Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Ropp_involutive.
Require Import XR_Rle_antisym.
Require Import XR_Rle_trans.
Require Import XR_Ropp_0.
Require Import XR_Ropp_le_contravar.
Require Import XR_Ropp_le_cancel.

Local Open Scope R_scope.

Lemma Rabs_Ropp : forall x:R, Rabs (- x) = Rabs x.
Proof.
  intro x.
  unfold Rabs.
  destruct (Rcase_abs x) as [ ha | ha ] ;
  destruct (Rcase_abs (-x)) as [ hb | hb ].
  {
    rewrite Ropp_involutive.
    apply Rle_antisym.
    {
      apply Rle_trans with R0.
      {
        left.
        exact ha.
      }
      {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        left.
        exact ha.
      }
    }
    {
      apply Rle_trans with R0.
      {
        left.
        exact hb.
      }
      {
        apply Ropp_le_cancel.
        rewrite Ropp_0.
        left.
        exact hb.
      }
    }
  }
  { reflexivity. }
  {
    rewrite Ropp_involutive.
    reflexivity.
  }
  {
    apply Rle_antisym.
    {
      apply Rle_trans with R0.
      {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        exact ha.
      }
      { exact ha. }
    }
    {
      apply Rle_trans with R0.
      {
        apply Ropp_le_cancel.
        rewrite Ropp_0.
        exact hb.
      }
      { exact hb. }
    }
  }
Qed.