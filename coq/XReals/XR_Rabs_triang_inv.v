Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rminus.
Require Import XR_Rlt_irrefl.
Require Import XR_Rle_trans.
Require Import XR_Rlt_le_trans.
Require Import XR_Ropp_plus_distr.
Require Import XR_Rplus_le_compat_l.
Require Import XR_Ropp_0.
Require Import XR_Ropp_le_cancel.
Require Import XR_Ropp_le_contravar.
Require Import XR_Rplus_le_reg_r.

Local Open Scope R_scope.

Lemma Rabs_triang_inv : forall a b:R, Rabs a - Rabs b <= Rabs (a - b).
Proof.
  intros x y.
  unfold Rabs.
  destruct (Rcase_abs (x-y)) as [ hm | hm ] ;
  destruct (Rcase_abs x) as [ hx | hx ] ;
  destruct (Rcase_abs y) as [ hy | hy ].
  {
    unfold Rminus.
    rewrite Ropp_plus_distr.
    right.
    reflexivity.
  }
  {
    unfold Rminus.
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    apply Rplus_le_compat_l.
    apply Rle_trans with R0.
    {
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      exact hy.
    }
    { exact hy. }
  }
  {
    exfalso.
    apply Rlt_irrefl with y.
    apply Rlt_le_trans with R0.
    { exact hy. }
    {
      apply Rle_trans with x.
      { exact hx. }
      {
        apply Rplus_le_reg_r with (-y).
        rewrite Rplus_opp_r.
        unfold Rminus in hm.
        left.
        exact hm.
      }
    }
  }
  {
    unfold Rminus.
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    apply Rle_trans with R0.
    {
      left.
      unfold Rminus in hm.
      exact hm.
    }
    {
      apply Ropp_le_cancel.
      rewrite Ropp_0.
      rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      unfold Rminus in hm.
      left.
      exact hm.
    }
  }
  {
    unfold Rminus.
    rewrite Ropp_involutive.
    apply Rle_trans with R0.
    {
      apply Ropp_le_cancel.
      rewrite Ropp_0.
      rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      unfold Rminus in hm.
      exact hm.
    }
    {
      unfold Rminus in hm.
      exact hm.
    }
  }
  {
    exfalso.
    apply Rlt_irrefl with x.
    apply Rlt_le_trans with R0.
    { exact hx. }
    {
      apply Rle_trans with y.
      { exact hy. }
      {
        apply Rplus_le_reg_r with (-y).
        rewrite Rplus_opp_r.
        unfold Rminus in hm.
        exact hm.
      }
    }
  }
  {
    unfold Rminus.
    rewrite Ropp_involutive.
    apply Rplus_le_compat_l.
    apply Rle_trans with R0.
    {
      left.
      exact hy.
    }
    {
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      left.
      exact hy.
    }
  }
  {
    right.
    reflexivity.
  }
Qed.

