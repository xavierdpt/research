Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Ropp_plus_distr.
Require Import XR_Rplus_le_compat.
Require Import XR_Ropp_0.
Require Import XR_Ropp_le_contravar.

Local Open Scope R_scope.

Lemma Rabs_triang : forall a b:R, Rabs (a + b) <= Rabs a + Rabs b.
Proof.
  intros x y.
  unfold Rabs.
  destruct (Rcase_abs (x+y)) as [ hp | hp ] ;
  destruct (Rcase_abs x) as [ hx | hx ] ;
  destruct (Rcase_abs y) as [ hy | hy ].
  {
    rewrite Ropp_plus_distr.
    right.
    reflexivity.
  }
  {
    rewrite Ropp_plus_distr.
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
    rewrite Ropp_plus_distr.
    apply Rplus_le_compat_r.
    apply Rle_trans with R0.
    {
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      exact hx.
    }
    { exact hx. }
  }
  {
    rewrite Ropp_plus_distr.
    apply Rplus_le_compat.
    {
      apply Rle_trans with R0.
      {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        exact hx.
      }
      { exact hx. }
    }
    {
      apply Rle_trans with R0.
      {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        exact hy.
      }
      { exact hy. }
    }
  }
  {
    apply Rplus_le_compat.
    {
      apply Rle_trans with R0.
      {
        left.
        exact hx.
      }
      {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        left.
        exact hx.
      }
    }
    {
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
  }
  {
    apply Rplus_le_compat_r.
    apply Rle_trans with R0.
    {
      left.
      exact hx.
    }
    {
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      left.
      exact hx.
    }
  }
  {
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
