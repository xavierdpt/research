Require Import XR_R.
Require Import XR_R0.
Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rmult.
Require Import XR_Rlt_irrefl.
Require Import XR_Rlt_trans.
Require Import XR_Ropp_involutive.
Require Import XR_Ropp_mult_distr_l.
Require Import XR_Ropp_mult_distr_r.
Require Import XR_Rmult_lt_0_compat.
Require Import XR_Ropp_0.
Require Import XR_Ropp_lt_contravar.
Require Import XR_Rle_lt_trans.
Require Import XR_Ropp_lt_cancel.

Local Open Scope R_scope.

Lemma Rabs_mult : forall x y:R, Rabs (x * y) = Rabs x * Rabs y.
Proof.
  intros x y.
  unfold Rabs.
  destruct (Rcase_abs (x*y)) as [ hp | hp ] ;
  destruct (Rcase_abs x) as [ hx | hx ] ;
  destruct (Rcase_abs y) as [ hy | hy ].
  {
    exfalso.
    apply Rlt_irrefl with R0.
    eapply Rlt_trans.
    2:exact hp.
    rewrite <- Ropp_involutive with (x*y).
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    apply Rmult_lt_0_compat.
    {
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact hx.
    }
    {
    rewrite <- Ropp_0.
    apply Ropp_lt_contravar.
    exact hy.
    }
  }
  {
    rewrite Ropp_mult_distr_l.
    reflexivity.
  }
  {
    rewrite Ropp_mult_distr_r.
    reflexivity.
  }
  {
    destruct hx as [ hx | hx ].
    {
      destruct hy as [ hy | hy ].
      {
        exfalso.
        apply Rlt_irrefl with R0.
        eapply Rlt_trans.
        2:exact hp.
        apply Rmult_lt_0_compat.
        { exact hx. }
        { exact hy. }
      }
      {
        subst y.
        rewrite Rmult_0_r.
        rewrite Ropp_0.
        reflexivity.
      }
    }
    {
      subst x.
      rewrite Rmult_0_l.
      rewrite Ropp_0.
      reflexivity.
    }
  }
  {
    rewrite <- Ropp_mult_distr_l.
    rewrite <- Ropp_mult_distr_r.
    rewrite Ropp_involutive.
    reflexivity.
  }
  {
    destruct hy as [ hy | hy ].
    {
      exfalso.
      apply Rlt_irrefl with R0.
      eapply Rle_lt_trans.
      { exact hp. }
      {
        apply Ropp_lt_cancel.
        rewrite Ropp_0.
        rewrite Ropp_mult_distr_l.
        apply Rmult_lt_0_compat.
        {
          rewrite <- Ropp_0.
          apply Ropp_lt_contravar.
          exact hx.
        }
        { exact hy. }
      }
    }
    {
      subst y.
      repeat rewrite Rmult_0_r.
      reflexivity.
    }
  }
  {
    destruct hx.
    {
      exfalso.
      apply Rlt_irrefl with R0.
      eapply Rle_lt_trans.
      { exact hp. }
      {
        apply Ropp_lt_cancel.
        rewrite Ropp_0.
        rewrite Ropp_mult_distr_r.
        {
          apply Rmult_lt_0_compat.
          { exact H. }
          {
            rewrite <- Ropp_0.
            apply Ropp_lt_contravar.
            exact hy.
          }
        }
      }
    }
    {
      subst x.
      repeat rewrite Rmult_0_l.
      reflexivity.
    }
  }
  { reflexivity. }
Qed.