Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Ropp_0.
Require Import XR_Ropp_le_contravar.
Require Import XR_Ropp_lt_cancel.
Require Import XR_Rlt_le_trans.

Local Open Scope R_scope.

Lemma Rabs_def2 : forall x a:R, Rabs x < a -> x < a /\ - a < x.
Proof.
  intros x y h.
  unfold Rabs in h.
  destruct (Rcase_abs x) as [ hx | hx ].
  {
    split.
    {
      apply Rlt_trans with R0.
      { exact hx. }
      {
        apply Rlt_trans with (-x).
        {
          rewrite <- Ropp_0.
          apply Ropp_lt_contravar.
          exact hx.
        }
        { exact h. }
      }
    }
    {
      apply Ropp_lt_cancel.
      rewrite Ropp_involutive.
      exact h.
    }
  }
  {
    split.
    { exact h. }
    {
      apply Rlt_le_trans with R0.
      {
        apply Rlt_le_trans with (-x).
        {
          apply Ropp_lt_contravar.
          exact h.
        }
        {
          rewrite <- Ropp_0.
          apply Ropp_le_contravar.
          exact hx.
        }
      }
      { exact hx. }
    }
  }
Qed.