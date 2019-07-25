Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rle_antisym.
Require Import XR_Rle_trans.
Require Import XR_Ropp_0.
Require Import XR_Ropp_le_contravar.

Local Open Scope R_scope.

Lemma Rabs_right : forall r, R0 <= r -> Rabs r = r.
Proof.
  intros x h.
  unfold Rabs.
  destruct (Rcase_abs x) as [ hl | hr ].
  {
    apply Rle_antisym.
    {
      apply Rle_trans with R0.
      {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        exact h.
      }
      { exact h. }
    }
    {
      apply Rle_trans with R0.
      {
        left.
        exact hl.
      }
      {
        rewrite <- Ropp_0.
        apply Ropp_le_contravar.
        left.
        exact hl.
      }
    }
  }
  { reflexivity. }
Qed.
