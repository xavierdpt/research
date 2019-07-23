Require Import XR_Rmin.
Require Import XR_Rlt.
Require Import XR_Rle_dec.
Require Import XR_Rlt_le_trans.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmin_Rgt_l : forall r1 r2 r, r < Rmin r1 r2  -> r < r1 /\ r < r2.
Proof.
  intros x y z.
  intro h.
  unfold Rmin in h.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  {
    split.
    { exact h. }
    {
      apply Rlt_le_trans with x.
      { exact h. }
      { exact hminl. }
    }
  }
  {
    split.
    {
      apply Rlt_trans with y.
      { exact h. }
      {
        apply Rnot_le_lt.
        exact hminr.
      }
    }
    {
      exact h.
    }
  }
Qed.