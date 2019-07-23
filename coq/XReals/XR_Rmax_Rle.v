Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_trans.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmax_Rle : forall r1 r2 r, r <= Rmax r1 r2 <-> r <= r1 \/ r <= r2.
Proof.
  intros x y z.
  split.
  {
    intro h.
    unfold Rmax in h.
    destruct (Rle_dec x y) as [ hmaxl | hmaxr ].
    {
      right.
      exact h.
    }
    {
      left.
      exact h.
    }
  }
  {
    intro h.
    unfold Rmax.
    destruct (Rle_dec x y) as [ hmaxl | hmaxr ].
    {
      destruct h as [ hx | hy ].
      {
        apply Rle_trans with x.
        { exact hx. }
        { exact hmaxl. }
      }
      { exact hy. }
    }
    {
      destruct h as [ hx | hy ].
      { exact hx. }
      {
        left.
        apply Rnot_le_lt.
        intro h.
        apply hmaxr.
        apply Rle_trans with z.
        { exact h. }
        { exact hy. }
      }
    }
  }
Qed.