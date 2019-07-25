Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_lt_trans.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmax_Rlt : forall x y z, Rmax x y < z <-> x < z /\ y < z.
Proof.
  intros x y z.
  split.
  {
    intro h.
    unfold Rmax in h.
    destruct (Rle_dec x y) as [ hl | hr ].
    {
      split.
      {
        apply Rle_lt_trans with y.
        { exact hl. }
        { exact h. }
      }
      { exact h. }
    }
    {
      split.
      { exact h. }
      {
        apply Rle_lt_trans with x.
        {
          left.
          apply Rnot_le_lt.
          exact hr.
        }
        { exact h. }
      }
    }
  }
  {
    intros [ hx hy ].
    unfold Rmax.
    destruct (Rle_dec x y) as [ hl | hr ].
    { exact hy. }
    { exact hx. }
  }
Qed.
