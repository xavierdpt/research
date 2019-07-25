Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_antisym.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmax_right : forall x y, x <= y -> Rmax x y = y.
Proof.
  intros x y h.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hl | hr ].
  { reflexivity. }
  {
    apply Rle_antisym.
    { exact h. }
    {
      left.
      apply Rnot_le_lt.
      exact hr.
    }
  }
Qed.
