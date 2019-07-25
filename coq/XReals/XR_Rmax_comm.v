Require Import XR_Rle_dec.
Require Import XR_Rmax.
Require Import XR_Rle_antisym.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmax_comm : forall x y:R, Rmax x y = Rmax y x.
Proof.
  intros x y.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hxyl | hxyr ] ;
  destruct (Rle_dec y x) as [ hyxl | hyxr ].
  {
    apply Rle_antisym.
    { exact hyxl. }
    { exact hxyl. }
  }
  { reflexivity. }
  { reflexivity. }
  {
    apply Rle_antisym.
    {
      left.
      apply Rnot_le_lt.
      exact hyxr.
    }
    {
      left.
      apply Rnot_le_lt.
      exact hxyr.
    }
  }
Qed.