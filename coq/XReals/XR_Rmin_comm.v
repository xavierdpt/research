Require Import XR_Rmin.
Require Import XR_Rle_dec.
Require Import XR_Rle_antisym.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmin_comm : forall x y:R, Rmin x y = Rmin y x.
Proof.
  intros x y.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hxyl | hxyr ] ;
  destruct (Rle_dec y x) as [ hyxl | hyxr ].
  {
    apply Rle_antisym.
    { exact hxyl. }
    { exact hyxl. }
  }
  { reflexivity. }
  { reflexivity. }
  {
    apply Rle_antisym.
    {
      left.
      apply Rnot_le_lt.
      exact hxyr.
    }
    {
      left.
      apply Rnot_le_lt.
      exact hyxr.
    }
  }
Qed.
