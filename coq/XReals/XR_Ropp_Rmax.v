Require Import XR_Rmin.
Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_antisym.
Require Import XR_Ropp_le_contravar.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Ropp_Rmax : forall x y, - Rmax x y = Rmin (-x) (-y).
Proof.
  intros x y.
  unfold Rmax, Rmin.
  destruct (Rle_dec x y) as [ hmax | hmax ] ;
  destruct (Rle_dec (-x) (-y)) as [ hmin | hmin ].
  {
    apply Rle_antisym.
    {
      apply Ropp_le_contravar.
      exact hmax.
    }
    { exact hmin. }
  }
  { reflexivity. }
  { reflexivity. }
  {
    apply Rle_antisym.
    {
      left.
      apply Ropp_lt_contravar.
      apply Rnot_le_lt.
      exact hmax.
    }
    {
      left.
      apply Rnot_le_lt.
      exact hmin.
    }
  }
Qed.
