Require Import XR_Rmin.
Require Import XR_Rmin_left.
Require Import XR_Rmin_right.
Require Import XR_Rle_dec.
Require Import XR_Rle_trans.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmin_assoc : forall x y z, Rmin x (Rmin y z) = Rmin (Rmin x y) z.
Proof.
  intros x y z.
  unfold Rmin at 2 4.
  destruct (Rle_dec y z) as [ hyz | hyz ] ;
  destruct (Rle_dec x y) as [ hxy | hxy ].
  {
    repeat rewrite Rmin_left.
    { reflexivity. }
    {
      apply Rle_trans with y.
      { exact hxy. }
      { exact hyz. }
    }
    { exact hxy. }
  }
  {
    apply Rnot_le_lt in hxy.
    rewrite (Rmin_right x y).
    {
      rewrite (Rmin_left y z).
      { reflexivity. }
      { exact hyz. }
    }
    {
      left.
      exact hxy.
    }
  }
  { reflexivity. }
  {
    apply Rnot_le_lt in hyz.
    apply Rnot_le_lt in hxy.
    repeat rewrite Rmin_right.
    { reflexivity. }
    {
      left.
      exact hyz.
    }
    {
      left.
      apply Rlt_trans with y.
      { exact hyz. }
      { exact hxy. }
    }
  }
Qed.