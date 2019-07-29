Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_antisym.
Require Import XR_Rnot_le_lt.
Require Import XR_Rle_trans.

Local Open Scope R_scope.

Lemma Rmax_assoc : forall a b c, Rmax a (Rmax b c) = Rmax (Rmax a b) c.
Proof.
  intros x y z.
  unfold Rmax.
  destruct (Rle_dec y z)  as [ hyz | hyz ] ;
  destruct (Rle_dec x y) as [ hxy | hxy ].
  {
    destruct (Rle_dec x z) as [ hxz | hxz ] ;
    destruct (Rle_dec y z) as [ hyz' | hyz' ].
    { reflexivity. }
    {
      apply Rle_antisym.
      {
        left.
        apply Rnot_le_lt.
        exact hyz'.
      }
      { exact hyz. }
    }
    {
      apply Rle_antisym.
      {
        apply Rle_trans with y.
        { exact hxy. }
        { exact hyz. }
      }
      {
        left.
        apply Rnot_le_lt.
        exact hxz.
      }
    }
    {
      apply Rle_antisym.
      { exact hxy. }
      {
        apply Rle_trans with z.
        { exact hyz. }
        {
          left.
          apply Rnot_le_lt.
          exact hxz.
        }
      }
    }
  }
  { reflexivity. }
  {
    destruct (Rle_dec y z) as [ hyz' | hyz' ].
    {
      apply Rle_antisym.
      { exact hyz'. }
      {
        left.
        apply Rnot_le_lt.
        exact hyz.
      }
    }
    { reflexivity. }
  }
  {
  destruct (Rle_dec x z) as [ hxz | hxz ].
  {
    apply Rle_antisym.
    { exact hxz. }
    {
      apply Rle_trans with y.
      {
        left.
        apply Rnot_le_lt.
        exact hyz.
      }
      {
        left.
        apply Rnot_le_lt.
        exact hxy.
      }
    }
  }
  { reflexivity. }
  }
Qed.

