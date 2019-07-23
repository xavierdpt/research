Require Import XR_Rmin.
Require Import XR_Rle_dec.
Require Import XR_Rle_trans.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rle_min_compat_r : forall x y z, x <= y -> Rmin x z <= Rmin y z.
Proof.
  intros x y z.
  intro h.
  unfold Rmin.
  destruct (Rle_dec x z) as [ hminxl | hminxr ] ;
  destruct (Rle_dec y z) as [ hminyl | hminyr ].
  { exact h. }
  { exact hminxl. }
  {
    apply Rle_trans with x.
    {
      left.
      apply Rnot_le_lt.
      exact hminxr.
    }
    { exact h. }
  }
  {
    right.
    reflexivity.
  }
Qed.
