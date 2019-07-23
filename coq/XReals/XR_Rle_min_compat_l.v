Require Import XR_Rmin.
Require Import XR_Rle_dec.
Require Import XR_Rle_trans.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rle_min_compat_l : forall x y z, x <= y -> Rmin z x <= Rmin z y.
Proof.
  intros x y z.
  intro h.
  unfold Rmin.
  destruct (Rle_dec z x) as [ hminxl | hminxr ] ;
  destruct (Rle_dec z y) as [ hminyl | hminyr ].
  {
    right.
    reflexivity.
  }
  {
    apply Rle_trans with x.
    { exact hminxl. }
    { exact h. }
  }
  {
    left.
    apply Rnot_le_lt.
    exact hminxr.
  }
  { exact h. }
Qed.