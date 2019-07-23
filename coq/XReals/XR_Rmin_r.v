Require Import XR_Rmin.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmin_r : forall x y:R, Rmin x y <= y.
Proof.
  intros x y.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  { exact hminl. }
  {
    right.
    reflexivity.
  }
Qed.
