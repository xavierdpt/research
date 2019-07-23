Require Import XR_Rmin.
Require Import XR_Rle_dec.
Require Import XR_Rnot_lt_le.

Local Open Scope R_scope.

Lemma Rmin_l : forall x y:R, Rmin x y <= x.
Proof.
  intros x y.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  {
    right.
    reflexivity.
  }
  {
    apply Rnot_lt_le.
    intro h.
    apply hminr.
    left.
    exact h.
  }
Qed.