Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmax_r : forall x y:R, y <= Rmax x y.
Proof.
  intros x y.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hl | hr ].
  {
    right.
    reflexivity.
  }
  {
    left.
    apply Rnot_le_lt.
    exact hr.
  }
Qed.
