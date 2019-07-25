Require Import XR_Rmax.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmax_l : forall x y:R, x <= Rmax x y.
Proof.
  intros x y.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hl | hr ].
  { exact hl. }
  {
    right.
    reflexivity.
  }
Qed.
