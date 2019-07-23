Require Import XR_Rle_dec.
Require Import XR_Rmin.

Local Open Scope R_scope.

Lemma Rmin_left : forall x y, x <= y -> Rmin x y = x.
Proof.
  intros x y.
  intro h.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  { reflexivity. }
  {
    exfalso.
    apply hminr.
    exact h.
  }
Qed.

