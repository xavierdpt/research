Require Import XR_Rmin.
Require Import XR_Rle_dec.
Require Import XR_Rle_antisym.

Local Open Scope R_scope.

Lemma Rmin_right : forall x y, y <= x -> Rmin x y = y.
Proof.
  intros x y.
  intro h.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  {
    apply Rle_antisym.
    { exact hminl. }
    { exact h. }
  }
  { reflexivity. }
Qed.
