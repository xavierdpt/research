Require Import XR_Rmax.
Require Import XR_Rle_dec.
Require Import XR_Rle_antisym.

Local Open Scope R_scope.

Lemma Rmax_left : forall x y, y <= x -> Rmax x y = x.
Proof.
  intros x y h.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hl | hr ].
  {
    apply Rle_antisym.
    { exact h. }
    { exact hl. }
  }
  { reflexivity. }
Qed.