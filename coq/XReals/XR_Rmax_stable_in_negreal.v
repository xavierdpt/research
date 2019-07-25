Require Import XR_Rmax.
Require Import XR_negreal.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmax_stable_in_negreal : forall x y:negreal, Rmax x y < R0.
Proof.
  intros x y.
  destruct x as [ x hx ].
  destruct y as [ y hy ].
  simpl.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hl | hr ].
  { exact hy. }
  { exact hx. }
Qed.
