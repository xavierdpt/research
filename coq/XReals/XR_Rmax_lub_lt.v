Require Import XR_Rmax.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmax_lub_lt : forall x y z:R, x < z -> y < z -> Rmax x y < z.
Proof.
  intros x y z.
  intros hx hy.
  unfold Rmax.
  destruct (Rle_dec x y) as [ hl | hr ].
  { exact hy. }
  { exact hx. }
Qed.
