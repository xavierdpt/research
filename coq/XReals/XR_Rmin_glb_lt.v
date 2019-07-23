Require Import XR_Rmin.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmin_glb_lt : forall x y z:R, z < x -> z < y -> z < Rmin x y.
Proof.
  intros x y z.
  intros hx hy.
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  { exact hx. }
  { exact hy. }
Qed.
