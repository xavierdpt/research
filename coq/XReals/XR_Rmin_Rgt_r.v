Require Import XR_Rmin.
Require Import XR_Rlt.
Require Import XR_Rle_dec.

Local Open Scope R_scope.

Lemma Rmin_Rgt_r : forall r1 r2 r, r < r1  /\ r < r2 -> r < Rmin r1 r2 .
Proof.
  intros x y z.
  intros [ hzx hzy ].
  unfold Rmin.
  destruct (Rle_dec x y) as [ hminl | hminr ].
  { exact hzx. }
  { exact hzy. }
Qed.
