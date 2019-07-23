Require Import XR_posreal.
Require Import XR_Rmin.
Require Import XR_Rmin_Rgt_r.

Local Open Scope R_scope.

Lemma Rmin_stable_in_posreal : forall x y:posreal, R0 < Rmin x y.
Proof.
  intros x y.
  destruct x as [ x hx ].
  destruct y as [ y hy ].
  simpl.
  apply Rmin_Rgt_r.
  split.
  { exact hx. }
  { exact hy. }
Qed.