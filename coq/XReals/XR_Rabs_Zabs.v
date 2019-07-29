Require Import XR_Rabs.
Require Import XR_Rabs_right.
Require Import XR_Rabs_R0.
Require Import XR_Rabs_Ropp.
Require Import XR_IZR.
Require Import XR_pos_INR.

Local Open Scope R_scope.

Lemma Rabs_Zabs : forall z:Z, Rabs (IZR z) = IZR (Z.abs z).
Proof.
  intros z.
  destruct z as [  | z | z ].
  {
    simpl.
    rewrite Rabs_R0.
    reflexivity.
  }
  {
    simpl.
    rewrite Rabs_right.
    { reflexivity. }
    { apply pos_INR. }
  }
  {
    simpl.
    rewrite Rabs_Ropp.
    rewrite Rabs_right.
    { reflexivity. }
    { apply pos_INR. }
  }
Qed.