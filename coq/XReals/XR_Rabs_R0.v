Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Ropp_0.

Local Open Scope R_scope.

Lemma Rabs_R0 : Rabs R0 = R0.

Proof.
  unfold Rabs.
  destruct (Rcase_abs R0) as [ hl | hr ].
  {
    rewrite Ropp_0.
    reflexivity.
  }
  { reflexivity. }
Qed.
