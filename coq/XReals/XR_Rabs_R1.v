Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rlt_irrefl.
Require Import XR_Rlt_trans.
Require Import XR_Rlt_0_1.

Local Open Scope R_scope.

Lemma Rabs_R1 : Rabs R1 = R1.
Proof.
  unfold Rabs.
  destruct (Rcase_abs R1) as [ hl | hr ].
  {
    exfalso.
    apply Rlt_irrefl with R0.
    apply Rlt_trans with R1.
    { exact Rlt_0_1. }
    { exact hl. }
  }
  { reflexivity. }
Qed.
