Require Import XR_R0.
Require Import XR_R2.
Require Import XR_R4.
Require Import XR_Rlt_irrefl.
Require Import XR_Rplus.
Require Import XR_Rplus_0_r.
Require Import XR_Rplus_lt_compat.
Require Import XR_Rlt_R0_R2.

Local Open Scope R_scope.

Lemma R4_neq_R0 : R4 <> R0.
Proof.
  intro h.
  apply Rlt_irrefl with R0.
  pattern R0 at 2 ; rewrite <- h.
  unfold R4.
  pattern R0 ; rewrite <- Rplus_0_r.
  apply Rplus_lt_compat.
  { exact Rlt_R0_R2. }
  { exact Rlt_R0_R2. }
Qed.
