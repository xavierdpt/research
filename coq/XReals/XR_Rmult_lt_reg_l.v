Require Import XR_R0.
Require Import XR_Rmult_1_l.
Require Import XR_Rmult_assoc.
Require Import XR_Rlt.
Require Import XR_Rinv_l.
Require Import XR_Rmult_lt_compat_l.
Require Import XR_Rmult_le_0_lt_compat.
Require Import XR_Rinv_neq_0_compat.
Require Import XR_Rlt_not_eq.
Require Import XR_Rnot_le_lt.

Local Open Scope R_scope.

Lemma Rmult_lt_reg_l : forall r r1 r2,
  R0 < r ->
  r * r1 < r * r2 ->
  r1 < r2.
Proof.


