Require Import XR_R.
Require Import XR_R0.
Require Import XR_R1.
Require Import XR_Rmult.
Require Import XR_Rinv.
Local Open Scope R_scope.
Axiom Rinv_l : forall r:R, r <> R0 -> / r * r = R1.
