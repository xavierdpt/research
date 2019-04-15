Require Import XR_R.
Require Import XR_R1.
Require Import XR_Rlt.
Require Import XR_Rle.
Require Import XR_Rminus.
Require Import XR_up.
Require Import XR_IZR.

Local Open Scope R_scope.

Axiom archimed : forall r:R, r < IZR (up r)  /\ IZR (up r) - r <= R1.
