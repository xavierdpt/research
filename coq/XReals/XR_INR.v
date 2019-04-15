Require Import XR_R.
Require Import XR_R0.
Require Import XR_R1.
Require Import XR_Rplus.

Local Open Scope R_scope.

Fixpoint INR (n:nat) : R :=
  match n with
  | O => R0
  | S O => R1
  | S n => INR n + R1
  end.
Arguments INR n%nat.
