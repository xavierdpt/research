Require Export XR_R.
Require Export XR_R0.
Require Export XR_R1.
Require Export XR_Rplus.

Local Open Scope R_scope.

Fixpoint INR (n:nat) : R :=
  match n with
  | O => R0
  | S O => R1
  | S n => INR n + R1
  end.
Arguments INR n%nat.
