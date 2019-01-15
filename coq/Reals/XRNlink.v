Require Export XRdefinitions.
Local Open Scope XR_scope.

Fixpoint INR (n:nat) : R :=
  match n with
  | O => R0
  | S O => R1
  | S n => INR n + R1
  end.
Arguments INR n%nat.