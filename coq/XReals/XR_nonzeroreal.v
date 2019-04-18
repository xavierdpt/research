Require Export XR_R0.

Local Open Scope R_scope.

Record nonzeroreal : Type := mknonzeroreal {
  nonzero :> R;
  cond_nonzero : nonzero <> R0
}.
