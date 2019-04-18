Require Export XR_R0.
Require Export XR_Rle.

Local Open Scope R_scope.

Record nonposreal : Type := mknonposreal {
  nonpos :> R;
  cond_nonpos : nonpos <= R0
}.
