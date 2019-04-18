Require Export XR_R0.
Require Export XR_Rlt.

Local Open Scope R_scope.

Record negreal : Type := mknegreal {
  neg :> R;
  cond_neg : neg < R0
}.
