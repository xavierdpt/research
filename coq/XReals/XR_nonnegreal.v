Require Export XR_R0.
Require Export XR_Rle.

Local Open Scope R_scope.

Record nonnegreal : Type := mknonnegreal {
  nonneg :> R;
  cond_nonneg : R0 <= nonneg
}.
