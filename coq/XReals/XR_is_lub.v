Require Export XR_R.
Require Export XR_Rle.
Require Export XR_is_upper_bound.

Local Open Scope R_scope.

Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).
