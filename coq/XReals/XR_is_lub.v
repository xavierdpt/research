Require Import XR_R.
Require Import XR_Rle.
Require Import XR_is_upper_bound.

Local Open Scope R_scope.

Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).
