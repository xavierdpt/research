Require Import XR_R.
Require Import XR_Rle.

Local Open Scope R_scope.

Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.
