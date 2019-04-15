Require Import XR_R.
Require Import XR_is_upper_bound.

Definition bound (E:R -> Prop) :=  exists m : R, is_upper_bound E m.
