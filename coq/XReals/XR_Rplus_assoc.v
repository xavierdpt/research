Require Import XR_R.
Require Import XR_Rplus.
Local Open Scope R_scope.
Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
