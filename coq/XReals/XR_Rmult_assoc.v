Require Import XR_R.
Require Import XR_Rmult.
Local Open Scope R_scope.
Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).
