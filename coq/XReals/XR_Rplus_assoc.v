Require Export XR_R.
Require Export XR_Rplus.
Local Open Scope R_scope.
Axiom Rplus_assoc : forall r1 r2 r3:R, r1 + r2 + r3 = r1 + (r2 + r3).
