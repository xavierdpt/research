Require Export XR_R.
Require Export XR_Rlt.
Local Open Scope R_scope.
Axiom Rlt_trans : forall r1 r2 r3:R, r1 < r2 -> r2 < r3 -> r1 < r3.
