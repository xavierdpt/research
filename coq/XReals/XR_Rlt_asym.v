Require Export XR_R.
Require Export XR_Rlt.
Local Open Scope R_scope.
Axiom Rlt_asym : forall r1 r2:R, r1 < r2 -> ~ r2 < r1.
