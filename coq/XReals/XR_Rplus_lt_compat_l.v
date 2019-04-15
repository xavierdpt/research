Require Export XR_R.
Require Export XR_Rlt.
Require Export XR_Rplus.
Local Open Scope R_scope.
Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
