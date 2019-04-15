Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rlt.
Require Export XR_Rmult.
Local Open Scope R_scope.
Axiom
  Rmult_lt_compat_l : forall r r1 r2:R, R0 < r -> r1 < r2 -> r * r1 < r * r2.
