Require Export XR_R.
Require Export XR_Rplus.
Require Export XR_Rmult.
Local Open Scope R_scope.
Axiom
  Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.
