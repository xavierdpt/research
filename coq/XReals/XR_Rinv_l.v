Require Export XR_R.
Require Export XR_R0.
Require Export XR_R1.
Require Export XR_Rmult.
Require Export XR_Rinv.
Local Open Scope R_scope.
Axiom Rinv_l : forall r:R, r <> R0 -> / r * r = R1.
