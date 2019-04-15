Require Import XR_R.
Require Import XR_Rlt.
Require Import XR_Rplus.
Local Open Scope R_scope.
Axiom Rplus_lt_compat_l : forall r r1 r2:R, r1 < r2 -> r + r1 < r + r2.
