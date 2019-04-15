Require Import XR_R.
Require Import XR_Rlt.
Local Open Scope R_scope.
Axiom total_order_T : forall r1 r2:R, {r1 < r2} + {r1 = r2} + {r2 < r1}.
