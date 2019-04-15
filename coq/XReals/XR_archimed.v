Require Export XR_R.
Require Export XR_R1.
Require Export XR_Rlt.
Require Export XR_Rle.
Require Export XR_Rminus.
Require Export XR_up.
Require Export XR_IZR.

Local Open Scope R_scope.

Axiom archimed : forall r:R, r < IZR (up r)  /\ IZR (up r) - r <= R1.
