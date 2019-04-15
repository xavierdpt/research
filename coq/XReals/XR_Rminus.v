Require Export XR_R.
Require Export XR_Rplus.
Require Export XR_Ropp.
Local Open Scope R_scope.
Definition Rminus (r1 r2:R) : R := r1 + - r2.
Infix "-" := Rminus : R_scope.
