Require Import XR_R.
Require Import XR_Rplus.
Require Import XR_Ropp.
Local Open Scope R_scope.
Definition Rminus (r1 r2:R) : R := r1 + - r2.
Infix "-" := Rminus : R_scope.
