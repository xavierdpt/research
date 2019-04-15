Require Import XR_R.
Require Import XR_Rinv.
Require Import XR_Rmult.
Local Open Scope R_scope.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.
Infix "/" := Rdiv   : R_scope.
