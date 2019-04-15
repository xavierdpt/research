Require Export XR_R.
Require Export XR_Rinv.
Require Export XR_Rmult.
Local Open Scope R_scope.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.
Infix "/" := Rdiv   : R_scope.
