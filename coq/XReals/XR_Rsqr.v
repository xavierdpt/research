Require Export XR_R.
Require Export XR_Rmult.

Local Open Scope R_scope.
Implicit Type r : R.

Definition Rsqr r : R := r * r.

Notation "r ²" := (Rsqr r) (at level 1, format "r ²") : R_scope.
