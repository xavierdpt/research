Require Export ZArith_base.

Parameter R : Set.

Delimit Scope XR_scope with R.
Bind Scope XR_scope with R.
Local Open Scope XR_scope.

Parameter R0 : R.
Parameter R1 : R.
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.
Parameter Rlt : R -> R -> Prop.
Parameter up : R -> Z.

Infix "+" := Rplus : XR_scope.
Infix "*" := Rmult : XR_scope.
Notation "- x" := (Ropp x) : XR_scope.
Notation "/ x" := (Rinv x) : XR_scope.

Infix "<" := Rlt : XR_scope.

Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
Definition Rminus (r1 r2:R) : R := r1 + - r2.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.

Infix "-" := Rminus : XR_scope.
Infix "/" := Rdiv   : XR_scope.

Infix "<=" := Rle : XR_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : XR_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : XR_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : XR_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : XR_scope.
