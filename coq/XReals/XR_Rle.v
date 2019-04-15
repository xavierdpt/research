Require Export XR_R.
Require Export XR_Rlt.
Local Open Scope R_scope.
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
Infix "<=" := Rle : R_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z) : R_scope.
Notation "x <= y < z"  := (x <= y /\ y <  z) : R_scope.
Notation "x < y < z"   := (x <  y /\ y <  z) : R_scope.
Notation "x < y <= z"  := (x <  y /\ y <= z) : R_scope.
