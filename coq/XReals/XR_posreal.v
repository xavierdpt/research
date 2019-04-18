Require Export XR_R0.
Require Export XR_Rlt.

Local Open Scope R_scope.

Record posreal : Type := mkposreal {
  pos :> R;
  cond_pos : R0 < pos
}.
