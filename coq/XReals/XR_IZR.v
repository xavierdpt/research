Require Export ZArith_base.
Require Export XR_R.
Require Export XR_R0.
Require Export XR_Ropp.
Require Export XR_INR.

Local Open Scope R_scope.

Definition IZR (z:Z) : R :=
  match z with
  | Z0 => R0
  | Zpos n => INR (Pos.to_nat n)
  | Zneg n => - INR (Pos.to_nat n)
  end.
Arguments IZR z%Z.
Arguments IZR _ : simpl nomatch.