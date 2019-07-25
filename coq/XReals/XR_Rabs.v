Require Import XR_R.
Require Import XR_Ropp.
Require Import XR_Rcase_abs.

Local Open Scope R_scope.

Definition Rabs r : R :=
  match Rcase_abs r with
    | left _ => - r
    | right _ => r
  end.
