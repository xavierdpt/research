Require Import XR_Rle_dec.

Local Open Scope R_scope.

Definition Rmin (x y:R) : R :=
  match Rle_dec x y with
    | left _ => x
    | right _ => y
  end.
