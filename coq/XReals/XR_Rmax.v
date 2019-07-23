Require Import XR_Rle_dec.

Local Open Scope R_scope.

Definition Rmax (x y:R) : R :=
  match Rle_dec x y with
    | left _ => y
    | right _ => x
  end.
