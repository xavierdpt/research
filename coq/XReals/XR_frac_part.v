Require Export XR_Rminus.
Require Export XR_IZR.
Require Export XR_Int_part.

Local Open Scope R_scope.

Definition frac_part r : R := r - IZR (Int_part r).
