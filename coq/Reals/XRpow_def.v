Require Import XRdefinitions.

Fixpoint pow (r:R) (n:nat) : R :=
  match n with
    | O => R1
    | S n => Rmult r (pow r n)
  end.
