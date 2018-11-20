Require Import XRbase.

Ltac split_Rmult :=
  match goal with
    |  |- ((?X1 * ?X2)%R <> R0) =>
      apply Rmult_integral_contrapositive; split; try split_Rmult
  end.
