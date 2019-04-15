Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_integral_contrapositive.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_integral_contrapositive_currified :
  forall r1 r2, r1 <> R0 -> r2 <> R0 -> r1 * r2 <> R0.
Proof.
  intros x y.
  intros hx hy.
  apply Rmult_integral_contrapositive.
  split.
  { exact hx. }
  { exact hy. }
Qed.
