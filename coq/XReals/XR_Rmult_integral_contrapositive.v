Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_integral.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_integral_contrapositive :
  forall r1 r2, r1 <> R0 /\ r2 <> R0 -> r1 * r2 <> R0.
Proof.
  intros x y [ hx hy ].
  assert (mi := Rmult_integral).
  specialize (mi x y).
  unfold not.
  intro heq.
  specialize (mi heq).
  clear heq.
  destruct mi as [ mix | miy ].
  { unfold not in hx. apply hx. exact mix. }
  { unfold not in hy. apply hy. exact miy. }
Qed.
