Require Export XR_Rminus.
Require Export XR_Rplus_opp_r.

Local Open Scope R_scope.

Lemma Rminus_not_eq_right : forall r1 r2, r2 - r1 <> R0 -> r1 <> r2.
Proof.
  intros x y.
  intro hneq.
  unfold not.
  intro heq.
  subst y.
  unfold not in hneq.
  apply hneq.
  unfold Rminus.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.