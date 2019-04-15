Require Export XR_R.
Require Export XR_R0.
Require Export XR_Rmult.
Require Export XR_Rmult_0_l.
Require Export XR_Rmult_0_r.

Local Open Scope R_scope.
Implicit Type r : R.

Lemma Rmult_neq_0_reg : forall r1 r2, r1 * r2 <> R0 -> r1 <> R0 /\ r2 <> R0.
Proof.
  intros x y.
  intro heq.
  unfold not in heq.
  split.
  {
    unfold not.
    intro heqx.
    subst x.
    apply heq.
    rewrite Rmult_0_l.
    reflexivity.
  }
  {
    unfold not.
    intro heqy.
    subst y.
    apply heq.
    rewrite Rmult_0_r.
    reflexivity.
  }
Qed.
