Require Export XR_IZR.
Require Export XR_minus_INR.
Require Export XR_Ropp_involutive.

Local Open Scope R_scope.

Lemma plus_IZR_NEG_POS : forall p q:positive,
  IZR (Zpos p + Zneg q) = IZR (Zpos p) + IZR (Zneg q).
Proof.
  intros p q.
  simpl.
  rewrite Z.pos_sub_spec.
  destruct (p ?= q)%positive eqn:h.
  {
    simpl.
    apply Pos.compare_eq in h.
    subst q.
    rewrite Rplus_opp_r.
    reflexivity.
  }
  {
    simpl.
    rewrite Pos2Nat.inj_sub.
    rewrite minus_INR.
    unfold Rminus.
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    rewrite Rplus_comm.
    reflexivity.

    apply Pos2Nat.inj_le.
    unfold Pos.le.
    rewrite h.
    intro eq.
    inversion eq.

    unfold Pos.lt.
    exact h.
  }
  {
    simpl.
    rewrite Pos2Nat.inj_sub.
    rewrite minus_INR.
    unfold Rminus.
    reflexivity.

    apply Pos2Nat.inj_le.
    unfold Pos.le.
    rewrite Pos.compare_antisym.
    rewrite h.
    simpl.
    intro eq.
    inversion eq.

    unfold Pos.lt.
    rewrite Pos.compare_antisym.
    rewrite h.
    simpl.
    reflexivity.
  }
Qed.