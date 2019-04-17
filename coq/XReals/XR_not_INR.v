Require Export XR_not_0_INR.

Local Open Scope R_scope.

Lemma not_INR : forall n m:nat,
  n <> m ->
  INR n <> INR m.
Proof.
  intro n.
  induction n as [ | n hin ].
  {
    intros m hm.
    apply not_eq_sym.
    simpl.
    apply not_0_INR.
    apply not_eq_sym.
    exact hm.
  }
  {
    intro m.
    destruct m as [ | m ].
    {
      intro hn.
      apply not_0_INR.
      exact hn.
    }
    {
      intro hnm.
      rewrite S_INR.
      rewrite S_INR.
      unfold not.
      intro heq.
      apply Rplus_eq_reg_r in heq.
      unfold not in hin.
      apply hin with m.
      {
        intro eq.
        subst m.
        apply hnm.
        reflexivity.
      }
      { exact heq. }
    }
  }
Qed.
