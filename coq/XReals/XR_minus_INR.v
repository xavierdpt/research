Require Export XR_Rminus.
Require Export XR_plus_INR.
Require Export XR_Ropp_0.
Require Export XR_Ropp_plus_distr.

Local Open Scope R_scope.

Lemma minus_INR : forall n m:nat,
  (m <= n)%nat ->
  INR (n - m) = INR n - INR m.
Proof.
  intros n.
  induction n as [ | n hin ].
  {
    intros m hm.
    simpl.
    inversion hm.
    subst m.
    simpl.
    unfold Rminus.
    rewrite Ropp_0.
    rewrite Rplus_0_r.
    reflexivity.
  }
  {
    intros m hmsn.
    destruct m as [ | m ].
    {
      simpl.
      unfold Rminus.
      rewrite Ropp_0.
      rewrite Rplus_0_r.
      reflexivity.
    }
    {
      simpl.
      rewrite hin.
      {
        rewrite S_INR.
        rewrite S_INR.
        unfold Rminus.
        rewrite Ropp_plus_distr.
        repeat rewrite Rplus_assoc.
        rewrite (Rplus_comm R1).
        repeat rewrite Rplus_assoc.
        rewrite Rplus_opp_l.
        rewrite Rplus_0_r.
        reflexivity.
      }
      {
        apply le_S_n.
        exact hmsn.
      }
    }
  }
Qed.