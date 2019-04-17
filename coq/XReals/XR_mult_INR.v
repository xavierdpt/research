Require Export XR_S_INR.
Require Export XR_plus_INR.
Require Export XR_Rmult_0_r.
Require Export XR_Rmult_0_l.
Require Export XR_Rmult_plus_distr_r.

Local Open Scope R_scope.

Lemma mult_INR : forall n m:nat,
  INR (n * m) = INR n * INR m.
Proof.
  intros n.
  induction n as [ | n hn ].
  {
    intro m.
    simpl.
    rewrite Rmult_0_l.
    reflexivity.
  }
  {
    intro m.
    simpl.
    rewrite plus_INR.
    rewrite hn.
    rewrite S_INR.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    rewrite Rplus_comm.
    reflexivity.
  }
Qed.