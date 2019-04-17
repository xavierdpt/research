Require Export Arith.
Require Export XR_S_INR.
Require Export XR_Rplus_0_r.
Require Export XR_Rplus_assoc.

Local Open Scope R_scope.

Lemma plus_INR : forall n m:nat,
  INR (n + m) = INR n + INR m.
Proof.
  intros n m.
  induction m as [ | m im ].
  {
    simpl.
    rewrite Rplus_0_r.
    rewrite <- plus_n_O.
    reflexivity.
  }
  {
    rewrite Nat.add_comm.
    simpl.
    rewrite S_INR.
    rewrite Nat.add_comm.
    rewrite im.
    rewrite S_INR.
    repeat rewrite <- Rplus_assoc.
    reflexivity.
  }
Qed.