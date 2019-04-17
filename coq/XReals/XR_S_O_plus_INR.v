Require Export XR_S_INR.
Require Export XR_Rplus_comm.

Local Open Scope R_scope.

Lemma S_O_plus_INR : forall n:nat,
  INR (1 + n) = INR 1 + INR n.
Proof.
  intro n.
  simpl.
  rewrite S_INR.
  rewrite Rplus_comm.
  reflexivity.
Qed.
