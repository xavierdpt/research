Require Import XR_Rsqr.
Require Import XR_Rmult_1_l.


Local Open Scope R_scope.

Lemma Rsqr_1 : Rsqr R1 = R1.
Proof.
  unfold Rsqr.
  rewrite Rmult_1_l.
  reflexivity.
Qed.