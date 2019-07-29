Require Import XR_Rsqr.
Require Import XR_Rlt_irrefl.
Require Import XR_Rmult_0_l.


Local Open Scope R_scope.

Lemma Rsqr_gt_0_0 : forall x:R, R0 < Rsqr x -> x <> R0.
Proof.
  intros x h.
  intro heq.
  subst x.
  unfold Rsqr in h.
  rewrite Rmult_0_l in h.
  apply Rlt_irrefl with R0.
  exact h.
Qed.