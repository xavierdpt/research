Require Import XR_R.
Require Import XR_Rsqr.
Require Import XR_Rsqr_neg.
Require Import XR_Rabs.
Require Import XR_Rcase_abs.

Local Open Scope R_scope.

Lemma Rsqr_abs : forall x:R, Rsqr x = Rsqr (Rabs x).
Proof.
  intro x.
  unfold Rabs.
  destruct (Rcase_abs x) as [ h | h ].
  {
  rewrite <- Rsqr_neg.
  reflexivity.
  }
  { reflexivity. }
Qed.
