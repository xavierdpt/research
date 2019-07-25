Require Import XR_Rabs.
Require Import XR_Ropp_minus_distr.
Require Import XR_Rabs_Ropp.

Local Open Scope R_scope.

Lemma Rabs_minus_sym : forall x y:R, Rabs (x - y) = Rabs (y - x).
Proof.
  intros x y.
  rewrite <- Ropp_minus_distr.
  rewrite Rabs_Ropp.
  reflexivity.
Qed.