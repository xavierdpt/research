Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Ropp_involutive.
Require Import XR_Ropp_0.
Require Import XR_Ropp_eq_compat.

Local Open Scope R_scope.

Lemma Rabs_no_R0 : forall r, r <> R0 -> Rabs r <> R0.
Proof.
  intros x h.
  intro heq.
  apply h.
  unfold Rabs in heq.
  destruct (Rcase_abs x) as [ hl | hr ].
  {
    rewrite <- Ropp_involutive with x.
    rewrite <- Ropp_0.
    apply Ropp_eq_compat.
    exact heq.
  }
  { exact heq. }
Qed.
