Require Import XR_Rle.
Require Import XR_Rabs.
Require Import XR_Rabs_left.
Require Import XR_Rabs_R0.
Require Import XR_Ropp_0.

Local Open Scope R_scope.

Lemma Rabs_left1 : forall a:R, a <= R0 -> Rabs a = - a.
Proof.
  intros x h.
  destruct h as [ h | h ].
  {
    apply Rabs_left.
    exact h.
  }
  {
    subst x.
    rewrite Rabs_R0.
    rewrite Ropp_0.
    reflexivity.
  }
Qed.