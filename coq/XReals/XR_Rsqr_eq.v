Require Import XR_Rsqr.
Require Import XR_Rabs.
Require Import XR_Rcase_abs.
Require Import XR_Rsqr_eq_abs_0.
Require Import XR_Ropp_involutive.

Local Open Scope R_scope.

Lemma Rsqr_eq : forall x y:R, Rsqr x = Rsqr y -> x = y \/ x = - y.
Proof.
  intros x y h.
  apply Rsqr_eq_abs_0 in h.
  unfold Rabs in h.
  destruct (Rcase_abs x) as [ hx | hx ] ;
  destruct (Rcase_abs y) as [ hy | hy ].
  {
    left.
    rewrite <- Ropp_involutive with x.
    rewrite <- Ropp_involutive with y.
    rewrite h.
    reflexivity.
  }
  {
    right.
    rewrite <- Ropp_involutive with x.
    rewrite h.
    reflexivity.
  }
  {
    right.
    exact h.
  }
  {
    left.
    exact h.
  }
Qed.