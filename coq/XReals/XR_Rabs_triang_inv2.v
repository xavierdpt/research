Require Import XR_Rabs.
Require Import XR_Rabs_minus_sym.
Require Import XR_Rabs_triang_inv.
Require Import XR_Rcase_abs.
Require Import XR_Rminus.
Require Import XR_Ropp_plus_distr.
Require Import XR_Ropp_involutive.
Require Import XR_Rle_trans.

Local Open Scope R_scope.

Lemma Rabs_triang_inv2 : forall a b:R, Rabs (Rabs a - Rabs b) <= Rabs (a - b).
Proof.
  intros x y.
  unfold Rabs at 1.
  destruct (Rcase_abs (Rabs x - Rabs y)) as [ h | h ].
  {
    rewrite Rabs_minus_sym.
    eapply Rle_trans.
    2:apply Rabs_triang_inv.
    unfold Rminus.
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    rewrite Rplus_comm.
    right.
    reflexivity.
  }
  { apply Rabs_triang_inv. }
Qed.