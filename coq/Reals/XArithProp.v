(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import XRbase.
Require Import XRbasic_fun.
Require Import Even.
Require Import Div2.
Require Import ArithRing.

Local Open Scope Z_scope.
Local Open Scope XR_scope.

Lemma minus_neq_O : forall n i:nat, (i < n)%nat -> (n - i)%nat <> 0%nat.
Proof.
  intros; red; intro.
  cut (forall n m:nat, (m <= n)%nat -> (n - m)%nat = 0%nat -> n = m).
  intro; assert (H2 := H1 _ _ (lt_le_weak _ _ H) H0); rewrite H2 in H;
    elim (lt_irrefl _ H).
  set (R := fun n m:nat => (m <= n)%nat -> (n - m)%nat = 0%nat -> n = m).
  cut
    ((forall n m:nat, R n m) ->
      forall n0 m:nat, (m <= n0)%nat -> (n0 - m)%nat = 0%nat -> n0 = m).
  intro; apply H1.
  apply nat_double_ind.
  unfold R; intros; inversion H2; reflexivity.
  unfold R; intros; simpl in H3; assumption.
  unfold R; intros; simpl in H4; assert (H5 := le_S_n _ _ H3);
    assert (H6 := H2 H5 H4); rewrite H6; reflexivity.
  unfold R; intros; apply H1; assumption.
Qed.

Lemma le_minusni_n : forall n i:nat, (i <= n)%nat -> (n - i <= n)%nat.
Proof.
  set (R := fun m n:nat => (n <= m)%nat -> (m - n <= m)%nat).
  cut
    ((forall m n:nat, R m n) -> forall n i:nat, (i <= n)%nat -> (n - i <= n)%nat).
  intro; apply H.
  apply nat_double_ind.
  unfold R; intros; simpl; apply le_n.
  unfold R; intros; simpl; apply le_n.
  unfold R; intros; simpl; apply le_trans with n.
  apply H0; apply le_S_n; assumption.
  apply le_n_Sn.
  unfold R; intros; apply H; assumption.
Qed.

Lemma lt_minus_O_lt : forall m n:nat, (m < n)%nat -> (0 < n - m)%nat.
Proof.
  intros n m; pattern n, m; apply nat_double_ind;
    [ intros; rewrite <- minus_n_O; assumption
      | intros; elim (lt_n_O _ H)
      | intros; simpl; apply H; apply lt_S_n; assumption ].
Qed.

Lemma even_odd_cor :
  forall n:nat,  exists p : nat, n = (2 * p)%nat \/ n = S (2 * p).
Proof.
  intro.
  assert (H := even_or_odd n).
  exists (div2 n).
  assert (H0 := even_odd_double n).
  elim H0; intros.
  elim H1; intros H3 _.
  elim H2; intros H4 _.
  replace (2 * div2 n)%nat with (double (div2 n)).
  elim H; intro.
  left.
  apply H3; assumption.
  right.
  apply H4; assumption.
  unfold double;ring.
Qed.

  (* 2m <= 2n => m<=n *)
Lemma le_double : forall m n:nat, (2 * m <= 2 * n)%nat -> (m <= n)%nat.
Proof.
  intros; apply INR_le.
  assert (H1 := le_INR _ _ H).
  do 2 rewrite mult_INR in H1.
  apply Rmult_le_reg_l with (INR 2).
  replace (INR 2) with (IZR 2).
  unfold IZR.
  unfold IPR.
  unfold IPR_2.
  pattern R0; rewrite <- Rplus_0_l.
  apply Rplus_lt_compat.
  exact Rlt_0_1.
  exact Rlt_0_1.
  reflexivity.
  assumption.
Qed.

(** Here, we have the euclidian division *)
(** This lemma is used in the proof of sin_eq_0 : (sin x)=0<->x=kPI *)
Lemma euclidian_division :
  forall x y:R,
    y <> R0 ->
    exists k : Z, (exists r : R, x = IZR k * y + r /\ R0 <= r < Rabs y).
Proof.
  intros.
  set
    (k0 :=
      match Rcase_abs y with
	| left _ => (1 - up (x / - y))%Z
	| right _ => (up (x / y) - 1)%Z
      end).
  exists k0.
  exists (x - IZR k0 * y).
  split.
  unfold Rminus.
  rewrite (Rplus_comm x).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  reflexivity.
  unfold k0; case (Rcase_abs y) as [Hlt|Hge].
  assert (H0 := archimed (x / - y)); rewrite <- Z_R_minus; simpl;
    unfold Rminus.
  replace (- ((R1 + - IZR (up (x / - y))) * y)) with
    ((IZR (up (x / - y)) - R1) * y).
  2:{
    unfold Rminus.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_r.
    rewrite Ropp_plus_distr.
    rewrite <- Ropp_mult_distr_l.
    rewrite Rmult_1_l.
    rewrite Rplus_comm.
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    reflexivity.
  }
  split.
  apply Rmult_le_reg_l with (/ - y).
  apply Rinv_0_lt_compat; apply Ropp_0_gt_lt_contravar; exact Hlt.
  rewrite Rmult_0_r; rewrite (Rmult_comm (/ - y)); rewrite Rmult_plus_distr_r;
    rewrite <- Ropp_inv_permute; [ idtac | assumption ].
  rewrite Ropp_mult_distr_r.
  rewrite Rmult_assoc.
  repeat rewrite Ropp_mult_distr_r_reverse.
  rewrite <- Ropp_mult_distr_l.
  rewrite Rinv_r.
  rewrite <- Ropp_mult_distr_r.
  rewrite Rmult_1_r.
  rewrite Ropp_involutive.
  apply Rplus_le_reg_l with (IZR (up (x / - y)) - x / - y).
  rewrite Rplus_0_r; unfold Rdiv; pattern (/ - y) at 4;
    rewrite <- Ropp_inv_permute; [ idtac | assumption ].

  unfold Rminus.
  repeat rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  pattern (-(x*/-y)) at 1;rewrite <- Rplus_0_r.
  rewrite Ropp_inv_permute.
  repeat rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  apply Rplus_le_reg_l with ((x*/y)).
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  rewrite Rplus_0_r.
  rewrite Rplus_comm.
  apply Rplus_le_reg_l with (IZR (up (x * / - y))).
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  unfold IZR at 2.
  unfold IPR.
  unfold Rminus in H0.
  unfold Rdiv in H0.
  rewrite <- Ropp_inv_permute in H0.
  rewrite <- Ropp_mult_distr_r in H0.
  rewrite Ropp_involutive in H0.
  rewrite <- Ropp_inv_permute.
  rewrite <- Ropp_mult_distr_r.
  apply H0.
  exact H.
  exact H.
  exact H.
  exact H.
 
  rewrite (Rabs_left _ Hlt).
  apply Rmult_lt_reg_l with (/ - y).
  apply Rinv_0_lt_compat.
  apply Ropp_0_gt_lt_contravar.
  exact Hlt.
  rewrite <- Rinv_l_sym.
  rewrite (Rmult_comm (/ - y)).
  rewrite Rmult_plus_distr_r.
  rewrite <- Ropp_inv_permute.
  2:assumption.
  rewrite Ropp_mult_distr_r.
  rewrite Rmult_assoc.
  repeat rewrite Ropp_mult_distr_r_reverse.
  rewrite <- Ropp_mult_distr_l.
  rewrite <- Rinv_r_sym.
  rewrite <- Ropp_mult_distr_r.
  rewrite Rmult_1_r.
  2:assumption.
  apply Rplus_lt_reg_l with (IZR (up (x / - y)) - R1).
  replace (IZR (up (x / - y)) - R1 + R1) with (IZR (up (x / - y))).
  2:{
    unfold Rminus.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    reflexivity.
  }
  replace (IZR (up (x / - y)) - R1 + (- (x * / y) + - (IZR (up (x / - y)) - R1)))
    with (- (x * / y)).
  2:{
    unfold Rminus.
    repeat rewrite Rplus_assoc.
    rewrite (Rplus_comm (- R1)).
    repeat rewrite Rplus_assoc.
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    repeat rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    rewrite Rplus_comm.
    repeat rewrite Rplus_assoc.
	rewrite Rplus_opp_l.
	rewrite Rplus_0_r.
    reflexivity.
  }
  apply Rgt_lt.
  unfold Rminus.
  rewrite Ropp_involutive.
  unfold IZR at 3.
  unfold IPR.
  repeat rewrite Rplus_assoc.
  rewrite (Rplus_comm (-R1)).
  repeat rewrite Rplus_assoc.
  rewrite (Rplus_comm R1).
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  rewrite Rplus_comm.
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  elim H0.
  intros H1 _.
  unfold Rdiv in H1.
  rewrite <- Ropp_inv_permute in H1.
  rewrite <- Ropp_mult_distr_r in H1.
  unfold Rdiv.
  rewrite <- Ropp_inv_permute.
  rewrite <- Ropp_mult_distr_r.
  exact H1.
  assumption.
  assumption.
  apply Ropp_neq_0_compat; assumption.
  assert (H0 := archimed (x / y)); rewrite <- Z_R_minus; simpl;
    cut (R0 < y).
  intro; unfold Rminus;
    replace (- ((IZR (up (x / y)) + -(R1)) * y)) with ((R1 - IZR (up (x / y))) * y).
    2:{
rewrite Ropp_mult_distr_l.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
unfold Rminus.
rewrite Rplus_comm.
reflexivity.
}
  split.
  apply Rmult_le_reg_l with (/ y).
  apply Rinv_0_lt_compat.
assumption.
  rewrite Rmult_0_r.
rewrite (Rmult_comm (/ y)).
rewrite Rmult_plus_distr_r.
rewrite Ropp_mult_distr_l.
    rewrite Rmult_assoc.
rewrite <- Rinv_r_sym.
      rewrite Rmult_1_r.
2:assumption.
      apply Rplus_le_reg_l with (IZR (up (x / y)) - x / y).
	rewrite Rplus_0_r.
unfold Rdiv.
	  replace
	    (IZR (up (x * / y)) - x * / y + (x * / y + - (IZR (up (x * / y)) + - IZR 1))) with R1.
2:{
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
unfold Rminus.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_l.
reflexivity.
}
 elim H0; intros _ H2; unfold Rdiv in H2;
	      exact H2.
  rewrite (Rabs_right _ Hge).
apply Rmult_lt_reg_l with (/ y).
  apply Rinv_0_lt_compat. assumption.
  rewrite <- (Rinv_l_sym _ H).
rewrite (Rmult_comm (/ y)).
    rewrite Rmult_plus_distr_r.
rewrite Ropp_mult_distr_l.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rmult_assoc.
rewrite <- Rinv_r_sym.
rewrite Rmult_1_r.
2:assumption.
      apply Rplus_lt_reg_l with (IZR (up (x / y)) - R1).
	replace (IZR (up (x / y)) - R1 + R1) with (IZR (up (x / y))).

2:{
unfold Rminus.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
reflexivity.
}
	  replace (IZR (up (x / y)) - R1 + (x * / y + (- IZR (up (x / y)) + IZR 1))) with (x * / y).
2:{
unfold Rminus.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm (-R1)).
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
reflexivity.
}
elim H0; unfold Rdiv;
	      intros H2 _; exact H2.
  destruct (total_order_T R0 y) as [[Hlt|Heq]|Hgt].
  assumption.
  elim H; symmetry ; exact Heq.
  apply Rge_le in Hge; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hge Hgt)).
Qed.

Lemma tech8 : forall n i:nat, (n <= S n + i)%nat.
Proof.
  intros; induction  i as [| i Hreci].
  replace (S n + 0)%nat with (S n); [ apply le_n_Sn | ring ].
  replace (S n + S i)%nat with (S (S n + i)).
  apply le_S; assumption.
  apply INR_eq; rewrite S_INR; do 2 rewrite plus_INR; do 2 rewrite S_INR.
repeat rewrite Rplus_assoc.
reflexivity.
Qed.

