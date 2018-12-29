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
Require Import XRfunctions.
Require Import XRanalysis1.
Require Import Omega.
Local Open Scope XR_scope.

(**********)
Lemma formule :
  forall (x h l1 l2:R) (f1 f2:R -> R),
    h <> R0 ->
    f2 x <> R0 ->
    f2 (x + h) <> R0 ->
    (f1 (x + h) / f2 (x + h) - f1 x / f2 x) / h -
    (l1 * f2 x - l2 * f1 x) / Rsqr (f2 x) =
    / f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1) +
    l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h)) -
    f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2) +
    l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x).
Proof.
  intros; unfold Rdiv, Rminus, Rsqr.
  repeat rewrite Rmult_plus_distr_r; repeat rewrite Rmult_plus_distr_l;
    repeat rewrite Rinv_mult_distr; try assumption.
  replace (l1 * f2 x * (/ f2 x * / f2 x)) with (l1 * / f2 x * (f2 x * / f2 x)).
{
  repeat rewrite Ropp_plus_distr.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  repeat rewrite Ropp_involutive.
  set (a := f2 x).
  set (b := f1 (x+h)).
  set (c := f2 (x+h)).
  set (d := f1 x).
  symmetry.
  repeat rewrite <- Rmult_assoc.
  repeat rewrite <- Rplus_assoc.
  rewrite (Rmult_comm (/c)).
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rmult_assoc;rewrite (Rmult_comm (/c));repeat rewrite <- Rmult_assoc.
  repeat rewrite Rmult_assoc;rewrite (Rmult_comm c);repeat rewrite <- Rmult_assoc.
  repeat rewrite Rmult_assoc;rewrite Rinv_l. rewrite Rmult_1_r; repeat rewrite <- Rmult_assoc.
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rmult_1_r.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  symmetry.
  repeat rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  symmetry.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  rewrite <- Rplus_0_r.
  repeat rewrite Rplus_assoc;apply Rplus_eq_compat_l;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  rewrite (Rmult_comm (/a)).
  repeat rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm l1).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  repeat rewrite Rplus_assoc;rewrite Rplus_comm;repeat rewrite <- Rplus_assoc.
  rewrite (Rmult_comm d);repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (/a));repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (/c));repeat rewrite Rmult_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  rewrite Rplus_comm.
  rewrite (Rmult_comm (/a)).
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm a).
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l, Rmult_1_r.
  rewrite (Rmult_comm d).
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (/h)).
  rewrite Rplus_opp_r.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
}
  replace (l1 * (/ f2 x * / f2 (x + h)) * f2 x) with
  (l1 * / f2 (x + h) * (f2 x * / f2 x)).
2:{
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  reflexivity.
  assumption.
  assumption.
}
  replace (l1 * (/ f2 x * / f2 (x + h)) * - f2 (x + h)) with
  (- (l1 * / f2 x * (f2 (x + h) * / f2 (x + h)))).
{
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  rewrite Rmult_comm.
  reflexivity.
}
  replace (f1 x * (/ f2 x * / f2 (x + h)) * (f2 (x + h) * / h)) with
  (f1 x * / f2 x * / h * (f2 (x + h) * / f2 (x + h))).
2:{
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  rewrite Rmult_comm.
  reflexivity.
}
  replace (f1 x * (/ f2 x * / f2 (x + h)) * (- f2 x * / h)) with
  (- (f1 x * / f2 (x + h) * / h * (f2 x * / f2 x))).
2:{
  rewrite <- Ropp_mult_distr_l.
  rewrite <- Ropp_mult_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite Ropp_mult_distr_l.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  reflexivity.
}
  replace (l2 * f1 x * (/ f2 x * / f2 x * / f2 (x + h)) * f2 (x + h)) with
  (l2 * f1 x * / f2 x * / f2 x * (f2 (x + h) * / f2 (x + h))).
2:{
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  reflexivity.
}
  replace (l2 * f1 x * (/ f2 x * / f2 x * / f2 (x + h)) * - f2 x) with
  (- (l2 * f1 x * / f2 x * / f2 (x + h) * (f2 x * / f2 x))).
2:{
  rewrite <- Ropp_mult_distr_r.
  repeat rewrite Ropp_mult_distr_l.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  reflexivity.
}
  repeat rewrite <- Rinv_r_sym; try assumption || ring.
{
  rewrite <- Ropp_mult_distr_r.
  repeat rewrite Ropp_mult_distr_l.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_compat_l.
  rewrite Rinv_l.
  reflexivity.
  assumption.
}
  apply prod_neq_R0; assumption.
Qed.

(* begin hide *)
Notation Rmin_pos := Rmin_pos (only parsing). (* compat *)
(* end hide *)

Remark Rlt_0_8 : R0 < R8.
Proof.
  unfold R8.
  apply Rplus_lt_0_compat.
  exact Rlt_0_4.
  exact Rlt_0_4.
Qed.

Lemma maj_term1 :
  forall (x h eps l1 alp_f2:R) (eps_f2 alp_f1d:posreal)
    (f1 f2:R -> R),
    R0 < eps ->
    f2 x <> R0 ->
    f2 (x + h) <> R0 ->
    (forall h:R,
      h <> R0 ->
      Rabs h < alp_f1d ->
      Rabs ((f1 (x + h) - f1 x) / h - l1) < Rabs (eps * f2 x / R8)) ->
    (forall a:R,
      Rabs a < Rmin eps_f2 alp_f2 -> / Rabs (f2 (x + a)) < R2 / Rabs (f2 x)) ->
    h <> R0 ->
    Rabs h < alp_f1d ->
    Rabs h < Rmin eps_f2 alp_f2 ->
    Rabs (/ f2 (x + h) * ((f1 (x + h) - f1 x) / h - l1)) < eps / R4.
Proof.
  intros.
  assert (H7 := H3 h H6).
  assert (H8 := H2 h H4 H5).
  apply Rle_lt_trans with
    (R2 / Rabs (f2 x) * Rabs ((f1 (x + h) - f1 x) / h - l1)).
  rewrite Rabs_mult.
  apply Rmult_le_compat_r.
  apply Rabs_pos.
  rewrite Rabs_Rinv; [ left; exact H7 | assumption ].
  apply Rlt_le_trans with (R2 / Rabs (f2 x) * Rabs (eps * f2 x / R8)).
  apply Rmult_lt_compat_l.
{
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  exact Rlt_0_2.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
}
  exact H8.
  right; unfold Rdiv.
  repeat rewrite Rabs_mult.

  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm R2).
  repeat rewrite Rmult_assoc.
  replace (Rabs (/R8)) with (/R8).
  replace (/R8 * R2) with (/R4).
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  replace (Rabs eps) with eps.
  rewrite Rmult_comm.
  rewrite <- Rabs_Rinv.
  repeat rewrite <- Rmult_assoc.
  rewrite <- Rabs_mult.
  rewrite Rinv_r.
  rewrite Rabs_R1.
  rewrite Rmult_1_l.
  reflexivity.

  assumption.
  assumption.

  rewrite Rabs_right. reflexivity.
  left. assumption.

  replace R8 with (R4*R2).
  rewrite Rinv_mult_distr.
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
  reflexivity.
  exact Neq_2_0.
  apply Rlt_not_eq'. exact Rlt_0_4.
  exact Neq_2_0.
  rewrite Rmult_comm.
  rewrite double.
  unfold R8.
  reflexivity.

  rewrite Rabs_right.
  reflexivity.

  left.
  apply Rinv_0_lt_compat.
  exact Rlt_0_8.
Qed.

Lemma maj_term2 :
  forall (x h eps l1 alp_f2 alp_f2t2:R) (eps_f2:posreal)
    (f2:R -> R),
    R0 < eps ->
    f2 x <> R0 ->
    f2 (x + h) <> R0 ->
    (forall a:R,
      Rabs a < alp_f2t2 ->
      Rabs (f2 (x + a) - f2 x) < Rabs (eps * Rsqr (f2 x) / (R8 * l1))) ->
    (forall a:R,
      Rabs a < Rmin eps_f2 alp_f2 -> / Rabs (f2 (x + a)) < R2 / Rabs (f2 x)) ->
    h <> R0 ->
    Rabs h < alp_f2t2 ->
    Rabs h < Rmin eps_f2 alp_f2 ->
    l1 <> R0 -> Rabs (l1 / (f2 x * f2 (x + h)) * (f2 x - f2 (x + h))) < eps / R4.
Proof.
  intros.
  assert (H8 := H3 h H6).
  assert (H9 := H2 h H5).
  apply Rle_lt_trans with
    (Rabs (l1 / (f2 x * f2 (x + h))) * Rabs (eps * Rsqr (f2 x) / (R8 * l1))).
  rewrite Rabs_mult; apply Rmult_le_compat_l.
  apply Rabs_pos.
  rewrite <- (Rabs_Ropp (f2 x - f2 (x + h))); rewrite Ropp_minus_distr.
  left; apply H9.
  apply Rlt_le_trans with
    (Rabs (R2 * (l1 / (f2 x * f2 x))) * Rabs (eps * Rsqr (f2 x) / (R8 * l1))).
  apply Rmult_lt_compat_r.
  apply Rabs_pos_lt.
  unfold Rdiv; unfold Rsqr; repeat apply prod_neq_R0;
    try assumption || discrR.
  red; intro H10; rewrite H10 in H; elim (Rlt_irrefl _ H).
  apply Rinv_neq_0_compat; apply prod_neq_R0; try assumption || discrR.
  unfold Rdiv.
  repeat rewrite Rinv_mult_distr; try assumption.
  repeat rewrite Rabs_mult.
  replace (Rabs R2) with R2.
  apply Rlt_not_eq'. exact Rlt_0_8.
  rewrite Rabs_right. reflexivity. left. exact Rlt_0_2.
  rewrite (Rmult_comm R2).
  replace (Rabs l1 * (Rabs (/ f2 x) * Rabs (/ f2 x)) * R2) with
  (Rabs l1 * (Rabs (/ f2 x) * (Rabs (/ f2 x) * R2))).
2:{
repeat rewrite Rmult_assoc.
reflexivity.
}
{
  unfold Rdiv.
  repeat rewrite Rabs_mult.
  repeat rewrite Rmult_assoc.
  apply Rmult_lt_compat_l.
  apply Rabs_pos_lt. assumption.
  repeat rewrite Rinv_mult_distr.
  repeat rewrite Rabs_mult.
  repeat rewrite Rmult_assoc.
  apply Rmult_lt_compat_l.
  apply Rabs_pos_lt.
  apply Rinv_neq_0_compat. assumption.
  replace (Rabs R2) with R2.
  rewrite Rmult_comm.
  Search (Rabs (/ _)).
  repeat rewrite Rabs_Rinv.
  assumption.
  assumption.
  assumption.
  rewrite Rabs_right. reflexivity. left. exact Rlt_0_2.
  assumption.
  assumption.
  assumption.
  assumption.
}
  right.
  unfold Rsqr, Rdiv.
  do 1 rewrite Rinv_mult_distr; try assumption || discrR.
  do 1 rewrite Rinv_mult_distr; try assumption || discrR.
  repeat rewrite Rabs_mult.
  repeat rewrite Rabs_Rinv; try assumption || discrR.
  replace (Rabs eps) with eps.
  replace (Rabs R8) with R8.
  replace (Rabs R2) with R2.
  replace R8 with (R4 * R2).
2:{
  rewrite Rmult_comm. rewrite double. unfold R8.
  reflexivity.
}
  rewrite Rinv_mult_distr; discrR.
  replace
  (R2 * (Rabs l1 * (/ Rabs (f2 x) * / Rabs (f2 x))) *
    (eps * (Rabs (f2 x) * Rabs (f2 x)) * (/ R4 * / R2 * / Rabs l1))) with
  (eps * / R4 * (Rabs l1 * / Rabs l1) * (Rabs (f2 x) * / Rabs (f2 x)) *
    (Rabs (f2 x) * / Rabs (f2 x)) * (R2 * / R2)).
2:{
  repeat rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm R2).
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (/R2)).
  repeat rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite (Rmult_comm (Rabs l1)).
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  symmetry.
  rewrite Rmult_comm.
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite Rmult_comm.
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  reflexivity.

  apply Rabs_no_R0. assumption.
  apply Rabs_no_R0. assumption.
  apply Rabs_no_R0. assumption.
  exact Neq_2_0.
  apply Rabs_no_R0. assumption.
  apply Rabs_no_R0. assumption.
  apply Rabs_no_R0. assumption.
  exact Neq_2_0.
}
  repeat rewrite <- Rinv_r_sym; try (apply Rabs_no_R0; assumption) || discrR.
{
  repeat rewrite Rmult_1_r.
  reflexivity.
}
exact Neq_2_0.
apply Rlt_not_eq'. exact Rlt_0_4.
exact Neq_2_0.
rewrite Rabs_right. reflexivity. left. apply Rlt_0_2.
rewrite Rabs_right. reflexivity. left. apply Rlt_0_8.
rewrite Rabs_right. reflexivity. left. assumption.
apply Rlt_not_eq'. exact Rlt_0_8.
apply Rlt_not_eq'. exact Rlt_0_8.
Qed.

Lemma maj_term3 :
  forall (x h eps l2 alp_f2:R) (eps_f2 alp_f2d:posreal)
    (f1 f2:R -> R),
    R0 < eps ->
    f2 x <> R0 ->
    f2 (x + h) <> R0 ->
    (forall h:R,
      h <> R0 ->
      Rabs h < alp_f2d ->
      Rabs ((f2 (x + h) - f2 x) / h - l2) <
      Rabs (Rsqr (f2 x) * eps / (R8 * f1 x))) ->
    (forall a:R,
      Rabs a < Rmin eps_f2 alp_f2 -> / Rabs (f2 (x + a)) < R2 / Rabs (f2 x)) ->
    h <> R0 ->
    Rabs h < alp_f2d ->
    Rabs h < Rmin eps_f2 alp_f2 ->
    f1 x <> R0 ->
    Rabs (f1 x / (f2 x * f2 (x + h)) * ((f2 (x + h) - f2 x) / h - l2)) <
    eps / R4.
Proof.
  intros.
  assert (H8 := H2 h H4 H5).
  assert (H9 := H3 h H6).
  apply Rle_lt_trans with
    (Rabs (f1 x / (f2 x * f2 (x + h))) * Rabs (Rsqr (f2 x) * eps / (R8 * f1 x))).
  rewrite Rabs_mult.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  left; apply H8.
  apply Rlt_le_trans with
    (Rabs (R2 * (f1 x / (f2 x * f2 x))) * Rabs (Rsqr (f2 x) * eps / (R8 * f1 x))).
  apply Rmult_lt_compat_r.
  apply Rabs_pos_lt.
  unfold Rdiv; unfold Rsqr; repeat apply prod_neq_R0;
    try assumption.
  red; intro H10; rewrite H10 in H; elim (Rlt_irrefl _ H).
  apply Rinv_neq_0_compat. apply prod_neq_R0. 2:assumption.
  apply Rlt_not_eq'. exact Rlt_0_8.
  unfold Rdiv.
  repeat rewrite Rinv_mult_distr; try assumption.
  repeat rewrite Rabs_mult.
  replace (Rabs R2) with R2.
  rewrite (Rmult_comm R2).
  replace (Rabs (f1 x) * (Rabs (/ f2 x) * Rabs (/ f2 x)) * R2) with
  (Rabs (f1 x) * (Rabs (/ f2 x) * (Rabs (/ f2 x) * R2))).
2:{
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  reflexivity.
}
  repeat apply Rmult_lt_compat_l.
  apply Rabs_pos_lt; assumption.
  apply Rabs_pos_lt; apply Rinv_neq_0_compat; assumption.
  repeat rewrite Rabs_Rinv; assumption || idtac.
  rewrite <- (Rmult_comm R2).
  unfold Rdiv in H9; exact H9.
{
  rewrite Rabs_right.
  reflexivity.
  left. exact Rlt_0_2.
}
  right.
  unfold Rsqr, Rdiv.
  rewrite Rinv_mult_distr; try assumption || discrR.
  rewrite Rinv_mult_distr; try assumption || discrR.
  repeat rewrite Rabs_mult.
  repeat rewrite Rabs_Rinv; try assumption || discrR.
  replace (Rabs eps) with eps.
  replace (Rabs R8) with R8.
  replace (Rabs R2) with R2.
  replace R8 with (R4 * R2).
2:{
  rewrite Rmult_comm.
  rewrite double.
  unfold R8.
  reflexivity.
}
  rewrite Rinv_mult_distr; discrR.
  replace
  (R2 * (Rabs (f1 x) * (/ Rabs (f2 x) * / Rabs (f2 x))) *
    (Rabs (f2 x) * Rabs (f2 x) * eps * (/ R4 * / R2 * / Rabs (f1 x)))) with
  (eps * / R4 * (Rabs (f2 x) * / Rabs (f2 x)) * (Rabs (f2 x) * / Rabs (f2 x)) *
    (Rabs (f1 x) * / Rabs (f1 x)) * (R2 * / R2)).
2:{
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ eps).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/R4)).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ R2).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/R2)).
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/R2)).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  apply Rmult_eq_compat_r.
  rewrite Rmult_comm.
  reflexivity.
}
  repeat rewrite <- Rinv_r_sym; try discrR || (apply Rabs_no_R0; assumption).

repeat rewrite Rmult_1_r.
reflexivity.

exact Neq_2_0. 
apply Rlt_not_eq'. exact Rlt_0_4.
exact Neq_2_0. 
rewrite Rabs_right. reflexivity. left. exact Rlt_0_2.
rewrite Rabs_right. reflexivity. left. exact Rlt_0_8.
rewrite Rabs_right. reflexivity. left. assumption.
apply Rlt_not_eq'. exact Rlt_0_8.
apply Rlt_not_eq'. exact Rlt_0_8.
Qed.

Lemma maj_term4 :
  forall (x h eps l2 alp_f2 alp_f2c:R) (eps_f2:posreal)
    (f1 f2:R -> R),
    R0 < eps ->
    f2 x <> R0 ->
    f2 (x + h) <> R0 ->
    (forall a:R,
      Rabs a < alp_f2c ->
      Rabs (f2 (x + a) - f2 x) <
      Rabs (Rsqr (f2 x) * f2 x * eps / (R8 * f1 x * l2))) ->
    (forall a:R,
      Rabs a < Rmin eps_f2 alp_f2 -> / Rabs (f2 (x + a)) < R2 / Rabs (f2 x)) ->
    h <> R0 ->
    Rabs h < alp_f2c ->
    Rabs h < Rmin eps_f2 alp_f2 ->
    f1 x <> R0 ->
    l2 <> R0 ->
    Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h)) * (f2 (x + h) - f2 x)) <
    eps / R4.
Proof.
  intros.
  assert (H9 := H2 h H5).
  assert (H10 := H3 h H6).
  apply Rle_lt_trans with
    (Rabs (l2 * f1 x / (Rsqr (f2 x) * f2 (x + h))) *
      Rabs (Rsqr (f2 x) * f2 x * eps / (R8 * f1 x * l2))).
  rewrite Rabs_mult.
  apply Rmult_le_compat_l.
  apply Rabs_pos.
  left; apply H9.
  apply Rlt_le_trans with
    (Rabs (R2 * l2 * (f1 x / (Rsqr (f2 x) * f2 x))) *
      Rabs (Rsqr (f2 x) * f2 x * eps / (R8 * f1 x * l2))).
  apply Rmult_lt_compat_r.
  apply Rabs_pos_lt.
  unfold Rdiv; unfold Rsqr; repeat apply prod_neq_R0;
    assumption || idtac.
  red; intro H11; rewrite H11 in H; elim (Rlt_irrefl _ H).
  apply Rinv_neq_0_compat; apply prod_neq_R0.
  apply prod_neq_R0.
  apply Rlt_not_eq'. exact Rlt_0_8.
  assumption.
  assumption.
  unfold Rdiv.
  repeat rewrite Rinv_mult_distr;
    try assumption || (unfold Rsqr; apply prod_neq_R0; assumption).
  repeat rewrite Rabs_mult.
  replace (Rabs R2) with R2.
  replace
  (R2 * Rabs l2 * (Rabs (f1 x) * (Rabs (/ Rsqr (f2 x)) * Rabs (/ f2 x)))) with
  (Rabs l2 * (Rabs (f1 x) * (Rabs (/ Rsqr (f2 x)) * (Rabs (/ f2 x) * R2)))).
2:{
  repeat rewrite <- Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  repeat apply Rmult_eq_compat_l.
  reflexivity.
}

  replace
  (Rabs l2 * Rabs (f1 x) * (Rabs (/ Rsqr (f2 x)) * Rabs (/ f2 (x + h)))) with
  (Rabs l2 * (Rabs (f1 x) * (Rabs (/ Rsqr (f2 x)) * Rabs (/ f2 (x + h))))).
2:{
  repeat rewrite Rmult_assoc.
  reflexivity.
}
  repeat apply Rmult_lt_compat_l.
  apply Rabs_pos_lt; assumption.
  apply Rabs_pos_lt; assumption.
  apply Rabs_pos_lt; apply Rinv_neq_0_compat; unfold Rsqr;
    apply prod_neq_R0; assumption.
  repeat rewrite Rabs_Rinv; [ idtac | assumption | assumption ].
  rewrite <- (Rmult_comm R2).
  unfold Rdiv in H10; exact H10.
{
  rewrite Rabs_right. reflexivity. left. apply Rlt_0_2.
}
  right; unfold Rsqr, Rdiv.
  rewrite Rinv_mult_distr; try assumption || discrR.
  rewrite Rinv_mult_distr; try assumption || discrR.
  rewrite Rinv_mult_distr; try assumption || discrR.
  rewrite Rinv_mult_distr; try assumption || discrR.
  repeat rewrite Rabs_mult.
  repeat rewrite Rabs_Rinv; try assumption || discrR.
  replace (Rabs eps) with eps.
  replace (Rabs R8) with R8.
  replace (Rabs R2) with R2.
  replace R8 with (R4 * R2).
2:{
  rewrite Rmult_comm.
  rewrite double.
  unfold R8.
  reflexivity.
}
  rewrite Rinv_mult_distr; discrR.
  replace
  (R2 * Rabs l2 *
    (Rabs (f1 x) * (/ Rabs (f2 x) * / Rabs (f2 x) * / Rabs (f2 x))) *
    (Rabs (f2 x) * Rabs (f2 x) * Rabs (f2 x) * eps *
      (/ R4 * / R2 * / Rabs (f1 x) * / Rabs l2))) with
  (eps * / R4 * (Rabs l2 * / Rabs l2) * (Rabs (f1 x) * / Rabs (f1 x)) *
    (Rabs (f2 x) * / Rabs (f2 x)) * (Rabs (f2 x) * / Rabs (f2 x)) *
    (Rabs (f2 x) * / Rabs (f2 x)) * (R2 * / R2)).
2:{
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ eps).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/R4)).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ R2).
  repeat rewrite Rmult_assoc.
  repeat apply Rmult_eq_compat_l.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/R2)).
  repeat rewrite Rmult_assoc.
  repeat rewrite <- Rmult_assoc.
  rewrite (Rmult_comm _ (/R2)).
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  repeat apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  reflexivity.
}
  repeat rewrite <- Rinv_r_sym; try discrR || (apply Rabs_no_R0; assumption).

repeat rewrite Rmult_1_r. reflexivity.
exact Neq_2_0.
apply Rlt_not_eq'. exact Rlt_0_4.
exact Neq_2_0.
symmetry. apply Rabs_right. left. exact Rlt_0_2.
symmetry. apply Rabs_right. left. exact Rlt_0_8.
symmetry. apply Rabs_right. left. assumption.
apply Rlt_not_eq'. exact Rlt_0_8.
apply Rlt_not_eq'. exact Rlt_0_8.

apply Rmult_integral_contrapositive_currified.
apply Rlt_not_eq'. exact Rlt_0_8.
assumption.

apply Rmult_integral_contrapositive_currified.
assumption.
assumption.
Qed.

Lemma D_x_no_cond : forall x a:R, a <> R0 -> D_x no_cond x (x + a).
Proof.
  intros.
  unfold D_x, no_cond.
  split.
  trivial.
  apply Rminus_not_eq.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  apply Ropp_neq_0_compat; assumption.
Qed.

Lemma Rabs_4 :
  forall a b c d:R, Rabs (a + b + c + d) <= Rabs a + Rabs b + Rabs c + Rabs d.
Proof.
  intros.
  apply Rle_trans with (Rabs (a + b) + Rabs (c + d)).
  replace (a + b + c + d) with (a + b + (c + d)); [ apply Rabs_triang | idtac ].
repeat rewrite <- Rplus_assoc. reflexivity.
  apply Rle_trans with (Rabs a + Rabs b + Rabs (c + d)).
  apply Rplus_le_compat_r.
  apply Rabs_triang.
  repeat rewrite Rplus_assoc; repeat apply Rplus_le_compat_l.
  apply Rabs_triang.
Qed.

Lemma Rlt_4 :
  forall a b c d e f g h:R,
    a < b -> c < d -> e < f -> g < h -> a + c + e + g < b + d + f + h.
Proof.
  intros; apply Rlt_trans with (b + c + e + g).
  repeat apply Rplus_lt_compat_r; assumption.
  repeat rewrite Rplus_assoc; apply Rplus_lt_compat_l.
  apply Rlt_trans with (d + e + g).
  rewrite Rplus_assoc; apply Rplus_lt_compat_r; assumption.
  rewrite Rplus_assoc; apply Rplus_lt_compat_l; apply Rlt_trans with (f + g).
  apply Rplus_lt_compat_r; assumption.
  apply Rplus_lt_compat_l; assumption.
Qed.

(* begin hide *)
Notation Rmin_2 := Rmin_glb_lt (only parsing).
(* end hide *)

Lemma quadruple : forall x:R, R4 * x = x + x + x + x.
Proof.
  intro.
  unfold R4. unfold R2.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_1_l.
  repeat rewrite <- Rplus_assoc.
  reflexivity.
Qed.

Lemma quadruple_var : forall x:R, x = x / R4 + x / R4 + x / R4 + x / R4.
Proof.
  intro; rewrite <- quadruple.
  unfold Rdiv; rewrite <- Rmult_assoc; rewrite Rinv_r_simpl_m; discrR.
  reflexivity.
  apply Rlt_not_eq'.
  exact Rlt_0_4.
Qed.

(**********)
Lemma continuous_neq_0 :
  forall (f:R -> R) (x0:R),
    continuity_pt f x0 ->
    f x0 <> R0 ->
    exists eps : posreal, (forall h:R, Rabs h < eps -> f (x0 + h) <> R0).
Proof.
  intros; unfold continuity_pt in H; unfold continue_in in H;
    unfold limit1_in in H; unfold limit_in in H; elim (H (Rabs (f x0 / R2))).
  intros; elim H1; intros.
  exists (mkposreal x H2).
  intros; assert (H5 := H3 (x0 + h)).
  cut
    (dist R_met (x0 + h) x0 < x ->
      dist R_met (f (x0 + h)) (f x0) < Rabs (f x0 / R2)).
  unfold dist; simpl; unfold R_dist;
    replace (x0 + h - x0) with h.
  intros; assert (H7 := H6 H4).
  red; intro.
  rewrite H8 in H7; unfold Rminus in H7; rewrite Rplus_0_l in H7;
    rewrite Rabs_Ropp in H7; unfold Rdiv in H7; rewrite Rabs_mult in H7;
      pattern (Rabs (f x0)) at 1 in H7; rewrite <- Rmult_1_r in H7.
  cut (R0 < Rabs (f x0)).
  intro; assert (H10 := Rmult_lt_reg_l _ _ _ H9 H7).
  cut (Rabs (/ R2) = / R2).
  assert (Hyp : R0 < R2).
exact Rlt_0_2.
  intro; rewrite H11 in H10; assert (H12 := Rmult_lt_compat_l R2 _ _ Hyp H10);
    rewrite Rmult_1_r in H12; rewrite <- Rinv_r_sym in H12;
      [ idtac | discrR ].
2:{ exact Neq_2_0. }
change R2 with (IZR 2) in H12. change R1 with (IZR 1) in H12.
  now apply lt_IZR in H12.
  unfold Rabs; case (Rcase_abs (/ R2)) as [Hlt|Hge].
  assert (Hyp : R0 < R2).
exact Rlt_0_2.
  assert (H11 := Rmult_lt_compat_l R2 _ _ Hyp Hlt); rewrite Rmult_0_r in H11;
    rewrite <- Rinv_r_sym in H11; [ idtac | discrR ].
  elim (Rlt_irrefl R0 (Rlt_trans _ _ _ Rlt_0_1 H11)).
exact Neq_2_0. reflexivity.
  apply (Rabs_pos_lt _ H0).
  unfold Rminus. rewrite Rplus_comm. repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_l; reflexivity.
  assert (H6 := Req_dec x0 (x0 + h)); elim H6; intro.
  intro; rewrite <- H7. unfold R_met, dist; unfold R_dist;
    unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
      apply Rabs_pos_lt.
  unfold Rdiv; apply prod_neq_R0;
    [ assumption | apply Rinv_neq_0_compat; discrR ].
exact Neq_2_0.
  intro; apply H5.
  split.
  unfold D_x, no_cond.
  split; trivial || assumption.
  assumption.
  change (R0 < Rabs (f x0 / R2)).
  apply Rabs_pos_lt; unfold Rdiv; apply prod_neq_R0.
  assumption.
  apply Rinv_neq_0_compat; discrR.
exact Neq_2_0.
Qed.
