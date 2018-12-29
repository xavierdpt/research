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
Require Import XSeqSeries.
Require Import XRtrigo1.
Require Import XRanalysis1.
Require Import XPSeries_reg.
Local Open Scope nat_scope.
Local Open Scope XR_scope.


(**********)
Lemma continuity_sin : continuity sin.
Proof.
  unfold continuity; intro.
  assert (H0 := continuity_cos (PI / R2 - x)).
  unfold continuity_pt in H0; unfold continue_in in H0; unfold limit1_in in H0;
    unfold limit_in in H0; simpl in H0; unfold R_dist in H0;
      unfold continuity_pt; unfold continue_in;
        unfold limit1_in; unfold limit_in;
          simpl; unfold R_dist; intros.
  elim (H0 _ H); intros.
  exists x0; intros.
  elim H1; intros.
  split.
  assumption.
  intros; rewrite <- (cos_shift x); rewrite <- (cos_shift x1); apply H3.
  elim H4; intros.
  split.
  unfold D_x, no_cond; split.
  trivial.
  red; intro; unfold D_x, no_cond in H5; elim H5; intros _ H8; elim H8;
    rewrite <- (Ropp_involutive x); rewrite <- (Ropp_involutive x1);
      apply Ropp_eq_compat; apply Rplus_eq_reg_l with (PI / R2);
        apply H7.
  replace (PI / R2 - x1 - (PI / R2 - x)) with (x - x1).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr'; apply H6.
  unfold Rminus.
  rewrite Rplus_comm.
  symmetry.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  reflexivity.
Qed.

Lemma CVN_R_sin :
  forall fn:nat -> R -> R,
    fn =
    (fun (N:nat) (x:R) => (-R1) ^ N / INR (fact (2 * N + 1)) * x ^ (2 * N)) ->
    CVN_R fn.
Proof.
  unfold CVN_R; unfold CVN_r; intros fn H r.
  exists (fun n:nat => / INR (fact (2 * n + 1)) * r ^ (2 * n)).
  cut
    { l:R |
        Un_cv
        (fun n:nat =>
          sum_f_R0
          (fun k:nat => Rabs (/ INR (fact (2 * k + 1)) * r ^ (2 * k))) n)
        l }.
  intros (x,p).
  exists x.
  split.
  apply p.
  intros; rewrite H; unfold Rdiv; do 2 rewrite Rabs_mult;
    rewrite pow_1_abs; rewrite Rmult_1_l.
  cut (R0 < / INR (fact (2 * n + 1))).
  intro; rewrite (Rabs_right _ (Rle_ge _ _ (Rlt_le _ _ H1))).
  apply Rmult_le_compat_l.
  left; apply H1.
  rewrite <- RPow_abs; apply pow_maj_Rabs.
  rewrite Rabs_Rabsolu; unfold Boule in H0; rewrite Rminus_0_r in H0; left;
    apply H0.
  apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  cut ((r:R) <> R0).
  intro; apply Alembert_C2.
  intro; apply Rabs_no_R0.
  apply prod_neq_R0.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  apply pow_nonzero; assumption.
  assert (H1 := Alembert_sin).
  unfold sin_n in H1; unfold Un_cv in H1; unfold Un_cv; intros.
  cut (R0 < eps / Rsqr r).
  intro; elim (H1 _ H3); intros N0 H4.
  exists N0; intros.
  unfold R_dist; assert (H6 := H4 _ H5).
  unfold R_dist in H5;
    replace
    (Rabs
      (Rabs (/ INR (fact (2 * S n + 1)) * r ^ (2 * S n)) /
        Rabs (/ INR (fact (2 * n + 1)) * r ^ (2 * n)))) with
    (Rsqr r *
      Rabs
      ((-R1) ^ S n / INR (fact (2 * S n + 1)) /
        ((-R1) ^ n / INR (fact (2 * n + 1))))).
  apply Rmult_lt_reg_l with (/ Rsqr r).
  apply Rinv_0_lt_compat; apply Rsqr_pos_lt; assumption.
  pattern (/ Rsqr r) at 1; rewrite <- (Rabs_right (/ Rsqr r)).
  rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_l.
  rewrite Rmult_0_r; rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite <- (Rmult_comm eps).
  apply H6.
  unfold Rsqr; apply prod_neq_R0; assumption.
  apply Rle_ge; left; apply Rinv_0_lt_compat; apply Rsqr_pos_lt; assumption.
  unfold Rdiv; rewrite (Rmult_comm (Rsqr r)); repeat rewrite Rabs_mult;
    rewrite Rabs_Rabsolu; rewrite pow_1_abs.
  rewrite Rmult_1_l.
  repeat rewrite Rmult_assoc; apply Rmult_eq_compat_l.
  rewrite Rinv_mult_distr.
  rewrite Rinv_involutive.
  rewrite Rabs_mult.
  rewrite Rabs_Rinv.
  rewrite pow_1_abs; rewrite Rinv_1; rewrite Rmult_1_l.
  rewrite Rinv_mult_distr.
  rewrite <- Rabs_Rinv.
  rewrite Rinv_involutive.
  rewrite Rabs_mult.
  do 2 rewrite Rabs_Rabsolu.
  rewrite (Rmult_comm (Rabs (r ^ (2 * S n)))).
  rewrite Rmult_assoc; apply Rmult_eq_compat_l.
  rewrite Rabs_Rinv.
  rewrite Rabs_Rabsolu.
  repeat rewrite Rabs_right.
  replace (r ^ (2 * S n)) with (r ^ (2 * n) * r * r).
  do 2 rewrite <- Rmult_assoc.
  rewrite <- Rinv_l_sym.
  unfold Rsqr. rewrite Rmult_1_l. reflexivity.
  apply pow_nonzero; assumption.
  replace (2 * S n)%nat with (S (S (2 * n))).
  simpl. rewrite Rmult_comm. repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l. rewrite Rmult_comm. reflexivity.
  ring.
  apply Rle_ge; apply pow_le; left; apply (cond_pos r).
  apply Rle_ge; apply pow_le; left; apply (cond_pos r).
  apply Rabs_no_R0; apply pow_nonzero; assumption.
  apply INR_fact_neq_0.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  apply Rabs_no_R0; apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  apply Rabs_no_R0; apply pow_nonzero; assumption.
  apply pow_nonzero; discrR.
  apply Rlt_not_eq. rewrite <- Ropp_0. apply Ropp_lt_contravar. exact Rlt_0_1.
  apply INR_fact_neq_0.
  apply pow_nonzero; discrR.
  apply Rlt_not_eq. rewrite <- Ropp_0. apply Ropp_lt_contravar. exact Rlt_0_1.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; apply Rsqr_pos_lt; assumption ].
  assert (H0 := cond_pos r); red; intro; rewrite H1 in H0;
    elim (Rlt_irrefl _ H0).
Qed.

(** (sin h)/h -> 1 when h -> 0 *)
Lemma derivable_pt_lim_sin_0 : derivable_pt_lim sin R0 R1.
Proof.
  unfold derivable_pt_lim; intros.
  set
    (fn := fun (N:nat) (x:R) => (-R1) ^ N / INR (fact (2 * N + 1)) * x ^ (2 * N)).
  cut (CVN_R fn).
  intro; cut (forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }).
  intro cv.
  set (r := mkposreal _ Rlt_0_1).
  cut (CVN_r fn r).
  intro; cut (forall (n:nat) (y:R), Boule R0 r y -> continuity_pt (fn n) y).
  intro; cut (Boule R0 r R0).
  intro; assert (H2 := SFL_continuity_pt _ cv _ X0 H0 _ H1).
  unfold continuity_pt in H2; unfold continue_in in H2; unfold limit1_in in H2;
    unfold limit_in in H2; simpl in H2; unfold R_dist in H2.
  elim (H2 _ H); intros alp H3.
  elim H3; intros.
  exists (mkposreal _ H4).
  simpl; intros.
  rewrite sin_0; rewrite Rplus_0_l; unfold Rminus; rewrite Ropp_0;
    rewrite Rplus_0_r.
  cut (Rabs (SFL fn cv h - SFL fn cv R0) < eps).
  intro; cut (SFL fn cv R0 = R1).
  intro; cut (SFL fn cv h = sin h / h).
  intro; rewrite H9 in H8; rewrite H10 in H8.
  apply H8.
  unfold SFL, sin.
  case (cv h) as (x,HUn).
  case (exist_sin (Rsqr h)) as (x0,Hsin).
  unfold Rdiv; rewrite (Rinv_r_simpl_m h x0 H6).
  eapply UL_sequence.
  apply HUn.
  unfold sin_in in Hsin; unfold sin_n, infinite_sum in Hsin;
    unfold SP, fn, Un_cv; intros.
  elim (Hsin _ H10); intros N0 H11.
  exists N0; intros.
  unfold R_dist; unfold R_dist in H11.
  replace
  (sum_f_R0 (fun k:nat => (-R1) ^ k / INR (fact (2 * k + 1)) * h ^ (2 * k)) n)
    with
      (sum_f_R0 (fun i:nat => (-R1) ^ i / INR (fact (2 * i + 1)) * Rsqr h ^ i) n).
  apply H11; assumption.
  apply sum_eq; intros; apply Rmult_eq_compat_l; unfold Rsqr;
    rewrite pow_sqr; reflexivity.
  unfold SFL, sin.
  case (cv R0) as (?,HUn).
  eapply UL_sequence.
  apply HUn.
  unfold SP, fn; unfold Un_cv; intros; exists 1%nat; intros.
  unfold R_dist;
    replace
    (sum_f_R0 (fun k:nat => (-R1) ^ k / INR (fact (2 * k + 1)) * R0 ^ (2 * k)) n)
    with R1.
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
  rewrite decomp_sum.
  simpl; rewrite Rmult_1_r; unfold Rdiv; rewrite Rinv_1;
    rewrite Rmult_1_r; pattern R1 at 1; rewrite <- Rplus_0_r;
      apply Rplus_eq_compat_l.
  symmetry ; apply sum_eq_R0; intros.
  rewrite Rmult_0_l; rewrite Rmult_0_r; reflexivity.
  unfold ge in H10; apply lt_le_trans with 1%nat; [ apply lt_n_Sn | apply H10 ].
  apply H5.
  split.
  unfold D_x, no_cond; split.
  trivial.
  apply (not_eq_sym (A:=R)); apply H6.
  unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r; apply H7.
  unfold Boule; unfold Rminus; rewrite Ropp_0;
    rewrite Rplus_0_r; rewrite Rabs_R0; apply (cond_pos r).
  intros; unfold fn;
    replace (fun x:R => (-R1) ^ n / INR (fact (2 * n + 1)) * x ^ (2 * n)) with
    (fct_cte ((-R1) ^ n / INR (fact (2 * n + 1))) * pow_fct (2 * n))%F;
    [ idtac | reflexivity ].
  apply continuity_pt_mult.
  apply derivable_continuous_pt.
  apply derivable_pt_const.
  apply derivable_continuous_pt.
  apply (derivable_pt_pow (2 * n) y).
  apply (X r).
  apply (CVN_R_CVS _ X).
  apply CVN_R_sin; unfold fn; reflexivity.
Qed.

(** ((cos h)-1)/h -> 0 when h -> 0 *)
Lemma derivable_pt_lim_cos_0 : derivable_pt_lim cos R0 R0.
Proof.
  unfold derivable_pt_lim; intros.
  assert (H0 := derivable_pt_lim_sin_0).
  unfold derivable_pt_lim in H0.
  cut (R0 < eps / R2).
  intro; elim (H0 _ H1); intros del H2.
  cut (continuity_pt sin R0).
  intro; unfold continuity_pt in H3; unfold continue_in in H3;
    unfold limit1_in in H3; unfold limit_in in H3; simpl in H3;
      unfold R_dist in H3.
  cut (R0 < eps / R2); [ intro | assumption ].
  elim (H3 _ H4); intros del_c H5.
  cut (R0 < Rmin del del_c).
  intro; set (delta := mkposreal _ H6).
  exists delta; intros.
  rewrite Rplus_0_l; replace (cos h - cos R0) with (-R2 * Rsqr (sin (h / R2))).
  unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r.
  change (-R2) with (-(R2)).
  unfold Rdiv; do 2 rewrite Ropp_mult_distr_l_reverse.
  rewrite Rabs_Ropp.
  replace (R2 * Rsqr (sin (h * / R2)) * / h) with
  (sin (h / R2) * (sin (h / R2) / (h / R2) - R1) + sin (h / R2)).
  apply Rle_lt_trans with
    (Rabs (sin (h / R2) * (sin (h / R2) / (h / R2) - R1)) + Rabs (sin (h / R2))).
  apply Rabs_triang.
  rewrite (double_var eps); apply Rplus_lt_compat.
  apply Rle_lt_trans with (Rabs (sin (h / R2) / (h / R2) - R1)).
  rewrite Rabs_mult; rewrite Rmult_comm;
    pattern (Rabs (sin (h / R2) / (h / R2) - R1)) at 2;
      rewrite <- Rmult_1_r; apply Rmult_le_compat_l.
  apply Rabs_pos.
  assert (H9 := SIN_bound (h / R2)).
  unfold Rabs; case (Rcase_abs (sin (h / R2))); intro.
  rewrite <- (Ropp_involutive R1).
  apply Ropp_le_contravar.
  elim H9; intros; assumption.
  elim H9; intros; assumption.
  cut (Rabs (h / R2) < del).
  intro; cut (h / R2 <> R0).
  intro; assert (H11 := H2 _ H10 H9).
  rewrite Rplus_0_l in H11; rewrite sin_0 in H11.
  rewrite Rminus_0_r in H11; apply H11.
  unfold Rdiv; apply prod_neq_R0.
  apply H7.
  apply Rinv_neq_0_compat; discrR.
exact Neq_2_0.
  apply Rlt_trans with (del / R2).
  unfold Rdiv; rewrite Rabs_mult.
  rewrite (Rabs_right (/ R2)).
  do 2 rewrite <- (Rmult_comm (/ R2)); apply Rmult_lt_compat_l.
  apply Rinv_0_lt_compat; exact Rlt_0_2.
  apply Rlt_le_trans with delta.
  apply H8.
  unfold delta; simpl; apply Rmin_l.
  apply Rle_ge; left; apply Rinv_0_lt_compat; exact Rlt_0_2.
  rewrite <- (Rplus_0_r (del / R2)); pattern del at 1;
    rewrite (double_var del); apply Rplus_lt_compat_l;
      unfold Rdiv; apply Rmult_lt_0_compat.
  apply (cond_pos del).
  apply Rinv_0_lt_compat; exact Rlt_0_2.
  elim H5; intros; assert (H11 := H10 (h / R2)).
  rewrite sin_0 in H11; do 2 rewrite Rminus_0_r in H11.
  apply H11.
  split.
  unfold D_x, no_cond; split.
  trivial.
  apply (not_eq_sym (A:=R)); unfold Rdiv; apply prod_neq_R0.
  apply H7.
  apply Rinv_neq_0_compat; discrR.
exact Neq_2_0.
  apply Rlt_trans with (del_c / R2).
  unfold Rdiv; rewrite Rabs_mult.
  rewrite (Rabs_right (/ R2)).
  do 2 rewrite <- (Rmult_comm (/ R2)).
  apply Rmult_lt_compat_l.
  apply Rinv_0_lt_compat; exact Rlt_0_2.
  apply Rlt_le_trans with  delta.
  apply H8.
  unfold delta; simpl; apply Rmin_r.
  apply Rle_ge; left; apply Rinv_0_lt_compat; exact Rlt_0_2.
  rewrite <- (Rplus_0_r (del_c / R2)); pattern del_c at 2;
    rewrite (double_var del_c); apply Rplus_lt_compat_l.
  unfold Rdiv; apply Rmult_lt_0_compat.
  apply H9.
  apply Rinv_0_lt_compat; exact Rlt_0_2.
  rewrite Rmult_minus_distr_l; rewrite Rmult_1_r; unfold Rminus;
    rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
      rewrite (Rmult_comm R2); unfold Rdiv, Rsqr.
  repeat rewrite Rmult_assoc.
  repeat apply Rmult_eq_compat_l.
  rewrite Rinv_mult_distr.
  rewrite Rinv_involutive.
  apply Rmult_comm.
exact Neq_2_0.
  apply H7.
  apply Rinv_neq_0_compat; discrR.
exact Neq_2_0.
  pattern h at 2; replace h with (R2 * (h / R2)).
  rewrite (cos_2a_sin (h / R2)).
  rewrite cos_0; unfold Rsqr.
{
symmetry.
unfold Rminus.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
repeat rewrite Ropp_mult_distr_l.
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
reflexivity.
}
  unfold Rdiv; rewrite <- Rmult_assoc; apply Rinv_r_simpl_m.
exact Neq_2_0.
  unfold Rmin; case (Rle_dec del del_c); intro.
  apply (cond_pos del).
  elim H5; intros; assumption.
  apply continuity_sin.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ assumption | apply Rinv_0_lt_compat; exact Rlt_0_2 ].
Qed.

(**********)
Theorem derivable_pt_lim_sin : forall x:R, derivable_pt_lim sin x (cos x).
Proof.
  intro; assert (H0 := derivable_pt_lim_sin_0).
  assert (H := derivable_pt_lim_cos_0).
  unfold derivable_pt_lim in H0, H.
  unfold derivable_pt_lim; intros.
  cut (R0 < eps / R2);
    [ intro
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ apply H1 | apply Rinv_0_lt_compat; exact Rlt_0_2 ] ].
  elim (H0 _ H2); intros alp1 H3.
  elim (H _ H2); intros alp2 H4.
  set (alp := Rmin alp1 alp2).
  cut (R0 < alp).
  intro; exists (mkposreal _ H5); intros.
  replace ((sin (x + h) - sin x) / h - cos x) with
  (sin x * ((cos h - R1) / h) + cos x * (sin h / h - R1)).
  apply Rle_lt_trans with
    (Rabs (sin x * ((cos h - R1) / h)) + Rabs (cos x * (sin h / h - R1))).
  apply Rabs_triang.
  rewrite (double_var eps); apply Rplus_lt_compat.
  apply Rle_lt_trans with (Rabs ((cos h - R1) / h)).
  rewrite Rabs_mult; rewrite Rmult_comm;
    pattern (Rabs ((cos h - R1) / h)) at 2; rewrite <- Rmult_1_r;
      apply Rmult_le_compat_l.
  apply Rabs_pos.
  assert (H8 := SIN_bound x); elim H8; intros.
  unfold Rabs; case (Rcase_abs (sin x)); intro.
  rewrite <- (Ropp_involutive R1).
  apply Ropp_le_contravar; assumption.
  assumption.
  cut (Rabs h < alp2).
  intro; assert (H9 := H4 _ H6 H8).
  rewrite cos_0 in H9; rewrite Rplus_0_l in H9; rewrite Rminus_0_r in H9;
    apply H9.
  apply Rlt_le_trans with alp.
  apply H7.
  unfold alp; apply Rmin_r.
  apply Rle_lt_trans with (Rabs (sin h / h - R1)).
  rewrite Rabs_mult; rewrite Rmult_comm;
    pattern (Rabs (sin h / h - R1)) at 2; rewrite <- Rmult_1_r;
      apply Rmult_le_compat_l.
  apply Rabs_pos.
  assert (H8 := COS_bound x); elim H8; intros.
  unfold Rabs; case (Rcase_abs (cos x)); intro.
  rewrite <- (Ropp_involutive R1); apply Ropp_le_contravar; assumption.
  assumption.
  cut (Rabs h < alp1).
  intro; assert (H9 := H3 _ H6 H8).
  rewrite sin_0 in H9; rewrite Rplus_0_l in H9; rewrite Rminus_0_r in H9;
    apply H9.
  apply Rlt_le_trans with alp.
  apply H7.
  unfold alp; apply Rmin_l.
  rewrite sin_plus.
{
  unfold Rminus.
  unfold Rdiv.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rmult_1_r.
  repeat rewrite <- Rmult_assoc.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  reflexivity.
}
  unfold alp; unfold Rmin; case (Rle_dec alp1 alp2); intro.
  apply (cond_pos alp1).
  apply (cond_pos alp2).
Qed.

Lemma derivable_pt_lim_cos : forall x:R, derivable_pt_lim cos x (- sin x).
Proof.
  intro; cut (forall h:R, sin (h + PI / R2) = cos h).
  intro; replace (- sin x) with (cos (x + PI / R2) * (R1 + R0)).
  generalize (derivable_pt_lim_comp (id + fct_cte (PI / R2))%F sin); intros.
  cut (derivable_pt_lim (id + fct_cte (PI / R2)) x (R1 + R0)).
  cut (derivable_pt_lim sin ((id + fct_cte (PI / R2))%F x) (cos (x + PI / R2))).
  intros; generalize (H0 _ _ _ H2 H1);
    replace (comp sin (id + fct_cte (PI / R2))%F) with
    (fun x:R => sin (x + PI / R2)); [ idtac | reflexivity ].
  unfold derivable_pt_lim; intros.
  elim (H3 eps H4); intros.
  exists x0.
  intros; rewrite <- (H (x + h)); rewrite <- (H x); apply H5; assumption.
  apply derivable_pt_lim_sin.
  apply derivable_pt_lim_plus.
  apply derivable_pt_lim_id.
  apply derivable_pt_lim_const.
  rewrite sin_cos; rewrite <- (Rplus_comm x).
{
  rewrite Ropp_involutive.
  rewrite Rplus_0_r.
  rewrite Rmult_1_r.
  reflexivity.
}
  intro; rewrite cos_sin; rewrite Rplus_comm; reflexivity.
Qed.

Lemma derivable_pt_sin : forall x:R, derivable_pt sin x.
Proof.
  unfold derivable_pt; intro.
  exists (cos x).
  apply derivable_pt_lim_sin.
Qed.

Lemma derivable_pt_cos : forall x:R, derivable_pt cos x.
Proof.
  unfold derivable_pt; intro.
  exists (- sin x).
  apply derivable_pt_lim_cos.
Qed.

Lemma derivable_sin : derivable sin.
Proof.
  unfold derivable; intro; apply derivable_pt_sin.
Qed.

Lemma derivable_cos : derivable cos.
Proof.
  unfold derivable; intro; apply derivable_pt_cos.
Qed.

Lemma derive_pt_sin :
  forall x:R, derive_pt sin x (derivable_pt_sin _) = cos x.
Proof.
  intros; apply derive_pt_eq_0.
  apply derivable_pt_lim_sin.
Qed.

Lemma derive_pt_cos :
  forall x:R, derive_pt cos x (derivable_pt_cos _) = - sin x.
Proof.
  intros; apply derive_pt_eq_0.
  apply derivable_pt_lim_cos.
Qed.
