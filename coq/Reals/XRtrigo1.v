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
Require Export XRtrigo_fun.
Require Export XRtrigo_def.
Require Export XRtrigo_alt.
Require Export XCos_rel.
Require Export XCos_plus.
Require Import ZArith_base.
Require Import Zcomplements.
Require Import XRanalysis1.
Require Import XRsqrt_def. 
Require Import XPSeries_reg.

Local Open Scope nat_scope.
Local Open Scope XR_scope.

Lemma CVN_R_cos :
  forall fn:nat -> R -> R,
    fn = (fun (N:nat) (x:R) => (-R1) ^ N / INR (fact (2 * N)) * x ^ (2 * N)) ->
    CVN_R fn.
Proof.
  unfold CVN_R in |- *; intros.
  cut ((r:R) <> R0).
  intro hyp_r; unfold CVN_r in |- *.
  exists (fun n:nat => / INR (fact (2 * n)) * r ^ (2 * n)).
  cut
    { l:R |
        Un_cv
        (fun n:nat =>
          sum_f_R0 (fun k:nat => Rabs (/ INR (fact (2 * k)) * r ^ (2 * k)))
          n) l }.
  intros (x,p).
  exists x.
  split.
  apply p.
  intros; rewrite H; unfold Rdiv in |- *; do 2 rewrite Rabs_mult.
  rewrite pow_1_abs; rewrite Rmult_1_l.
  cut (R0 < / INR (fact (2 * n))).
  intro; rewrite (Rabs_right _ (Rle_ge _ _ (Rlt_le _ _ H1))).
  apply Rmult_le_compat_l.
  left; apply H1.
  rewrite <- RPow_abs; apply pow_maj_Rabs.
  rewrite Rabs_Rabsolu.
  unfold Boule in H0; rewrite Rminus_0_r in H0.
  left; apply H0.
  apply Rinv_0_lt_compat; apply INR_fact_lt_0.
  apply Alembert_C2.
  intro; apply Rabs_no_R0.
  apply prod_neq_R0.
  apply Rinv_neq_0_compat.
  apply INR_fact_neq_0.
  apply pow_nonzero; assumption.
  assert (H0 := Alembert_cos).
  unfold cos_n in H0; unfold Un_cv in H0; unfold Un_cv in |- *; intros.
  cut (R0 < eps / Rsqr r).
  intro; elim (H0 _ H2); intros N0 H3.
  exists N0; intros.
  unfold R_dist in |- *; assert (H5 := H3 _ H4).
  unfold R_dist in H5;
    replace
    (Rabs
      (Rabs (/ INR (fact (2 * S n)) * r ^ (2 * S n)) /
        Rabs (/ INR (fact (2 * n)) * r ^ (2 * n)))) with
    (Rsqr r *
      Rabs ((-R1) ^ S n / INR (fact (2 * S n)) / ((-R1) ^ n / INR (fact (2 * n))))).
  apply Rmult_lt_reg_l with (/ Rsqr r).
  apply Rinv_0_lt_compat; apply Rsqr_pos_lt; assumption.
  pattern (/ Rsqr r) at 1 in |- *; replace (/ Rsqr r) with (Rabs (/ Rsqr r)).
  rewrite <- Rabs_mult; rewrite Rmult_minus_distr_l; rewrite Rmult_0_r;
    rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l; rewrite <- (Rmult_comm eps); apply H5.
  unfold Rsqr in |- *; apply prod_neq_R0; assumption.
  rewrite Rabs_Rinv.
  rewrite Rabs_right.
  reflexivity.
  apply Rle_ge; apply Rle_0_sqr.
  unfold Rsqr in |- *; apply prod_neq_R0; assumption.
  rewrite (Rmult_comm (Rsqr r)); unfold Rdiv in |- *; repeat rewrite Rabs_mult;
    rewrite Rabs_Rabsolu; rewrite pow_1_abs; rewrite Rmult_1_l;
      repeat rewrite Rmult_assoc; apply Rmult_eq_compat_l.
  rewrite Rabs_Rinv.
  rewrite Rabs_mult; rewrite (pow_1_abs n); rewrite Rmult_1_l;
    rewrite <- Rabs_Rinv.
  rewrite Rinv_involutive.
  rewrite Rinv_mult_distr.
  rewrite Rabs_Rinv.
  rewrite Rinv_involutive.
  rewrite (Rmult_comm (Rabs (Rabs (r ^ (2 * S n))))); rewrite Rabs_mult;
    rewrite Rabs_Rabsolu; rewrite Rmult_assoc; apply Rmult_eq_compat_l.
  rewrite Rabs_Rinv.
  do 2 rewrite Rabs_Rabsolu; repeat rewrite Rabs_right.
  replace (r ^ (2 * S n)) with (r ^ (2 * n) * r * r).
  repeat rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  unfold Rsqr in |- *.
rewrite Rmult_1_l. reflexivity.
  apply pow_nonzero; assumption.
  replace (2 * S n)%nat with (S (S (2 * n))).
  simpl in |- *.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Rmult_comm.
reflexivity.
simpl. rewrite <- plus_n_Sm. reflexivity.
  apply Rle_ge; apply pow_le; left; apply (cond_pos r).
  apply Rle_ge; apply pow_le; left; apply (cond_pos r).
  apply Rabs_no_R0; apply pow_nonzero; assumption.
  apply Rabs_no_R0; apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  apply Rabs_no_R0; apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  apply Rabs_no_R0; apply pow_nonzero; assumption.
  apply INR_fact_neq_0.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  apply prod_neq_R0.
  apply pow_nonzero.
apply Rlt_dichotomy_converse. left. rewrite <- Ropp_0. apply Ropp_lt_contravar. exact Rlt_0_1.
  apply Rinv_neq_0_compat; apply INR_fact_neq_0.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  apply H1.
  apply Rinv_0_lt_compat; apply Rsqr_pos_lt; assumption.
  assert (H0 := cond_pos r); red in |- *; intro; rewrite H1 in H0;
    elim (Rlt_irrefl _ H0).
Qed.

(**********)
Lemma continuity_cos : continuity cos.
Proof.
  set (fn := fun (N:nat) (x:R) => (-R1) ^ N / INR (fact (2 * N)) * x ^ (2 * N)).
  cut (CVN_R fn).
  intro; cut (forall x:R, { l:R | Un_cv (fun N:nat => SP fn N x) l }).
  intro cv; cut (forall n:nat, continuity (fn n)).
  intro; cut (forall x:R, cos x = SFL fn cv x).
  intro; cut (continuity (SFL fn cv) -> continuity cos).
  intro; apply H1.
  apply SFL_continuity; assumption.
  unfold continuity in |- *; unfold continuity_pt in |- *;
    unfold continue_in in |- *; unfold limit1_in in |- *;
      unfold limit_in in |- *; simpl in |- *; unfold R_dist in |- *;
        intros.
  elim (H1 x _ H2); intros.
  exists x0; intros.
  elim H3; intros.
  split.
  apply H4.
  intros; rewrite (H0 x); rewrite (H0 x1); apply H5; apply H6.
  intro; unfold cos, SFL in |- *.
  case (cv x) as (x1,HUn); case (exist_cos (Rsqr x)) as (x0,Hcos); intros.
  symmetry; eapply UL_sequence.
  apply HUn.
  unfold cos_in, infinite_sum in Hcos; unfold Un_cv in |- *; intros.
  elim (Hcos _ H0); intros N0 H1.
  exists N0; intros.
  unfold R_dist in H1; unfold R_dist, SP in |- *.
  replace (sum_f_R0 (fun k:nat => fn k x) n) with
  (sum_f_R0 (fun i:nat => cos_n i * Rsqr x ^ i) n).
  apply H1; assumption.
  apply sum_eq; intros.
  unfold cos_n, fn in |- *; apply Rmult_eq_compat_l.
  unfold Rsqr in |- *; rewrite pow_sqr; reflexivity.
  intro; unfold fn in |- *;
    replace (fun x:R => (-R1) ^ n / INR (fact (2 * n)) * x ^ (2 * n)) with
    (fct_cte ((-R1) ^ n / INR (fact (2 * n))) * pow_fct (2 * n))%F;
    [ idtac | reflexivity ].
  apply continuity_mult.
  apply derivable_continuous; apply derivable_const.
  apply derivable_continuous; apply (derivable_pow (2 * n)).
  apply CVN_R_CVS; apply X.
  apply CVN_R_cos; unfold fn in |- *; reflexivity.
Qed.

Lemma sin_gt_cos_7_8 : sin (R7 / R8) > cos (R7 / R8).
Proof. 

cut (R0<R8);try intro.
cut (R0<R4);try intro.
cut (R0<R7);try intro.
cut (R0<R2);try intro.
cut (R0<R6);try intro.
cut (R6+R1=R7); try intro.
cut (R4 + R2 = R6);try intro.
cut (R0 < / R2);try intro.
cut (R1 + R7 = R8);try intro.
cut (R6 <> R0);try intro.
cut (R0 < / R6); try intro.
cut(R12 + R12 <> R0);try intro.
cut(R0 < R12 + R12);try intro.
cut(R8 <> R0);try intro.

assert (lo1 : R0 <= R7/R8).
{
left.
apply Rmult_lt_reg_r with R8.
assumption.
rewrite Rmult_0_l.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
assumption.
assumption.
}
assert (up1 : R7/R8 <= R4).
{
left.
apply Rmult_lt_reg_r with R8.
assumption.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R8.
unfold R7.
unfold R4.
unfold R3.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
rewrite Rmult_1_l.
apply Rplus_lt_le_compat.
apply Rplus_lt_le_compat.
apply Rplus_lt_le_compat.
apply Rplus_lt_le_compat.
apply Rplus_lt_le_compat.
apply Rplus_lt_le_compat.
pattern R1 at 1;rewrite <- Rplus_0_l.
apply Rplus_lt_le_compat.
do 24 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat apply Rplus_lt_compat;exact Rlt_0_1.
right;reflexivity.
right;reflexivity.
right;reflexivity.
right;reflexivity.
right;reflexivity.
right;reflexivity.
right;reflexivity.
assumption.
}
assert (lo : -R2 <= R7/R8).
{
  apply Rle_trans with R0.
  rewrite <- Ropp_0.
  apply Ropp_le_contravar.
  left. exact Rlt_0_2.
  assumption.
}
assert (up : R7/R8 <= R2).
{
  left.
  apply Rmult_lt_reg_r with R8.
  assumption.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  unfold R8.
  unfold R7.
  unfold R4.
  unfold R3.
  unfold R2.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_lt_le_compat; [ idtac | right ; reflexivity ].
  apply Rplus_lt_le_compat; [ idtac | right ; reflexivity ].
  apply Rplus_lt_le_compat; [ idtac | right ; reflexivity ].
  apply Rplus_lt_le_compat; [ idtac | right ; reflexivity ].
  apply Rplus_lt_le_compat; [ idtac | right ; reflexivity ].
  apply Rplus_lt_le_compat; [ idtac | right ; reflexivity ].
  pattern R1 at 1 ; rewrite <- Rplus_0_l.
  apply Rplus_lt_le_compat; [ idtac | right ; reflexivity ].
  do 8 (pattern R0 at 1;rewrite <- Rplus_0_l).
  repeat apply Rplus_lt_compat;exact Rlt_0_1.
  assumption.
}
destruct (pre_sin_bound _ 0 lo1 up1) as [lower _ ].
destruct (pre_cos_bound _ 0 lo up) as [_ upper].
apply Rle_lt_trans with (1 := upper).
apply Rlt_le_trans with (2 := lower).
unfold cos_approx, sin_approx.
simpl sum_f_R0.
unfold cos_term, sin_term; simpl fact; rewrite !INR_IZR_INZ.
simpl plus; simpl mult; simpl Z_of_nat.

change (IZR 2) with R2.
simpl.
repeat rewrite Rmult_1_l.
change (IZR 1) with R1.
unfold Rdiv.
repeat rewrite Rinv_1.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_1_l.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_1_l.
repeat rewrite Ropp_involutive.
replace (IZR 24) with (R12 + R12).
replace (IZR 6) with R6.

2:{
unfold R6.
unfold R3.
unfold R2.
change R1 with (IZR 1).
repeat rewrite <- plus_IZR.
simpl.
reflexivity.
}

2:{
unfold R12.
unfold R6.
unfold R3.
unfold R2.
change R1 with (IZR 1).
repeat rewrite <- plus_IZR.
simpl.
reflexivity.
}

repeat rewrite Ropp_mult_distr_l.
apply Rmult_lt_reg_r with R2.

2:{
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.

apply Rmult_lt_reg_r with R8.
2:{
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.

apply Rmult_lt_reg_r with R8.
2:{
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/ R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
rewrite Rmult_1_l.
rewrite (Rmult_comm (/R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
rewrite (Rmult_comm (/R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
rewrite (Rmult_comm (/R8)).
rewrite (Rmult_comm (/R8)).
rewrite (Rmult_comm (/R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
repeat rewrite Rmult_assoc.

apply Rmult_lt_reg_r with R8.
2:{
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.

apply Rmult_lt_reg_r with R8.
2:{
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite (Rmult_comm (/R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
rewrite (Rmult_comm (/R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
rewrite (Rmult_comm (/R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.

apply Rmult_lt_reg_r with R6.
2:{
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R6)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.

apply Rmult_lt_reg_r with (R12+R12).
2:{

rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/ (R12+R12))).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.

repeat rewrite <- Rmult_assoc.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
pattern R8 at 1;replace R8 with (R7+R1).
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
rewrite (Rmult_comm R2).
repeat rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
repeat rewrite <- Rplus_assoc.
rewrite Rmult_1_r.
rewrite (Rmult_comm R2).
unfold R2 at 4.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
unfold R2 at 1.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
unfold R7 at 9.
rewrite (Rplus_comm R4).
unfold R3.
rewrite (Rplus_comm R2).
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
repeat rewrite <- Rplus_assoc.
unfold R2 at 3.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
repeat rewrite <- Rplus_assoc.
unfold R2 at 1.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
pattern R8 at 1;replace R8 with (R1+R7).
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
repeat rewrite <- Rplus_assoc.
unfold R7 at 1.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
repeat rewrite <- Rplus_assoc.
unfold R7 at 9.
rewrite (Rplus_comm R4).
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
repeat rewrite <- Rplus_assoc.
unfold R8 at 1.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rplus_assoc.
apply Rplus_lt_compat_l.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
pattern R8 at 6;replace R8 with (R1+R7).
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
repeat rewrite Rmult_assoc.
pattern R8 at 2;rewrite (Rmult_comm R8).
repeat rewrite Rmult_assoc.
pattern R12 at 2;rewrite (Rmult_comm R12).
repeat rewrite <- Rmult_assoc.
pattern R6 at 5;replace R6 with (R4+R2).
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
apply Rplus_lt_compat_r.
unfold R4 at 2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
rewrite <- Rplus_0_l.
apply Rplus_lt_compat_r.
replace R12 with (R2*R6).
repeat rewrite <- Rmult_assoc.
rewrite <- (Rmult_plus_distr_r _ _ R6).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R6 R8).
repeat rewrite <- Rmult_assoc.
rewrite <- (Rmult_plus_distr_r _ _ R6).
rewrite <- (Rmult_plus_distr_r _ _ R6).
rewrite <- (Rmult_plus_distr_r _ _ R6).
apply Ropp_lt_cancel.
rewrite Ropp_0.
rewrite Ropp_mult_distr_l.
repeat rewrite Ropp_plus_distr.
repeat rewrite Ropp_mult_distr_l.
repeat rewrite Ropp_involutive.
apply Rmult_lt_reg_r with (/R6).
2:{
rewrite Rmult_0_l.
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
repeat rewrite <- Rmult_assoc.
rewrite Rmult_1_r.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
pattern R8 at 1;replace R8 with (R1+R7).
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
rewrite Rmult_1_r.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R2).
repeat rewrite <- Rmult_assoc.
unfold R2 at 2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
repeat rewrite <- Ropp_mult_distr_l.
rewrite Rplus_opp_r.
rewrite Rplus_0_l.
rewrite (Rmult_comm R4).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R4).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R2).
rewrite (Rmult_comm R6).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R2).
rewrite (Rmult_comm R4).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R2).
rewrite (Rmult_comm R7).
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm R7).
repeat rewrite <- Rmult_assoc.
replace (R8 * R6 * R2 * R8 * R7 * R7) with (R8 * R8 * R7 * R7 * R6 * R2).
pattern R8 at 3;replace R8 with (R1+R7).
repeat rewrite Ropp_mult_distr_l.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
repeat rewrite <- (Rmult_plus_distr_r _ _ R2).
apply Rmult_lt_reg_r with (/R2).
2:{
rewrite Rmult_0_l.
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
repeat rewrite <- Rmult_assoc.
pattern R6 at 2;replace R6 with (R4+R2).
repeat rewrite Rmult_plus_distr_l.
repeat rewrite <- Rplus_assoc.
pattern R7 at 3;replace R7 with (R6+R1).
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Rplus_assoc.
repeat rewrite <- Ropp_mult_distr_l.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
rewrite Rplus_comm.
repeat rewrite Ropp_mult_distr_l.
repeat rewrite <- Rplus_assoc.
rewrite Rmult_1_r.
pattern R7 at 1;replace R7 with (R6+R1).
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
repeat rewrite <- Ropp_mult_distr_l.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
do 4 (pattern R0 at 1;rewrite <- Rplus_0_l).

repeat apply Rplus_lt_compat;repeat apply Rmult_lt_0_compat;try assumption.

exact Neq_2_0.

}

assumption.

repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
reflexivity.

assumption.

}

assumption.
unfold R12.
unfold R2.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
reflexivity.

unfold R8.
unfold R7.
unfold R3.
repeat rewrite Rplus_assoc.
fold R2.
fold R4.
reflexivity.

assumption.

}

assumption.
assumption.

}

assumption.
assumption.
assumption.
assumption.
assumption.

}

assumption.
assumption.

}

assumption.
assumption.
assumption.
assumption.
assumption.

}

assumption.
assumption.

}

assumption.
exact Neq_2_0.

}

assumption.
apply Rlt_irrefl with R0.
pattern R0 at 2;rewrite <- H12.
assumption.

unfold R12.
unfold R6.
unfold R3.
unfold R2.
repeat rewrite <- Rplus_assoc.
do 23 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat apply Rplus_lt_compat;exact Rlt_0_1.

apply Rlt_irrefl with R0.
pattern R0 at 2;rewrite <- H10.
unfold R12.
unfold R6.
unfold R3.
unfold R2.
repeat rewrite <- Rplus_assoc.
do 23 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat apply Rplus_lt_compat;exact Rlt_0_1.

apply Rinv_0_lt_compat.
assumption.

apply Rlt_irrefl with R0.
pattern R0 at 2;rewrite <- H8.
assumption.

unfold R7.
rewrite (Rplus_comm R4).
unfold R3.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm R2).
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm R4).
repeat rewrite <- Rplus_assoc.
fold R2.
fold R4.
fold R8.
reflexivity.

apply Rinv_0_lt_compat.
assumption.

unfold R6.
unfold R4.
unfold R3.
unfold R2.
repeat rewrite <- Rplus_assoc.
reflexivity.

unfold R7.
unfold R6.
unfold R4.
unfold R3.
unfold R2.
repeat rewrite <- Rplus_assoc.
reflexivity.

unfold R6.
pattern R0 at 1;rewrite <- Rplus_0_l.
apply Rplus_lt_compat;exact Rlt_0_3.

exact Rlt_0_2.

unfold R7.
unfold R4.
unfold R3.
unfold R2.
do 6 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_lt_compat;exact Rlt_0_1.

unfold R4.
pattern R0 at 1;rewrite <- Rplus_0_l.
apply Rplus_lt_compat;exact Rlt_0_2.

unfold R8.
unfold R4.
do 3 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_lt_compat;exact Rlt_0_2.


Qed.

Remark Rlt_0_7 : R0 < R7.
unfold R7. unfold R4. unfold R3.  unfold R2.
do 6 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_lt_compat;exact Rlt_0_1.
Qed.

Remark Rlt_0_8 : R0 < R8.
unfold R8. unfold R4.
do 3 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_lt_compat;exact Rlt_0_2.
Qed.

Remark Neq_8_0 : R8 <> R0.
apply Rgt_not_eq.
unfold Rgt.
exact Rlt_0_8.
Qed.

Remark lt_0_frac_7_8: R0 < R7 / R8.
unfold Rdiv.
apply Rmult_lt_reg_r with R8.
exact Rlt_0_8.
rewrite Rmult_0_l.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
exact Rlt_0_7.
exact Neq_8_0.
Qed.

Remark Rlt_7_8 : R7 < R8.
unfold R7.
unfold R8.
apply Rplus_le_lt_compat.
right. reflexivity.
unfold R3.
unfold R4.
apply Rplus_le_lt_compat.
right. reflexivity.
unfold R2.
pattern R1 at 1;rewrite <- Rplus_0_l.
apply Rplus_lt_le_compat.
exact Rlt_0_1.
right. reflexivity.
Qed.

Remark Neq_4_0 : R4 <> R0.
intro eq.
apply Rlt_irrefl with R0.
pattern R0 at 2;rewrite <- eq.
exact Rlt_0_4.
Qed.

Definition PI_2_aux : {z | R7/R8 <= z <= R7/R4 /\ -cos z = R0}.
assert (cc : continuity (fun r =>- cos r)).
 apply continuity_opp, continuity_cos.
assert (cvp : R0 < cos (R7/R8)).
 assert (int78 : -R2 <= R7/R8 <= R2).
 {
    split.
    {
apply Rle_trans with R0.
apply Ropp_le_cancel.
rewrite Ropp_involutive.
rewrite Ropp_0.
left. exact Rlt_0_2.
left. exact lt_0_frac_7_8.
    }
    {
left.
apply Rmult_lt_reg_r with R8.
exact Rlt_0_8.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
pattern R7;rewrite <- Rplus_0_l.
apply Rplus_lt_compat.
exact Rlt_0_8.

exact Rlt_7_8.

exact Neq_8_0.
    }
  }
 destruct int78 as [lower upper].
 case (pre_cos_bound _ 0 lower upper).
 unfold cos_approx; simpl sum_f_R0; unfold cos_term.
 intros cl _; apply Rlt_le_trans with (2 := cl); simpl.
{
unfold Rdiv.
rewrite Rinv_1.
repeat rewrite Rmult_1_r.
rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_1_l.
fold R2.
apply Rmult_lt_reg_r with R2.
exact Rlt_0_2.
rewrite Rmult_0_l.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Ropp_mult_distr_l.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite Rmult_1_l.
apply Rplus_lt_reg_l with (-R2).
rewrite Rplus_0_r.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
repeat rewrite <- Ropp_mult_distr_l.
apply Ropp_lt_contravar.
apply Rmult_lt_reg_r with (R8*R8).
apply Rmult_lt_0_compat;exact Rlt_0_8.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R8)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
{
apply Rmult_gt_0_lt_compat.
unfold Rgt. exact Rlt_0_7.
unfold Rgt. pattern R0 ; rewrite <- Rplus_0_l. apply Rplus_lt_compat;exact Rlt_0_8.
pattern R7 ; rewrite <- Rplus_0_l. apply Rplus_lt_compat.
exact Rlt_0_8.
exact Rlt_7_8.
exact Rlt_7_8.
}
exact Neq_8_0.
exact Neq_8_0.
exact Neq_2_0.
}
assert (cun : cos (R7/R4) < R0).
 replace (R7/R4) with (R7/R8 + R7/R8).
2:{
  unfold Rdiv.
  rewrite <- Rmult_plus_distr_l.
  apply Rmult_eq_compat_l.
  pattern (/R8);rewrite <- Rmult_1_l.
  rewrite <- Rmult_plus_distr_r.
  fold R2.
  apply Rmult_eq_reg_l with (/R2).
  rewrite <- Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_l.
  rewrite <- Rinv_mult_distr.
  unfold R2.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  fold R8.
  reflexivity.
  exact Neq_2_0.
  exact Neq_4_0.
  exact Neq_2_0.
  intro eq.
  apply Rlt_irrefl with R0.
  pattern R0 at 2;rewrite <- eq.
  apply Rinv_0_lt_compat.
  exact Rlt_0_2.
}
 rewrite cos_plus.
 apply Rlt_minus; apply Rsqr_incrst_1.
   exact sin_gt_cos_7_8.
  apply Rlt_le; assumption.
 apply Rlt_le; apply Rlt_trans with (1 := cvp); exact sin_gt_cos_7_8.
apply IVT; auto.
{
  unfold Rdiv.
  apply Rmult_lt_compat_l.
  exact Rlt_0_7.
  apply Rinv_lt_contravar.
  unfold R8. unfold R4. unfold R2.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_l.
  repeat rewrite <- Rplus_assoc.
  do 31 (pattern R0 at 1;rewrite <- Rplus_0_l).
  repeat apply Rplus_lt_compat;exact Rlt_0_1.
  unfold R8.
  pattern R4 at 1;rewrite <- Rplus_0_l.
  apply Rplus_lt_le_compat.
  exact Rlt_0_4.
  right. reflexivity.
}
{
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  assumption.
}
{
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  assumption.
}
Qed.

Definition PI2 := proj1_sig PI_2_aux.

Definition PI := R2 * PI2.

Lemma cos_pi2 : cos PI2 = R0.
unfold PI2; case PI_2_aux; simpl.
intros x [_ q]; rewrite <- (Ropp_involutive (cos x)), q; apply Ropp_0.
Qed.

Lemma pi2_int : R7/R8 <= PI2 <= R7/R4.
unfold PI2; case PI_2_aux; simpl; tauto.
Qed.

(**********)
Lemma cos_minus : forall x y:R, cos (x - y) = cos x * cos y + sin x * sin y.
Proof.
  intros; unfold Rminus in |- *; rewrite cos_plus.
  rewrite <- cos_sym; rewrite sin_antisym.
  unfold Rminus.
  apply Rplus_eq_compat_l.
  rewrite <- Ropp_mult_distr_r.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

(**********)
Lemma sin2_cos2 : forall x:R, Rsqr (sin x) + Rsqr (cos x) = R1.
Proof.
  intro; unfold Rsqr in |- *; rewrite Rplus_comm; rewrite <- (cos_minus x x);
    unfold Rminus in |- *; rewrite Rplus_opp_r; apply cos_0.
Qed.

Lemma cos2 : forall x:R, Rsqr (cos x) = R1 - Rsqr (sin x).
Proof.
  intros x; rewrite <- (sin2_cos2 x).
  unfold Rminus.
  rewrite Rplus_comm.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma sin2 : forall x:R, Rsqr (sin x) = R1 - Rsqr (cos x).
Proof.
  intro x; generalize (cos2 x); intro H1; rewrite H1.
  unfold Rminus in |- *; rewrite Ropp_plus_distr; rewrite <- Rplus_assoc;
    rewrite Rplus_opp_r; rewrite Rplus_0_l; symmetry  in |- *;
      apply Ropp_involutive.
Qed.

(**********)
Lemma cos_PI2 : cos (PI / R2) = R0.
Proof.
 unfold PI; generalize cos_pi2; replace ((R2 * PI2)/R2) with PI2.
  tauto.
  unfold Rdiv.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_l.
  reflexivity.
  exact Neq_2_0.
Qed.

Remark Rlt_0_6 : R0 < R6.
pattern R0;rewrite <- Rplus_0_l.
unfold R6.
apply Rplus_lt_compat;exact Rlt_0_3.
Qed.

Remark Neq_6_0 : R6 <> R0.
apply Rgt_not_eq.
exact Rlt_0_6.
Qed.

Lemma sin_pos_tech : forall x, R0 < x < R2 -> R0 < sin x. 
intros x [int1 int2].
assert (lo : R0 <= x) by (apply Rlt_le; assumption).
assert (up : x <= R4).
{
  apply Rlt_le.
  apply Rlt_trans with (1:=int2).
  unfold R4.
  pattern R2 at 1;rewrite <- Rplus_0_l.
  apply Rplus_lt_le_compat.
  exact Rlt_0_2.
  right. reflexivity.
}
destruct (pre_sin_bound _ 0 lo up) as [t _]; clear lo up.
apply Rlt_le_trans with (2:= t); clear t.
unfold sin_approx; simpl sum_f_R0; unfold sin_term; simpl.

unfold Rdiv.
rewrite Rinv_1.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
apply Rplus_lt_reg_l with (-x).
rewrite Rplus_0_r.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
apply Ropp_lt_contravar.
pattern x at 4;rewrite <- Rmult_1_r.
repeat rewrite Rmult_assoc.
apply Rmult_lt_compat_l.
assumption.
replace (R1 + R1 + R1 + R1 + R1 + R1) with R6.
apply Rmult_lt_reg_r with R6.
exact Rlt_0_6.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite Rmult_1_l.
replace R6 with (R2*R2+R2).
pattern (x*x);rewrite <- Rplus_0_r.
apply Rplus_lt_compat.
apply Rmult_gt_0_lt_compat;try assumption.
exact Rlt_0_2.
exact Rlt_0_2.
unfold R2.
unfold R6.
unfold R3.
unfold R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_6_0.
unfold R6. unfold R3. unfold R2.
repeat rewrite <-  Rplus_assoc.
reflexivity.
Qed.

Lemma sin_PI2 : sin (PI / R2) = R1.
replace (PI / R2) with PI2.
2:{
unfold PI.
rewrite Rmult_comm.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
}
assert (int' : R0 < PI2 < R2).
 destruct pi2_int; split.
{
  apply Rlt_le_trans with (R7/R8).
  exact lt_0_frac_7_8.
  assumption.
}
{
  apply Rle_lt_trans with (R7/R4).
  assumption.
  unfold Rdiv.
  apply Rmult_lt_reg_r with R4.
  exact Rlt_0_4.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  unfold R2.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  fold R8.
  exact Rlt_7_8.
  exact Neq_4_0.
}
assert (lo2 := sin_pos_tech PI2 int').
assert (t2 : Rabs (sin PI2) = R1).
 rewrite <- Rabs_R1; apply Rsqr_eq_abs_0.
 rewrite Rsqr_1, sin2, cos_pi2, Rsqr_0, Rminus_0_r; reflexivity.
revert t2; rewrite Rabs_pos_eq;[| apply Rlt_le]; tauto.
Qed.

Lemma PI_RGT_0 : PI > R0.
Proof. unfold PI; destruct pi2_int.
unfold Rgt.
apply Rmult_lt_0_compat.
exact Rlt_0_2.
apply Rlt_le_trans with (R7/R8).
exact lt_0_frac_7_8.
assumption.
Qed.

Lemma PI_4 : PI <= R4.
Proof. unfold PI; destruct pi2_int.
replace R4 with (R2*R2).
apply Rmult_le_compat_l.
left. exact Rlt_0_2.
left.
apply Rle_lt_trans with (R7 / R4).
assumption.
replace R4 with (R2*R2).
unfold Rdiv.
rewrite Rinv_mult_distr.
do 2 apply Rmult_lt_reg_r with R2.
exact Rlt_0_2.
apply Rmult_lt_compat_r.
exact Rlt_0_2.
exact Rlt_0_2.
exact Rlt_0_2.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R2)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
unfold R7.
unfold R4.
unfold R3.
unfold R2.
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_lt_compat_r.
pattern R1 at 1;rewrite <- Rplus_0_l.
apply Rplus_lt_compat_r.
exact Rlt_0_1.
exact Neq_2_0.
exact Neq_2_0.
exact Neq_2_0.
exact Neq_2_0.

unfold R4.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite <- Rplus_assoc.
reflexivity.

unfold R4.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite <- Rplus_assoc.
reflexivity.
Qed.

(**********)
Lemma PI_neq0 : PI <> R0.
Proof.
  red in |- *; intro; assert (H0 := PI_RGT_0); rewrite H in H0;
    elim (Rlt_irrefl _ H0).
Qed.


(**********)
Lemma cos_PI : cos PI = -R1.
Proof.
  replace PI with (PI / R2 + PI / R2).
  rewrite cos_plus.
  rewrite sin_PI2; rewrite cos_PI2.
  rewrite Rmult_0_l.
  unfold Rminus.
  rewrite Rplus_0_l.
  rewrite Rmult_1_r.
  reflexivity.
  symmetry  in |- *; apply double_var.
Qed.

Lemma sin_PI : sin PI = R0.
Proof.
  assert (H := sin2_cos2 PI).
  rewrite cos_PI in H.
  rewrite <- Rsqr_neg in H.
  rewrite Rsqr_1 in H.
  cut (Rsqr (sin PI) = R0).
  intro; apply (Rsqr_eq_0 _ H0).
  apply Rplus_eq_reg_l with R1.
  rewrite Rplus_0_r; rewrite Rplus_comm; exact H.
Qed.

Lemma sin_bound : forall (a : R) (n : nat), R0 <= a -> a <= PI ->
       sin_approx a (2 * n + 1) <= sin a <= sin_approx a (2 * (n + 1)).
Proof.
intros a n a0 api; apply pre_sin_bound.
 assumption.
apply Rle_trans with (1:= api) (2 := PI_4).
Qed.

Lemma cos_bound : forall (a : R) (n : nat), - PI / R2 <= a -> a <= PI / R2 ->
       cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1)).
Proof.
intros a n lower upper; apply pre_cos_bound.
 apply Rle_trans with (2 := lower).
 apply Rmult_le_reg_r with R2.
exact Rlt_0_2.
 replace ((-PI/R2) * R2) with (-PI).
2:{
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
}
 assert (t := PI_4).
rewrite <- Ropp_mult_distr_l.
apply Ropp_le_contravar.
replace (R2*R2) with R4.
assumption.
unfold R4.
unfold R2 at 3.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
reflexivity.
apply Rle_trans with (1 := upper).
apply Rmult_le_reg_r with R2. exact Rlt_0_2.
replace ((PI/R2) * R2) with PI.
2:{ 
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
}
generalize PI_4; intros.
replace (R2*R2) with R4.
assumption.
unfold R4.
unfold R2 at 3.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
reflexivity.
Qed.

(**********)
Lemma neg_cos : forall x:R, cos (x + PI) = - cos x.
Proof.
  intro x; rewrite cos_plus; rewrite sin_PI; rewrite cos_PI.
  rewrite Rmult_0_r.
  unfold Rminus.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  rewrite <- Ropp_mult_distr_r.
  rewrite Rmult_1_r.
  reflexivity.
Qed.

(**********)
Lemma sin_cos : forall x:R, sin x = - cos (PI / R2 + x).
Proof.
  intro x; rewrite cos_plus; rewrite sin_PI2; rewrite cos_PI2.
rewrite Rmult_0_l.
unfold Rminus.
rewrite Rplus_0_l.
rewrite Rmult_1_l.
rewrite Ropp_involutive.
reflexivity.
Qed.

(**********)
Lemma sin_plus : forall x y:R, sin (x + y) = sin x * cos y + cos x * sin y.
Proof.
  intros.
  rewrite (sin_cos (x + y)).
  replace (PI / R2 + (x + y)) with (PI / R2 + x + y).
  rewrite cos_plus.
2:{
repeat rewrite <- Rplus_assoc.
reflexivity.
}
  rewrite (sin_cos (PI / R2 + x)).
  replace (PI / R2 + (PI / R2 + x)) with (x + PI).
  rewrite neg_cos.
  replace (cos (PI / R2 + x)) with (- sin x).
  
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Ropp_mult_distr_l.
rewrite Ropp_mult_distr_l.
rewrite Ropp_mult_distr_l.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
rewrite Ropp_involutive.
reflexivity.

  rewrite sin_cos; rewrite Ropp_involutive; reflexivity.
  pattern PI at 1 in |- *; rewrite (double_var PI).

change (IZR 2) with R2.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
reflexivity.

Qed.

Lemma sin_minus : forall x y:R, sin (x - y) = sin x * cos y - cos x * sin y.
Proof.
  intros; unfold Rminus in |- *; rewrite sin_plus.
  rewrite <- cos_sym; rewrite sin_antisym.
  rewrite <- Ropp_mult_distr_r.
  reflexivity.
Qed.

(**********)
Definition tan (x:R) : R := sin x / cos x.

Lemma tan_plus :
  forall x y:R,
    cos x <> R0 ->
    cos y <> R0 ->
    cos (x + y) <> R0 ->
    R1 - tan x * tan y <> R0 ->
    tan (x + y) = (tan x + tan y) / (R1 - tan x * tan y).
Proof.
  intros; unfold tan in |- *; rewrite sin_plus; rewrite cos_plus;
    unfold Rdiv in |- *;
      replace (cos x * cos y - sin x * sin y) with
      (cos x * cos y * (R1 - sin x * / cos x * (sin y * / cos y))).
  rewrite Rinv_mult_distr.
  repeat rewrite <- Rmult_assoc;
    replace ((sin x * cos y + cos x * sin y) * / (cos x * cos y)) with
    (sin x * / cos x + sin y * / cos y).
  reflexivity.
  rewrite Rmult_plus_distr_r; rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc; repeat rewrite (Rmult_comm (sin x));
    repeat rewrite <- Rmult_assoc.
  repeat rewrite Rinv_r_simpl_m; [ reflexivity | assumption | assumption ].
  assumption.
  assumption.
  apply prod_neq_R0; assumption.
  assumption.
  unfold Rminus in |- *; rewrite Rmult_plus_distr_l; rewrite Rmult_1_r;
    apply Rplus_eq_compat_l; repeat rewrite Rmult_assoc;
      rewrite (Rmult_comm (sin x)); rewrite (Rmult_comm (cos y));
        rewrite <- Ropp_mult_distr_r_reverse; repeat rewrite <- Rmult_assoc;
          rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l; rewrite (Rmult_comm (sin x));
    rewrite <- Ropp_mult_distr_r_reverse; repeat rewrite Rmult_assoc;
      apply Rmult_eq_compat_l; rewrite (Rmult_comm (/ cos y));
        rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  apply Rmult_1_r.
  assumption.
  assumption.
Qed.

(*******************************************************)
(** * Some properties of cos, sin and tan              *)
(*******************************************************)

Lemma sin_2a : forall x:R, sin (R2 * x) = R2 * sin x * cos x.
Proof.
  intro x; rewrite double; rewrite sin_plus.
  rewrite <- (Rmult_comm (sin x)); symmetry  in |- *; rewrite Rmult_assoc;
    apply double.
Qed.

Lemma cos_2a : forall x:R, cos (R2 * x) = cos x * cos x - sin x * sin x.
Proof.
  intro x; rewrite double; apply cos_plus.
Qed.

Lemma cos_2a_cos : forall x:R, cos (R2 * x) = R2 * cos x * cos x - R1.
Proof.
  intro x; rewrite double; unfold Rminus in |- *; rewrite Rmult_assoc;
    rewrite cos_plus; generalize (sin2_cos2 x); rewrite double;
      intro H1; rewrite <- H1.
unfold Rsqr.
unfold Rminus.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rplus_comm.
rewrite Ropp_plus_distr.
rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
reflexivity.
Qed.

Lemma cos_2a_sin : forall x:R, cos (R2 * x) = R1 - R2 * sin x * sin x.
Proof.
  intro x; rewrite Rmult_assoc; unfold Rminus in |- *; repeat rewrite double.
  generalize (sin2_cos2 x); intro H1; rewrite <- H1; rewrite cos_plus.
unfold Rsqr, Rminus.
rewrite Ropp_plus_distr.
repeat rewrite <- Rplus_assoc.
apply Rplus_eq_compat_r.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
Qed.

Lemma tan_2a :
  forall x:R,
    cos x <> R0 ->
    cos (R2 * x) <> R0 ->
    R1 - tan x * tan x <> R0 -> tan (R2 * x) = R2 * tan x / (R1 - tan x * tan x).
Proof.
  repeat rewrite double; intros; repeat rewrite double; rewrite double in H0;
    apply tan_plus; assumption.
Qed.

Lemma sin_neg : forall x:R, sin (- x) = - sin x.
Proof.
  apply sin_antisym.
Qed.

Lemma cos_neg : forall x:R, cos (- x) = cos x.
Proof.
  intro; symmetry  in |- *; apply cos_sym.
Qed.

Lemma tan_0 : tan R0 = R0.
Proof.
  unfold tan in |- *; rewrite sin_0; rewrite cos_0.
  unfold Rdiv in |- *; apply Rmult_0_l.
Qed.

Lemma tan_neg : forall x:R, tan (- x) = - tan x.
Proof.
  intros x; unfold tan in |- *; rewrite sin_neg; rewrite cos_neg;
    unfold Rdiv in |- *.
  apply Ropp_mult_distr_l_reverse.
Qed.

Lemma tan_minus :
  forall x y:R,
    cos x <> R0 ->
    cos y <> R0 ->
    cos (x - y) <> R0 ->
    R1 + tan x * tan y <> R0 ->
    tan (x - y) = (tan x - tan y) / (R1 + tan x * tan y).
Proof.
  intros; unfold Rminus in |- *; rewrite tan_plus.
  rewrite tan_neg; unfold Rminus in |- *; rewrite <- Ropp_mult_distr_l_reverse;
    rewrite Rmult_opp_opp; reflexivity.
  assumption.
  rewrite cos_neg; assumption.
  assumption.
  rewrite tan_neg; unfold Rminus in |- *; rewrite <- Ropp_mult_distr_l_reverse;
    rewrite Rmult_opp_opp; assumption.
Qed.

Lemma cos_3PI2 : cos (R3 * (PI / R2)) = R0.
Proof.
  replace (R3 * (PI / R2)) with (PI + PI / R2).
  rewrite cos_plus; rewrite sin_PI; rewrite cos_PI2.
rewrite Rmult_0_r.
unfold Rminus.
rewrite Rplus_0_l.
rewrite Rmult_0_l.
rewrite Ropp_0.
reflexivity.
  pattern PI at 1 in |- *; rewrite (double_var PI).
change (IZR 2) with R2.
unfold R3.
unfold R2 at 4.
repeat rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
reflexivity.
Qed.

Lemma sin_2PI : sin (R2 * PI) = R0.
Proof.
  rewrite sin_2a; rewrite sin_PI.
  rewrite Rmult_0_r.
  rewrite Rmult_0_l.
  reflexivity.
Qed.

Lemma cos_2PI : cos (R2 * PI) = R1.
Proof.
  rewrite cos_2a; rewrite sin_PI; rewrite cos_PI.
unfold Rminus.
rewrite Rmult_0_l.
rewrite Ropp_0.
rewrite Rplus_0_r.
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
rewrite Ropp_involutive.
reflexivity.
Qed.

Lemma neg_sin : forall x:R, sin (x + PI) = - sin x.
Proof.
  intro x; rewrite sin_plus; rewrite sin_PI; rewrite cos_PI.
rewrite Rmult_0_r.
rewrite Rplus_0_r.
rewrite <- Ropp_mult_distr_r.
rewrite Rmult_1_r.
reflexivity.
Qed.

Lemma sin_PI_x : forall x:R, sin (PI - x) = sin x.
Proof.
  intro x; rewrite sin_minus; rewrite sin_PI; rewrite cos_PI.
  unfold Rminus.
  rewrite Rmult_0_l.
  rewrite Rplus_0_l.
  rewrite <- Ropp_mult_distr_l.
  rewrite Rmult_1_l.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

Lemma sin_period : forall (x:R) (k:nat), sin (x + R2 * INR k * PI) = sin x.
Proof.
  intros x k; induction  k as [| k Hreck].
  simpl in |- *.
  rewrite Rmult_0_r.
  rewrite Rmult_0_l.
  rewrite Rplus_0_r.
  reflexivity.

  replace (x + R2 * INR (S k) * PI) with (x + R2 * INR k * PI + R2 * PI).
  rewrite sin_plus in |- *; rewrite sin_2PI in |- *; rewrite cos_2PI in |- *.
  rewrite Rmult_0_r.
  rewrite Rplus_0_r.
  rewrite Rmult_1_r.
  rewrite Hreck.
  reflexivity.

  rewrite S_INR in |- *.
  repeat rewrite Rplus_assoc.
  apply Rplus_eq_compat_l.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_r.
  apply Rplus_eq_compat_l.
  rewrite Rmult_1_r.
  reflexivity.
Qed.

Lemma cos_period : forall (x:R) (k:nat), cos (x + R2 * INR k * PI) = cos x.
Proof.
  intros x k; induction  k as [| k Hreck].
  simpl in |- *.
  rewrite Rmult_0_r.
  rewrite Rmult_0_l.
  rewrite Rplus_0_r.
  reflexivity.

  replace (x + R2 * INR (S k) * PI) with (x + R2 * INR k * PI + R2 * PI).
  rewrite cos_plus in |- *; rewrite sin_2PI in |- *; rewrite cos_2PI in |- *.
  rewrite Rmult_1_r.
  rewrite Rmult_0_r.
  unfold Rminus.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  rewrite Hreck.
  reflexivity.
  rewrite S_INR in |- *.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_r.
  repeat rewrite <- Rplus_assoc.
  reflexivity.
Qed.

Lemma sin_shift : forall x:R, sin (PI / R2 - x) = cos x.
Proof.
  intro x; rewrite sin_minus; rewrite sin_PI2; rewrite cos_PI2.
  unfold Rminus.
  rewrite Rmult_0_l.
  rewrite Ropp_0.
  rewrite Rplus_0_r.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Lemma cos_shift : forall x:R, cos (PI / R2 - x) = sin x.
Proof.
  intro x; rewrite cos_minus; rewrite sin_PI2; rewrite cos_PI2.
  rewrite Rmult_0_l.
  rewrite Rplus_0_l.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Lemma cos_sin : forall x:R, cos x = sin (PI / R2 + x).
Proof.
  intro x; rewrite sin_plus; rewrite sin_PI2; rewrite cos_PI2.
  rewrite Rmult_0_l.
  rewrite Rplus_0_r.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Lemma PI2_RGT_0 : R0 < PI / R2.
Proof.
  unfold Rdiv in |- *; apply Rmult_lt_0_compat;
    [ apply PI_RGT_0 | apply Rinv_0_lt_compat; prove_sup ].
  exact Rlt_0_2.
Qed.

Lemma SIN_bound : forall x:R, -R1 <= sin x <= R1.
Proof.
  intro; destruct (Rle_dec (-R1) (sin x)) as [Hle|Hnle].
  destruct (Rle_dec (sin x) R1) as [Hle'|Hnle'].
  split; assumption.
  cut (R1 < sin x).
  intro;
    generalize
      (Rsqr_incrst_1 R1 (sin x) H (Rlt_le R0 R1 Rlt_0_1)
        (Rlt_le R0 (sin x) (Rlt_trans R0 R1 (sin x) Rlt_0_1 H)));
      rewrite Rsqr_1; intro; rewrite sin2 in H0; unfold Rminus in H0.
        generalize (Rplus_lt_compat_l (-R1) R1 (R1 + - Rsqr (cos x)) H0);
          repeat rewrite <- Rplus_assoc; change (-R1) with (-(R1)); rewrite Rplus_opp_l;
            rewrite Rplus_0_l; intro; rewrite <- Ropp_0 in H1;
              generalize (Ropp_lt_gt_contravar (-R0) (- Rsqr (cos x)) H1);
                repeat rewrite Ropp_involutive; intro; generalize (Rle_0_sqr (cos x));
                  intro; elim (Rlt_irrefl R0 (Rle_lt_trans R0 (Rsqr (cos x)) R0 H3 H2)).
  auto with real.
  cut (sin x < -R1).
  intro; generalize (Ropp_lt_gt_contravar (sin x) (-R1) H);
    change (-R1) with (-(R1));
    rewrite Ropp_involutive; clear H; intro;
      generalize
        (Rsqr_incrst_1 R1 (- sin x) H (Rlt_le R0 R1 Rlt_0_1)
          (Rlt_le R0 (- sin x) (Rlt_trans R0 R1 (- sin x) Rlt_0_1 H)));
        rewrite Rsqr_1; intro; rewrite <- Rsqr_neg in H0;
          rewrite sin2 in H0; unfold Rminus in H0;
            generalize (Rplus_lt_compat_l (-R1) R1 (R1 + - Rsqr (cos x)) H0);
              rewrite <- Rplus_assoc; change (-R1) with (-(R1)); rewrite Rplus_opp_l;
                rewrite Rplus_0_l; intro; rewrite <- Ropp_0 in H1;
                  generalize (Ropp_lt_gt_contravar (-R0) (- Rsqr (cos x)) H1);
                    repeat rewrite Ropp_involutive; intro; generalize (Rle_0_sqr (cos x));
                      intro; elim (Rlt_irrefl R0 (Rle_lt_trans R0 (Rsqr (cos x)) R0 H3 H2)).
  auto with real.
Qed.

Lemma COS_bound : forall x:R, -R1 <= cos x <= R1.
Proof.
  intro; rewrite <- sin_shift; apply SIN_bound.
Qed.

Lemma cos_sin_0 : forall x:R, ~ (cos x = R0 /\ sin x = R0).
Proof.
  intro; red in |- *; intro; elim H; intros; generalize (sin2_cos2 x); intro;
    rewrite H0 in H2; rewrite H1 in H2; repeat rewrite Rsqr_0 in H2;
      rewrite Rplus_0_r in H2; generalize Rlt_0_1; intro;
        rewrite <- H2 in H3; elim (Rlt_irrefl R0 H3).
Qed.

Lemma cos_sin_0_var : forall x:R, cos x <> R0 \/ sin x <> R0.
Proof.
  intros x.
  destruct (Req_dec (cos x) R0). 2: now left.
  right. intros H'.
  apply (cos_sin_0 x).
  now split.
Qed.

(*****************************************************************)
(** * Using series definitions of cos and sin                    *)
(*****************************************************************)

Definition sin_lb (a:R) : R := sin_approx a 3.
Definition sin_ub (a:R) : R := sin_approx a 4.
Definition cos_lb (a:R) : R := cos_approx a 3.
Definition cos_ub (a:R) : R := cos_approx a 4.

Lemma sin_lb_gt_0 : forall a:R, R0 < a -> a <= PI / R2 -> R0 < sin_lb a.
Proof.
  intros.
  unfold sin_lb in |- *; unfold sin_approx in |- *; unfold sin_term in |- *.
  set (Un := fun i:nat => a ^ (2 * i + 1) / INR (fact (2 * i + 1))).
  replace
  (sum_f_R0
    (fun i:nat => (-R1) ^ i * (a ^ (2 * i + 1) / INR (fact (2 * i + 1)))) 3)
    with (sum_f_R0 (fun i:nat => (-R1) ^ i * Un i) 3);
      [ idtac | apply sum_eq; intros; unfold Un in |- *; reflexivity ].
  cut (forall n:nat, Un (S n) < Un n).
  intro; simpl in |- *.
  repeat rewrite Rmult_1_l; repeat rewrite Rmult_1_r;
    replace (-R1 * Un 1%nat) with (- Un 1%nat);
[ idtac | rewrite <- Ropp_mult_distr_l; rewrite Rmult_1_l; reflexivity ];
    replace (-R1 * -R1 * Un 2%nat) with (Un 2%nat);
 [ idtac | rewrite <- Ropp_mult_distr_l;
rewrite <- Ropp_mult_distr_l;
rewrite <- Ropp_mult_distr_r;
rewrite <- Ropp_mult_distr_l;
rewrite Ropp_involutive;
rewrite Rmult_1_l;
rewrite Rmult_1_l;
reflexivity ];
    replace (-R1 * (-R1 * -R1) * Un 3%nat) with (- Un 3%nat);
    [ idtac | repeat rewrite <- Ropp_mult_distr_l;
repeat rewrite <- Ropp_mult_distr_r;
repeat rewrite <- Ropp_mult_distr_l;
rewrite Ropp_involutive;
repeat rewrite Rmult_1_l;
reflexivity ];
    replace (Un 0%nat + - Un 1%nat + Un 2%nat + - Un 3%nat) with
    (Un 0%nat - Un 1%nat + (Un 2%nat - Un 3%nat)) ;
 [ idtac | unfold Rminus;
repeat rewrite <- Rplus_assoc;
reflexivity ].
  apply Rplus_lt_0_compat.
  unfold Rminus in |- *; apply Rplus_lt_reg_l with (Un 1%nat);
    rewrite Rplus_0_r; rewrite (Rplus_comm (Un 1%nat));
      rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
        apply H1.
  unfold Rminus in |- *; apply Rplus_lt_reg_l with (Un 3%nat);
    rewrite Rplus_0_r; rewrite (Rplus_comm (Un 3%nat));
      rewrite Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_r;
        apply H1.
  intro; unfold Un in |- *.
  cut ((2 * S n + 1)%nat = (2 * n + 1 + 2)%nat).
  intro; rewrite H1.
  rewrite pow_add; unfold Rdiv in |- *; rewrite Rmult_assoc;
    apply Rmult_lt_compat_l.
  apply pow_lt; assumption.
  rewrite <- H1; apply Rmult_lt_reg_l with (INR (fact (2 * n + 1))).
  apply lt_INR_0; apply neq_O_lt.
  assert (H2 := fact_neq_0 (2 * n + 1)).
  red in |- *; intro; elim H2; symmetry  in |- *; assumption.
  rewrite <- Rinv_r_sym.
  apply Rmult_lt_reg_l with (INR (fact (2 * S n + 1))).
  apply lt_INR_0; apply neq_O_lt.
  assert (H2 := fact_neq_0 (2 * S n + 1)).
  red in |- *; intro; elim H2; symmetry  in |- *; assumption.
  rewrite (Rmult_comm (INR (fact (2 * S n + 1)))); repeat rewrite Rmult_assoc;
    rewrite <- Rinv_l_sym.
  do 2 rewrite Rmult_1_r; apply Rle_lt_trans with (INR (fact (2 * n + 1)) * R4).
  apply Rmult_le_compat_l.
  apply pos_INR.
  simpl in |- *; rewrite Rmult_1_r; replace R4 with (Rsqr R2).
2:{
  unfold Rsqr. unfold R2 at 1.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l. fold R4. reflexivity.
}
    apply Rsqr_incr_1.
  
  apply Rle_trans with (PI / R2);
    [ assumption
      | unfold Rdiv in |- *; apply Rmult_le_reg_l with R2;
        [ exact Rlt_0_2
          | rewrite <- Rmult_assoc; rewrite Rinv_r_simpl_m
             ] ].
  replace (R2*R2) with R4.
  apply PI_4.
  unfold R2 at 1. rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l. fold R4. reflexivity.
  exact Neq_2_0.
  left; assumption.
  left; exact Rlt_0_2.
  rewrite H1; replace (2 * n + 1 + 2)%nat with (S (S (2 * n + 1))).
  do 2 rewrite fact_simpl; do 2 rewrite mult_INR.
  repeat rewrite <- Rmult_assoc.
  rewrite <- (Rmult_comm (INR (fact (2 * n + 1)))).
  apply Rmult_lt_compat_l.
  apply lt_INR_0; apply neq_O_lt.
  assert (H2 := fact_neq_0 (2 * n + 1)).
  red in |- *; intro; elim H2; symmetry  in |- *; assumption.
  do 2 rewrite S_INR; rewrite plus_INR; rewrite mult_INR; set (x := INR n);
    unfold INR in |- *.
  replace (((R1 + R1) * x + R1 + R1 + R1) * ((R1 + R1) * x + R1 + R1)) with (R4 * x * x + R10 * x + R6).
2:{
  unfold R10.
  unfold R6.
  unfold R5.
  unfold R4.
  unfold R3.
  unfold R2.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_1_l.
  repeat rewrite Rmult_1_r.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  repeat rewrite Rplus_assoc.
  repeat apply Rplus_eq_compat_l.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.

  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  rewrite Rplus_comm.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_eq_compat_r.
  reflexivity.
}
  apply Rplus_lt_reg_l with (-(R4)); rewrite Rplus_opp_l;
    replace (-(R4) + (R4 * x * x + R10 * x + R6)) with (R4 * x * x + R10 * x + R2).
2:{
symmetry.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
apply Rplus_eq_compat_l.
unfold R6.
unfold R4.
unfold R3.
unfold R2.
repeat rewrite Ropp_plus_distr.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
reflexivity.
}
  apply Rplus_le_lt_0_compat.
  cut (R0 <= x).
  intro; apply Rplus_le_le_0_compat; repeat apply Rmult_le_pos;
    assumption || left; prove_sup.
exact Rlt_0_4.
unfold R10, R5, R3, R2.
do 9 (pattern R0 at 1;rewrite <- Rplus_0_l).
repeat rewrite <- Rplus_assoc.
repeat apply Rplus_lt_compat;exact Rlt_0_1.
  apply pos_INR.
exact Rlt_0_2.
simpl.
rewrite (plus_comm _ 0).
simpl.
rewrite <- plus_n_Sm.
rewrite (plus_comm _ 0).
simpl.
rewrite <- plus_n_Sm.
rewrite <- plus_n_Sm.
rewrite (plus_comm _ 0).
simpl.
reflexivity.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
simpl.
rewrite (plus_comm _ 0).
simpl.
repeat rewrite <- plus_n_Sm.
rewrite (plus_comm _ 0).
simpl.
rewrite (plus_comm _ 0).
simpl.
rewrite (plus_comm _ 0).
simpl.
reflexivity.
Qed.

Lemma SIN : forall a:R, R0 <= a -> a <= PI -> sin_lb a <= sin a <= sin_ub a.
Proof.
  intros; unfold sin_lb, sin_ub in |- *; apply (sin_bound a 1 H H0).
Qed.

Lemma COS :
  forall a:R, - PI / R2 <= a -> a <= PI / R2 -> cos_lb a <= cos a <= cos_ub a.
Proof.
  intros; unfold cos_lb, cos_ub in |- *; apply (cos_bound a 1 H H0).
Qed.

(**********)
Lemma _PI2_RLT_0 : - (PI / R2) < R0.
Proof.
  assert (H := PI_RGT_0).
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  unfold Rdiv.
  apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat.
  exact Rlt_0_2.
Qed.

Lemma PI4_RLT_PI2 : PI / R4 < PI / R2.
Proof.
  assert (H := PI_RGT_0).
  unfold Rdiv.
  apply Rmult_lt_compat_l.
  assumption.
  replace R4 with (R2*R2).
  rewrite Rinv_mult_distr.
  pattern (/R2) at 3;rewrite <- Rmult_1_l.
  apply Rmult_lt_compat_r.
  apply Rinv_0_lt_compat.
  exact Rlt_0_2.
  apply Rmult_lt_reg_r with R2.
  exact Rlt_0_2.
  rewrite Rmult_1_l.
  rewrite Rinv_l.
  unfold R2.
  pattern R1 at 1;rewrite <- Rplus_0_l.
  apply Rplus_lt_compat_r.
  exact Rlt_0_1.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.
  unfold R4.
  unfold R2.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  repeat rewrite <- Rplus_assoc.
  reflexivity.
Qed.

Lemma PI2_Rlt_PI : PI / R2 < PI.
Proof.
  assert (H := PI_RGT_0).
  pattern PI at 2;rewrite <- Rmult_1_r.
  unfold Rdiv.
  apply Rmult_lt_compat_l.
  assumption.
  apply Rmult_lt_reg_r with R2.
  exact Rlt_0_2.
  rewrite Rmult_1_l.
  rewrite Rinv_l.
  unfold R2.
  pattern R1 at 1;rewrite <- Rplus_0_l.
  apply Rplus_lt_compat_r.
  exact Rlt_0_1.
  exact Neq_2_0.
Qed.

(***************************************************)
(** * Increasing and decreasing of [cos] and [sin] *)
(***************************************************)
Theorem sin_gt_0 : forall x:R, R0 < x -> x < PI -> R0 < sin x.
Proof.
  intros; elim (SIN x (Rlt_le R0 x H) (Rlt_le x PI H0)); intros H1 _;
    case (Rtotal_order x (PI / R2)); intro H2.
  apply Rlt_le_trans with (sin_lb x).
  apply sin_lb_gt_0; [ assumption | left; assumption ].
  assumption.
  elim H2; intro H3.
  rewrite H3; rewrite sin_PI2; apply Rlt_0_1.
  rewrite <- sin_PI_x; generalize (Ropp_gt_lt_contravar x (PI / R2) H3);
    intro H4; generalize (Rplus_lt_compat_l PI (- x) (- (PI / R2)) H4).
  replace (PI + - (PI / R2)) with (PI / R2).
  intro H5; generalize (Ropp_lt_gt_contravar x PI H0); intro H6;
    change (- PI < - x) in H6; generalize (Rplus_lt_compat_l PI (- PI) (- x) H6).
  rewrite Rplus_opp_r.
  intro H7;
    elim
      (SIN (PI - x) (Rlt_le R0 (PI - x) H7)
        (Rlt_le (PI - x) PI (Rlt_trans (PI - x) (PI / R2) PI H5 PI2_Rlt_PI)));
      intros H8 _;
        generalize (sin_lb_gt_0 (PI - x) H7 (Rlt_le (PI - x) (PI / R2) H5));
          intro H9; apply (Rlt_le_trans R0 (sin_lb (PI - x)) (sin (PI - x)) H9 H8).
  apply Rplus_eq_reg_r with (PI/R2).
  unfold Rdiv.
  rewrite <- Rmult_plus_distr_r.
  pattern PI at 1;rewrite <- Rmult_1_r.
  pattern PI at 2;rewrite <- Rmult_1_r.
  rewrite <- Rmult_plus_distr_l.
  fold R2.
  rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  reflexivity.
  exact Neq_2_0.
Qed.

Theorem cos_gt_0 : forall x:R, - (PI / R2) < x -> x < PI / R2 -> R0 < cos x.
Proof.
  intros; rewrite cos_sin;
    generalize (Rplus_lt_compat_l (PI / R2) (- (PI / R2)) x H).
  rewrite Rplus_opp_r; intro H1;
    generalize (Rplus_lt_compat_l (PI / R2) x (PI / R2) H0);
      rewrite <- double_var; intro H2; apply (sin_gt_0 (PI / R2 + x) H1 H2).
Qed.

Lemma sin_ge_0 : forall x:R, R0 <= x -> x <= PI -> R0 <= sin x.
Proof.
  intros x H1 H2; elim H1; intro H3;
    [ elim H2; intro H4;
      [ left; apply (sin_gt_0 x H3 H4)
        | rewrite H4; right; symmetry  in |- *; apply sin_PI ]
      | rewrite <- H3; right; symmetry  in |- *; apply sin_0 ].
Qed.

Lemma cos_ge_0 : forall x:R, - (PI / R2) <= x -> x <= PI / R2 -> R0 <= cos x.
Proof.
  intros x H1 H2; elim H1; intro H3;
    [ elim H2; intro H4;
      [ left; apply (cos_gt_0 x H3 H4)
        | rewrite H4; right; symmetry  in |- *; apply cos_PI2 ]
      | rewrite <- H3; rewrite cos_neg; right; symmetry  in |- *; apply cos_PI2 ].
Qed.

Lemma sin_le_0 : forall x:R, PI <= x -> x <= R2 * PI -> sin x <= R0.
Proof.
  intros x H1 H2; apply Rge_le; rewrite <- Ropp_0;
    rewrite <- (Ropp_involutive (sin x)); apply Ropp_le_ge_contravar;
      rewrite <- neg_sin; replace (x + PI) with (x - PI + R2 * INR 1 * PI);
        [ rewrite (sin_period (x - PI) 1); apply sin_ge_0;
          [ replace (x - PI) with (x + - PI);
            [ rewrite Rplus_comm; replace R0 with (- PI + PI);
              [ apply Rplus_le_compat_l; assumption | idtac ]
              | idtac ]
            | replace (x - PI) with (x + - PI); rewrite Rplus_comm;
              [ pattern PI at 2 in |- *; replace PI with (- PI + R2 * PI);
                [ apply Rplus_le_compat_l; assumption | idtac ]
                | idtac ] ]
          | unfold INR in |- *; idtac ].
rewrite Rplus_opp_l. reflexivity.
unfold Rminus. reflexivity.
unfold R2. rewrite Rmult_plus_distr_r. rewrite Rmult_1_l. rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l. reflexivity.
unfold Rminus. rewrite Rplus_comm. reflexivity.
rewrite Rmult_1_r.
unfold R2. rewrite Rmult_plus_distr_r. rewrite Rmult_1_l. rewrite <- Rplus_assoc.
apply Rplus_eq_compat_r.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r. reflexivity.
Qed.

Lemma cos_le_0 : forall x:R, PI / R2 <= x -> x <= R3 * (PI / R2) -> cos x <= R0.
Proof.
  intros x H1 H2; apply Rge_le; rewrite <- Ropp_0;
    rewrite <- (Ropp_involutive (cos x)); apply Ropp_le_ge_contravar;
      rewrite <- neg_cos; replace (x + PI) with (x - PI + R2 * INR 1 * PI).
  rewrite cos_period; apply cos_ge_0.
  replace (- (PI / R2)) with (- PI + PI / R2).
2:{
  apply Rplus_eq_reg_r with (PI/R2).
  rewrite Rplus_opp_l.
  unfold Rdiv.
  rewrite Rplus_assoc.
  rewrite <- Rmult_plus_distr_r.
  pattern PI at 2;rewrite <- Rmult_1_r.
  pattern PI at 3;rewrite <- Rmult_1_r.
  rewrite <- Rmult_plus_distr_l.
  fold R2.
  rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite Rplus_opp_l.
  reflexivity.
  exact Neq_2_0.
}
  unfold Rminus in |- *; rewrite (Rplus_comm x); apply Rplus_le_compat_l;
    assumption.
  unfold Rminus in |- *; rewrite Rplus_comm;
    replace (PI / R2) with (- PI + R3 * (PI / R2)).
2:{
unfold R3.
rewrite Rmult_plus_distr_r.
rewrite (Rmult_comm R2).
unfold Rdiv.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_l.
rewrite Rmult_1_r.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
reflexivity.
  exact Neq_2_0.
}
  apply Rplus_le_compat_l; assumption.
  unfold INR in |- *.

rewrite Rmult_1_r.
unfold R2.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
Qed.

Lemma sin_lt_0 : forall x:R, PI < x -> x < R2 * PI -> sin x < R0.
Proof.
  intros x H1 H2; rewrite <- Ropp_0; rewrite <- (Ropp_involutive (sin x));
    apply Ropp_lt_gt_contravar; rewrite <- neg_sin;
      replace (x + PI) with (x - PI + R2 * INR 1 * PI);
      [ rewrite (sin_period (x - PI) 1); apply sin_gt_0;
        [ replace (x - PI) with (x + - PI);
          [ rewrite Rplus_comm; replace R0 with (- PI + PI);
            [ apply Rplus_lt_compat_l; assumption | idtac ]
            | idtac ]
          | replace (x - PI) with (x + - PI); rewrite Rplus_comm;
            [ pattern PI at 2 in |- *; replace PI with (- PI + R2 * PI);
              [ apply Rplus_lt_compat_l; assumption | idtac ]
              | idtac ] ]
        | unfold INR in |- *; idtac ].

rewrite Rplus_opp_l.
reflexivity.

reflexivity.

unfold R2. rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.

rewrite Rplus_comm. reflexivity.

unfold Rminus.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rmult_1_r.
unfold R2.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
Qed.

Lemma sin_lt_0_var : forall x:R, - PI < x -> x < R0 -> sin x < R0.
Proof.
  intros; generalize (Rplus_lt_compat_l (R2 * PI) (- PI) x H);
    replace (R2 * PI + - PI) with PI;
    [ intro H1; rewrite Rplus_comm in H1;
      generalize (Rplus_lt_compat_l (R2 * PI) x R0 H0);
        intro H2; rewrite (Rplus_comm (R2 * PI)) in H2;
          rewrite <- (Rplus_comm R0) in H2; rewrite Rplus_0_l in H2;
            rewrite <- (sin_period x 1); unfold INR in |- *;
              replace (R2 * R1 * PI) with (R2 * PI);
              [ apply (sin_lt_0 (x + R2 * PI) H1 H2) | idtac ]
      | idtac ].

rewrite Rmult_1_r. reflexivity.
unfold R2. rewrite Rmult_plus_distr_r. rewrite Rmult_1_l.
rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
reflexivity.
Qed.

Lemma cos_lt_0 : forall x:R, PI / R2 < x -> x < R3 * (PI / R2) -> cos x < R0.
Proof.
  intros x H1 H2; rewrite <- Ropp_0; rewrite <- (Ropp_involutive (cos x));
    apply Ropp_lt_gt_contravar; rewrite <- neg_cos;
      replace (x + PI) with (x - PI + R2 * INR 1 * PI).
  rewrite cos_period; apply cos_gt_0.
  replace (- (PI / R2)) with (- PI + PI / R2).
  unfold Rminus in |- *; rewrite (Rplus_comm x); apply Rplus_lt_compat_l;
    assumption.
2:{
  unfold Rminus in |- *; rewrite Rplus_comm;
    replace (PI / R2) with (- PI + R3 * (PI / R2)).
  apply Rplus_lt_compat_l; assumption.
  unfold INR in |- *.

unfold R3.
rewrite Rmult_plus_distr_r.
rewrite (Rmult_comm R2).
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
rewrite Rmult_1_l.
reflexivity.
exact Neq_2_0.
}

pattern (-PI) at 1;rewrite <- Rmult_1_r.
rewrite <- Rinv_r with R2.
repeat rewrite <- Rmult_assoc.
unfold Rdiv.
rewrite <- Rmult_plus_distr_r.
rewrite Ropp_mult_distr_l.
apply Rmult_eq_compat_r.
unfold R2.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
reflexivity.
exact Neq_2_0.

simpl.
rewrite Rmult_1_r.
unfold Rminus.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
unfold R2.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
Qed.

Lemma tan_gt_0 : forall x:R, R0 < x -> x < PI / R2 -> R0 < tan x.
Proof.
  intros x H1 H2; unfold tan in |- *; generalize _PI2_RLT_0;
    generalize (Rlt_trans R0 x (PI / R2) H1 H2); intros;
      generalize (Rlt_trans (- (PI / R2)) R0 x H0 H1); intro H5;
        generalize (Rlt_trans x (PI / R2) PI H2 PI2_Rlt_PI);
          intro H7; unfold Rdiv in |- *; apply Rmult_lt_0_compat.
  apply sin_gt_0; assumption.
  apply Rinv_0_lt_compat; apply cos_gt_0; assumption.
Qed.

Lemma tan_lt_0 : forall x:R, - (PI / R2) < x -> x < R0 -> tan x < R0.
Proof.
  intros x H1 H2; unfold tan in |- *;
    generalize (cos_gt_0 x H1 (Rlt_trans x R0 (PI / R2) H2 PI2_RGT_0));
      intro H3; rewrite <- Ropp_0;
        replace (sin x / cos x) with (- (- sin x / cos x)).
  rewrite <- sin_neg; apply Ropp_gt_lt_contravar;
    change (R0 < sin (- x) / cos x) in |- *; unfold Rdiv in |- *;
      apply Rmult_lt_0_compat.
  apply sin_gt_0.
  rewrite <- Ropp_0; apply Ropp_gt_lt_contravar; assumption.
  apply Rlt_trans with (PI / R2).
  rewrite <- (Ropp_involutive (PI / R2)); apply Ropp_gt_lt_contravar; assumption.
  apply PI2_Rlt_PI.
  apply Rinv_0_lt_compat; assumption.
  unfold Rdiv in |- *.
  rewrite <- Ropp_mult_distr_l.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

Lemma cos_ge_0_3PI2 :
  forall x:R, R3 * (PI / R2) <= x -> x <= R2 * PI -> R0 <= cos x.
Proof.
  intros; rewrite <- cos_neg; rewrite <- (cos_period (- x) 1);
    unfold INR in |- *; replace (- x + R2 * R1 * PI) with (R2 * PI - x).
2:{
rewrite Rmult_1_r.
rewrite Rplus_comm.
reflexivity.
}
  generalize (Ropp_le_ge_contravar x (R2 * PI) H0); intro H1;
    generalize (Rge_le (- x) (- (R2 * PI)) H1); clear H1;
      intro H1; generalize (Rplus_le_compat_l (R2 * PI) (- (R2 * PI)) (- x) H1).
  rewrite Rplus_opp_r.
  intro H2; generalize (Ropp_le_ge_contravar (R3 * (PI / R2)) x H); intro H3;
    generalize (Rge_le (- (R3 * (PI / R2))) (- x) H3); clear H3;
      intro H3;
        generalize (Rplus_le_compat_l (R2 * PI) (- x) (- (R3 * (PI / R2))) H3).
  replace (R2 * PI + - (R3 * (PI / R2))) with (PI / R2).
2:{
apply Rmult_eq_reg_r with R2.
unfold Rdiv.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite Ropp_mult_distr_r.
rewrite Ropp_mult_distr_l.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite (Rmult_comm PI).
rewrite <- Ropp_mult_distr_r.
rewrite Ropp_mult_distr_l.
repeat rewrite <- Rmult_assoc.
rewrite <- Rmult_plus_distr_r.
unfold R3.
unfold R2.
pattern PI at 1;rewrite <- Rmult_1_l.
apply Rmult_eq_compat_r.
repeat rewrite Ropp_plus_distr.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
rewrite Rplus_opp_r, Rplus_0_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
exact Neq_2_0.
}
  intro H4;
    apply
      (cos_ge_0 (R2 * PI - x)
        (Rlt_le (- (PI / R2)) (R2 * PI - x)
          (Rlt_le_trans (- (PI / R2)) R0 (R2 * PI - x) _PI2_RLT_0 H2)) H4).
Qed.

Lemma form1 :
  forall p q:R, cos p + cos q = R2 * cos ((p - q) / R2) * cos ((p + q) / R2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / R2 + (p + q) / R2).
2:{
unfold Rminus.
apply Rmult_eq_reg_r with R2.
unfold Rdiv.
rewrite <- Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm p q).
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
unfold R2.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
}
  rewrite <- (cos_neg q); replace (- q) with ((p - q) / R2 - (p + q) / R2).
2:{
unfold Rdiv.
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm p q).
rewrite Rplus_comm.
rewrite Ropp_plus_distr.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_r.
rewrite <- Ropp_plus_distr.
rewrite <- Ropp_mult_distr_l.
pattern q;rewrite <- Rmult_1_r.
rewrite <- Rmult_plus_distr_l.
fold R2.
rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
}
  rewrite cos_plus; rewrite cos_minus.
rewrite (Rmult_comm R2).
unfold Rdiv.
set (sR2:=/R2).
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
unfold Rminus.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
reflexivity.
Qed.

Lemma form2 :
  forall p q:R, cos p - cos q = -R2 * sin ((p - q) / R2) * sin ((p + q) / R2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / R2 + (p + q) / R2).
2:{
unfold Rdiv.
rewrite <- Rmult_plus_distr_r.
unfold Rminus.
rewrite (Rplus_comm p q).
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
pattern p;rewrite <- Rmult_1_r.
rewrite <- Rmult_plus_distr_l.
fold R2.
rewrite Rmult_assoc.
rewrite Rinv_r.
reflexivity.
exact Neq_2_0.
}
  rewrite <- (cos_neg q); replace (- q) with ((p - q) / R2 - (p + q) / R2).
2:{
unfold Rdiv, Rminus.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
rewrite Ropp_plus_distr.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm (-q)).
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_l.
pattern (-q);rewrite <- Rmult_1_r.
rewrite <- Rmult_plus_distr_l.
fold R2.
rewrite Rmult_assoc.
rewrite Rinv_r.
reflexivity.
exact Neq_2_0.
}
  rewrite cos_plus; rewrite cos_minus.
unfold Rdiv, Rminus.
set (sR2:=/R2).
unfold R2.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite Ropp_plus_distr.
repeat rewrite <- Rplus_assoc.
apply Rplus_eq_compat_r.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
reflexivity.
Qed.

Lemma form3 :
  forall p q:R, sin p + sin q = R2 * cos ((p - q) / R2) * sin ((p + q) / R2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / R2 + (p + q) / R2).
  pattern q at 3 in |- *; replace q with ((p + q) / R2 - (p - q) / R2).
  rewrite sin_plus; rewrite sin_minus.
{
unfold Rminus, Rdiv.
set (sR2:=/R2).
unfold R2.
repeat rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rplus_comm.
rewrite Rmult_comm.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite Rmult_comm.
reflexivity.
}
  pattern q at 3 in |- *; rewrite double_var; unfold Rdiv in |- *.
change (IZR 2) with R2.
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
rewrite <- Rmult_plus_distr_r.
apply Rmult_eq_compat_r.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm q).
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_l.
reflexivity.

  pattern p at 3 in |- *; rewrite double_var; unfold Rdiv in |- *.
change (IZR 2) with R2.
unfold Rminus.
rewrite <- Rmult_plus_distr_r.
rewrite <- Rmult_plus_distr_r.
apply Rmult_eq_compat_r.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm (-q)).
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
reflexivity.

Qed.

Lemma form4 :
  forall p q:R, sin p - sin q = R2 * cos ((p + q) / R2) * sin ((p - q) / R2).
Proof.
  intros p q; pattern p at 1 in |- *;
    replace p with ((p - q) / R2 + (p + q) / R2).
2:{
unfold Rdiv.
rewrite <- Rmult_plus_distr_r.
unfold Rminus.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm (-q)).
rewrite Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_r.
pattern p;rewrite <- Rmult_1_r.
rewrite <- Rmult_plus_distr_l.
fold R2.
rewrite Rmult_assoc.
rewrite Rinv_r.
reflexivity.
exact Neq_2_0.
}
  pattern q at 3 in |- *; replace q with ((p + q) / R2 - (p - q) / R2).
2:{
unfold Rdiv.
unfold Rminus.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
repeat rewrite Rplus_assoc.
rewrite (Rplus_comm q).
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_r.
rewrite Rplus_0_l.
pattern q;rewrite <- Rmult_1_r.
rewrite <- Rmult_plus_distr_l.
fold R2.
rewrite Rmult_assoc.
rewrite Rinv_r.
reflexivity.
exact Neq_2_0.
}
  rewrite sin_plus; rewrite sin_minus.
unfold Rdiv, Rminus.
set (sR2:=/R2).
unfold R2.
repeat rewrite Rmult_plus_distr_r.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rmult_comm.
rewrite Rplus_opp_r.
rewrite Rplus_0_l.
rewrite Rmult_comm.
reflexivity.
Qed.

Lemma sin_increasing_0 :
  forall x y:R,
    - (PI / R2) <= x ->
    x <= PI / R2 -> - (PI / R2) <= y -> y <= PI / R2 -> sin x < sin y -> x < y.
Proof.
  intros; cut (sin ((x - y) / R2) < R0).
  intro H4; case (Rtotal_order ((x - y) / R2) R0); intro H5.
  assert (Hyp : R0 < R2).
  exact Rlt_0_2.
  generalize (Rmult_lt_compat_l R2 ((x - y) / R2) R0 Hyp H5).
  unfold Rdiv in |- *.
  rewrite <- Rmult_assoc.
  rewrite Rinv_r_simpl_m.
  rewrite Rmult_0_r.
  clear H5; intro H5; apply Rminus_lt; assumption.
  exact Neq_2_0.
  elim H5; intro H6.
  rewrite H6 in H4; rewrite sin_0 in H4; elim (Rlt_irrefl R0 H4).
  change (R0 < (x - y) / R2) in H6;
    generalize (Ropp_le_ge_contravar (- (PI / R2)) y H1).
  rewrite Ropp_involutive.
  intro H7; generalize (Rge_le (PI / R2) (- y) H7); clear H7; intro H7;
    generalize (Rplus_le_compat x (PI / R2) (- y) (PI / R2) H0 H7).
  rewrite <- double_var.
  intro H8.
  assert (Hyp : R0 < R2).
  exact Rlt_0_2.
  generalize
    (Rmult_le_compat_l (/ R2) (x - y) PI
      (Rlt_le R0 (/ R2) (Rinv_0_lt_compat R2 Hyp)) H8).
  repeat rewrite (Rmult_comm (/ R2)).
  intro H9;
    generalize
      (sin_gt_0 ((x - y) / R2) H6
        (Rle_lt_trans ((x - y) / R2) (PI / R2) PI H9 PI2_Rlt_PI));
      intro H10;
        elim
          (Rlt_irrefl (sin ((x - y) / R2))
            (Rlt_trans (sin ((x - y) / R2)) R0 (sin ((x - y) / R2)) H4 H10)).
  generalize (Rlt_minus (sin x) (sin y) H3); clear H3; intro H3;
    rewrite form4 in H3;
      generalize (Rplus_le_compat x (PI / R2) y (PI / R2) H0 H2).
  rewrite <- double_var.
  assert (Hyp : R0 < R2).
  exact Rlt_0_2.
  intro H4;
    generalize
      (Rmult_le_compat_l (/ R2) (x + y) PI
        (Rlt_le R0 (/ R2) (Rinv_0_lt_compat R2 Hyp)) H4).
  repeat rewrite (Rmult_comm (/ R2)).
  clear H4; intro H4;
    generalize (Rplus_le_compat (- (PI / R2)) x (- (PI / R2)) y H H1);
      replace (- (PI / R2) + - (PI / R2)) with (- PI).
2:{
unfold Rdiv.
rewrite Ropp_mult_distr_l.
fold (- PI / R2).
change R2 with (IZR 2).
rewrite <- double_var.
reflexivity.
}
  intro H5;
    generalize
      (Rmult_le_compat_l (/ R2) (- PI) (x + y)
        (Rlt_le R0 (/ R2) (Rinv_0_lt_compat R2 Hyp)) H5).
  replace (/ R2 * (x + y)) with ((x + y) / R2) by apply Rmult_comm.
  replace (/ R2 * - PI) with (- (PI / R2)).
2:{
unfold Rdiv.
rewrite Ropp_mult_distr_l.
rewrite Rmult_comm.
reflexivity.
}
  clear H5; intro H5; elim H4; intro H40.
  elim H5; intro H50.
  generalize (cos_gt_0 ((x + y) / R2) H50 H40); intro H6;
    generalize (Rmult_lt_compat_l R2 R0 (cos ((x + y) / R2)) Hyp H6).
  rewrite Rmult_0_r.
  clear H6; intro H6; case (Rcase_abs (sin ((x - y) / R2))); intro H7.
  assumption.
  generalize (Rge_le (sin ((x - y) / R2)) R0 H7); clear H7; intro H7;
    generalize
      (Rmult_le_pos (R2 * cos ((x + y) / R2)) (sin ((x - y) / R2))
        (Rlt_le R0 (R2 * cos ((x + y) / R2)) H6) H7); intro H8;
      generalize
        (Rle_lt_trans R0 (R2 * cos ((x + y) / R2) * sin ((x - y) / R2)) R0 H8 H3);
        intro H9; elim (Rlt_irrefl R0 H9).
  rewrite <- H50 in H3; rewrite cos_neg in H3; rewrite cos_PI2 in H3;
    rewrite Rmult_0_r in H3; rewrite Rmult_0_l in H3;
      elim (Rlt_irrefl R0 H3).
  unfold Rdiv in H3.
  rewrite H40 in H3; assert (H50 := cos_PI2); unfold Rdiv in H50;
    rewrite H50 in H3; rewrite Rmult_0_r in H3; rewrite Rmult_0_l in H3;
      elim (Rlt_irrefl R0 H3).
Qed.

Lemma sin_increasing_1 :
  forall x y:R,
    - (PI / R2) <= x ->
    x <= PI / R2 -> - (PI / R2) <= y -> y <= PI / R2 -> x < y -> sin x < sin y.
Proof.
  intros; generalize (Rplus_lt_compat_l x x y H3); intro H4;
    generalize (Rplus_le_compat (- (PI / R2)) x (- (PI / R2)) x H H);
      replace (- (PI / R2) + - (PI / R2)) with (- PI).
  assert (Hyp : R0 < R2).
  exact Rlt_0_2.
  intro H5; generalize (Rle_lt_trans (- PI) (x + x) (x + y) H5 H4); intro H6;
    generalize
      (Rmult_lt_compat_l (/ R2) (- PI) (x + y) (Rinv_0_lt_compat R2 Hyp) H6);
      replace (/ R2 * - PI) with (- (PI / R2)).
2:{
unfold Rdiv.
rewrite Ropp_mult_distr_l.
rewrite Rmult_comm.
reflexivity.
}
  replace (/ R2 * (x + y)) with ((x + y) / R2) by apply Rmult_comm.
  clear H4 H5 H6; intro H4; generalize (Rplus_lt_compat_l y x y H3); intro H5;
    rewrite Rplus_comm in H5;
      generalize (Rplus_le_compat y (PI / R2) y (PI / R2) H2 H2).
  rewrite <- double_var.
  intro H6; generalize (Rlt_le_trans (x + y) (y + y) PI H5 H6); intro H7;
    generalize (Rmult_lt_compat_l (/ R2) (x + y) PI (Rinv_0_lt_compat R2 Hyp) H7);
      replace (/ R2 * PI) with (PI / R2) by apply Rmult_comm.
  replace (/ R2 * (x + y)) with ((x + y) / R2) by apply Rmult_comm.
  clear H5 H6 H7; intro H5; generalize (Ropp_le_ge_contravar (- (PI / R2)) y H1);
    rewrite Ropp_involutive; clear H1; intro H1;
      generalize (Rge_le (PI / R2) (- y) H1); clear H1; intro H1;
        generalize (Ropp_le_ge_contravar y (PI / R2) H2); clear H2;
          intro H2; generalize (Rge_le (- y) (- (PI / R2)) H2);
            clear H2; intro H2; generalize (Rplus_lt_compat_l (- y) x y H3);
              replace (- y + x) with (x - y) by apply Rplus_comm.
  rewrite Rplus_opp_l.
  intro H6;
    generalize (Rmult_lt_compat_l (/ R2) (x - y) R0 (Rinv_0_lt_compat R2 Hyp) H6);
      rewrite Rmult_0_r; replace (/ R2 * (x - y)) with ((x - y) / R2) by apply Rmult_comm.
  clear H6; intro H6;
    generalize (Rplus_le_compat (- (PI / R2)) x (- (PI / R2)) (- y) H H2);
      replace (- (PI / R2) + - (PI / R2)) with (- PI).
2:{
apply Rmult_eq_reg_r with R2.
unfold Rdiv.
repeat rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
}
  intro H7;
    generalize
      (Rmult_le_compat_l (/ R2) (- PI) (x - y)
        (Rlt_le R0 (/ R2) (Rinv_0_lt_compat R2 Hyp)) H7);
      replace (/ R2 * - PI) with (- (PI / R2)).
2:{
unfold Rdiv.
rewrite Ropp_mult_distr_l.
rewrite Rmult_comm.
reflexivity.
}
  replace (/ R2 * (x - y)) with ((x - y) / R2) by apply Rmult_comm.
  clear H7; intro H7; clear H H0 H1 H2; apply Rminus_lt; rewrite form4;
    generalize (cos_gt_0 ((x + y) / R2) H4 H5); intro H8;
      generalize (Rmult_lt_0_compat R2 (cos ((x + y) / R2)) Hyp H8);
        clear H8; intro H8; cut (- PI < - (PI / R2)).
  intro H9;
    generalize
      (sin_lt_0_var ((x - y) / R2)
        (Rlt_le_trans (- PI) (- (PI / R2)) ((x - y) / R2) H9 H7) H6);
      intro H10;
        generalize
          (Rmult_lt_gt_compat_neg_l (sin ((x - y) / R2)) R0 (
            R2 * cos ((x + y) / R2)) H10 H8); intro H11; rewrite Rmult_0_r in H11;
          rewrite Rmult_comm; assumption.
  apply Ropp_lt_gt_contravar; apply PI2_Rlt_PI.

apply Rmult_eq_reg_r with R2.
unfold Rdiv.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
Qed.

Lemma sin_decreasing_0 :
  forall x y:R,
    x <= R3 * (PI / R2) ->
    PI / R2 <= x -> y <= R3 * (PI / R2) -> PI / R2 <= y -> sin x < sin y -> y < x.
Proof.
  intros; rewrite <- (sin_PI_x x) in H3; rewrite <- (sin_PI_x y) in H3;
    generalize (Ropp_lt_gt_contravar (sin (PI - x)) (sin (PI - y)) H3);
      repeat rewrite <- sin_neg;
        generalize (Rplus_le_compat_l (- PI) x (R3 * (PI / R2)) H);
          generalize (Rplus_le_compat_l (- PI) (PI / R2) x H0);
            generalize (Rplus_le_compat_l (- PI) y (R3 * (PI / R2)) H1);
              generalize (Rplus_le_compat_l (- PI) (PI / R2) y H2);
                replace (- PI + x) with (x - PI) by apply Rplus_comm.
  replace (- PI + PI / R2) with (- (PI / R2)).
  replace (- PI + y) with (y - PI) by apply Rplus_comm.
  replace (- PI + R3 * (PI / R2)) with (PI / R2).
  replace (- (PI - x)) with (x - PI).
  replace (- (PI - y)) with (y - PI).
  intros; change (sin (y - PI) < sin (x - PI)) in H8;
    apply Rplus_lt_reg_l with (- PI); rewrite Rplus_comm.
  rewrite (Rplus_comm _ x).
  apply (sin_increasing_0 (y - PI) (x - PI) H4 H5 H6 H7 H8).

  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite Rplus_comm.
  reflexivity.

  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  rewrite Rplus_comm.
  reflexivity.

  unfold R3. unfold R2 at 2.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_1_l.
  apply Rmult_eq_reg_r with R2.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite Rinv_l.
  repeat rewrite Rmult_1_r.
  unfold R2.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  repeat rewrite Rplus_assoc.
  rewrite Rplus_comm.
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_r, Rplus_0_r.
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.

  apply Rmult_eq_reg_r with R2.
  unfold Rdiv.
  rewrite Ropp_mult_distr_l.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_assoc.
  repeat rewrite Rinv_l.
  repeat rewrite Rmult_1_r.
  unfold R2.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_r.
  reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.
Qed.

Lemma sin_decreasing_1 :
  forall x y:R,
    x <= R3 * (PI / R2) ->
    PI / R2 <= x -> y <= R3 * (PI / R2) -> PI / R2 <= y -> x < y -> sin y < sin x.
Proof.
  intros; rewrite <- (sin_PI_x x); rewrite <- (sin_PI_x y);
    generalize (Rplus_le_compat_l (- PI) x (R3 * (PI / R2)) H);
      generalize (Rplus_le_compat_l (- PI) (PI / R2) x H0);
        generalize (Rplus_le_compat_l (- PI) y (R3 * (PI / R2)) H1);
          generalize (Rplus_le_compat_l (- PI) (PI / R2) y H2);
            generalize (Rplus_lt_compat_l (- PI) x y H3);
              replace (- PI + PI / R2) with (- (PI / R2)).
2:{
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_plus_distr_r.
unfold Rdiv.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
exact Neq_2_0.
}
  replace (- PI + y) with (y - PI) by apply Rplus_comm.
  replace (- PI + R3 * (PI / R2)) with (PI / R2).
2:{
apply Rmult_eq_reg_r with R2.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
repeat rewrite Rinv_l.
repeat rewrite Rmult_1_r.
unfold R3.
unfold R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
}
  replace (- PI + x) with (x - PI) by apply Rplus_comm.
  intros; apply Ropp_lt_cancel; repeat rewrite <- sin_neg;
    replace (- (PI - x)) with (x - PI).
2:{
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rplus_comm.
reflexivity.
}
  replace (- (PI - y)) with (y - PI).
2:{
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rplus_comm.
reflexivity.
}
  apply (sin_increasing_1 (x - PI) (y - PI) H7 H8 H5 H6 H4).
Qed.

Lemma cos_increasing_0 :
  forall x y:R,
    PI <= x -> x <= R2 * PI -> PI <= y -> y <= R2 * PI -> cos x < cos y -> x < y.
Proof.
  intros x y H1 H2 H3 H4; rewrite <- (cos_neg x); rewrite <- (cos_neg y);
    rewrite <- (cos_period (- x) 1); rewrite <- (cos_period (- y) 1);
      unfold INR in |- *;
        replace (- x + R2 * R1 * PI) with (PI / R2 - (x - R3 * (PI / R2))).
2:{
unfold Rminus, Rdiv.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rmult_1_r.
apply Rmult_eq_reg_r with R2.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
unfold R3.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
}
  replace (- y + R2 * R1 * PI) with (PI / R2 - (y - R3 * (PI / R2))).
2:{
apply Rmult_eq_reg_r with R2.
unfold Rminus, Rdiv.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
unfold R3.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
}
  repeat rewrite cos_shift; intro H5;
    generalize (Rplus_le_compat_l (-R3 * (PI / R2)) PI x H1);
      generalize (Rplus_le_compat_l (-R3 * (PI / R2)) x (R2 * PI) H2);
        generalize (Rplus_le_compat_l (-R3 * (PI / R2)) PI y H3);
          generalize (Rplus_le_compat_l (-R3 * (PI / R2)) y (R2 * PI) H4).
  replace (-R3 * (PI / R2) + y) with (y - R3 * (PI / R2)).
  replace (-R3 * (PI / R2) + x) with (x - R3 * (PI / R2)).
  replace (-R3 * (PI / R2) + R2 * PI) with (PI / R2).
  replace (-R3 * (PI / R2) + PI) with (- (PI / R2)).
  clear H1 H2 H3 H4; intros H1 H2 H3 H4;
    apply Rplus_lt_reg_l with (-R3 * (PI / R2));
      replace (-R3 * (PI / R2) + x) with (x - R3 * (PI / R2)).
  replace (-R3 * (PI / R2) + y) with (y - R3 * (PI / R2)).
  apply (sin_increasing_0 (x - R3 * (PI / R2)) (y - R3 * (PI / R2)) H4 H3 H2 H1 H5).

unfold Rminus, Rdiv.
rewrite Rplus_comm.
apply Rplus_eq_compat_r.
repeat rewrite <- Rmult_assoc.
repeat rewrite <- Ropp_mult_distr_l.
reflexivity.

unfold Rminus, Rdiv.
rewrite Rplus_comm.
apply Rplus_eq_compat_r.
repeat rewrite <- Rmult_assoc.
repeat rewrite <- Ropp_mult_distr_l.
reflexivity.

unfold Rminus, Rdiv.
apply Rmult_eq_reg_r with R2.
repeat rewrite Ropp_mult_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
repeat rewrite Rmult_1_r.
unfold R3, R2.
repeat rewrite Ropp_plus_distr.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
rewrite Rplus_opp_l, Rplus_0_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.

unfold Rminus, Rdiv.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
repeat rewrite Rmult_1_r.
unfold R3, R2.
repeat rewrite Ropp_plus_distr.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.

unfold Rminus, Rdiv.
rewrite Rplus_comm.
apply Rplus_eq_compat_r.
repeat rewrite <- Rmult_assoc.
repeat rewrite <- Ropp_mult_distr_l.
reflexivity.

unfold Rminus, Rdiv.
rewrite Rplus_comm.
apply Rplus_eq_compat_r.
repeat rewrite <- Rmult_assoc.
repeat rewrite <- Ropp_mult_distr_l.
reflexivity.
Qed.

Lemma cos_increasing_1 :
  forall x y:R,
    PI <= x -> x <= R2 * PI -> PI <= y -> y <= R2 * PI -> x < y -> cos x < cos y.
Proof.
  intros x y H1 H2 H3 H4 H5;
    generalize (Rplus_le_compat_l (-R3 * (PI / R2)) PI x H1);
      generalize (Rplus_le_compat_l (-R3 * (PI / R2)) x (R2 * PI) H2);
        generalize (Rplus_le_compat_l (-R3 * (PI / R2)) PI y H3);
          generalize (Rplus_le_compat_l (-R3 * (PI / R2)) y (R2 * PI) H4);
            generalize (Rplus_lt_compat_l (-R3 * (PI / R2)) x y H5);
              rewrite <- (cos_neg x); rewrite <- (cos_neg y);
                rewrite <- (cos_period (- x) 1); rewrite <- (cos_period (- y) 1);
                  unfold INR in |- *; replace (-R3 * (PI / R2) + x) with (x - R3 * (PI / R2)).
  replace (-R3 * (PI / R2) + y) with (y - R3 * (PI / R2)).
  replace (-R3 * (PI / R2) + PI) with (- (PI / R2)) .
  replace (-R3 * (PI / R2) + R2 * PI) with (PI / R2).
  clear H1 H2 H3 H4 H5; intros H1 H2 H3 H4 H5;
    replace (- x + R2 * R1 * PI) with (PI / R2 - (x - R3 * (PI / R2))) .
  replace (- y + R2 * R1 * PI) with (PI / R2 - (y - R3 * (PI / R2))) .
  repeat rewrite cos_shift;
    apply
      (sin_increasing_1 (x - R3 * (PI / R2)) (y - R3 * (PI / R2)) H5 H4 H3 H2 H1).

unfold Rminus, Rdiv.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rmult_1_r.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R3, R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.

unfold Rminus, Rdiv.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rmult_1_r.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R3, R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.

unfold Rminus, Rdiv.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R3, R2.
repeat rewrite Ropp_plus_distr.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.

unfold Rminus, Rdiv.
apply Rmult_eq_reg_r with R2.
repeat rewrite Ropp_mult_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
repeat rewrite Rmult_1_r.
unfold R3, R2.
repeat rewrite Ropp_plus_distr.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.

unfold Rdiv, Rminus.
rewrite Rplus_comm.
apply Rplus_eq_compat_r.
repeat rewrite <- Ropp_mult_distr_l.
reflexivity.

unfold Rdiv, Rminus.
rewrite Rplus_comm.
apply Rplus_eq_compat_r.
repeat rewrite <- Ropp_mult_distr_l.
reflexivity.
Qed.

Lemma cos_decreasing_0 :
  forall x y:R,
    R0 <= x -> x <= PI -> R0 <= y -> y <= PI -> cos x < cos y -> y < x.
Proof.
  intros; generalize (Ropp_lt_gt_contravar (cos x) (cos y) H3);
    repeat rewrite <- neg_cos; intro H4;
      change (cos (y + PI) < cos (x + PI)) in H4; rewrite (Rplus_comm x) in H4;
        rewrite (Rplus_comm y) in H4; generalize (Rplus_le_compat_l PI R0 x H);
          generalize (Rplus_le_compat_l PI x PI H0);
            generalize (Rplus_le_compat_l PI R0 y H1);
              generalize (Rplus_le_compat_l PI y PI H2); rewrite Rplus_0_r.
  rewrite <- double.
  clear H H0 H1 H2 H3; intros; apply Rplus_lt_reg_l with PI;
    apply (cos_increasing_0 (PI + y) (PI + x) H0 H H2 H1 H4).
Qed.

Lemma cos_decreasing_1 :
  forall x y:R,
    R0 <= x -> x <= PI -> R0 <= y -> y <= PI -> x < y -> cos y < cos x.
Proof.
  intros; apply Ropp_lt_cancel; repeat rewrite <- neg_cos;
    rewrite (Rplus_comm x); rewrite (Rplus_comm y);
      generalize (Rplus_le_compat_l PI R0 x H);
        generalize (Rplus_le_compat_l PI x PI H0);
          generalize (Rplus_le_compat_l PI R0 y H1);
            generalize (Rplus_le_compat_l PI y PI H2); rewrite Rplus_0_r.
  rewrite <- double.
  generalize (Rplus_lt_compat_l PI x y H3); clear H H0 H1 H2 H3; intros;
    apply (cos_increasing_1 (PI + x) (PI + y) H3 H2 H1 H0 H).
Qed.

Lemma tan_diff :
  forall x y:R,
    cos x <> R0 -> cos y <> R0 -> tan x - tan y = sin (x - y) / (cos x * cos y).
Proof.
  intros; unfold tan in |- *; rewrite sin_minus.
  unfold Rminus, Rdiv.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc.
  symmetry.
  rewrite (Rmult_comm (cos y)).
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  apply Rplus_eq_compat_l.
  rewrite Ropp_mult_distr_r.
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (cos x)).
  repeat rewrite Rmult_assoc.
  rewrite (Rmult_comm (/ cos x)).
  repeat rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite <- Ropp_mult_distr_l.
  reflexivity.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.

Lemma tan_increasing_0 :
  forall x y:R,
    - (PI / R4) <= x ->
    x <= PI / R4 -> - (PI / R4) <= y -> y <= PI / R4 -> tan x < tan y -> x < y.
Proof.
  intros; generalize PI4_RLT_PI2; intro H4;
    generalize (Ropp_lt_gt_contravar (PI / R4) (PI / R2) H4);
      intro H5; change (- (PI / R2) < - (PI / R4)) in H5;
        generalize
          (cos_gt_0 x (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) x H5 H)
            (Rle_lt_trans x (PI / R4) (PI / R2) H0 H4)); intro HP1;
          generalize
            (cos_gt_0 y (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) y H5 H1)
              (Rle_lt_trans y (PI / R4) (PI / R2) H2 H4)); intro HP2;
            generalize
              (not_eq_sym
                (Rlt_not_eq R0 (cos x)
                  (cos_gt_0 x (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) x H5 H)
                    (Rle_lt_trans x (PI / R4) (PI / R2) H0 H4))));
              intro H6;
                generalize
                  (not_eq_sym
                    (Rlt_not_eq R0 (cos y)
                      (cos_gt_0 y (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) y H5 H1)
                        (Rle_lt_trans y (PI / R4) (PI / R2) H2 H4))));
                  intro H7; generalize (tan_diff x y H6 H7); intro H8;
                    generalize (Rlt_minus (tan x) (tan y) H3); clear H3;
                      intro H3; rewrite H8 in H3; cut (sin (x - y) < R0).
  intro H9; generalize (Ropp_le_ge_contravar (- (PI / R4)) y H1);
    rewrite Ropp_involutive; intro H10; generalize (Rge_le (PI / R4) (- y) H10);
      clear H10; intro H10; generalize (Ropp_le_ge_contravar y (PI / R4) H2);
        intro H11; generalize (Rge_le (- y) (- (PI / R4)) H11);
          clear H11; intro H11;
            generalize (Rplus_le_compat (- (PI / R4)) x (- (PI / R4)) (- y) H H11);
              generalize (Rplus_le_compat x (PI / R4) (- y) (PI / R4) H0 H10).
  replace (PI / R4 + PI / R4) with (PI / R2).
2:{
apply Rmult_eq_reg_r with R4.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R2)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
unfold R4.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
exact Neq_4_0.
exact Neq_4_0.
 }
  replace (- (PI / R4) + - (PI / R4)) with (- (PI / R2)).
  intros; case (Rtotal_order R0 (x - y)); intro H14.
  generalize
    (sin_gt_0 (x - y) H14 (Rle_lt_trans (x - y) (PI / R2) PI H12 PI2_Rlt_PI));
    intro H15; elim (Rlt_irrefl R0 (Rlt_trans R0 (sin (x - y)) R0 H15 H9)).
  elim H14; intro H15.
  rewrite <- H15 in H9; rewrite sin_0 in H9; elim (Rlt_irrefl R0 H9).
  apply Rminus_lt; assumption.

repeat rewrite <- Ropp_plus_distr.
apply Ropp_eq_compat.
apply Rmult_eq_reg_r with R4.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R2)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
unfold R4.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
exact Neq_4_0.
exact Neq_4_0.

  case (Rcase_abs (sin (x - y))); intro H9.
  assumption.
  generalize (Rge_le (sin (x - y)) R0 H9); clear H9; intro H9;
    generalize (Rinv_0_lt_compat (cos x) HP1); intro H10;
      generalize (Rinv_0_lt_compat (cos y) HP2); intro H11;
        generalize (Rmult_lt_0_compat (/ cos x) (/ cos y) H10 H11);
          replace (/ cos x * / cos y) with (/ (cos x * cos y)).
  intro H12;
    generalize
      (Rmult_le_pos (sin (x - y)) (/ (cos x * cos y)) H9
        (Rlt_le R0 (/ (cos x * cos y)) H12)); intro H13;
      elim
        (Rlt_irrefl R0 (Rle_lt_trans R0 (sin (x - y) * / (cos x * cos y)) R0 H13 H3)).
  apply Rinv_mult_distr.
  assumption.
  assumption.
Qed.

Lemma tan_increasing_1 :
  forall x y:R,
    - (PI / R4) <= x ->
    x <= PI / R4 -> - (PI / R4) <= y -> y <= PI / R4 -> x < y -> tan x < tan y.
Proof.
  intros; apply Rminus_lt; generalize PI4_RLT_PI2; intro H4;
    generalize (Ropp_lt_gt_contravar (PI / R4) (PI / R2) H4);
      intro H5; change (- (PI / R2) < - (PI / R4)) in H5;
        generalize
          (cos_gt_0 x (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) x H5 H)
            (Rle_lt_trans x (PI / R4) (PI / R2) H0 H4)); intro HP1;
          generalize
            (cos_gt_0 y (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) y H5 H1)
              (Rle_lt_trans y (PI / R4) (PI / R2) H2 H4)); intro HP2;
            generalize
              (not_eq_sym
                (Rlt_not_eq R0 (cos x)
                  (cos_gt_0 x (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) x H5 H)
                    (Rle_lt_trans x (PI / R4) (PI / R2) H0 H4))));
              intro H6;
                generalize
                  (not_eq_sym
                    (Rlt_not_eq R0 (cos y)
                      (cos_gt_0 y (Rlt_le_trans (- (PI / R2)) (- (PI / R4)) y H5 H1)
                        (Rle_lt_trans y (PI / R4) (PI / R2) H2 H4))));
                  intro H7; rewrite (tan_diff x y H6 H7);
                    generalize (Rinv_0_lt_compat (cos x) HP1); intro H10;
                      generalize (Rinv_0_lt_compat (cos y) HP2); intro H11;
                        generalize (Rmult_lt_0_compat (/ cos x) (/ cos y) H10 H11);
                          replace (/ cos x * / cos y) with (/ (cos x * cos y)).
  clear H10 H11; intro H8; generalize (Ropp_le_ge_contravar y (PI / R4) H2);
    intro H11; generalize (Rge_le (- y) (- (PI / R4)) H11);
      clear H11; intro H11;
        generalize (Rplus_le_compat (- (PI / R4)) x (- (PI / R4)) (- y) H H11).
  replace (- (PI / R4) + - (PI / R4)) with (- (PI / R2)).
2:{
repeat rewrite <- Ropp_plus_distr.
apply Ropp_eq_compat.
apply Rmult_eq_reg_r with R4.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_assoc.
rewrite (Rmult_comm (/R2)).
repeat rewrite Rmult_assoc.
rewrite Rinv_r.
rewrite Rmult_1_r.
unfold R4.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_r.
repeat rewrite <- Rplus_assoc.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
exact Neq_4_0.
exact Neq_4_0.
}
  clear H11; intro H9; generalize (Rlt_minus x y H3); clear H3; intro H3;
    clear H H0 H1 H2 H4 H5 HP1 HP2; generalize PI2_Rlt_PI;
      intro H1; generalize (Ropp_lt_gt_contravar (PI / R2) PI H1);
        clear H1; intro H1;
          generalize
            (sin_lt_0_var (x - y) (Rlt_le_trans (- PI) (- (PI / R2)) (x - y) H1 H9) H3);
            intro H2;
              generalize
                (Rmult_lt_gt_compat_neg_l (sin (x - y)) R0 (/ (cos x * cos y)) H2 H8);
                rewrite Rmult_0_r; intro H4; assumption.
  apply Rinv_mult_distr; assumption.
Qed.

Lemma sin_incr_0 :
  forall x y:R,
    - (PI / R2) <= x ->
    x <= PI / R2 -> - (PI / R2) <= y -> y <= PI / R2 -> sin x <= sin y -> x <= y.
Proof.
  intros; case (Rtotal_order (sin x) (sin y)); intro H4;
    [ left; apply (sin_increasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (sin_increasing_1 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl (sin y) H8) ] ]
          | elim (Rlt_irrefl (sin x) (Rle_lt_trans (sin x) (sin y) (sin x) H3 H5)) ] ].
Qed.

Lemma sin_incr_1 :
  forall x y:R,
    - (PI / R2) <= x ->
    x <= PI / R2 -> - (PI / R2) <= y -> y <= PI / R2 -> x <= y -> sin x <= sin y.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (sin_increasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (sin x) (sin y)); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (sin_increasing_0 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl y H8) ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma sin_decr_0 :
  forall x y:R,
    x <= R3 * (PI / R2) ->
    PI / R2 <= x ->
    y <= R3 * (PI / R2) -> PI / R2 <= y -> sin x <= sin y -> y <= x.
Proof.
  intros; case (Rtotal_order (sin x) (sin y)); intro H4;
    [ left; apply (sin_decreasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ generalize (sin_decreasing_1 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl (sin y) H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl (sin x) (Rle_lt_trans (sin x) (sin y) (sin x) H3 H5)) ] ].
Qed.

Lemma sin_decr_1 :
  forall x y:R,
    x <= R3 * (PI / R2) ->
    PI / R2 <= x ->
    y <= R3 * (PI / R2) -> PI / R2 <= y -> x <= y -> sin y <= sin x.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (sin_decreasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (sin x) (sin y)); intro H6;
          [ generalize (sin_decreasing_0 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl y H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma cos_incr_0 :
  forall x y:R,
    PI <= x ->
    x <= R2 * PI -> PI <= y -> y <= R2 * PI -> cos x <= cos y -> x <= y.
Proof.
  intros; case (Rtotal_order (cos x) (cos y)); intro H4;
    [ left; apply (cos_increasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (cos_increasing_1 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl (cos y) H8) ] ]
          | elim (Rlt_irrefl (cos x) (Rle_lt_trans (cos x) (cos y) (cos x) H3 H5)) ] ].
Qed.

Lemma cos_incr_1 :
  forall x y:R,
    PI <= x ->
    x <= R2 * PI -> PI <= y -> y <= R2 * PI -> x <= y -> cos x <= cos y.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (cos_increasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (cos x) (cos y)); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (cos_increasing_0 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl y H8) ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma cos_decr_0 :
  forall x y:R,
    R0 <= x -> x <= PI -> R0 <= y -> y <= PI -> cos x <= cos y -> y <= x.
Proof.
  intros; case (Rtotal_order (cos x) (cos y)); intro H4;
    [ left; apply (cos_decreasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ generalize (cos_decreasing_1 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl (cos y) H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl (cos x) (Rle_lt_trans (cos x) (cos y) (cos x) H3 H5)) ] ].
Qed.

Lemma cos_decr_1 :
  forall x y:R,
    R0 <= x -> x <= PI -> R0 <= y -> y <= PI -> x <= y -> cos y <= cos x.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (cos_decreasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (cos x) (cos y)); intro H6;
          [ generalize (cos_decreasing_0 x y H H0 H1 H2 H6); intro H8;
            rewrite H5 in H8; elim (Rlt_irrefl y H8)
            | elim H6; intro H7;
              [ right; symmetry  in |- *; assumption | left; assumption ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

Lemma tan_incr_0 :
  forall x y:R,
    - (PI / R4) <= x ->
    x <= PI / R4 -> - (PI / R4) <= y -> y <= PI / R4 -> tan x <= tan y -> x <= y.
Proof.
  intros; case (Rtotal_order (tan x) (tan y)); intro H4;
    [ left; apply (tan_increasing_0 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order x y); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (tan_increasing_1 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl (tan y) H8) ] ]
          | elim (Rlt_irrefl (tan x) (Rle_lt_trans (tan x) (tan y) (tan x) H3 H5)) ] ].
Qed.

Lemma tan_incr_1 :
  forall x y:R,
    - (PI / R4) <= x ->
    x <= PI / R4 -> - (PI / R4) <= y -> y <= PI / R4 -> x <= y -> tan x <= tan y.
Proof.
  intros; case (Rtotal_order x y); intro H4;
    [ left; apply (tan_increasing_1 x y H H0 H1 H2 H4)
      | elim H4; intro H5;
        [ case (Rtotal_order (tan x) (tan y)); intro H6;
          [ left; assumption
            | elim H6; intro H7;
              [ right; assumption
                | generalize (tan_increasing_0 y x H1 H2 H H0 H7); intro H8;
                  rewrite H5 in H8; elim (Rlt_irrefl y H8) ] ]
          | elim (Rlt_irrefl x (Rle_lt_trans x y x H3 H5)) ] ].
Qed.

(**********)
Lemma sin_eq_0_1 : forall x:R, (exists k : Z, x = IZR k * PI) -> sin x = R0.
Proof.
  intros.
  elim H; intros.
  apply (Zcase_sign x0).
  intro.
  rewrite H1 in H0.
  simpl in H0.
  rewrite H0; rewrite Rmult_0_l; apply sin_0.
  intro.
  cut (0 <= x0)%Z.
  intro.
  elim (IZN x0 H2); intros.
  rewrite H3 in H0.
  rewrite <- INR_IZR_INZ in H0.
  rewrite H0.
  elim (even_odd_cor x1); intros.
  elim H4; intro.
  rewrite H5.
  rewrite mult_INR.
  simpl in |- *.
  rewrite <- (Rplus_0_l ((R1 + R1) * INR x2 * PI)).
  rewrite sin_period.
  apply sin_0.
  rewrite H5.
  rewrite S_INR; rewrite mult_INR.
  simpl in |- *.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l; rewrite sin_plus.
  rewrite sin_PI.
  rewrite Rmult_0_r.
  rewrite <- (Rplus_0_l ((R1 + R1) * INR x2 * PI)).
  rewrite sin_period.
  rewrite sin_0.
rewrite Rmult_0_l. rewrite Rplus_0_l. reflexivity.
  apply le_IZR.
  left; apply IZR_lt.
  assert (H2 := Z.gt_lt_iff).
  elim (H2 x0 0%Z); intros.
  apply H3; assumption.
  intro.
  rewrite H0.
  replace (sin (IZR x0 * PI)) with (- sin (- IZR x0 * PI)).
  cut (0 <= - x0)%Z.
  intro.
  rewrite <- Ropp_Ropp_IZR.
  elim (IZN (- x0) H2); intros.
  rewrite H3.
  rewrite <- INR_IZR_INZ.
  elim (even_odd_cor x1); intros.
  elim H4; intro.
  rewrite H5.
  rewrite mult_INR.
  simpl in |- *.
  rewrite <- (Rplus_0_l ((R1 + R1) * INR x2 * PI)).
  rewrite sin_period.
  rewrite sin_0. rewrite Ropp_0. reflexivity.
  rewrite H5.
  rewrite S_INR; rewrite mult_INR.
  simpl in |- *.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l; rewrite sin_plus.
  rewrite sin_PI.
  rewrite Rmult_0_r.
  rewrite <- (Rplus_0_l ((R1 + R1) * INR x2 * PI)).
  rewrite sin_period.
  rewrite sin_0. rewrite Rmult_0_l. rewrite Ropp_plus_distr.
rewrite Ropp_0. rewrite Rplus_0_r. reflexivity.
  apply le_IZR.
  apply Rplus_le_reg_l with (IZR x0).
  rewrite Rplus_0_r.
  rewrite Ropp_Ropp_IZR.
  rewrite Rplus_opp_r.
  apply Rlt_le.
change R0 with (IZR 0).
apply IZR_lt.
assumption.
  rewrite <- sin_neg.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite Ropp_involutive.
  reflexivity.
Qed.

Lemma sin_eq_0_0 (x:R) : sin x = R0 ->  exists k : Z, x = IZR k * PI.
Proof.
  intros Hx.
  destruct (euclidian_division x PI PI_neq0) as (q & r & EQ & Hr & Hr').
  exists q.
  rewrite <- (Rplus_0_r (_*_)). subst. apply Rplus_eq_compat_l.
  rewrite sin_plus in Hx.
  assert (H : sin (IZR q * PI) = R0) by (apply sin_eq_0_1; now exists q).
  rewrite H, Rmult_0_l, Rplus_0_l in Hx.
  destruct (Rmult_integral _ _ Hx) as [H'|H'].
  - exfalso.
    generalize (sin2_cos2 (IZR q * PI)).
    rewrite H, H', Rsqr_0, Rplus_0_l.
    intros; now apply R1_neq_R0.
  - rewrite Rabs_right in Hr'; [|left; apply PI_RGT_0].
    destruct Hr as [Hr | ->]; trivial.
    exfalso.
    generalize (sin_gt_0 r Hr Hr'). rewrite H'. apply Rlt_irrefl.
Qed.

Lemma cos_eq_0_0 (x:R) :
  cos x = R0 ->  exists k : Z, x = IZR k * PI + PI / R2.
Proof.
  rewrite cos_sin. intros Hx.
  destruct (sin_eq_0_0 (PI/R2 + x) Hx) as (k,Hk). clear Hx.
  exists (k-1)%Z. rewrite <- Z_R_minus; simpl.
  symmetry in Hk.
unfold Rminus.
rewrite Rmult_plus_distr_r.
rewrite Hk.
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
apply Rmult_eq_reg_r with R2.
repeat rewrite Rmult_plus_distr_r.
unfold Rdiv.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_1_r.
symmetry.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
rewrite Rplus_opp_l, Rplus_0_l.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
Qed.

Lemma cos_eq_0_1 (x:R) :
  (exists k : Z, x = IZR k * PI + PI / R2) -> cos x = R0.
Proof.
  rewrite cos_sin. intros (k,->).
  replace (_ + _) with (IZR k * PI + PI).
2:{
symmetry.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
apply Rmult_eq_reg_r with R2.
unfold Rdiv.
rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_assoc.
rewrite Rinv_l.
rewrite Rmult_1_r.
unfold R2.
rewrite Rmult_plus_distr_l.
rewrite Rmult_1_r.
reflexivity.
exact Neq_2_0.
exact Neq_2_0.
}
  rewrite neg_sin, <- Ropp_0. apply Ropp_eq_compat.
  apply sin_eq_0_1. now exists k.
Qed.

Lemma sin_eq_O_2PI_0 (x:R) :
  R0 <= x -> x <= R2 * PI -> sin x = R0 ->
  x = R0 \/ x = PI \/ x = R2 * PI.
Proof.

Admitted.

Lemma sin_eq_O_2PI_1 (x:R) :
  R0 <= x -> x <= R2 * PI ->
  x = R0 \/ x = PI \/ x = R2 * PI -> sin x = R0.
Proof.
  intros _ _ [ -> |[ -> | -> ]].
  - now rewrite sin_0.
  - now rewrite sin_PI.
  - now rewrite sin_2PI.
Qed.

Lemma cos_eq_0_2PI_0 (x:R) :
  R0 <= x -> x <= R2 * PI -> cos x = R0 ->
  x = PI / R2 \/ x = R3 * (PI / R2).
Proof.
  intros Lo Hi Hx.
  destruct (Rtotal_order x (R3 * (PI / R2))) as [LT|[EQ|GT]].
  - rewrite cos_sin in Hx.
    assert (Lo' : R0 <= PI / R2 + x).
    { apply Rplus_le_le_0_compat. apply Rlt_le, PI2_RGT_0. trivial. }
    assert (Hi' : PI / R2 + x <= R2 * PI).
    { apply Rlt_le.
      replace (R2 * PI) with (PI / R2 + R3 * (PI / R2)) .
2:{ admit. }
      now apply Rplus_lt_compat_l. }
    destruct (sin_eq_O_2PI_0 (PI / R2 + x) Lo' Hi' Hx) as [H|[H|H]].
    + exfalso.
      apply (Rplus_le_compat_l (PI/R2)) in Lo.
      rewrite Rplus_0_r, H in Lo.
      apply (Rlt_irrefl R0 (Rlt_le_trans R0 (PI / R2) R0 PI2_RGT_0 Lo)).
    + left.
      apply (Rplus_eq_compat_l (-(PI/R2))) in H.
      ring_simplify in H. rewrite H. field.
    + right.
      apply (Rplus_eq_compat_l (-(PI/2))) in H.
      ring_simplify in H. rewrite H. field.
  - now right.
  - exfalso.
    destruct (cos_eq_0_0 x Hx) as (k,Hk). clear Hx Lo.
    subst.
    assert (LT : (k < 2)%Z).
    { apply lt_IZR. simpl.
      apply (Rmult_lt_reg_r PI); [apply PI_RGT_0|].
      apply Rlt_le_trans with (IZR k * PI + PI/2); trivial.
      rewrite <- (Rplus_0_r (IZR k * PI)) at 1.
      apply Rplus_lt_compat_l. apply PI2_RGT_0. }
    assert (GT' : (1 < k)%Z).
    { apply lt_IZR. simpl.
      apply (Rmult_lt_reg_r PI); [apply PI_RGT_0|rewrite Rmult_1_l].
      replace (3*(PI/2)) with (PI/2 + PI) in GT by field.
      rewrite Rplus_comm in GT.
      now apply Rplus_lt_reg_l in GT. }
    omega.
Qed.

Lemma cos_eq_0_2PI_1 (x:R) :
  0 <= x -> x <= 2 * PI ->
  x = PI / 2 \/ x = 3 * (PI / 2) -> cos x = 0.
Proof.
 intros Lo Hi [ -> | -> ].
 - now rewrite cos_PI2.
 - now rewrite cos_3PI2.
Qed.
