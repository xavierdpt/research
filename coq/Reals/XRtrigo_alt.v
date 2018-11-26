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
Require Import XRtrigo_def.
Local Open Scope XR_scope.

(***************************************************************)
(** Using series definitions of cos and sin                    *)
(***************************************************************)

Definition sin_term (a:R) (i:nat) : R :=
  (-R1) ^ i * (a ^ (2 * i + 1) / INR (fact (2 * i + 1))).

Definition cos_term (a:R) (i:nat) : R :=
  (-R1) ^ i * (a ^ (2 * i) / INR (fact (2 * i))).

Definition sin_approx (a:R) (n:nat) : R := sum_f_R0 (sin_term a) n.

Definition cos_approx (a:R) (n:nat) : R := sum_f_R0 (cos_term a) n.

(**********)
(*
Lemma Alt_PI_4 : Alt_PI <= 4.
Proof.
  assert (H0 := PI_ineq 0).
  elim H0; clear H0; intros _ H0.
  unfold tg_alt, PI_tg in H0; simpl in H0.
  rewrite Rinv_1 in H0; rewrite Rmult_1_r in H0; unfold Rdiv in H0.
  apply Rmult_le_reg_l with (/ 4).
  apply Rinv_0_lt_compat; prove_sup0.
  rewrite <- Rinv_l_sym; [ rewrite Rmult_comm; assumption | discrR ].
Qed.
*)
(**********)
Theorem pre_sin_bound :
  forall (a:R) (n:nat),
    R0 <= a ->
    a <= R4 -> sin_approx a (2 * n + 1) <= sin a <= sin_approx a (2 * (n + 1)).
Proof.
  intros; case (Req_dec a R0); intro Hyp_a.
  rewrite Hyp_a; rewrite sin_0; split; right; unfold sin_approx;
    apply sum_eq_R0 || (symmetry ; apply sum_eq_R0);
      intros; unfold sin_term; rewrite pow_add;
        simpl; unfold Rdiv; rewrite Rmult_0_l.
{
  rewrite Rmult_0_r.
  rewrite Rmult_0_l.
  rewrite Rmult_0_r.
  reflexivity.
}
{
  rewrite Rmult_0_r.
  rewrite Rmult_0_l.
  rewrite Rmult_0_r.
  reflexivity.
}
  unfold sin_approx; cut (R0 < a).
  intro Hyp_a_pos.
  rewrite (decomp_sum (sin_term a) (2 * n + 1)).
  rewrite (decomp_sum (sin_term a) (2 * (n + 1))).
  replace (sin_term a 0) with a.
  cut
    (sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * n + 1)) <= sin a - a /\
      sin a - a <= sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * (n + 1))) ->
      a + sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * n + 1)) <= sin a /\
      sin a <= a + sum_f_R0 (fun i:nat => sin_term a (S i)) (pred (2 * (n + 1)))).
  intro; apply H1.
  set (Un := fun n:nat => a ^ (2 * S n + 1) / INR (fact (2 * S n + 1))).
  replace (pred (2 * n + 1)) with (2 * n)%nat.
  replace (pred (2 * (n + 1))) with (S (2 * n)).
  replace (sum_f_R0 (fun i:nat => sin_term a (S i)) (2 * n)) with
  (- sum_f_R0 (tg_alt Un) (2 * n)).
  replace (sum_f_R0 (fun i:nat => sin_term a (S i)) (S (2 * n))) with
  (- sum_f_R0 (tg_alt Un) (S (2 * n))).
  cut
    (sum_f_R0 (tg_alt Un) (S (2 * n)) <= a - sin a <=
      sum_f_R0 (tg_alt Un) (2 * n) ->
      - sum_f_R0 (tg_alt Un) (2 * n) <= sin a - a <=
      - sum_f_R0 (tg_alt Un) (S (2 * n))).
  intro; apply H2.
  apply alternated_series_ineq.
  unfold Un_decreasing, Un; intro;
    cut ((2 * S (S n0) + 1)%nat = S (S (2 * S n0 + 1))).
  intro; rewrite H3.
  replace (a ^ S (S (2 * S n0 + 1))) with (a ^ (2 * S n0 + 1) * (a * a)).
  unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l.
  left; apply pow_lt; assumption.
  apply Rmult_le_reg_l with (INR (fact (S (S (2 * S n0 + 1))))).
  rewrite <- H3; apply lt_INR_0; apply neq_O_lt; red; intro;
    assert (H5 := eq_sym H4); elim (fact_neq_0 _ H5).
  rewrite <- H3; rewrite (Rmult_comm (INR (fact (2 * S (S n0) + 1))));
    rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite H3; do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
    repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r.
  do 2 rewrite S_INR; rewrite plus_INR; rewrite mult_INR; repeat rewrite S_INR;
    simpl;
      replace
      (((R0 + R1 + R1) * (INR n0 + R1) + (R0 + R1) + R1 + R1) *
        ((R0 + R1 + R1) * (INR n0 + R1) + (R0 + R1) + R1)) with
      (R4 * INR n0 * INR n0 + R18 * INR n0 + R20).
2:{
repeat rewrite Rplus_0_l.
unfold R20. unfold R18. unfold R10. unfold R9. unfold R5. unfold R4. unfold R3. unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_1_r.
repeat rewrite Rmult_1_l.

repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

reflexivity.


}

  apply Rle_trans with R20.
  apply Rle_trans with R16.
  replace R16 with (Rsqr R4).
2:{
  unfold Rsqr.
  unfold R16.
  unfold R8.
  unfold R4 at 1.
  unfold R2.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_1_l.
  repeat rewrite <- Rplus_assoc.
  reflexivity.
}
  apply Rsqr_incr_1.
  assumption.
  assumption.
  left.
  {
    unfold R4. pattern R0 at 1;rewrite <- Rplus_0_l.
    apply Rplus_lt_compat; exact Rlt_0_2.
  }
  {
    unfold R20.
    unfold R10.
    unfold R16.
    unfold R8.
    unfold R5.
    unfold R4.
    unfold R3.
    unfold R2.
    repeat rewrite <- Rplus_assoc.
    repeat apply Rplus_le_compat_r.
    pattern R1 at 1;rewrite <- Rplus_0_l.
    apply Rplus_le_compat_r.
    do 3 (pattern R0 at 1;rewrite <- Rplus_0_l).
    left.
    repeat apply Rplus_lt_compat;exact Rlt_0_1.
  }
  rewrite <- (Rplus_0_l R20) at 1.
  apply Rplus_le_compat_r.
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos.
  apply Rmult_le_pos.
{ left.
    unfold R4. pattern R0 at 1;rewrite <- Rplus_0_l.
    apply Rplus_lt_compat; exact Rlt_0_2.
  }
  apply pos_INR.
  apply pos_INR.
  apply Rmult_le_pos.
  {
    left.
    unfold R18. unfold R9. unfold R3. unfold R2.
    do 17 (pattern R0 at 1;rewrite <- Rplus_0_l).
    repeat rewrite <- Rplus_assoc.
    repeat apply Rplus_lt_compat; exact Rlt_0_1.
  }
  apply pos_INR.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  simpl.
{
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite (plus_comm  _ 0).
  simpl.
  rewrite (plus_comm  _ 1).
  simpl.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  reflexivity.
  }
  {
  simpl.
  rewrite (plus_comm  _ 0).
  simpl.
  rewrite (plus_comm _ 1).
  simpl.
  rewrite (plus_comm _ 1).
  simpl.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  reflexivity.
  }
  assert (H3 := cv_speed_pow_fact a); unfold Un; unfold Un_cv in H3;
    unfold R_dist in H3; unfold Un_cv; unfold R_dist;
      intros; elim (H3 eps H4); intros N H5.
  exists N; intros; apply H5.
  replace (2 * S n0 + 1)%nat with (S (2 * S n0)).
  unfold ge; apply le_trans with (2 * S n0)%nat.
  apply le_trans with (2 * S N)%nat.
  apply le_trans with (2 * N)%nat.
  apply le_n_2n.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_Sn.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_S; assumption.
  apply le_n_Sn.
  {
   simpl.
   rewrite (plus_comm _ 0).
   simpl.
   rewrite (plus_comm _ 1).
   simpl.
   repeat rewrite <- plus_n_Sm.
    reflexivity.
  }
  unfold sin.
  destruct (exist_sin (Rsqr a)) as (x,p).
  unfold sin_in, infinite_sum, R_dist in p;
      unfold Un_cv, R_dist;
      intros.
  cut (R0 < eps / Rabs a).
  intro H4; destruct (p _ H4) as (N,H6).
  exists N; intros.
  replace (sum_f_R0 (tg_alt Un) n0) with
  (a * (R1 - sum_f_R0 (fun i:nat => sin_n i * Rsqr a ^ i) (S n0))).
  unfold Rminus; rewrite Rmult_plus_distr_l; rewrite Rmult_1_r;
    rewrite Ropp_plus_distr; rewrite Ropp_involutive;
      repeat rewrite Rplus_assoc; rewrite (Rplus_comm a);
        rewrite (Rplus_comm (- a)); repeat rewrite Rplus_assoc;
          rewrite Rplus_opp_l; rewrite Rplus_0_r; apply Rmult_lt_reg_l with (/ Rabs a).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  pattern (/ Rabs a) at 1; rewrite <- (Rabs_Rinv a Hyp_a).
  rewrite <- Rabs_mult, Rmult_plus_distr_l, <- 2!Rmult_assoc, <- Rinv_l_sym;
    [ rewrite Rmult_1_l | assumption ];
      rewrite (Rmult_comm (/ Rabs a)),
        <- Rabs_Ropp, Ropp_plus_distr, Ropp_involutive, Rmult_1_l.
          unfold Rminus, Rdiv in H6. apply H6; unfold ge;
            apply le_trans with n0; [ exact H5 | apply le_n_Sn ].
  rewrite (decomp_sum (fun i:nat => sin_n i * Rsqr a ^ i) (S n0)).
  replace (sin_n 0) with R1.
  simpl; rewrite Rmult_1_r; unfold Rminus;
    rewrite Ropp_plus_distr; rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
      rewrite Rplus_0_l; rewrite Ropp_mult_distr_r_reverse;
        rewrite <- Ropp_mult_distr_l_reverse; rewrite scal_sum;
          apply sum_eq.
  intros; unfold sin_n, Un, tg_alt;
    replace ((-R1) ^ S i) with (- (-R1) ^ i).
  replace (a ^ (2 * S i + 1)) with (Rsqr a * Rsqr a ^ i * a).
  unfold Rdiv.
{
simpl.
rewrite (plus_comm i 0).
simpl.
rewrite (plus_comm _ 1).
simpl (plus 1 _).
repeat rewrite <- plus_n_Sm.
rewrite <- Ropp_mult_distr_r.
rewrite <- Ropp_mult_distr_l.
rewrite <- Ropp_mult_distr_l.
rewrite <- Ropp_mult_distr_l.
rewrite Ropp_involutive.
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
reflexivity.

}
  rewrite pow_add; rewrite pow_Rsqr; simpl.
{
rewrite Rmult_1_r.
reflexivity.
}
  simpl.
{
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
reflexivity.
}
  unfold sin_n; unfold Rdiv; simpl; rewrite Rinv_1;
    rewrite Rmult_1_r; reflexivity.
  apply lt_O_Sn.
  unfold Rdiv; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat; apply Rabs_pos_lt; assumption.
  intros; elim H2; intros.
  replace (sin a - a) with (- (a - sin a)).
2:{
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rplus_comm.
reflexivity.
}
  split; apply Ropp_le_contravar; assumption.
  replace (- sum_f_R0 (tg_alt Un) (S (2 * n))) with
  (-R1 * sum_f_R0 (tg_alt Un) (S (2 * n))). rewrite scal_sum.
2:{
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
reflexivity.
}
  apply sum_eq; intros; unfold sin_term, Un, tg_alt;
    change ((-R1) ^ S i) with (-R1 * (-R1) ^ i).
  unfold Rdiv.
{
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
rewrite <- Ropp_mult_distr_r.
rewrite Rmult_1_r.
rewrite <- Ropp_mult_distr_l.
reflexivity.
}
  replace (- sum_f_R0 (tg_alt Un) (2 * n)) with
  (-R1 * sum_f_R0 (tg_alt Un) (2 * n)).
rewrite scal_sum.
2:{
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
reflexivity.
}
  apply sum_eq; intros.
  unfold sin_term, Un, tg_alt;
    change ((-R1) ^ S i) with (-R1 * (-R1) ^ i).
  unfold Rdiv.
{
rewrite <- Ropp_mult_distr_r.
rewrite <- Ropp_mult_distr_l.
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
rewrite Rmult_1_r.
reflexivity.
}
  replace (2 * (n + 1))%nat with (S (S (2 * n))).
  reflexivity.
{
rewrite (plus_comm _ 1).
simpl.
rewrite (plus_comm _ 0).
simpl.
rewrite <- plus_n_Sm.
reflexivity.
}
  replace (2 * n + 1)%nat with (S (2 * n)).
  reflexivity.
 {
rewrite (plus_comm _ 1).
simpl.
rewrite (plus_comm _ 0).
simpl.
reflexivity.
}
  intro; elim H1; intros.
  split.
  apply Rplus_le_reg_l with (- a).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (- a)); apply H2.
  apply Rplus_le_reg_l with (- a).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (- a)); apply H3.
  unfold sin_term; simpl; unfold Rdiv; rewrite Rinv_1.
{
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.
reflexivity.
}
  replace (2 * (n + 1))%nat with (S (S (2 * n))).
  apply lt_O_Sn.
  ring.
  replace (2 * n + 1)%nat with (S (2 * n)).
  apply lt_O_Sn.
  ring.
  inversion H; [ assumption | elim Hyp_a; symmetry ; assumption ].
Qed.

(**********)
Lemma pre_cos_bound :
  forall (a:R) (n:nat),
    - R2 <= a -> a <= R2 ->
    cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1)).
Proof.
  cut
    ((forall (a:R) (n:nat),
      R0 <= a ->
      a <= R2 ->
      cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1))) ->
    forall (a:R) (n:nat),
      - R2 <= a ->
      a <= R2 ->
      cos_approx a (2 * n + 1) <= cos a <= cos_approx a (2 * (n + 1))).
  intros H a n; apply H.
  intros; unfold cos_approx.
  rewrite (decomp_sum (cos_term a0) (2 * n0 + 1)).
  rewrite (decomp_sum (cos_term a0) (2 * (n0 + 1))).
  replace (cos_term a0 0) with R1.
  cut
    (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * n0 + 1)) <= cos a0 - R1 /\
      cos a0 - R1 <=
      sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * (n0 + 1))) ->
      R1 + sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * n0 + 1)) <= cos a0 /\
      cos a0 <=
      R1 + sum_f_R0 (fun i:nat => cos_term a0 (S i)) (pred (2 * (n0 + 1)))).
  intro; apply H2.
  set (Un := fun n:nat => a0 ^ (2 * S n) / INR (fact (2 * S n))).
  replace (pred (2 * n0 + 1)) with (2 * n0)%nat.
  replace (pred (2 * (n0 + 1))) with (S (2 * n0)).
  replace (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (2 * n0)) with
  (- sum_f_R0 (tg_alt Un) (2 * n0)).
  replace (sum_f_R0 (fun i:nat => cos_term a0 (S i)) (S (2 * n0))) with
  (- sum_f_R0 (tg_alt Un) (S (2 * n0))).
  cut
    (sum_f_R0 (tg_alt Un) (S (2 * n0)) <= R1 - cos a0 <=
      sum_f_R0 (tg_alt Un) (2 * n0) ->
      - sum_f_R0 (tg_alt Un) (2 * n0) <= cos a0 - R1 <=
      - sum_f_R0 (tg_alt Un) (S (2 * n0))).
  intro; apply H3.
  apply alternated_series_ineq.
  unfold Un_decreasing; intro; unfold Un.
  cut ((2 * S (S n1))%nat = S (S (2 * S n1))).
  intro; rewrite H4;
    replace (a0 ^ S (S (2 * S n1))) with (a0 ^ (2 * S n1) * (a0 * a0)).
  unfold Rdiv; rewrite Rmult_assoc; apply Rmult_le_compat_l.
  apply pow_le; assumption.
  apply Rmult_le_reg_l with (INR (fact (S (S (2 * S n1))))).
  rewrite <- H4; apply lt_INR_0; apply neq_O_lt; red; intro;
    assert (H6 := eq_sym H5); elim (fact_neq_0 _ H6).
  rewrite <- H4; rewrite (Rmult_comm (INR (fact (2 * S (S n1)))));
    rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; rewrite H4; do 2 rewrite fact_simpl; do 2 rewrite mult_INR;
    repeat rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; do 2 rewrite S_INR; rewrite mult_INR; repeat rewrite S_INR;
    simpl;
      replace
      (((R0 + R1 + R1) * (INR n1 + R1) + R1 + R1) * ((R0 + R1 + R1) * (INR n1 + R1) + R1))
    with (R4 * INR n1 * INR n1 + R14 * INR n1 + R12).
2:{

repeat rewrite Rplus_0_l.
unfold R14.
unfold R12.
unfold R7.
unfold R6.
unfold R4.
unfold R3.
unfold R2.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_plus_distr_l.
repeat rewrite Rmult_1_l.
repeat rewrite Rmult_1_r.


repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

rewrite Rplus_comm;
repeat rewrite Rplus_assoc; repeat apply Rplus_eq_compat_l;
repeat rewrite <- Rplus_assoc; repeat apply Rplus_eq_compat_r.

reflexivity.

}
  apply Rle_trans with R12.
  apply Rle_trans with R4.
  replace R4 with (Rsqr R2).
  2:{
    unfold Rsqr. 
   unfold R4. unfold R2.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_1_r.
  repeat rewrite <- Rplus_assoc.
  reflexivity.
}
  apply Rsqr_incr_1.
  assumption.
  assumption.
  left. exact Rlt_0_2.
  {
    left.
    unfold R12. unfold R6. unfold R4. unfold R3. unfold R2.
    repeat rewrite <- Rplus_assoc.
    repeat apply Rplus_lt_compat_r.
    pattern R1 at 1;rewrite <- Rplus_0_l.
    apply Rplus_lt_compat_r.
    do 7 ( pattern R0 at 1;rewrite <- Rplus_0_l).
    repeat apply Rplus_lt_compat;exact Rlt_0_1.
  }
  rewrite <- (Rplus_0_l R12) at 1;
    apply Rplus_le_compat_r.
  apply Rplus_le_le_0_compat.
  apply Rmult_le_pos.
  apply Rmult_le_pos.
  {
    left.
    unfold R4. pattern R0 at 1;rewrite <- Rplus_0_l.
    apply Rplus_lt_compat; exact Rlt_0_2.
  }
  apply pos_INR.
  apply pos_INR.
  apply Rmult_le_pos.
  {
    left.
    unfold R14. unfold R7. unfold R4. unfold R3. unfold R2.
    repeat rewrite <- Rplus_assoc.
    do 13 ( pattern R0 at 1;rewrite <- Rplus_0_l).
    repeat apply Rplus_lt_compat;exact Rlt_0_1.
  }
  apply pos_INR.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  simpl.
{
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
reflexivity.
}
{
simpl. rewrite (plus_comm _ 0). simpl. repeat rewrite plus_n_Sm. reflexivity.
}
  assert (H4 := cv_speed_pow_fact a0); unfold Un; unfold Un_cv in H4;
    unfold R_dist in H4; unfold Un_cv; unfold R_dist;
      intros; elim (H4 eps H5); intros N H6; exists N; intros.
  apply H6; unfold ge; apply le_trans with (2 * S N)%nat.
  apply le_trans with (2 * N)%nat.
  apply le_n_2n.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_Sn.
  apply (fun m n p:nat => mult_le_compat_l p n m); apply le_n_S; assumption.
  unfold cos. destruct (exist_cos (Rsqr a0)) as (x,p).
  unfold cos_in, infinite_sum, R_dist in p;
   unfold Un_cv, R_dist; intros.
  destruct (p _ H4) as (N,H6).
  exists N; intros.
  replace (sum_f_R0 (tg_alt Un) n1) with
  (R1 - sum_f_R0 (fun i:nat => cos_n i * Rsqr a0 ^ i) (S n1)).
  unfold Rminus; rewrite Ropp_plus_distr; rewrite Ropp_involutive;
    repeat rewrite Rplus_assoc; rewrite (Rplus_comm R1);
      rewrite (Rplus_comm (-(R1))); repeat rewrite Rplus_assoc;
        rewrite Rplus_opp_l; rewrite Rplus_0_r; rewrite <- Rabs_Ropp;
          rewrite Ropp_plus_distr; rewrite Ropp_involutive;
            unfold Rminus in H6; apply H6.
  unfold ge; apply le_trans with n1.
  exact H5.
  apply le_n_Sn.
  rewrite (decomp_sum (fun i:nat => cos_n i * Rsqr a0 ^ i) (S n1)).
  replace (cos_n 0) with R1.
  simpl; rewrite Rmult_1_r; unfold Rminus;
    rewrite Ropp_plus_distr; rewrite <- Rplus_assoc; rewrite Rplus_opp_r;
      rewrite Rplus_0_l;
        replace (- sum_f_R0 (fun i:nat => cos_n (S i) * (Rsqr a0 * Rsqr a0 ^ i)) n1)
    with
      (-R1 * sum_f_R0 (fun i:nat => cos_n (S i) * (Rsqr a0 * Rsqr a0 ^ i)) n1).
2:{
rewrite <- Ropp_mult_distr_l. rewrite Rmult_1_l. reflexivity.
}
 rewrite scal_sum; apply sum_eq;
        intros; unfold cos_n, Un, tg_alt.
  replace ((-R1) ^ S i) with (- (-R1) ^ i).
  replace (a0 ^ (2 * S i)) with (Rsqr a0 * Rsqr a0 ^ i).
  unfold Rdiv.
{
repeat rewrite <- Ropp_mult_distr_l.
repeat rewrite <- Ropp_mult_distr_r.
rewrite Ropp_involutive.
rewrite Rmult_1_r.
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
reflexivity.
}
  rewrite pow_Rsqr; reflexivity.
  simpl.
{
rewrite <- Ropp_mult_distr_l. rewrite Rmult_1_l. reflexivity.
}
  unfold cos_n; unfold Rdiv; simpl; rewrite Rinv_1;
    rewrite Rmult_1_r; reflexivity.
  apply lt_O_Sn.
  intros; elim H3; intros; replace (cos a0 - R1) with (- (R1 - cos a0)).
2:{
unfold Rminus.
rewrite Ropp_plus_distr.
rewrite Ropp_involutive.
rewrite Rplus_comm.
reflexivity.
}
  split; apply Ropp_le_contravar; assumption.
  replace (- sum_f_R0 (tg_alt Un) (S (2 * n0))) with
  (-R1 * sum_f_R0 (tg_alt Un) (S (2 * n0))).
2:{
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
reflexivity.
}
(* something went wrong here *)

(*
  apply sum_eq. intros; unfold cos_term, Un, tg_alt;
    change ((-R1) ^ S i) with (-R1 * (-R1) ^ i).
  unfold Rdiv; ring.
  replace (- sum_f_R0 (tg_alt Un) (2 * n0)) with
  (-1 * sum_f_R0 (tg_alt Un) (2 * n0)); [ rewrite scal_sum | ring ];
  apply sum_eq; intros; unfold cos_term, Un, tg_alt;
    change ((-1) ^ S i) with (-1 * (-1) ^ i).
  unfold Rdiv; ring.
  replace (2 * (n0 + 1))%nat with (S (S (2 * n0))).
  reflexivity.
  ring.
  replace (2 * n0 + 1)%nat with (S (2 * n0)).
  reflexivity.
  ring.
  intro; elim H2; intros; split.
  apply Rplus_le_reg_l with (-(1)).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (-1)); apply H3.
  apply Rplus_le_reg_l with (-(1)).
  rewrite <- Rplus_assoc; rewrite Rplus_opp_l; rewrite Rplus_0_l;
    rewrite (Rplus_comm (-1)); apply H4.
  unfold cos_term; simpl; unfold Rdiv; rewrite Rinv_1;
    ring.
  replace (2 * (n0 + 1))%nat with (S (S (2 * n0))).
  apply lt_O_Sn.
  ring.
  replace (2 * n0 + 1)%nat with (S (2 * n0)).
  apply lt_O_Sn.
  ring.
  intros; destruct (total_order_T 0 a) as [[Hlt|Heq]|Hgt].
  apply H; [ left; assumption | assumption ].
  apply H; [ right; assumption | assumption ].
  cut (0 < - a).
  intro; cut (forall (x:R) (n:nat), cos_approx x n = cos_approx (- x) n).
  intro; rewrite H3; rewrite (H3 a (2 * (n + 1))%nat); rewrite cos_sym; apply H.
  left; assumption.
  rewrite <- (Ropp_involutive 2); apply Ropp_le_contravar; exact H0.
  intros; unfold cos_approx; apply sum_eq; intros;
    unfold cos_term; do 2 rewrite pow_Rsqr; rewrite Rsqr_neg;
      unfold Rdiv; reflexivity.
  apply Ropp_0_gt_lt_contravar; assumption.
*)
Admitted.
