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
Require Import XR_sqrt.
Local Open Scope XR_scope.

Lemma tan_PI : tan PI = R0.
Proof.
  unfold tan; rewrite sin_PI; rewrite cos_PI; unfold Rdiv;
    apply Rmult_0_l.
Qed.

Lemma sin_3PI2 : sin (R3 * (PI / R2)) = -R1.
Proof.
  replace (R3 * (PI / R2)) with (PI + PI / R2).
  rewrite sin_plus; rewrite sin_PI; rewrite cos_PI; rewrite sin_PI2.
rewrite Rmult_0_l.
rewrite Rplus_0_l.
rewrite Rmult_1_r.
reflexivity.
  pattern PI at 1; rewrite (double_var PI).
change (IZR 2) with R2.
unfold R3. unfold R2 at 4.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
reflexivity.
Qed.

Lemma tan_2PI : tan (R2 * PI) = R0.
Proof.
  unfold tan; rewrite sin_2PI; unfold Rdiv; apply Rmult_0_l.
Qed.

Lemma sin_cos_PI4 : sin (PI / R4) = cos (PI / R4).
Proof.
  rewrite cos_sin.
  replace (PI / R2 + PI / R4) with (- (PI / R4) + PI).
  rewrite neg_sin, sin_neg.
rewrite Ropp_involutive. reflexivity.
apply Rmult_eq_reg_r with (R2*R4).
unfold Rdiv.
repeat rewrite Rmult_plus_distr_r.
rewrite Ropp_mult_distr_r.
repeat rewrite Rmult_assoc.
repeat rewrite <- Rmult_plus_distr_l.
apply Rmult_eq_compat_l.
rewrite <- Ropp_mult_distr_l.
rewrite (Rmult_comm R2).
repeat rewrite <- Rmult_assoc.
rewrite Rinv_l, Rmult_1_l.
symmetry.
rewrite Rmult_comm.
repeat rewrite <- Rmult_assoc.
rewrite Rinv_r, Rmult_1_l.
symmetry.
rewrite Rplus_comm.
rewrite Rmult_comm.
rewrite double.
unfold R4 at 2.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
reflexivity.
exact Neq_2_0.
apply Rlt_not_eq'. exact Rlt_0_4.
apply Rmult_integral_contrapositive_currified.
exact Neq_2_0.
apply Rlt_not_eq'. exact Rlt_0_4.
Qed.

Remark P623 : PI / R2 - PI / R3 = PI / R6.
Proof.
  unfold Rdiv, Rminus.
  rewrite Ropp_mult_distr_r.
  rewrite <- Rmult_plus_distr_l.
  apply Rmult_eq_compat_l.
  apply Rmult_eq_reg_r with (R2*R3).
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_l, Rmult_1_l.
  rewrite Rplus_comm.
  rewrite Rmult_comm.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_r, Rmult_1_l.
  repeat rewrite Rmult_assoc.
  replace (R2*R3) with R6.
  rewrite Rinv_l.
  unfold R3.
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  reflexivity.
  apply Rlt_not_eq'. exact Rlt_0_6.
  rewrite double. unfold R6. reflexivity.
  apply Rlt_not_eq'. exact Rlt_0_3.
  exact Neq_2_0.
  apply Rmult_integral_contrapositive_currified.
  exact Neq_2_0.
  apply Rlt_not_eq'. exact Rlt_0_3.
Qed.

Lemma sin_PI3_cos_PI6 : sin (PI / R3) = cos (PI / R6).
Proof.
  replace (PI / R6) with (PI / R2 - PI / R3).
  now rewrite cos_shift.
  exact P623.
Qed.

Lemma sin_PI6_cos_PI3 : cos (PI / R3) = sin (PI / R6).
Proof.
  replace (PI / R6) with (PI / R2 - PI / R3).
  now rewrite sin_shift.
  exact P623.
Qed.

Lemma PI6_RGT_0 : R0 < PI / R6.
Proof.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply PI_RGT_0 | apply Rinv_0_lt_compat ].
  exact Rlt_0_6.
Qed.

Lemma PI6_RLT_PI2 : PI / R6 < PI / R2.
Proof.
  unfold Rdiv; apply Rmult_lt_compat_l.
  apply PI_RGT_0.
  apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat.
  exact Rlt_0_2.
  exact Rlt_0_6.
  unfold R6. unfold R3. unfold R2.
  repeat rewrite <- Rplus_assoc.
  repeat apply Rplus_lt_compat_r.
  pattern R1 at 1;rewrite <- Rplus_0_l.
  repeat apply Rplus_lt_compat_r.
  repeat apply Rplus_lt_0_compat;exact Rlt_0_1.
Qed.

Lemma sin_PI6 : sin (PI / R6) = R1 / R2.
Proof.
  apply Rmult_eq_reg_l with (R2 * cos (PI / R6)).
  replace (R2 * cos (PI / R6) * sin (PI / R6)) with
  (R2 * sin (PI / R6) * cos (PI / R6)).
  rewrite <- sin_2a; replace (R2 * (PI / R6)) with (PI / R3).
  rewrite sin_PI3_cos_PI6.
{
  unfold Rdiv.
  rewrite Rmult_1_l.
  symmetry.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l.
  reflexivity.
  exact Neq_2_0.
}
{
  symmetry.
  unfold R6.
  rewrite <- double.
  change (IZR 2) with R2.
  rewrite Rmult_comm.
  unfold Rdiv.
  rewrite Rinv_mult_distr.
  rewrite (Rmult_comm (/R2)).
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l, Rmult_1_r.
  reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_3_0.
}
{
  repeat rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  rewrite Rmult_comm.
  reflexivity.
}
  apply prod_neq_R0.
exact Neq_2_0.
  cut (R0 < cos (PI / R6));
    [ intro H1; auto with real
      | apply cos_gt_0;
        [ apply (Rlt_trans (- (PI / R2)) R0 (PI / R6) _PI2_RLT_0 PI6_RGT_0)
          | apply PI6_RLT_PI2 ] ].
Qed.

Lemma sqrt2_neq_0 : sqrt R2 <> R0.
Proof.
  assert (Hyp : R0 < R2);
    [ exact Rlt_0_2
      | generalize (Rlt_le R0 R2 Hyp); intro H1; red; intro H2;
        generalize (sqrt_eq_0 R2 H1 H2); intro H; absurd (R2 = R0);
          [ idtac | assumption ] ].
exact Neq_2_0.
Qed.

Lemma R1_sqrt2_neq_0 : R1 / sqrt R2 <> R0.
Proof.
  generalize (Rinv_neq_0_compat (sqrt R2) sqrt2_neq_0); intro H;
    generalize (prod_neq_R0 R1 (/ sqrt R2) R1_neq_R0 H);
      intro H0; assumption.
Qed.

Lemma sqrt3_2_neq_0 : R2 * sqrt R3 <> R0.
Proof.
  apply prod_neq_R0;
    [ idtac
      | assert (Hyp : R0 < R3);
        [ idtac
          | generalize (Rlt_le R0 R3 Hyp); intro H1; red; intro H2;
            generalize (sqrt_eq_0 R3 H1 H2); intro H; absurd (R3 = R0);
              [ idtac | assumption ] ] ].
exact Neq_2_0.
exact Rlt_0_3.
exact Neq_3_0.
Qed.

Lemma Rlt_sqrt2_0 : R0 < sqrt R2.
Proof.
  assert (Hyp : R0 < R2);
    [ exact Rlt_0_2
      | generalize (sqrt_positivity R2 (Rlt_le R0 R2 Hyp)); intro H1; elim H1;
        intro H2;
          [ assumption
            | absurd (R0 = sqrt R2);
              [ apply (not_eq_sym (A:=R)); apply sqrt2_neq_0 | assumption ] ] ].
Qed.

Lemma Rlt_sqrt3_0 : R0 < sqrt R3.
Proof.
  cut (0%nat <> 1%nat);
    [ intro H0; assert (Hyp : R0 < R2);
      [ exact Rlt_0_2
        | generalize (Rlt_le R0 R2 Hyp); intro H1; assert (Hyp2 : R0 < R3);
          [ exact Rlt_0_3
            | generalize (Rlt_le R0 R3 Hyp2); intro H2;
              generalize (lt_INR_0 1 (neq_O_lt 1 H0));
                unfold INR; intro H3;
                  generalize (Rplus_lt_compat_l R2 R0 R1 H3);
                    rewrite Rplus_comm; rewrite Rplus_0_l; replace (R2 + R1) with R3;
                      [ intro H4; generalize (sqrt_lt_1 R2 R3 H1 H2 H4); clear H3; intro H3;
                        apply (Rlt_trans R0 (sqrt R2) (sqrt R3) Rlt_sqrt2_0 H3)
                        | idtac ] ] ]
      | discriminate ].
unfold R3.
reflexivity.
Qed.

Lemma PI4_RGT_0 : R0 < PI / R4.
Proof.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply PI_RGT_0 | apply Rinv_0_lt_compat; idtac ].
exact Rlt_0_4.
Qed.

Lemma cos_PI4 : cos (PI / R4) = R1 / sqrt R2.
Proof with trivial.
  apply Rsqr_inj...
  apply cos_ge_0...
  left; apply (Rlt_trans (- (PI / R2)) R0 (PI / R4) _PI2_RLT_0 PI4_RGT_0)...
  left; apply PI4_RLT_PI2...
  left; apply (Rmult_lt_0_compat R1 (/ sqrt R2))...
  exact Rlt_0_1...
  apply Rinv_0_lt_compat; apply Rlt_sqrt2_0...
  rewrite Rsqr_div...
  rewrite Rsqr_1; rewrite Rsqr_sqrt...
  unfold Rsqr; pattern (cos (PI / R4)) at 1;
    rewrite <- sin_cos_PI4;
      replace (sin (PI / R4) * cos (PI / R4)) with
      (R1 / R2 * (R2 * sin (PI / R4) * cos (PI / R4))).
  rewrite <- sin_2a; replace (R2 * (PI / R4)) with (PI / R2).
  rewrite sin_PI2...
{
rewrite Rmult_1_r. reflexivity.
}
{
  unfold R4. rewrite <- double.
  symmetry.
  unfold Rdiv.
  rewrite Rmult_comm.
  rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l, Rmult_1_r.
  reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.
}
{
  unfold Rdiv.
  rewrite Rmult_1_l.
  repeat rewrite <- Rmult_assoc.
  rewrite Rinv_l, Rmult_1_l.
  reflexivity.
  exact Neq_2_0.
}
left. exact Rlt_0_2.
  apply sqrt2_neq_0...
Qed.

Lemma sin_PI4 : sin (PI / R4) = R1 / sqrt R2.
Proof.
  rewrite sin_cos_PI4; apply cos_PI4.
Qed.

Lemma tan_PI4 : tan (PI / R4) = R1.
Proof.
  unfold tan; rewrite sin_cos_PI4.
  unfold Rdiv; apply Rinv_r.
  change (cos (PI / R4) <> R0); rewrite cos_PI4; apply R1_sqrt2_neq_0.
Qed.

Lemma cos3PI4 : cos (R3 * (PI / R4)) = -R1 / sqrt R2.
Proof.
  replace (R3 * (PI / R4)) with (PI / R2 - - (PI / R4)).
  rewrite cos_shift; rewrite sin_neg; rewrite sin_PI4.
  unfold Rdiv.

  rewrite <- Ropp_mult_distr_l.
  reflexivity.

  unfold Rminus.
  rewrite Ropp_involutive.
  unfold R3.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  apply Rplus_eq_compat_r.
  symmetry.
  unfold R4.
  rewrite <- double.
  unfold Rdiv.
  rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l, Rmult_1_r.
  reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.
Qed.

Lemma sin3PI4 : sin (R3 * (PI / R4)) = R1 / sqrt R2.
Proof.
  replace (R3 * (PI / R4)) with (PI / R2 - - (PI / R4)).
  now rewrite sin_shift, cos_neg, cos_PI4.
  unfold Rminus.
  rewrite Ropp_involutive.
  unfold R3.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  apply Rplus_eq_compat_r.
  symmetry.
  unfold R4.
  rewrite <- double.
  unfold Rdiv.
  rewrite Rinv_mult_distr.
  repeat rewrite Rmult_assoc.
  rewrite Rmult_comm.
  repeat rewrite Rmult_assoc.
  rewrite Rinv_l, Rmult_1_r.
  reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.
Qed.

Lemma cos_PI6 : cos (PI / R6) = sqrt R3 / R2.
Proof with trivial.
  apply Rsqr_inj...
  apply cos_ge_0...
  left; apply (Rlt_trans (- (PI / R2)) R0 (PI / R6) _PI2_RLT_0 PI6_RGT_0)...
  left; apply PI6_RLT_PI2...
  left; apply (Rmult_lt_0_compat (sqrt R3) (/ R2))...
  apply Rlt_sqrt3_0...
  apply Rinv_0_lt_compat; exact Rlt_0_2...
  rewrite Rsqr_div...
  rewrite cos2; unfold Rsqr; rewrite sin_PI6; rewrite sqrt_def...
unfold Rdiv, Rminus.
repeat rewrite Rmult_1_l.
unfold R3.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
pattern R1;rewrite double_var.
unfold Rdiv.
rewrite Ropp_mult_distr_l.
rewrite <- Rmult_plus_distr_r.
rewrite <- Rmult_plus_distr_r.
rewrite Rinv_mult_distr.
repeat rewrite <- Rmult_assoc.
rewrite <- Rmult_plus_distr_r.
apply Rmult_eq_compat_r.
rewrite Rinv_r.
repeat rewrite Rplus_assoc.
apply Rplus_eq_compat_l.
pattern R1;rewrite double_var.
unfold Rdiv.
rewrite Rmult_1_l.
repeat rewrite Rplus_assoc.
rewrite Rplus_opp_r, Rplus_0_r.
reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.
left. exact Rlt_0_3.
  exact Neq_2_0.
Qed.

Lemma tan_PI6 : tan (PI / R6) = R1 / sqrt R3.
Proof.
  unfold tan; rewrite sin_PI6; rewrite cos_PI6; unfold Rdiv;
    repeat rewrite Rmult_1_l; rewrite Rinv_mult_distr.
  rewrite Rinv_involutive.
  rewrite (Rmult_comm (/ R2)); rewrite Rmult_assoc; rewrite <- Rinv_r_sym.
  apply Rmult_1_r.
  exact Neq_2_0.
  exact Neq_2_0.
  red; intro; assert (H1 := Rlt_sqrt3_0); rewrite H in H1;
    elim (Rlt_irrefl R0 H1).
  apply Rinv_neq_0_compat; discrR.
  exact Neq_2_0.
Qed.

Lemma sin_PI3 : sin (PI / R3) = sqrt R3 / R2.
Proof.
  rewrite sin_PI3_cos_PI6; apply cos_PI6.
Qed.

Lemma cos_PI3 : cos (PI / R3) = R1 / R2.
Proof.
  rewrite sin_PI6_cos_PI3; apply sin_PI6.
Qed.

Lemma tan_PI3 : tan (PI / R3) = sqrt R3.
Proof.
  unfold tan; rewrite sin_PI3; rewrite cos_PI3; unfold Rdiv;
    rewrite Rmult_1_l; rewrite Rinv_involutive.
  rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  apply Rmult_1_r.
  exact Neq_2_0.
  exact Neq_2_0.
Qed.

Lemma sin_2PI3 : sin (R2 * (PI / R3)) = sqrt R3 / R2.
Proof.
  rewrite double; rewrite sin_plus; rewrite sin_PI3; rewrite cos_PI3;
    unfold Rdiv; repeat rewrite Rmult_1_l; rewrite (Rmult_comm (/ R2));
      repeat rewrite <- Rmult_assoc; rewrite double_var;
        reflexivity.
Qed.

Lemma cos_2PI3 : cos (R2 * (PI / R3)) = -R1 / R2.
Proof.
  rewrite cos_2a, sin_PI3, cos_PI3.
  replace (sqrt R3 / R2 * (sqrt R3 / R2)) with ((sqrt R3 * sqrt R3) / R4).
  rewrite sqrt_sqrt.
unfold Rdiv, Rminus.
repeat rewrite Rmult_1_l.
unfold R4.
rewrite <- double.
rewrite Rinv_mult_distr.
repeat rewrite Ropp_mult_distr_l.
repeat rewrite <- Rmult_assoc.
rewrite <- Rmult_plus_distr_r.
apply Rmult_eq_compat_r.
pattern (/R2) at 1;rewrite <- Rmult_1_l.
rewrite <- Rmult_plus_distr_r.
unfold R3.
rewrite Ropp_plus_distr.
rewrite Rplus_comm.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
rewrite <- Ropp_mult_distr_l.
rewrite Rinv_r.
reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
  exact Neq_2_0.
left. exact Rlt_0_3.
unfold Rdiv.
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
symmetry.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
apply Rmult_eq_compat_l.
rewrite <- Rinv_mult_distr.
unfold R4.
rewrite <- double.
reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
Qed.

Lemma tan_2PI3 : tan (R2 * (PI / R3)) = - sqrt R3.
Proof.
  unfold tan; rewrite sin_2PI3, cos_2PI3.
unfold Rdiv.
rewrite <- Ropp_mult_distr_l.
rewrite Rmult_1_l.
rewrite <- Ropp_inv_permute.
rewrite <- Ropp_mult_distr_r.
rewrite Rinv_involutive.
rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
reflexivity.
  exact Neq_2_0.
  exact Neq_2_0.
exact half_nz.
Qed.

Remark P45 : PI / R4 + PI = R5 * (PI / R4).
Proof.
unfold R5.
unfold R3.
symmetry.
repeat rewrite Rplus_assoc.
rewrite Rplus_comm.
repeat rewrite Rplus_assoc.
fold R4.
rewrite Rmult_plus_distr_r.
rewrite Rmult_1_l.
rewrite (Rmult_comm R4).
unfold Rdiv.
repeat rewrite Rmult_assoc.
rewrite Rinv_l, Rmult_1_r.
reflexivity.
apply Rlt_not_eq'. exact Rlt_0_4.
Qed.

Lemma cos_5PI4 : cos (R5 * (PI / R4)) = -R1 / sqrt R2.
Proof.
  replace (R5 * (PI / R4)) with (PI / R4 + PI).
  rewrite neg_cos; rewrite cos_PI4; unfold Rdiv.
rewrite <- Ropp_mult_distr_l. reflexivity.
exact P45.
Qed.

Lemma sin_5PI4 : sin (R5 * (PI / R4)) = -R1 / sqrt R2.
Proof.
  replace (R5 * (PI / R4)) with (PI / R4 + PI).
  rewrite neg_sin; rewrite sin_PI4; unfold Rdiv.
rewrite <- Ropp_mult_distr_l. reflexivity.
exact P45.
Qed.

Lemma sin_cos5PI4 : cos (R5 * (PI / R4)) = sin (R5 * (PI / R4)).
Proof.
  rewrite cos_5PI4; rewrite sin_5PI4; reflexivity.
Qed.

Lemma Rgt_3PI2_0 : R0 < R3 * (PI / R2).
Proof.
  apply Rmult_lt_0_compat;
    [ idtac
      | unfold Rdiv; apply Rmult_lt_0_compat;
        [ apply PI_RGT_0 | apply Rinv_0_lt_compat; idtac ] ].
exact Rlt_0_3.
exact Rlt_0_2.
Qed.

Lemma Rgt_2PI_0 : R0 < R2 * PI.
Proof.
  apply Rmult_lt_0_compat; [ idtac | apply PI_RGT_0 ].
exact Rlt_0_2.
Qed.

Lemma Rlt_PI_3PI2 : PI < R3 * (PI / R2).
Proof.
  generalize PI2_RGT_0; intro H1;
    generalize (Rplus_lt_compat_l PI R0 (PI / R2) H1);
      replace (PI + PI / R2) with (R3 * (PI / R2)).
  rewrite Rplus_0_r; intro H2; assumption.
  pattern PI at 2; rewrite double_var.
unfold R3.
unfold R2 at 1.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
reflexivity.
Qed.

Lemma Rlt_3PI2_2PI : R3 * (PI / R2) < R2 * PI.
Proof.
  generalize PI2_RGT_0; intro H1;
    generalize (Rplus_lt_compat_l (R3 * (PI / R2)) R0 (PI / R2) H1);
      replace (R3 * (PI / R2) + PI / R2) with (R2 * PI).
  rewrite Rplus_0_r; intro H2; assumption.
  rewrite double; pattern PI at 1 2; rewrite double_var.
  repeat rewrite <- Rplus_assoc.
  apply Rplus_eq_compat_r.
  symmetry.
unfold R3.
unfold R2 at 1.
repeat rewrite Rmult_plus_distr_r.
repeat rewrite Rmult_1_l.
reflexivity.
Qed.

(***************************************************************)
(** Radian -> Degree | Degree -> Radian                        *)
(***************************************************************)

Definition R180 := R18 * R10.

Definition plat : R := R180.
Definition toRad (x:R) : R := x * PI * / plat.
Definition toDeg (x:R) : R := x * plat * / PI.

Remark Neq_180_0 : R180 <> R0.
Proof.
unfold R180.
apply Rmult_integral_contrapositive_currified.
apply Rlt_not_eq'.
unfold R18. apply Rplus_lt_0_compat.
unfold R9. apply Rplus_lt_0_compat.
apply Rplus_lt_0_compat.
exact Rlt_0_3.
exact Rlt_0_3.
exact Rlt_0_3.
unfold R9. apply Rplus_lt_0_compat.
apply Rplus_lt_0_compat.
exact Rlt_0_3.
exact Rlt_0_3.
exact Rlt_0_3.
apply Rlt_not_eq'.
unfold R10.
 apply Rplus_lt_0_compat.
exact Rlt_0_5.
exact Rlt_0_5.
Qed.

Lemma rad_deg : forall x:R, toRad (toDeg x) = x.
Proof.
  intro; unfold toRad, toDeg;
    replace (x * plat * / PI * PI * / plat) with
    (x * (plat * / plat) * (PI * / PI)).
  repeat rewrite <- Rinv_r_sym.
repeat rewrite Rmult_1_r. reflexivity.
  apply PI_neq0.

unfold plat.
exact Neq_180_0.

repeat rewrite Rmult_assoc.
repeat apply Rmult_eq_compat_l.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
rewrite Rmult_comm.
repeat rewrite Rmult_assoc.
repeat apply Rmult_eq_compat_l.
rewrite Rmult_comm.
reflexivity.
Qed.

Lemma toRad_inj : forall x y:R, toRad x = toRad y -> x = y.
Proof.
  intros; unfold toRad in H; apply Rmult_eq_reg_l with PI.
  rewrite <- (Rmult_comm x); rewrite <- (Rmult_comm y).
  apply Rmult_eq_reg_l with (/ plat).
  rewrite <- (Rmult_comm (x * PI)); rewrite <- (Rmult_comm (y * PI));
    assumption.
  apply Rinv_neq_0_compat; unfold plat; discrR.
exact Neq_180_0.
  apply PI_neq0.

Qed.

Lemma deg_rad : forall x:R, toDeg (toRad x) = x.
Proof.
  intro x; apply toRad_inj; rewrite (rad_deg (toRad x)); reflexivity.
Qed.

Definition sind (x:R) : R := sin (toRad x).
Definition cosd (x:R) : R := cos (toRad x).
Definition tand (x:R) : R := tan (toRad x).

Lemma Rsqr_sin_cos_d_one : forall x:R, Rsqr (sind x) + Rsqr (cosd x) = R1.
Proof.
  intro x; unfold sind; unfold cosd; apply sin2_cos2.
Qed.

(***************************************************)
(**               Other properties                 *)
(***************************************************)

Lemma sin_lb_ge_0 : forall a:R, R0 <= a -> a <= PI / R2 -> R0 <= sin_lb a.
Proof.
  intros; case (Rtotal_order R0 a); intro.
  left; apply sin_lb_gt_0; assumption.
  elim H1; intro.
  rewrite <- H2; unfold sin_lb; unfold sin_approx;
    unfold sum_f_R0; unfold sin_term;
      repeat rewrite pow_ne_zero.
  unfold Rdiv; repeat rewrite Rmult_0_l; repeat rewrite Rmult_0_r;
    repeat rewrite Rplus_0_r; right; reflexivity.
  discriminate.
  discriminate.
  discriminate.
  discriminate.
  elim (Rlt_irrefl R0 (Rle_lt_trans R0 a R0 H H2)).
Qed.
