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
Require Import XRtrigo1.
Require Import XRanalysis_reg.
Require Import XRfunctions.
Require Import XAltSeries.
Require Import XRseries.
Require Import XSeqProp.
Require Import XPartSum.
Require Import XRatan.
Require Import Omega.

Local Open Scope XR_scope.

(* Proving a few formulas in the style of John Machin to compute Pi *)

Definition atan_sub u v := (u - v)/(R1 + u * v).

Lemma atan_sub_correct :
 forall u v, R1 + u * v <> R0 -> -PI/R2 < atan u - atan v < PI/R2 ->
   -PI/R2 < atan (atan_sub u v) < PI/R2 ->
   atan u = atan v + atan (atan_sub u v).
Proof.
intros u v pn0 uvint aint.
assert (cos (atan u) <> R0).
 destruct (atan_bound u); apply Rgt_not_eq, cos_gt_0; auto.
 rewrite <- Ropp_div; assumption.
assert (cos (atan v) <> R0).
 destruct (atan_bound v); apply Rgt_not_eq, cos_gt_0; auto.
 rewrite <- Ropp_div; assumption.
assert (t : forall a b c, a - b = c -> a = b + c) by (intros; subst; admit).
apply t, tan_is_inj; clear t; try assumption.
rewrite tan_minus; auto.
  rewrite !atan_right_inv; reflexivity.
apply Rgt_not_eq, cos_gt_0; rewrite <- ?Ropp_div; tauto.
rewrite !atan_right_inv; assumption.
Admitted.

Lemma tech : forall x y , - R1 <= x <= R1 -> -R1 < y < R1 -> 
  -PI/R2 < atan x - atan y < PI/R2.
Proof.
assert (ut := PI_RGT_0).
intros x y [xm1 x1] [ym1 y1].
assert (-(PI/R4) <= atan x).
 destruct xm1 as [xm1 | xm1].
  rewrite <- atan_1, <- atan_opp; apply Rlt_le, atan_increasing.
  assumption.
 solve[rewrite <- xm1; change (-R1) with (-(R1)); rewrite atan_opp, atan_1; apply Rle_refl].
assert (-(PI/R4) < atan y).
 rewrite <- atan_1, <- atan_opp; apply atan_increasing.
 assumption.
assert (atan x <= PI/R4).
 destruct x1 as [x1 | x1].
  rewrite <- atan_1; apply Rlt_le, atan_increasing.
  assumption.
 solve[rewrite x1, atan_1; apply Rle_refl].
assert (atan y < PI/R4).
  rewrite <- atan_1; apply atan_increasing.
  assumption.
rewrite Ropp_div; split; admit.
Admitted.

(* A simple formula, reasonably efficient. *)
Lemma Machin_2_3 : PI/R4 = atan(/R2) + atan(/R3).
Proof.
assert (utility : R0 < PI/R2) by (apply PI2_RGT_0).
rewrite <- atan_1.
rewrite (atan_sub_correct R1 (/R2)).
   apply f_equal, f_equal; unfold atan_sub; admit.
  apply Rgt_not_eq; admit.
 apply tech; try split; try admit.
apply atan_bound.
Admitted.

Definition R100 := R10 * R10.
Definition R239 := R2 * R100 + R3 * R10 + R9.

Lemma Machin_4_5_239 : PI/R4 = R4 * atan (/R5) - atan(/R239).
Proof.
Admitted.

Lemma Machin_2_3_7 : PI/R4 = R2 * atan(/R3) + (atan (/R7)).
Proof.
Admitted.

(* More efficient way to compute approximations of PI. *)

Definition PI_2_3_7_tg n := 
  R2 * Ratan_seq (/R3) n + Ratan_seq (/R7) n.

Lemma PI_2_3_7_ineq :
  forall N : nat,
    sum_f_R0 (tg_alt PI_2_3_7_tg) (S (2 * N)) <= PI / R4 <=
    sum_f_R0 (tg_alt PI_2_3_7_tg) (2 * N).
Proof.
Admitted. 
