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
Local Open Scope XR_scope.

(*****************************************************************)
(**           To define transcendental functions                 *)
(**           and exponential function                           *)
(*****************************************************************)

(*********)

Lemma mixup : forall x n, R0 < x -> (Z.to_nat ( up x) <= n)%nat -> IZR (up x) <= INR n.
Proof.
intros x n hx h.
destruct (archimed x) as [ al ar ].
apply inj_le in h.
rewrite Z2Nat.id in h.
2:{
  apply le_IZR.
  change (IZR 0) with R0.
  apply Rle_trans with x.
  left. assumption.
  left. assumption.
}
apply IZR_le in h.
rewrite INR_IZR_INZ.
exact h.
Qed.

Lemma Alembert_exp :
  Un_cv (fun n:nat => Rabs (/ INR (fact (S n)) * / / INR (fact n))) R0.
Proof.
  unfold Un_cv.
  intros e he.
  unfold R_dist.
  unfold Rminus.
  rewrite Ropp_0.

  set (Nr := / e).

  exists (Z.to_nat (up Nr)).
  intros n hn.

  rewrite Rplus_0_r.
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  rewrite Rabs_Rabsolu.
  rewrite Rabs_Rabsolu.
  rewrite Rinv_involutive.
  2:{
    apply Rlt_not_eq'.
    change R0 with (INR 0%nat).
    apply lt_INR.
    apply lt_O_fact.
  }
  rewrite Rabs_Rinv.
  2:{
    apply Rlt_not_eq'.
    change R0 with (INR 0%nat).
    apply lt_INR.
    apply lt_O_fact.
  }
  rewrite Rmult_comm.
  rewrite Rabs_right.
  2:{
    change R0 with (INR 0%nat).
    left.
    apply lt_INR.
    apply lt_O_fact.
  }
  rewrite Rabs_right.
  2:{
    change R0 with (INR 0%nat).
    left.
    apply lt_INR.
    apply lt_O_fact.
  }
  simpl.
  rewrite plus_INR.
  rewrite mult_INR.
  set (f:=INR(fact n)).
  pattern f at 2;rewrite <- Rmult_1_l.
  rewrite <- Rmult_plus_distr_r.
  rewrite Rinv_mult_distr.
  rewrite <- Rmult_assoc.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_l.
  2:{
    unfold f.
    change R0 with (INR 0%nat).
    apply Rlt_not_eq'.
    apply lt_INR.
    apply lt_O_fact.
  }
  2:{
    apply Rlt_not_eq'.
    apply Rlt_le_trans with R1.
    exact Rlt_0_1.
    pattern R1 at 1;rewrite <- Rplus_0_r.
    apply Rplus_le_compat_l.
    change R0 with (INR 0%nat).
    apply le_INR.
    apply le_0_n.
  }
  2:{
    unfold f.
    change R0 with (INR 0%nat).
    apply Rlt_not_eq'.
    apply lt_INR.
    apply lt_O_fact.
  }
  clear f.
  destruct (archimed Nr) as [al ar].
  unfold Nr in *. clear Nr.
  rewrite <- (Rinv_involutive e).
  2:{ apply Rlt_not_eq'. exact he. }
  apply Rinv_lt_contravar.
  {
    apply Rmult_lt_0_compat.
    { apply Rinv_0_lt_compat. exact he. }
    { apply Rlt_le_trans with R1.
      { exact Rlt_0_1. }
      {
        pattern R1 at 1;rewrite <- Rplus_0_r.
        apply Rplus_le_compat_l.
        change R0 with (INR 0).
        apply le_INR.
        apply le_0_n.
      }
    }
  }
  unfold ge in hn.
  apply Rlt_le_trans with (IZR (up (/ e))).
  { exact al. }
  apply Rplus_le_reg_r with (- / e).
  apply Rle_trans with R1.
  exact ar.
  apply Rplus_le_reg_r with (/ e).
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_r.
  apply Rplus_le_compat_l.
  apply Rle_trans with (IZR (up (/ e))).
  left. exact al.
  apply mixup.
  apply Rinv_0_lt_compat. exact he.
  exact hn.
Qed.
