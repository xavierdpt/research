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
Require Import XPSeries_reg.
Require Import XRtrigo1.
Require Import XRanalysis_reg.
Require Import XRfunctions.
Require Import XAltSeries.
Require Import XRseries.
Require Import XSeqProp.
Require Import XRanalysis5.
Require Import XSeqSeries.
Require Import XPartSum.
Require Import Omega.

Local Open Scope XR_scope.

(** Tools *)

Lemma Ropp_div : forall x y, -x/y = -(x/y).
Proof.
intros x y; unfold Rdiv; rewrite <-Ropp_mult_distr_l_reverse; reflexivity.
Qed.

Definition pos_half_prf : R0 < /R2.
Proof.
  apply Rinv_0_lt_compat.
  exact Rlt_0_2.
Qed.

Definition pos_half := mkposreal (/R2) pos_half_prf.

Lemma Boule_half_to_interval :
  forall x , Boule (/R2) pos_half x -> R0 <= x <= R1.
Proof.
unfold Boule, pos_half; simpl.
intros x b; apply Rabs_def2 in b; destruct b; split.
{
  left.
  apply Rplus_lt_reg_r with (-/R2).
  rewrite Rplus_0_l.
  assumption.
}
{
  replace R1 with (/R2+/R2).
  left.
  apply Rplus_lt_reg_r with (-/R2).
  repeat rewrite Rplus_assoc.
  rewrite Rplus_opp_r, Rplus_0_r.
  assumption.
  pattern (/R2);rewrite <- Rmult_1_l.
  rewrite <- Rmult_plus_distr_r.
  fold R2.
  rewrite Rinv_r.
  reflexivity.
  exact Neq_2_0.
}
Qed.

Lemma Boule_lt : forall c r x, Boule c r x -> Rabs x < Rabs c + r.
Proof.
unfold Boule; intros c r x h.
apply Rabs_def2 in h; destruct h; apply Rabs_def1;
 (destruct (Rle_lt_dec R0 c);[rewrite Rabs_pos_eq | 
    rewrite <- Rabs_Ropp, Rabs_pos_eq]).
{
  apply Rplus_lt_reg_l with (-c).
  rewrite <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
  rewrite Rplus_comm.
  assumption.
}
{ assumption. }
{
  admit.
}
{
  left.
  apply Ropp_lt_cancel.
  rewrite Ropp_involutive, Ropp_0.
  assumption.
}
{
  admit.
}
{ assumption. }
{ admit. }
{
  left.
  apply Ropp_lt_cancel.
  rewrite Ropp_involutive, Ropp_0.
  assumption.
}
Admitted.

(* The following lemma does not belong here. *)
Lemma Un_cv_ext :
  forall un vn, (forall n, un n = vn n) ->
  forall l, Un_cv un l -> Un_cv vn l.
Proof.
intros un vn quv l P eps ep; destruct (P eps ep) as [N Pn]; exists N.
intro n; rewrite <- quv; apply Pn.
Qed.

(* The following two lemmas are general purposes about alternated series.
  They do not belong here. *)
Lemma Alt_first_term_bound :forall f l N n,
   Un_decreasing f -> Un_cv f R0 ->
   Un_cv (sum_f_R0 (tg_alt f)) l ->
   (N <= n)%nat ->
   R_dist (sum_f_R0 (tg_alt f) n) l <= f N.
Proof.

Admitted.

Lemma Alt_CVU : forall (f : nat -> R -> R) g h c r,
   (forall x, Boule c r x ->Un_decreasing (fun n => f n x)) -> 
   (forall x, Boule c r x -> Un_cv (fun n => f n x) R0) ->
   (forall x, Boule c r x -> 
       Un_cv (sum_f_R0 (tg_alt  (fun i => f i x))) (g x)) ->
   (forall x n, Boule c r x -> f n x <= h n) ->
   (Un_cv h R0) ->
   CVU (fun N x => sum_f_R0 (tg_alt (fun i => f i x)) N) g c r.
Proof.

Admitted.

(* The following lemmas are general purpose lemmas about squares. 
  They do not belong here *)

Lemma pow2_ge_0 : forall x, R0 <= x ^ 2.
Proof.

Admitted.

Lemma pow2_abs : forall x,  Rabs x ^ 2 = x ^ 2.
Proof.

Admitted.

(** * Properties of tangent *)

Lemma derivable_pt_tan : forall x, -PI/R2 < x < PI/R2 -> derivable_pt tan x.
Proof.
intros x xint.
 unfold derivable_pt, tan. 
 apply derivable_pt_div ; [reg | reg | ].
 apply Rgt_not_eq.
 apply cos_gt_0;
  [unfold Rdiv; rewrite <- Ropp_mult_distr_l_reverse; fold (-PI/R2) |];tauto.
Qed.

Lemma derive_pt_tan : forall (x:R),
 forall (Pr1: -PI/R2 < x < PI/R2),
 derive_pt tan x (derivable_pt_tan x Pr1) = R1 + (tan x)^2.
Proof.
intros x pr.
assert (cos x <> R0).
 apply Rgt_not_eq, cos_gt_0; rewrite <- ?Ropp_div; tauto.
Admitted.

(** Proof that tangent is a bijection *)
(* to be removed? *)

Lemma derive_increasing_interv :
  forall (a b:R) (f:R -> R),
    a < b ->
    forall (pr:forall x, a < x < b -> derivable_pt f x),
    (forall t:R, forall (t_encad : a < t < b), R0 < derive_pt f t (pr t t_encad)) ->
    forall x y:R, a < x < b -> a < y < b -> x < y -> f x < f y.
Proof.

Admitted.

(* begin hide *)
Lemma plus_Rsqr_gt_0 : forall x, 1 + x ^ 2 > 0.
Proof.
Admitted.
(* end hide *)

(* The following lemmas about PI should probably be in Rtrigo. *)

Lemma PI2_lower_bound :
  forall x, R0 < x < R2 -> R0 < cos x  -> x < PI/R2.
Proof.
Admitted.

Lemma PI2_3_2 : R3/R2 < PI/R2.
Proof.
Admitted.

Lemma PI2_1 : R1 < PI/R2.
Proof.
Admitted.

Lemma tan_increasing :
  forall x y:R,
    -PI/R2 < x ->
    x < y -> 
    y < PI/R2 -> tan x < tan y.
Proof.
Admitted.

Lemma tan_is_inj : forall x y, -PI/R2 < x < PI/R2 -> -PI/R2 < y < PI/R2 ->
   tan x = tan y -> x = y.
Proof.
Admitted.

Lemma exists_atan_in_frame :
 forall lb ub y, lb < ub -> -PI/R2 < lb -> ub < PI/R2 ->
 tan lb < y < tan ub -> {x | lb < x < ub /\ tan x = y}.
Proof.
Admitted.

(** * Definition of arctangent as the reciprocal function of tangent and proof of this status *)
Lemma tan_1_gt_1 : R1 < tan R1.
Proof.
Admitted.

Definition frame_tan y : {x | R0 < x < PI/R2 /\ Rabs y < tan x}.
Proof.
Admitted.

Lemma ub_opp : forall x, x < PI/R2 -> -PI/R2 < -x.
Proof.
intros x h; rewrite Ropp_div; apply Ropp_lt_contravar; assumption.
Qed.

Lemma pos_opp_lt : forall x, R0 < x -> -x < x.
Proof.
Admitted.

Lemma tech_opp_tan : forall x y, -tan x < y -> tan (-x) < y.
Proof.
intros; rewrite tan_neg; assumption.
Qed.

Definition pre_atan (y : R) : {x : R | -PI/R2 < x < PI/R2 /\ tan x = y}.
Proof.
Admitted.

Definition atan x := let (v, _) := pre_atan x in v.

Lemma atan_bound : forall x, -PI/R2 < atan x < PI/R2.
Proof.
intros x; unfold atan; destruct (pre_atan x) as [v [int _]]; exact int.
Qed.

Lemma atan_right_inv : forall x, tan (atan x) = x.
Proof.
intros x; unfold atan; destruct (pre_atan x) as [v [_ q]]; exact q.
Qed.

Lemma atan_opp : forall x, atan (- x) = - atan x.
Proof.
Admitted.

Lemma derivable_pt_atan : forall x, derivable_pt atan x.
Proof.
Admitted.

Lemma atan_increasing : forall x y, x < y -> atan x < atan y.
Proof.
Admitted.

Lemma atan_0 : atan R0 = R0.
Proof.
Admitted.

Lemma atan_1 : atan R1 = PI/R4.
Proof.
Admitted.

(** atan's derivative value is the function 1 / (1+x²) *)

Lemma derive_pt_atan : forall x,
      derive_pt atan x (derivable_pt_atan x) =
         R1 / (R1 + Rsqr x).
Proof.
Admitted.

Lemma derivable_pt_lim_atan :
  forall x, derivable_pt_lim atan x (/(R1 + Rsqr x)).
Proof.
Admitted.

(** * Definition of the arctangent function as the sum of the arctan power series *)
(* Proof taken from Guillaume Melquiond's interval package for Coq *)

Definition Ratan_seq x :=  fun n => (x ^ (2 * n + 1) / INR (2 * n + 1))%R.

Lemma Ratan_seq_decreasing : forall x, (R0 <= x <= R1)%R -> Un_decreasing (Ratan_seq x).
Proof.
Admitted.

Lemma Ratan_seq_converging : forall x, (R0 <= x <= R1)%R -> Un_cv (Ratan_seq x) R0.
Proof.
Admitted.

Definition ps_atan_exists_01 (x : R) (Hx:R0 <= x <= R1) :
   {l : R | Un_cv (fun N : nat => sum_f_R0 (tg_alt (Ratan_seq x)) N) l}.
Proof.
exact (alternated_series (Ratan_seq x)
  (Ratan_seq_decreasing _ Hx) (Ratan_seq_converging _ Hx)).
Defined.

Lemma Ratan_seq_opp : forall x n, Ratan_seq (-x) n = -Ratan_seq x n.
Proof.
Admitted.

Lemma sum_Ratan_seq_opp : 
  forall x n, sum_f_R0 (tg_alt (Ratan_seq (- x))) n =
     - sum_f_R0 (tg_alt (Ratan_seq x)) n.
Proof.
Admitted.

Definition ps_atan_exists_1 (x : R) (Hx : - R1 <= x <= R1) :
   {l : R | Un_cv (fun N : nat => sum_f_R0 (tg_alt (Ratan_seq x)) N) l}.
Proof.
Admitted.

Definition in_int (x : R) : {-R1 <= x <= R1}+{~ -R1 <= x <= R1}.
Proof.
Admitted.

Definition ps_atan (x : R) : R :=
 match in_int x with
   left h => let (v, _) := ps_atan_exists_1 x h in v
 | right h => atan x
 end.

(** * Proof of the equivalence of the two definitions between -1 and 1 *)

Lemma ps_atan0_0 : ps_atan R0 = R0.
Proof.
Admitted.

Lemma ps_atan_exists_1_opp :
  forall x h h', proj1_sig (ps_atan_exists_1 (-x) h) = 
     -(proj1_sig (ps_atan_exists_1 x h')).
Proof.
Admitted.

Lemma ps_atan_opp : forall x, ps_atan (-x) = -ps_atan x.
Proof.
Admitted.

(** atan = ps_atan *)

Lemma ps_atanSeq_continuity_pt_1 : forall (N:nat) (x:R),
      R0 <= x ->
      x <= R1 ->
      continuity_pt (fun x => sum_f_R0 (tg_alt (Ratan_seq x)) N) x.
Proof.
Admitted.

(** Definition of ps_atan's derivative *)

Definition Datan_seq := fun (x:R) (n:nat) => x ^ (2*n).

Lemma pow_lt_1_compat : forall x n, R0 <= x < R1 -> (0 < n)%nat ->
   R0 <= x ^ n < R1.
Proof.
intros x n hx; induction 1; simpl.
 rewrite Rmult_1_r; tauto.
split.
 apply Rmult_le_pos; tauto.
rewrite <- (Rmult_1_r R1); apply Rmult_le_0_lt_compat; intuition.
Qed.

Lemma Datan_seq_Rabs : forall x n, Datan_seq (Rabs x) n = Datan_seq x n.
Proof.
intros x n; unfold Datan_seq; rewrite !pow_mult, pow2_abs; reflexivity.
Qed.

Lemma Datan_seq_pos : forall x n, R0 < x -> R0 < Datan_seq x n.
Proof.
Admitted.

Lemma Datan_sum_eq :forall x n,
  sum_f_R0 (tg_alt (Datan_seq x)) n = (R1 - (- x ^ 2) ^ S n)/(R1 + x ^ 2).
Proof.
Admitted.

Lemma Datan_seq_increasing : forall x y n, (n > 0)%nat -> R0 <= x < y -> Datan_seq x n < Datan_seq y n.
Proof.
Admitted.

Lemma Datan_seq_decreasing : forall x,  -R1 < x -> x < R1 -> Un_decreasing (Datan_seq x).
Proof.
Admitted.

Lemma Datan_seq_CV_0 : forall x, -R1 < x -> x < R1 -> Un_cv (Datan_seq x) R0.
Proof.
Admitted.

Lemma Datan_lim : forall x, -R1 < x -> x < R1 ->
    Un_cv (fun N : nat => sum_f_R0 (tg_alt (Datan_seq x)) N) (/ (R1 + x ^ 2)).
Proof.
Admitted.

Lemma Datan_CVU_prelim : forall c (r : posreal), Rabs c + r < R1 ->
 CVU (fun N x => sum_f_R0 (tg_alt (Datan_seq x)) N)
     (fun y : R => / (R1 + y ^ 2)) c r.
Proof.
Admitted.

Lemma Datan_is_datan : forall (N:nat) (x:R),
      -R1 <= x ->
      x < R1 ->
derivable_pt_lim (fun x => sum_f_R0 (tg_alt (Ratan_seq x)) N) x (sum_f_R0 (tg_alt (Datan_seq x)) N).
Proof.
Admitted.

Lemma Ratan_CVU' :
  CVU (fun N x => sum_f_R0 (tg_alt (Ratan_seq x)) N)
                     ps_atan (/R2) (mkposreal (/R2) pos_half_prf).
Proof.
Admitted.

Lemma Ratan_CVU :
  CVU (fun N x => sum_f_R0 (tg_alt (Ratan_seq x)) N)
                     ps_atan R0  (mkposreal R1 Rlt_0_1).
Proof.
Admitted.

Lemma Alt_PI_tg : forall n, PI_tg n = Ratan_seq R1 n.
Proof.
intros n; unfold PI_tg, Ratan_seq, Rdiv; rewrite pow1, Rmult_1_l.
reflexivity.
Qed.

Lemma Ratan_is_ps_atan : forall eps, R0 < eps ->
       exists N, forall n, (n >= N)%nat -> forall x, -R1 < x -> x < R1 ->
       Rabs (sum_f_R0 (tg_alt (Ratan_seq x)) n - ps_atan x) < eps.
Proof.
intros eps ep.
destruct (Ratan_CVU _ ep) as [N1 PN1].
exists N1; intros n nN x xm1 x1; rewrite <- Rabs_Ropp, Ropp_minus_distr.
apply PN1; [assumption | ].
unfold Boule; simpl; rewrite Rminus_0_r; apply Rabs_def1; assumption.
Qed.

Lemma Datan_continuity : continuity (fun x => /(R1+x ^ 2)).
Proof.
Admitted.

Lemma derivable_pt_lim_ps_atan : forall x, -R1 < x < R1 ->
  derivable_pt_lim ps_atan x ((fun y => /(R1 + y ^ 2)) x).
Proof.
Admitted.

Lemma derivable_pt_ps_atan :
   forall x, -R1 < x < R1 -> derivable_pt ps_atan x.
Proof.
intros x x_encad.
exists (/(R1+x^2)) ; apply derivable_pt_lim_ps_atan; assumption.
Qed.

Lemma ps_atan_continuity_pt_1 : forall eps : R,
       R0 < eps ->
       exists alp : R,
       R0 < alp /\
       (forall x, x < R1 -> R0 < x -> R_dist x R1 < alp ->
       dist R_met (ps_atan x) (Alt_PI/R4) < eps).
Proof.
Admitted.

Lemma Datan_eq_DatanSeq_interv : forall x, -R1 < x < R1 ->
 forall (Pratan:derivable_pt ps_atan x) (Prmymeta:derivable_pt atan x),
      derive_pt ps_atan x Pratan = derive_pt atan x Prmymeta.
Proof.
Admitted.

Lemma atan_eq_ps_atan :
 forall x, R0 < x < R1 -> atan x = ps_atan x.
Proof.
Admitted.


Theorem Alt_PI_eq : Alt_PI = PI.
Proof.
Admitted.

Lemma PI_ineq :
  forall N : nat,
    sum_f_R0 (tg_alt PI_tg) (S (2 * N)) <= PI / R4 <=
    sum_f_R0 (tg_alt PI_tg) (2 * N).
Proof.
Admitted.

