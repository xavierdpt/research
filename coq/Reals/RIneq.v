Require Export Raxioms.
Require Import Rpow_def.
Require Import Zpower.
Require Export ZArithRing.
Require Import Omega.
Require Export RealField.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Implicit Type r : R.

Lemma Rle_refl : forall r, r <= r.
Proof.
  intros r.
  unfold Rle.
  right.
  reflexivity.
Qed.
Hint Immediate Rle_refl: rorders.

Lemma Rge_refl : forall r, r >= r.
Proof.  
 apply Rle_refl.
Qed.
Hint Immediate Rge_refl: rorders.

Lemma Rlt_irrefl : forall r, ~ r < r.
Proof.
  intros r h.
  apply (Rlt_asym r r).
  exact h.
  exact h.
Qed.
Hint Resolve Rlt_irrefl: real.

Lemma Rgt_irrefl : forall r, ~ r > r.
Proof. exact Rlt_irrefl. Qed.

Lemma Rlt_not_eq : forall r1 r2, r1 < r2 -> r1 <> r2.
Proof.
  intros x y h.
  red. intro eq. subst y. 
  apply Rlt_irrefl in h.
  exact h.
Qed.

Lemma Rgt_not_eq : forall r1 r2, r1 > r2 -> r1 <> r2.
Proof.
  intros x y h.
  intro eq. subst y.
  apply Rlt_irrefl in h.
  exact h.
Qed.

Lemma Rlt_dichotomy_converse : forall r1 r2, r1 < r2 \/ r1 > r2 -> r1 <> r2.
Proof.
  intros x y [lt | gt].
  apply Rlt_not_eq. exact lt.
  apply Rgt_not_eq. exact gt.
Qed.
Hint Resolve Rlt_dichotomy_converse: real.

Lemma Req_dec : forall r1 r2, r1 = r2 \/ r1 <> r2.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  right. apply Rlt_dichotomy_converse. left. exact lt.
  left. exact eq.
  right. apply Rlt_dichotomy_converse. right. exact gt.
Qed.
Hint Resolve Req_dec: real.

(**********)
Lemma Rtotal_order : forall r1 r2, r1 < r2 \/ r1 = r2 \/ r1 > r2.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  left. exact lt.
  right. left. exact eq.
  right. right. exact gt.
Qed.

Lemma Rdichotomy : forall r1 r2, r1 <> r2 -> r1 < r2 \/ r1 > r2.
Proof.
  intros x y hneq.
  destruct (Rtotal_order x y) as [ lt | [ eq | gt ] ].
  left. exact lt.
  contradiction.
  right. exact gt.
Qed.

Lemma Rlt_le : forall r1 r2, r1 < r2 -> r1 <= r2.
Proof.
  intros x y h.
  left. exact h.
Qed.
Hint Resolve Rlt_le: real.

Lemma Rgt_ge : forall r1 r2, r1 > r2 -> r1 >= r2.
Proof.
  intros x y h.
  left. exact h.
Qed.

Lemma Rle_ge : forall r1 r2, r1 <= r2 -> r2 >= r1.
Proof.
  intros x y h.
  destruct h as [lt | eq].
  left. exact lt.
  right. symmetry. exact eq.
Qed.
Hint Immediate Rle_ge: real.
Hint Resolve Rle_ge: rorders.

Lemma Rge_le : forall r1 r2, r1 >= r2 -> r2 <= r1.
Proof.
  intros x y h.
  destruct h as [gt | eq].
  left. exact gt.
  right. symmetry. exact eq.
Qed.
Hint Resolve Rge_le: real.
Hint Immediate Rge_le: rorders.

Lemma Rlt_gt : forall r1 r2, r1 < r2 -> r2 > r1.
Proof.
  intros x y h. exact h.
Qed.
Hint Resolve Rlt_gt: rorders.

Lemma Rgt_lt : forall r1 r2, r1 > r2 -> r2 < r1.
Proof.
  intros x y h. exact h.
Qed.
Hint Immediate Rgt_lt: rorders.

Lemma Rnot_le_lt : forall r1 r2, ~ r1 <= r2 -> r2 < r1.
Proof.
  intros x y hn.
  destruct (Rtotal_order x y) as [ lt | [ eq | gt ] ].
  exfalso. apply hn. left. exact lt.
  exfalso. apply hn. right. exact eq.
  exact gt.
Qed.
Hint Immediate Rnot_le_lt: real.

Lemma Rnot_ge_gt : forall r1 r2, ~ r1 >= r2 -> r2 > r1.
Proof.
  intros x y hn.
  destruct (Rtotal_order x y) as [ lt | [ eq | gt ] ].
  exact lt.
  exfalso. apply hn. right. exact eq.
  exfalso. apply hn. left. exact gt.
Qed.

Lemma Rnot_le_gt : forall r1 r2, ~ r1 <= r2 -> r1 > r2.
Proof.
  intros x y hn.
  apply Rnot_le_lt. exact hn.
Qed.

Lemma Rnot_ge_lt : forall r1 r2, ~ r1 >= r2 -> r1 < r2.
Proof.
  intros x y hn.
  apply Rnot_ge_gt.
  exact hn.
Qed.

Lemma Rnot_lt_le : forall r1 r2, ~ r1 < r2 -> r2 <= r1.
Proof.
  intros x y hn.
  destruct (Rtotal_order x y) as [ lt | [ eq | gt ] ].
  contradiction.
  right. symmetry. exact eq.
  left. exact gt.
Qed.

Lemma Rnot_gt_le : forall r1 r2, ~ r1 > r2 -> r1 <= r2.
Proof.
  intros x y hn.
  apply Rnot_lt_le.
  exact hn.
Qed.

Lemma Rnot_gt_ge : forall r1 r2, ~ r1 > r2 -> r2 >= r1.
Proof.
  intros x y hn.
  destruct (Rtotal_order x y) as [ lt | [ eq | gt ] ].
  left. exact lt.
  right. symmetry. exact eq.
  contradiction.
Qed.

Lemma Rnot_lt_ge : forall r1 r2, ~ r1 < r2 -> r1 >= r2.
Proof.
  intros x y hn.
  destruct (Rtotal_order x y) as [ lt | [ eq | gt ] ].
  contradiction.
  right. exact eq.
  left. exact gt.
Qed.

Lemma Rlt_not_le : forall r1 r2, r2 < r1 -> ~ r1 <= r2.
Proof.
  intros x y hlt.
  intros [hlt' | heq].
  apply Rlt_asym in hlt'. contradiction.
  subst y. apply Rlt_irrefl in hlt. exact hlt.
Qed.
Hint Immediate Rlt_not_le: real.

Lemma Rgt_not_le : forall r1 r2, r1 > r2 -> ~ r1 <= r2.
Proof. exact Rlt_not_le. Qed.

Lemma Rlt_not_ge : forall r1 r2, r1 < r2 -> ~ r1 >= r2.
Proof.
  intros x y hlt hge.
  apply Rge_le in hge.
  apply Rlt_not_le with x y.
  destruct hge as [hlt' | eq].
  exact hlt'.
  subst y. apply Rlt_irrefl in hlt. contradiction.
  left. exact hlt.
Qed.
Hint Immediate Rlt_not_ge: real.

Lemma Rgt_not_ge : forall r1 r2, r2 > r1 -> ~ r1 >= r2.
Proof. exact Rlt_not_ge. Qed.

Lemma Rle_not_lt : forall r1 r2, r2 <= r1 -> ~ r1 < r2.
Proof.
  intros x y hle hlt.
  destruct hle as [hlt' | eq].
  apply Rlt_asym in hlt. contradiction.
  subst y. apply Rlt_irrefl in hlt. exact hlt.
Qed.

Lemma Rge_not_lt : forall r1 r2, r1 >= r2 -> ~ r1 < r2.
Proof.
  intros x y hge hlt.
  apply Rlt_not_ge with x y.
  exact hlt. exact hge.
Qed.

Lemma Rle_not_gt : forall r1 r2, r1 <= r2 -> ~ r1 > r2.
Proof.
  intros x y hle hgt.
  apply Rge_not_lt with y x.
  apply Rle_ge. exact hle.
  exact hgt.
Qed.

Lemma Rge_not_gt : forall r1 r2, r2 >= r1 -> ~ r1 > r2.
Proof.
  intros x y hge hlt.
  apply Rle_not_gt with x y.
  apply Rge_le. exact hge.
  exact hlt.
Qed.

Lemma Req_le : forall r1 r2, r1 = r2 -> r1 <= r2.
Proof.
  intros x y eq. subst y. right. reflexivity.
Qed.
Hint Immediate Req_le: real.

Lemma Req_ge : forall r1 r2, r1 = r2 -> r1 >= r2.
Proof.
  intros x y eq. subst y. right. reflexivity.
Qed.
Hint Immediate Req_ge: real.

Lemma Req_le_sym : forall r1 r2, r2 = r1 -> r1 <= r2.
Proof.
  intros x y eq. right. symmetry. exact eq.
Qed.
Hint Immediate Req_le_sym: real.

Lemma Req_ge_sym : forall r1 r2, r2 = r1 -> r1 >= r2.
Proof.
  intros x y eq. right. symmetry. exact eq.
Qed.
Hint Immediate Req_ge_sym: real.

Lemma Rgt_asym : forall r1 r2:R, r1 > r2 -> ~ r2 > r1.
Proof.
  intros x y hgt hlt.
  apply Rlt_asym in hlt. contradiction.
Qed.

Lemma Rle_antisym : forall r1 r2, r1 <= r2 -> r2 <= r1 -> r1 = r2.
Proof.
  intros x y hxy hyx.
  destruct hxy as [ltxy | eqxy].
  destruct hyx as [ltyx | eqyx].
  apply Rlt_asym in ltxy. contradiction.
  symmetry. exact eqyx.
  exact eqxy.
Qed.
Hint Resolve Rle_antisym: real.

Lemma Rge_antisym : forall r1 r2, r1 >= r2 -> r2 >= r1 -> r1 = r2.
Proof.
  intros x y hxy hyx.
  apply Rge_le in hxy.
  apply Rge_le in hyx.
  apply Rle_antisym.
  exact hyx. exact hxy.
Qed.

Lemma Rle_le_eq : forall r1 r2, r1 <= r2 /\ r2 <= r1 <-> r1 = r2.
Proof.
  intros x y.
  split.
  intros [hxy hyx].
  apply Rle_antisym. exact hxy. exact hyx.
  intro eq. subst y. split.
  right. reflexivity.
  right. reflexivity.
Qed.

Lemma Rge_ge_eq : forall r1 r2, r1 >= r2 /\ r2 >= r1 <-> r1 = r2.
Proof.
  intros x y.
  split.
  intros [hxy hyx].
  apply Rge_antisym. exact hxy. exact hyx.
  intro eq. subst y. split.
  right. reflexivity.
  right. reflexivity.
Qed.

(** *** Compatibility with equality *)

Lemma Rlt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 < r4 -> r4 = r3 -> r1 < r3.
Proof.
  intros x x' y y'.
  intros xx'eq hlt y'yeq.
  subst x' y'. exact hlt.
Qed.

Lemma Rgt_eq_compat :
  forall r1 r2 r3 r4, r1 = r2 -> r2 > r4 -> r4 = r3 -> r1 > r3.
Proof.
  intros x x' y y' eqx hlt eqy.
  subst x' y'. exact hlt.
Qed.

Lemma Rle_trans : forall r1 r2 r3, r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  intros x y z.
  intros hxy hyz.
  destruct hxy as [ltxy | eqxy].
  destruct hyz as [ltyz | eqyz].
  left. apply Rlt_trans with y. exact ltxy. exact ltyz.
  subst z. left. exact ltxy.
  subst y. exact hyz.
Qed.

Lemma Rge_trans : forall r1 r2 r3, r1 >= r2 -> r2 >= r3 -> r1 >= r3.
Proof.
  intros x y z.
  intros hxy hyz.
  apply Rle_ge.
  apply Rge_le in hxy.
  apply Rge_le in hyz.
  apply Rle_trans with y. exact hyz. exact hxy.
Qed.

Lemma Rgt_trans : forall r1 r2 r3, r1 > r2 -> r2 > r3 -> r1 > r3.
Proof.
  intros x y z hxy hyz.
  apply Rlt_trans with y. exact hyz. exact hxy.
Qed.

Lemma Rle_lt_trans : forall r1 r2 r3, r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros x y z hxy hyz.
  destruct hxy as [hxy | hxy ].
  apply Rlt_trans with y. exact hxy. exact hyz.
  subst y. exact hyz.
Qed.

Lemma Rlt_le_trans : forall r1 r2 r3, r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof.
  intros x y z hxy hyz.
  destruct hyz as [ hyz | hyz ].
  apply Rlt_trans with y. exact hxy. exact hyz.
  subst y. exact hxy.
Qed.

Lemma Rge_gt_trans : forall r1 r2 r3, r1 >= r2 -> r2 > r3 -> r1 > r3.
Proof.
  intros x y z hge hgt.
  apply Rge_le in hge.
  apply Rlt_le_trans with y. exact hgt. exact hge.
Qed.

Lemma Rgt_ge_trans : forall r1 r2 r3, r1 > r2 -> r2 >= r3 -> r1 > r3.
Proof.
  intros x y z hxy hyz.
  apply Rle_lt_trans with y.
  apply Rge_le. exact hyz.
  exact hxy.
Qed.

Lemma Rlt_dec : forall r1 r2, {r1 < r2} + {~ r1 < r2}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  left. exact lt.
  subst y. right. apply Rlt_irrefl.
  right. intro c. apply Rlt_asym in c. contradiction.
Qed.

Lemma Rle_dec : forall r1 r2, {r1 <= r2} + {~ r1 <= r2}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  left. left. exact lt.
  left. right. exact eq.
  right. intro c. destruct c as [ c | c ].
  apply Rlt_asym in c. contradiction.
  subst y. apply Rlt_irrefl in gt. exact gt.
Qed.

Lemma Rgt_dec : forall r1 r2, {r1 > r2} + {~ r1 > r2}.
Proof.
intros x y. apply Rlt_dec.
Qed.

Lemma Rge_dec : forall r1 r2, {r1 >= r2} + {~ r1 >= r2}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].

  right. intro c. destruct c as [ c | c ].
  apply Rlt_asym in c. contradiction.
  subst y. apply Rlt_irrefl in lt. exact lt.

  left. right. exact eq.

  left. left. exact gt.

Qed.

Lemma Rlt_le_dec : forall r1 r2, {r1 < r2} + {r2 <= r1}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  left. exact lt.
  right. right. symmetry. exact eq.
  right. left. exact gt. 
Qed.

Lemma Rgt_ge_dec : forall r1 r2, {r1 > r2} + {r2 >= r1}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  right. left. exact lt.
  right. right. symmetry. exact eq.
  left. exact gt.
Qed.

Lemma Rle_lt_dec : forall r1 r2, {r1 <= r2} + {r2 < r1}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  left. left. exact lt.
  left. right. exact eq.
  right. exact gt.
Qed.

Lemma Rge_gt_dec : forall r1 r2, {r1 >= r2} + {r2 > r1}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ].
  right. exact lt.
  left. right. exact eq.
  left. left. exact gt.
Qed.

Lemma Rlt_or_le : forall r1 r2, r1 < r2 \/ r2 <= r1.
Proof.
  intros x y.
  destruct (Rlt_le_dec x y) as [ l | r ].
  left. exact l.
  right. exact r.
Qed.

Lemma Rgt_or_ge : forall r1 r2, r1 > r2 \/ r2 >= r1.
Proof.

  intros x y.
  destruct (Rgt_ge_dec x y) as [ l | r ].
  left. exact l.
  right. exact r.
Qed.

Lemma Rle_or_lt : forall r1 r2, r1 <= r2 \/ r2 < r1.
Proof.
  intros x y.
  destruct (Rle_lt_dec x y) as [ l | r ].
  left. exact l.
  right. exact r.
Qed.

Lemma Rge_or_gt : forall r1 r2, r1 >= r2 \/ r2 > r1.
Proof.
  intros x y.
  destruct (Rge_gt_dec x y) as [ l | r ].
  left. exact l.
  right. exact r.
Qed.

Lemma Rle_lt_or_eq_dec : forall r1 r2, r1 <= r2 -> {r1 < r2} + {r1 = r2}.
Proof.
  intros x y h.
  destruct (total_order_T x y) as [ [ lt | eq ] | gt ]. 
  left. exact lt.
  right. exact eq.
  apply Rle_not_lt in h. contradiction.
Qed.

Lemma inser_trans_R :
  forall r1 r2 r3 r4, r1 <= r2 < r3 -> {r1 <= r2 < r4} + {r4 <= r2 < r3}.
Proof.
  intros w x y z.
  intros [hwx hxy].
  destruct (total_order_T x z) as [ [ lt | eq ] | gt ].
  left. split. exact hwx. exact lt.
  subst z. right. split. right. reflexivity. exact hxy.
  right. split. left. exact gt. exact hxy.
Qed.

Lemma Rplus_0_r : forall r, r + 0 = r.
Proof.
  intro x.
  rewrite Rplus_comm.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
Hint Resolve Rplus_0_r: real.

Lemma Rplus_ne : forall r, r + 0 = r /\ 0 + r = r.
Proof.
  intro x. split.
  apply Rplus_0_r.
  apply Rplus_0_l.
Qed.
Hint Resolve Rplus_ne: real.

Lemma Rplus_opp_l : forall r, - r + r = 0.
Proof.
  intro x.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.
Hint Resolve Rplus_opp_l: real.

Lemma Rplus_opp_r_uniq : forall r1 r2, r1 + r2 = 0 -> r2 = - r1.
Proof.
  intros x y eq.
  rewrite <- Rplus_0_r.
  rewrite <- eq.
  rewrite <- Rplus_assoc.
  rewrite (Rplus_opp_l x).
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Definition f_equal_R := (f_equal (A:=R)).

Hint Resolve f_equal_R : real.

Lemma Rplus_eq_compat_l : forall r r1 r2, r1 = r2 -> r + r1 = r + r2.
Proof.
  intros x y z eq. subst . reflexivity.
Qed.

Lemma Rplus_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 + r = r2 + r.
Proof.
  intros x y z eq. subst y. reflexivity.
Qed.

Lemma Rplus_eq_reg_l : forall r r1 r2, r + r1 = r + r2 -> r1 = r2.
Proof.
  intros x y z eq.
  rewrite <- Rplus_0_l with y.
  rewrite <- Rplus_opp_l with x.
  rewrite Rplus_assoc.
  rewrite eq.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
Hint Resolve Rplus_eq_reg_l: real.

Lemma Rplus_eq_reg_r : forall r r1 r2, r1 + r = r2 + r -> r1 = r2.
Proof.
  intros x y z eq.
  apply Rplus_eq_reg_l with x.
  rewrite Rplus_comm.
  rewrite eq.
  rewrite Rplus_comm.
  reflexivity.
Qed.

Lemma Rplus_0_r_uniq : forall r r1, r + r1 = r -> r1 = 0.
Proof.
  intros x y eq.
  rewrite <- Rplus_opp_l with x.
  pattern x at 2; rewrite <- eq.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Rplus_eq_0_l :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0.
Proof.
  intros x y hx hy eq.
  destruct hx as [ltx | eqx].
  destruct hy as [lty | eqy].
  {
    apply Rplus_lt_compat_l with x 0 y in lty .
    rewrite eq in lty. clear eq.
    rewrite Rplus_0_r in lty.
    apply Rlt_asym in lty.
    contradiction.
  }
  subst y. rewrite Rplus_0_r in eq. exact eq.
  subst x. reflexivity.
Qed.

Lemma Rplus_eq_R0 :
  forall r1 r2, 0 <= r1 -> 0 <= r2 -> r1 + r2 = 0 -> r1 = 0 /\ r2 = 0.
Proof.
  intros x y hx hy eq.
  split.
  apply Rplus_eq_0_l with y. exact hx. exact hy. exact eq.
  apply Rplus_eq_0_l with x. exact hy. exact hx. rewrite Rplus_comm. exact eq.
Qed.

Lemma Rinv_r : forall r, r <> 0 -> r * / r = 1.
Proof.
  intros x h.
  rewrite Rmult_comm.
  rewrite Rinv_l.
  reflexivity.
  exact h.
Qed.
Hint Resolve Rinv_r: real.

Lemma Rinv_l_sym : forall r, r <> 0 -> 1 = / r * r.
Proof.
  intros x h.
  symmetry.
  apply Rinv_l.
  exact h.
Qed.
Hint Resolve Rinv_l_sym: real.

Lemma Rinv_r_sym : forall r, r <> 0 -> 1 = r * / r.
Proof.
  intros x h.
  symmetry.
  apply Rinv_r.
  exact h.
Qed.
Hint Resolve Rinv_r_sym: real.

Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  intro x.
  apply Rplus_0_r_uniq with (x*0).
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_0_r.
  reflexivity.
Qed.
Hint Resolve Rmult_0_r: real.

Lemma Rmult_0_l : forall r, 0 * r = 0.
Proof.
  intro x.
  rewrite Rmult_comm.
  apply Rmult_0_r.
Qed.
Hint Resolve Rmult_0_l: real.

Lemma Rmult_ne : forall r, r * 1 = r /\ 1 * r = r.
Proof.
  intro x.
  split.
  rewrite Rmult_comm.
  Search ( 1 * _).
  rewrite Rmult_1_l.
  reflexivity.
  rewrite Rmult_1_l.
  reflexivity.
Qed.
Hint Resolve Rmult_ne: real.

Lemma Rmult_1_r : forall r, r * 1 = r.
Proof.
  intros x.
  rewrite Rmult_comm.
  rewrite Rmult_1_l.
  reflexivity.
Qed.
Hint Resolve Rmult_1_r: real.

Lemma Rmult_eq_compat_l : forall r r1 r2, r1 = r2 -> r * r1 = r * r2.
Proof.
  intros x y z eq.
  subst y. reflexivity.
Qed.

Lemma Rmult_eq_compat_r : forall r r1 r2, r1 = r2 -> r1 * r = r2 * r.
Proof.
  intros x y z eq.
  subst y. reflexivity.
Qed.

Lemma Rmult_eq_reg_l : forall r r1 r2, r * r1 = r * r2 -> r <> 0 -> r1 = r2.
Proof.
  intros x y z eq neq.
  rewrite <- Rmult_1_l with y.
  rewrite <- Rmult_1_l with z.
  rewrite <- Rinv_l with x.
  rewrite Rmult_assoc.
  rewrite Rmult_assoc.
  apply Rmult_eq_compat_l.
  exact eq.
  exact neq.
Qed.

Lemma Rmult_eq_reg_r : forall r r1 r2, r1 * r = r2 * r -> r <> 0 -> r1 = r2.
Proof.
  intros x y z eq neq.
  apply Rmult_eq_reg_l with x.
  rewrite Rmult_comm with x y.
  rewrite Rmult_comm with x z.
  exact eq.
  exact neq.
Qed.

Lemma Rmult_integral : forall r1 r2, r1 * r2 = 0 -> r1 = 0 \/ r2 = 0.
Proof.
  intros x y h.
  destruct (Req_dec x 0).
  left. exact H.
  right.
  apply Rmult_eq_reg_l with x.
  rewrite h.
  rewrite Rmult_0_r.
  reflexivity.
  exact H.
Qed.

Lemma Rmult_eq_0_compat : forall r1 r2, r1 = 0 \/ r2 = 0 -> r1 * r2 = 0.
Proof.
  intros x y [ eq | eq ].
  subst x. apply Rmult_0_l.
  subst y.  apply Rmult_0_r.
Qed.
Hint Resolve Rmult_eq_0_compat: real.

Lemma Rmult_eq_0_compat_r : forall r1 r2, r1 = 0 -> r1 * r2 = 0.
Proof.
  intros x y eq.
  subst x.
  rewrite Rmult_0_l.
  reflexivity.
Qed.

Lemma Rmult_eq_0_compat_l : forall r1 r2, r2 = 0 -> r1 * r2 = 0.
Proof.
  intros x y eq. subst y.
  rewrite Rmult_0_r.
  reflexivity.
Qed.

Lemma Rmult_neq_0_reg : forall r1 r2, r1 * r2 <> 0 -> r1 <> 0 /\ r2 <> 0.
Proof.
  intros x y h.
  split.
  intro eq. subst x. apply h. rewrite Rmult_0_l. reflexivity.
  intro eq. subst y. apply h. rewrite Rmult_0_r. reflexivity.
Qed.

Lemma Rmult_integral_contrapositive :
  forall r1 r2, r1 <> 0 /\ r2 <> 0 -> r1 * r2 <> 0.
Proof.
  intro x.
  intro y.
  intros [hx hy].
  intro eq.
  apply hy.
  rewrite <- Rmult_1_l with y.
  rewrite Rinv_l_sym with x.
  rewrite Rmult_assoc.
  rewrite eq.
  rewrite Rmult_0_r.
  reflexivity.
  exact hx.
Qed.
Hint Resolve Rmult_integral_contrapositive: real.

Lemma Rmult_integral_contrapositive_currified :
  forall r1 r2, r1 <> 0 -> r2 <> 0 -> r1 * r2 <> 0.
Proof.
  intros x y hx hy.
  apply Rmult_integral_contrapositive.
  split. exact hx. exact hy.
Qed.

Lemma Rmult_plus_distr_r :
  forall r1 r2 r3, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  intros x y z.
  rewrite Rmult_comm with (x+y) z.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_comm with z x.
  rewrite Rmult_comm with z y.
  reflexivity.
Qed.

Definition Rsqr r : R := r * r.

Notation "r ²" := (Rsqr r) (at level 1, format "r ²") : R_scope.

Lemma Rsqr_0 : Rsqr 0 = 0.
Proof.
  unfold Rsqr.
  apply Rmult_0_r.
Qed.

Lemma Rsqr_0_uniq : forall r, Rsqr r = 0 -> r = 0.
  intros x h.
  unfold Rsqr in h.
  destruct (Req_dec x 0) as [ eq | neq ].
  exact eq.
  apply Rmult_eq_reg_l with x.
  rewrite h. rewrite Rmult_0_r. reflexivity.
  exact neq.
Qed.

Lemma Ropp_eq_compat : forall r1 r2, r1 = r2 -> - r1 = - r2.
Proof.
  intros x y eq.
  subst y. reflexivity.
Qed.
Hint Resolve Ropp_eq_compat: real.

Lemma Ropp_0 : -0 = 0.
Proof.
  apply Rplus_eq_reg_l with 0.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  ring.
Qed.
Hint Resolve Ropp_0: real.

Lemma Ropp_eq_0_compat : forall r, r = 0 -> - r = 0.
Proof.
  intros x h.
  subst x.
  apply Ropp_0.
Qed.
Hint Resolve Ropp_eq_0_compat: real.

Lemma Ropp_involutive : forall r, - - r = r.
Proof.
  intro x.
  apply Rplus_eq_reg_l with ( - x).
  rewrite Rplus_opp_r.
  rewrite Rplus_comm.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.
Hint Resolve Ropp_involutive: real.

Lemma Ropp_neq_0_compat : forall r, r <> 0 -> - r <> 0.
Proof.
  intros x h.
  intro eq. apply h.
  rewrite <- Ropp_involutive with x.
  apply Ropp_eq_0_compat.
  exact eq.
Qed.
Hint Resolve Ropp_neq_0_compat: real.

Lemma Ropp_plus_distr : forall r1 r2, - (r1 + r2) = - r1 + - r2.
Proof.
  intros x y.
  apply Rplus_eq_reg_l with (x+y).
  rewrite Rplus_opp_r.
  rewrite Rplus_assoc.
  rewrite <- Rplus_assoc with y (-x) (-y).
  rewrite Rplus_comm with y (-x).
  rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.
Hint Resolve Ropp_plus_distr: real.

(* stopped here *)

Lemma Ropp_mult_distr_l : forall r1 r2, - (r1 * r2) = - r1 * r2.
Proof.
  intros x y.
  apply Rplus_eq_reg_l with (x*y).
  rewrite Rplus_opp_r.
  rewrite <- Rmult_plus_distr_r.
  rewrite Rplus_opp_r.
  rewrite Rmult_0_l.
  reflexivity.
Qed.

Lemma Ropp_mult_distr_l_reverse : forall r1 r2, - r1 * r2 = - (r1 * r2).
Proof.
  symmetry.
  apply Ropp_mult_distr_l.
Qed.
Hint Resolve Ropp_mult_distr_l_reverse: real.

(* stopped here *)

Lemma Rmult_opp_opp : forall r1 r2, - r1 * - r2 = r1 * r2.
Proof.
  intros x y.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite Rmult_comm.
  rewrite Ropp_mult_distr_l_reverse.
  rewrite Ropp_involutive.
  rewrite Rmult_comm.
  reflexivity.
Qed.
Hint Resolve Rmult_opp_opp: real.

Lemma Ropp_mult_distr_r : forall r1 r2, - (r1 * r2) = r1 * - r2.
Proof.
  intros x y.
  rewrite Rmult_comm with x (-y).
  rewrite <- Ropp_mult_distr_l.
  rewrite Rmult_comm.
  reflexivity.
Qed.

Lemma Ropp_mult_distr_r_reverse : forall r1 r2, r1 * - r2 = - (r1 * r2).
Proof.
  intros x y.
  symmetry.
  apply Ropp_mult_distr_r.
Qed.

(* stopped here *)

Lemma Rminus_0_r : forall r, r - 0 = r.
Proof.
  intro x.
  apply Rplus_eq_reg_r with 0.
  unfold Rminus.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  reflexivity.
Qed.
Hint Resolve Rminus_0_r: real.

Lemma Rminus_0_l : forall r, 0 - r = - r.
Proof.
  intro x.
  apply Rplus_eq_reg_l with 0.
  unfold Rminus.
  rewrite <- Rplus_assoc.
  rewrite Rplus_0_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
Hint Resolve Rminus_0_l: real.

Lemma Ropp_minus_distr : forall r1 r2, - (r1 - r2) = r2 - r1.
Proof.
  intros x y.
  apply Rplus_eq_reg_l with (x-y).
  rewrite Rplus_opp_r.
  unfold Rminus.
  rewrite Rplus_assoc.
  rewrite <- (Rplus_assoc (-y) ).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.
Hint Resolve Ropp_minus_distr: real.

Lemma Ropp_minus_distr' : forall r1 r2, - (r2 - r1) = r1 - r2.
Proof.
  intros x y.
  apply Ropp_minus_distr.
Qed.

Lemma Rminus_diag_eq : forall r1 r2, r1 = r2 -> r1 - r2 = 0.
Proof.
  intros x y eq.
  subst y. unfold Rminus. rewrite Rplus_opp_r.
  reflexivity.
Qed.
Hint Resolve Rminus_diag_eq: real.

Lemma Rminus_diag_uniq : forall r1 r2, r1 - r2 = 0 -> r1 = r2.
Proof.
  intros x y h.
  apply Rplus_eq_reg_r with (-y).
  unfold Rminus in h.
  rewrite h.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.
Hint Immediate Rminus_diag_uniq: real.

Lemma Rminus_diag_uniq_sym : forall r1 r2, r2 - r1 = 0 -> r1 = r2.
Proof.
  intros x y eq.
  apply Rplus_eq_reg_r with (-x).
  rewrite Rplus_opp_r.
  unfold Rminus in eq.
  rewrite eq.
  reflexivity.
Qed.
Hint Immediate Rminus_diag_uniq_sym: real.

Lemma Rplus_minus : forall r1 r2, r1 + (r2 - r1) = r2.
Proof.
  intros x y.
  unfold Rminus.
  rewrite <- Rplus_assoc.
  rewrite Rplus_comm.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
Hint Resolve Rplus_minus: real.

Lemma Rminus_eq_contra : forall r1 r2, r1 <> r2 -> r1 - r2 <> 0.
Proof.
  intros x y neq eq.
  apply neq.
  apply Rplus_eq_reg_r with (-y).
  unfold Rminus in eq.
  rewrite eq.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.
Hint Resolve Rminus_eq_contra: real.

Lemma Rminus_not_eq : forall r1 r2, r1 - r2 <> 0 -> r1 <> r2.
Proof.
  intros x y neq eq.
  subst y.
  unfold Rminus in neq.
  rewrite Rplus_opp_r in neq.
  contradiction.
Qed.
Hint Resolve Rminus_not_eq: real.

Lemma Rminus_not_eq_right : forall r1 r2, r2 - r1 <> 0 -> r1 <> r2.
Proof.
  intros x y neq eq.
  subst y.
  unfold Rminus in neq.
  rewrite Rplus_opp_r in neq.
  contradiction.
Qed.
Hint Resolve Rminus_not_eq_right: real.

Lemma Rmult_minus_distr_l :
  forall r1 r2 r3, r1 * (r2 - r3) = r1 * r2 - r1 * r3.
Proof.
  intros x y z.
  unfold Rminus.
  rewrite Rmult_plus_distr_l.
  rewrite Ropp_mult_distr_r.
  reflexivity.
Qed.

Lemma Rinv_1 : / 1 = 1.
Proof.
  apply Rmult_eq_reg_l with 1.
  rewrite Rmult_1_r.
  rewrite Rinv_r.
  reflexivity.
  exact R1_neq_R0.
  exact R1_neq_R0.
Qed.
Hint Resolve Rinv_1: real.

Lemma Rinv_neq_0_compat : forall r, r <> 0 -> / r <> 0.
Proof.
  intros x neq eq.
  apply neq.
  rewrite <- eq.
  apply Rmult_eq_reg_l with 1.
  pattern 1 at 1;rewrite <- Rinv_r with x.
  rewrite eq.
  rewrite Rmult_0_r. 
  rewrite Rmult_0_r. 
  rewrite Rmult_0_l.
  reflexivity.
  exact neq. 
  exact R1_neq_R0.
Qed.
Hint Resolve Rinv_neq_0_compat: real.

Lemma Rinv_involutive : forall r, r <> 0 -> / / r = r.
Proof.
  intros x neq.
  apply Rmult_eq_reg_l with (/ x).
  rewrite Rinv_l.
  rewrite Rinv_r.
  reflexivity.
  apply Rinv_neq_0_compat. exact neq.
  exact neq.
  apply Rinv_neq_0_compat. exact neq.
Qed.
Hint Resolve Rinv_involutive: real.

Lemma Rinv_mult_distr :
  forall r1 r2, r1 <> 0 -> r2 <> 0 -> / (r1 * r2) = / r1 * / r2.
Proof.
  intros x y hx hy.
  apply Rmult_eq_reg_l with (x*y).
  rewrite Rinv_r.
  rewrite Rmult_comm with (/ x) (/ y).
  rewrite Rmult_assoc.
  rewrite <- Rmult_assoc with y (/ y) (/ x).
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite Rinv_r.
  reflexivity.
  exact hx. exact hy.
  apply Rmult_integral_contrapositive_currified. exact hx. exact hy.
  apply Rmult_integral_contrapositive_currified. exact hx. exact hy.
Qed.

Lemma Ropp_inv_permute : forall r, r <> 0 -> - / r = / - r.
Proof.
  intros x neq.
  apply Rmult_eq_reg_l with (- x).
  rewrite Rinv_r.
  rewrite Rmult_opp_opp.
  rewrite Rinv_r.
  reflexivity.
  exact neq.
  apply Ropp_neq_0_compat. exact neq.
  apply Ropp_neq_0_compat. exact neq.
Qed.

Lemma Rinv_r_simpl_r : forall r1 r2, r1 <> 0 -> r1 * / r1 * r2 = r2.
Proof.
  intros x y neq.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  reflexivity.
  exact neq.
Qed.

Lemma Rinv_r_simpl_l : forall r1 r2, r1 <> 0 -> r2 * r1 * / r1 = r2.
Proof.
  intros x y neq.
  rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  reflexivity.
  exact neq.
Qed.

Lemma Rinv_r_simpl_m : forall r1 r2, r1 <> 0 -> r1 * r2 * / r1 = r2.
Proof.
  intros x y neq.
  rewrite Rmult_comm.
  rewrite <- Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_l.
  reflexivity.
  exact neq.
Qed.
Hint Resolve Rinv_r_simpl_l Rinv_r_simpl_r Rinv_r_simpl_m: real.

Lemma Rinv_mult_simpl :
  forall r1 r2 r3, r1 <> 0 -> r1 * / r2 * (r3 * / r1) = r3 * / r2.
Proof.
  intros x y z neq.
  rewrite Rmult_comm with x (/ y).
  rewrite Rmult_assoc.
  rewrite Rmult_comm with z (/ x).
  rewrite <- Rmult_assoc with x (/ x) z .
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  rewrite Rmult_comm with (/ y) z.
  reflexivity.
  exact neq.
Qed.

(** Remark: [Rplus_lt_compat_l] is an axiom *)

Lemma Rplus_gt_compat_l : forall r r1 r2, r1 > r2 -> r + r1 > r + r2.
Proof.
  intros x y z h.
  apply Rplus_lt_compat_l.
  exact h.
Qed.
Hint Resolve Rplus_gt_compat_l: real.

Lemma Rplus_lt_compat_r : forall r r1 r2, r1 < r2 -> r1 + r < r2 + r.
Proof.
  intros x y z h.
  rewrite Rplus_comm with y x.
  rewrite Rplus_comm with z x.
  apply Rplus_lt_compat_l.
  exact h.
Qed.
Hint Resolve Rplus_lt_compat_r: real.

Lemma Rplus_gt_compat_r : forall r r1 r2, r1 > r2 -> r1 + r > r2 + r.
Proof.
  intros x y z h.
  apply Rplus_lt_compat_r.
  exact h.
Qed.

Lemma Rplus_le_compat_l : forall r r1 r2, r1 <= r2 -> r + r1 <= r + r2.
Proof.
  intros x y z [h | h].
  left. apply Rplus_lt_compat_l. exact h.
  subst y. right. reflexivity.
Qed.

Lemma Rplus_ge_compat_l : forall r r1 r2, r1 >= r2 -> r + r1 >= r + r2.
Proof.
  intros x y z [h | h].
  left. apply Rplus_gt_compat_l. exact h.
  right. subst y. reflexivity.
Qed.
Hint Resolve Rplus_ge_compat_l: real.

Lemma Rplus_le_compat_r : forall r r1 r2, r1 <= r2 -> r1 + r <= r2 + r.
Proof.
  intros x y z [h | h].
  left. apply Rplus_lt_compat_r. exact h.
  right. subst y. reflexivity.
Qed.
Hint Resolve Rplus_le_compat_l Rplus_le_compat_r: real.

Lemma Rplus_ge_compat_r : forall r r1 r2, r1 >= r2 -> r1 + r >= r2 + r.
Proof.
  intros x y z [h | h].
  left. apply Rplus_gt_compat_r. exact h.
  right. subst y. reflexivity.
Qed.

Lemma Rplus_lt_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros w x y z hwx hyz.
  apply (Rlt_trans _ (w+z) _).
  apply Rplus_lt_compat_l. exact hyz.
  apply Rplus_lt_compat_r. exact hwx.
Qed.
Hint Immediate Rplus_lt_compat: real.

Lemma Rplus_le_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 <= r4 -> r1 + r3 <= r2 + r4.
Proof.
  intros w x y z hwx hyz.
  apply (Rle_trans _ (w+z) _).
  apply Rplus_le_compat_l. exact hyz.
  apply Rplus_le_compat_r. exact hwx.
Qed.
Hint Immediate Rplus_le_compat: real.

Lemma Rplus_gt_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof.
  intros w x y z hwx hyz.
  apply (Rgt_trans _ (w+z) _).
  apply Rplus_gt_compat_l. exact hyz.
  apply Rplus_gt_compat_r. exact hwx.
Qed.

Lemma Rplus_ge_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 >= r4 -> r1 + r3 >= r2 + r4.
Proof.
  intros w x y z hwx hyz.
  apply (Rge_trans _ (w+z) _).
  apply Rplus_ge_compat_l. exact hyz.
  apply Rplus_ge_compat_r. exact hwx.
Qed.

Lemma Rplus_lt_le_compat :
  forall r1 r2 r3 r4, r1 < r2 -> r3 <= r4 -> r1 + r3 < r2 + r4.
Proof.
  intros w x y z hwx hyz.
  destruct hyz as [ hyz | hyz ].
  apply Rplus_lt_compat. exact hwx. exact hyz.
  subst z. apply Rplus_lt_compat_r. exact hwx.
Qed.

Lemma Rplus_le_lt_compat :
  forall r1 r2 r3 r4, r1 <= r2 -> r3 < r4 -> r1 + r3 < r2 + r4.
Proof.
  intros w x y z hwx hyz.
  destruct hwx as [ hwx | hwx ].
  apply Rplus_lt_compat. exact hwx. exact hyz.
  subst w. apply Rplus_lt_compat_l. exact hyz.
Qed.
Hint Immediate Rplus_lt_le_compat Rplus_le_lt_compat: real.

Lemma Rplus_gt_ge_compat :
  forall r1 r2 r3 r4, r1 > r2 -> r3 >= r4 -> r1 + r3 > r2 + r4.
Proof.
  intros w x y z hwx hyz.
  destruct hyz as [ hyz | hyz ].
  apply Rplus_gt_compat. exact hwx. exact hyz.
  subst z. apply Rplus_gt_compat_r. exact hwx.
Qed.

Lemma Rplus_ge_gt_compat :
  forall r1 r2 r3 r4, r1 >= r2 -> r3 > r4 -> r1 + r3 > r2 + r4.
Proof.
  intros w x y z hwx hyz.
  destruct hwx as [ hwx | hwx ].
  apply Rplus_gt_compat. exact hwx. exact hyz.
  subst w. apply Rplus_gt_compat_l. exact hyz.
Qed.

Lemma Rplus_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros x y hx hy.
  rewrite <- Rplus_0_l with 0.
  apply Rplus_lt_compat. exact hx. exact hy.
Qed.

Lemma Rplus_le_lt_0_compat : forall r1 r2, 0 <= r1 -> 0 < r2 -> 0 < r1 + r2.
Proof.
  intros x y hx hy.
  rewrite <- Rplus_0_l with 0.
  apply Rplus_le_lt_compat. exact hx. exact hy.
Qed.

Lemma Rplus_lt_le_0_compat : forall r1 r2, 0 < r1 -> 0 <= r2 -> 0 < r1 + r2.
Proof.
  intros x y hx hy.
  rewrite <- Rplus_0_l with 0.
  apply Rplus_lt_le_compat. exact hx. exact hy.
Qed.

Lemma Rplus_le_le_0_compat : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 + r2.
Proof.
  intros x y hx hy.
  destruct hx as [ hx | hx ].
  left.   apply Rplus_lt_le_0_compat. exact hx. exact hy.
  subst x. rewrite Rplus_0_l. exact hy.
Qed.

Lemma sum_inequa_Rle_lt :
  forall a x b c y d:R,
    a <= x -> x < b -> c < y -> y <= d -> a + c < x + y < b + d.
Proof.
  intros a x b c y d.
  intros hax hxb hcy  hyd.
  split.
  apply Rplus_le_lt_compat. exact hax. exact hcy.
  apply Rplus_lt_le_compat. exact hxb. exact hyd.
Qed.

Lemma Rplus_lt_reg_l : forall r r1 r2, r + r1 < r + r2 -> r1 < r2.
Proof.
  intros x y z h.
  rewrite <- Rplus_0_l with y.
  rewrite <- Rplus_0_l with z.
  rewrite <- Rplus_opp_l with x.
  rewrite Rplus_assoc.
  rewrite Rplus_assoc.
  apply Rplus_le_lt_compat.
  right. reflexivity.
  exact h.
Qed.

Lemma Rplus_lt_reg_r : forall r r1 r2, r1 + r < r2 + r -> r1 < r2.
Proof.
  intros x y z h.
  apply Rplus_lt_reg_l with x.
  rewrite Rplus_comm with x y.
  rewrite Rplus_comm with x z.
  exact h.
Qed.

Lemma Rplus_le_reg_l : forall r r1 r2, r + r1 <= r + r2 -> r1 <= r2.
Proof.
  intros x y z h.
  rewrite <- Rplus_0_l with y.
  rewrite <- Rplus_0_l with z.
  rewrite <- Rplus_opp_l with x.
  rewrite Rplus_assoc.
  rewrite Rplus_assoc.
  apply Rplus_le_compat.
  right. reflexivity.
  exact h.
Qed.

Lemma Rplus_le_reg_r : forall r r1 r2, r1 + r <= r2 + r -> r1 <= r2.
Proof.
  intros x y z h.
  apply Rplus_le_reg_l with x.
  rewrite Rplus_comm with x y.
  rewrite Rplus_comm with x z.
  exact h.
Qed.

Lemma Rplus_gt_reg_l : forall r r1 r2, r + r1 > r + r2 -> r1 > r2.
Proof.
  intros x y z h.
  apply Rplus_lt_reg_l with x.
  exact h.
Qed.

Lemma Rplus_ge_reg_l : forall r r1 r2, r + r1 >= r + r2 -> r1 >= r2.
Proof.
  intros x y z h.
  destruct h as [ h | h ].
  left. apply Rplus_gt_reg_l with x. exact h.
  right. apply Rplus_eq_reg_l with x. exact h.
Qed.

Lemma Rplus_le_reg_pos_r :
  forall r1 r2 r3, 0 <= r2 -> r1 + r2 <= r3 -> r1 <= r3.
Proof.
  intros x y z hy hxyz.
  apply Rle_trans with (x+y).
  pattern x at 1;rewrite <- Rplus_0_r with x.
  apply Rplus_le_compat. right. reflexivity. exact hy. exact hxyz.
Qed.

Lemma Rplus_lt_reg_pos_r : forall r1 r2 r3, 0 <= r2 -> r1 + r2 < r3 -> r1 < r3.
Proof.
  intros x y z hx hxyz.
  destruct hx as [ hx | hx ].
  apply Rlt_trans with (x+y).
  pattern x at 1;rewrite <- Rplus_0_r with x.
  apply Rplus_lt_compat_l. exact hx. exact hxyz.
  subst y. rewrite Rplus_0_r in hxyz. exact hxyz.
Qed.

Lemma Rplus_ge_reg_neg_r :
  forall r1 r2 r3, 0 >= r2 -> r1 + r2 >= r3 -> r1 >= r3.
Proof.
  intros x y z hy hxyz.
  apply Rge_trans with (x+y).
  pattern x at 1;rewrite <- Rplus_0_r with x.
  apply Rplus_ge_compat_l. exact hy. exact hxyz.
Qed.

Lemma Rplus_gt_reg_neg_r : forall r1 r2 r3, 0 >= r2 -> r1 + r2 > r3 -> r1 > r3.
Proof.
  intros x y z hy hxyz.
  destruct hy as [ hy | hy ].
  apply Rgt_trans with (x+y).
  pattern x at 1;rewrite <- Rplus_0_r with x.
  apply Rplus_gt_compat_l. exact hy. exact hxyz.
  subst y. rewrite Rplus_0_r in hxyz. exact hxyz.
Qed.

Lemma Ropp_gt_lt_contravar : forall r1 r2, r1 > r2 -> - r1 < - r2.
Proof.
  intros x y h.
  apply Rplus_lt_reg_l with x.
  rewrite Rplus_opp_r.
  apply Rplus_lt_reg_r with y.
  rewrite Rplus_0_l.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  exact h.
Qed.
Hint Resolve Ropp_gt_lt_contravar.

Lemma Ropp_lt_gt_contravar : forall r1 r2, r1 < r2 -> - r1 > - r2.
Proof.
  intros x y h.
  apply Ropp_gt_lt_contravar. exact h.
Qed.
Hint Resolve Ropp_lt_gt_contravar: real.

Lemma Ropp_lt_contravar : forall r1 r2, r2 < r1 -> - r1 < - r2.
Proof.
  intros x y h.
  apply Ropp_lt_gt_contravar.
  exact h.
Qed.
Hint Resolve Ropp_lt_contravar: real.

Lemma Ropp_gt_contravar : forall r1 r2, r2 > r1 -> - r1 > - r2.
Proof.
  intros x y h.
  apply Ropp_lt_gt_contravar.
  exact h.
Qed.

Lemma Ropp_le_ge_contravar : forall r1 r2, r1 <= r2 -> - r1 >= - r2.
Proof.
  intros x y h.
  apply Rplus_ge_reg_l with x.
  rewrite Rplus_opp_r.
  rewrite Rplus_comm.
  apply Rplus_ge_reg_l with y.
  rewrite Rplus_0_r.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  apply Rle_ge.
  exact h.
Qed.
Hint Resolve Ropp_le_ge_contravar: real.

Lemma Ropp_ge_le_contravar : forall r1 r2, r1 >= r2 -> - r1 <= - r2.
Proof.
  intros x y h.
  apply Rge_le.
  apply Ropp_le_ge_contravar.
  apply Rge_le.
  exact h.
Qed.
Hint Resolve Ropp_ge_le_contravar: real.

Lemma Ropp_le_contravar : forall r1 r2, r2 <= r1 -> - r1 <= - r2.
Proof.
  intros x y h.
  apply Ropp_ge_le_contravar.
  apply Rle_ge.
  exact h.
Qed.
Hint Resolve Ropp_le_contravar: real.

Lemma Ropp_ge_contravar : forall r1 r2, r2 >= r1 -> - r1 >= - r2.
Proof.
  intros x y h.
  apply Ropp_le_ge_contravar.
  apply Rge_le.
  exact h.
Qed.

Lemma Ropp_0_lt_gt_contravar : forall r, 0 < r -> 0 > - r.
Proof.
  intros x h.
  rewrite <- Ropp_0.
  apply Ropp_gt_contravar.
  exact h.
Qed.
Hint Resolve Ropp_0_lt_gt_contravar: real.

Lemma Ropp_0_gt_lt_contravar : forall r, 0 > r -> 0 < - r.
Proof.
  intros x h.
  rewrite <- Ropp_0.
  apply Ropp_gt_contravar.
  exact h.
Qed.
Hint Resolve Ropp_0_gt_lt_contravar: real.

Lemma Ropp_lt_gt_0_contravar : forall r, r > 0 -> - r < 0.
Proof.
  intros x h.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  exact h.
Qed.
Hint Resolve Ropp_lt_gt_0_contravar: real.

Lemma Ropp_gt_lt_0_contravar : forall r, r < 0 -> - r > 0.
Proof.
  intros x h.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  exact h.
Qed.
Hint Resolve Ropp_gt_lt_0_contravar: real.

Lemma Ropp_0_le_ge_contravar : forall r, 0 <= r -> 0 >= - r.
Proof.
  intros x h.
  rewrite <- Ropp_0.
  apply Ropp_ge_contravar.
  apply Rle_ge.
  exact h.
Qed.
Hint Resolve Ropp_0_le_ge_contravar: real.

Lemma Ropp_0_ge_le_contravar : forall r, 0 >= r -> 0 <= - r.
Proof.
  intros x h.
  rewrite <- Ropp_0.
  apply Ropp_le_contravar.
  apply Rge_le.
  exact h.
Qed.
Hint Resolve Ropp_0_ge_le_contravar: real.

Lemma Ropp_lt_cancel : forall r1 r2, - r2 < - r1 -> r1 < r2.
Proof.
  intros x y h.
  rewrite <- Ropp_involutive with x.
  rewrite <- Ropp_involutive with y.
  apply Ropp_lt_contravar.
  exact h.
Qed.
Hint Immediate Ropp_lt_cancel: real.

Lemma Ropp_gt_cancel : forall r1 r2, - r2 > - r1 -> r1 > r2.
Proof.
  intros x y h.
  rewrite <- Ropp_involutive with x.
  rewrite <- Ropp_involutive with y.
  apply Ropp_lt_contravar.
  exact h.
Qed.

Lemma Ropp_le_cancel : forall r1 r2, - r2 <= - r1 -> r1 <= r2.
Proof.
  intros x y h.
  rewrite <- Ropp_involutive with x.
  rewrite <- Ropp_involutive with y.
  apply Ropp_le_contravar.
  exact h.
Qed.
Hint Immediate Ropp_le_cancel: real.

Lemma Ropp_ge_cancel : forall r1 r2, - r2 >= - r1 -> r1 >= r2.
Proof.
  intros x y h.
  rewrite <- Ropp_involutive with x.
  rewrite <- Ropp_involutive with y.
  apply Ropp_ge_contravar.
  exact h.
Qed.

Lemma Rmult_lt_compat_r : forall r r1 r2, 0 < r -> r1 < r2 -> r1 * r < r2 * r.
Proof.
  intros x y z hx hyz.
  Check Rmult_lt_compat_l.
  rewrite Rmult_comm with y x.
  rewrite Rmult_comm with z x.
  apply Rmult_lt_compat_l.
  exact hx.
  exact hyz.
Qed.
Hint Resolve Rmult_lt_compat_r.

Lemma Rmult_gt_compat_r : forall r r1 r2, r > 0 -> r1 > r2 -> r1 * r > r2 * r.
Proof.
  intros x y z hx hyz.
  apply Rmult_lt_compat_r.
  exact hx.
  exact hyz.
Qed.

Lemma Rmult_gt_compat_l : forall r r1 r2, r > 0 -> r1 > r2 -> r * r1 > r * r2.
Proof.
  intros x y z hx hyz.
  apply Rmult_lt_compat_l.
  exact hx.
  exact hyz.
Qed.

Lemma Rmult_le_compat_l :
  forall r r1 r2, 0 <= r -> r1 <= r2 -> r * r1 <= r * r2.
Proof.
  intros x y z hx hyz.
  destruct hx as [ hx | hx ].
  destruct hyz as [ hyz | hyz ].
  left.
  apply Rmult_lt_compat_l. exact hx. exact hyz.
  subst z. right. reflexivity.
  subst x. rewrite Rmult_0_l.  rewrite Rmult_0_l. right. reflexivity.
Qed.
Hint Resolve Rmult_le_compat_l: real.

Lemma Rmult_le_compat_r :
  forall r r1 r2, 0 <= r -> r1 <= r2 -> r1 * r <= r2 * r.
Proof.
  intros x y z hx hyz.
  rewrite Rmult_comm with y x.
  rewrite Rmult_comm with z x.
  apply Rmult_le_compat_l.
  exact hx.
  exact hyz.
Qed.
Hint Resolve Rmult_le_compat_r: real.

Lemma Rmult_ge_compat_l :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r * r1 >= r * r2.
Proof.
  intros x y z hx hyz.
  apply Rle_ge.
  apply Rmult_le_compat_l.
  apply Rge_le.
  exact hx.
  apply Rge_le.
  exact hyz.
Qed.

Lemma Rmult_ge_compat_r :
  forall r r1 r2, r >= 0 -> r1 >= r2 -> r1 * r >= r2 * r.
Proof.
  intros x y z hx hyz.
  rewrite Rmult_comm with y x.
  rewrite Rmult_comm with z x.
  apply Rmult_ge_compat_l.
  exact hx.
  exact hyz.
Qed.

Lemma Rmult_le_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 <= r2 -> r3 <= r4 -> r1 * r3 <= r2 * r4.
Proof.
  intros w x y z.
  intros hw hy hwx hyz.
  apply Rle_trans with (w*z).
  apply Rmult_le_compat_l. exact hw. exact hyz.
  apply Rmult_le_compat_r.
  apply Rle_trans with y. exact hy. exact hyz.
  exact hwx.
Qed.
Hint Resolve Rmult_le_compat: real.

Lemma Rmult_ge_compat :
  forall r1 r2 r3 r4,
    r2 >= 0 -> r4 >= 0 -> r1 >= r2 -> r3 >= r4 -> r1 * r3 >= r2 * r4.
Proof.
  intros w x y z.
  intros hx hz hwx hyz.
  apply Rle_ge.
  apply Rmult_le_compat;apply Rge_le.
  exact hx.
  exact hz.
  exact hwx.
  exact hyz.
Qed.

Lemma Rmult_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 > 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros w x y z.
  intros hy hx hwx hyz.
  apply Rlt_trans with (y*x).
  rewrite Rmult_comm with w y.
  apply Rmult_lt_compat_l.
  exact hy. exact hwx.
  rewrite Rmult_comm with y x.
  apply Rmult_lt_compat_l.
  exact hx. exact hyz.
Qed.

Lemma Rmult_le_0_lt_compat :
  forall r1 r2 r3 r4,
    0 <= r1 -> 0 <= r3 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.
  intros w x y z.
  intros hw hy hwx hyz.
  destruct hw as [ hw | hw ].
  {
    destruct hy as [ hy | hy ].
    {
      apply Rlt_trans with (w*z).
      apply Rmult_lt_compat_l.
      exact hw.
      exact hyz.
      apply Rmult_lt_compat_r.
      apply Rlt_trans with y.
      exact hy. exact hyz.
      exact hwx.
    }
    {
      subst y.
      rewrite Rmult_0_r.
      apply Rlt_trans with (w*z).
      rewrite <- Rmult_0_r with w.
      apply Rmult_lt_compat_l.
      exact hw.
      exact hyz.
      apply Rmult_lt_compat_r.
      exact hyz.
      exact hwx.
    }
  }
  {
    subst w.
    destruct hy as [ hy | hy ].
    {
      rewrite Rmult_0_l.
      rewrite <- Rmult_0_r with x.
      apply Rmult_lt_compat_l.
      exact hwx.
      apply Rlt_trans with y.
      exact hy.
      exact hyz.
    }
    {
      subst y.
      rewrite Rmult_0_r.
      rewrite <- Rmult_0_r with x.
      apply Rmult_lt_compat_l.
      exact hwx.
      exact hyz.
  }
}
Qed.

Lemma Rmult_lt_0_compat : forall r1 r2, 0 < r1 -> 0 < r2 -> 0 < r1 * r2.
Proof.
  intros x y hx hy.
  rewrite <- Rmult_0_r with x.
  apply Rmult_lt_compat_l.
  exact hx.
  exact hy.
Qed.

Lemma Rmult_gt_0_compat : forall r1 r2, r1 > 0 -> r2 > 0 -> r1 * r2 > 0.
Proof.
exact Rmult_lt_0_compat.
Qed.

Lemma Rmult_le_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r2 <= r * r1.
Proof.
  intros x y z hx hyz.
  apply Ropp_le_cancel.
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_l.
  apply Rmult_le_compat_l.
  rewrite <- Ropp_0.
  apply Ropp_le_contravar.
  exact hx.
  exact hyz.
Qed.
Hint Resolve Rmult_le_compat_neg_l: real.

Lemma Rmult_le_ge_compat_neg_l :
  forall r r1 r2, r <= 0 -> r1 <= r2 -> r * r1 >= r * r2.
Proof.
  intros x y z hx hyz.
  apply Rle_ge.
  apply Rmult_le_compat_neg_l.
  exact hx.
  exact hyz.
Qed.
Hint Resolve Rmult_le_ge_compat_neg_l: real.

Lemma Rmult_lt_gt_compat_neg_l :
  forall r r1 r2, r < 0 -> r1 < r2 -> r * r1 > r * r2.
Proof.
  intros x y z hx hyz.
  apply Ropp_lt_cancel.
  rewrite Ropp_mult_distr_l.
  rewrite Ropp_mult_distr_l.
  apply Rmult_lt_compat_l.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  exact hx.
  exact hyz.
Qed.

Lemma Rmult_lt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof. (* this one is not obvious *)
  intros x y z hx h.
  destruct (Rtotal_order y z) as [ lt | [ eq | gt ] ].
  {
    exact lt.
  }
  {
    subst y.
    apply Rlt_irrefl in h.
    contradiction.
  }
  {
    exfalso.
    apply Rlt_irrefl with (x * y).
    apply Rlt_trans with (x*z).
    exact h.
    apply Rmult_lt_compat_l.
    exact hx.
    apply Rgt_lt.
    exact gt.
  }
Qed.

Lemma Rmult_gt_reg_l : forall r r1 r2, 0 < r -> r * r1 < r * r2 -> r1 < r2.
Proof.
  exact Rmult_lt_reg_l.
Qed.

Lemma Rmult_le_reg_l : forall r r1 r2, 0 < r -> r * r1 <= r * r2 -> r1 <= r2.
Proof.
  intros x y z hx hy.
  destruct hy as [ hy | hy ].
  left. apply Rmult_lt_reg_l with x. exact hx. exact hy.
  right. apply Rmult_eq_reg_l with x. exact hy.
  apply Rgt_not_eq. exact hx.
Qed.

Lemma Rmult_le_reg_r : forall r r1 r2, 0 < r -> r1 * r <= r2 * r -> r1 <= r2.
Proof.
  intros x y z hx h.
  apply Rmult_le_reg_l with x.
  exact hx.
  rewrite Rmult_comm with x y.
  rewrite Rmult_comm with x z.
  exact h.
Qed.

Lemma Rlt_minus : forall r1 r2, r1 < r2 -> r1 - r2 < 0.
Proof.
  intros x y h.
  apply Rplus_lt_reg_r with y.
  rewrite Rplus_0_l.
  unfold Rminus.
  rewrite  Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  exact h.
Qed.
Hint Resolve Rlt_minus: real.

Lemma Rgt_minus : forall r1 r2, r1 > r2 -> r1 - r2 > 0.
Proof.
  intros x y h.
  apply Rplus_lt_reg_r with (- (x-y)).
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  rewrite Ropp_minus_distr.
  apply Rlt_minus.
  exact h.
Qed.

Lemma Rlt_Rminus : forall a b:R, a < b -> 0 < b - a.
Proof.
  intros x y h.
  apply Rgt_minus.
  exact h.
Qed.

Lemma Rle_minus : forall r1 r2, r1 <= r2 -> r1 - r2 <= 0.
Proof.
  intros x y h.
  destruct h as [h|h].
  left. apply Rlt_minus. exact h.
  subst y. right.
  rewrite Rminus_diag_eq. reflexivity. reflexivity.
Qed.

Lemma Rge_minus : forall r1 r2, r1 >= r2 -> r1 - r2 >= 0.
Proof.
  intros x y h.
  apply Rle_ge.
  apply Rplus_le_reg_l with (-(x-y)).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  rewrite Ropp_minus_distr.
  apply Rle_minus.
  apply Rge_le.
  exact h.
Qed.

Lemma Rminus_lt : forall r1 r2, r1 - r2 < 0 -> r1 < r2.
Proof.
  intros x y h.
  apply Rplus_lt_reg_r with (-y).
  rewrite Rplus_opp_r.
  exact h.
Qed.

Lemma Rminus_gt : forall r1 r2, r1 - r2 > 0 -> r1 > r2.
Proof.
  intros x y h.
  apply Rminus_lt.
  apply Ropp_lt_cancel.
  rewrite Ropp_minus_distr.
  Search (-0).
  rewrite Ropp_0.
  exact h.
Qed.

Lemma Rminus_gt_0_lt : forall a b, 0 < b - a -> a < b.
Proof.
  intros x y h.
  apply Rminus_gt.
  exact h.
Qed.

Lemma Rminus_le : forall r1 r2, r1 - r2 <= 0 -> r1 <= r2.
Proof.
  intros x y h.
  apply Rplus_le_reg_r with (- y).
  rewrite Rplus_opp_r.
  exact h.
Qed.

Lemma Rminus_ge : forall r1 r2, r1 - r2 >= 0 -> r1 >= r2.
Proof.
  intros x y h.
  apply Rle_ge.
  apply Rplus_le_reg_r with (-y).
  rewrite Rplus_opp_r.
  apply Rge_le.
  exact h.
Qed.

Lemma tech_Rplus : forall r (s:R), 0 <= r -> 0 < s -> r + s <> 0.
Proof.
  intros x y hx hy.
  destruct hx as [hx | hx].
  apply Rgt_not_eq.
  apply Rlt_trans with x. exact hx.
  pattern x at 1;rewrite <- Rplus_0_r with x.
  apply Rplus_lt_compat_l. exact hy.
  subst x. rewrite Rplus_0_l. apply Rgt_not_eq. exact hy.
Qed.
Hint Immediate tech_Rplus: real.

Lemma Rle_0_sqr : forall r, 0 <= Rsqr r.
Proof.
  intros x.
  destruct (Rtotal_order x 0) as [lt | [ eq | gt]].
  unfold Rsqr. left.
  {
    rewrite <- Ropp_involutive with (x*x).
    Search( - (_*_)).
    rewrite Ropp_mult_distr_l.
    rewrite Ropp_mult_distr_r.
    assert (lt':0 < -x).
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      exact lt.
    apply Rmult_lt_0_compat.
    exact lt'.
    exact lt'.
  }
  subst x. right. unfold Rsqr. rewrite Rmult_0_l. reflexivity.
  left. unfold Rsqr. apply Rmult_lt_0_compat. exact gt. exact gt.
Qed.

Lemma Rlt_0_sqr : forall r, r <> 0 -> 0 < Rsqr r.
Proof.
  intros x neq.
  destruct (Rle_0_sqr x) as [h' | h'].
  exact h'.
  unfold Rsqr in h'.
  exfalso.
  apply neq.
  apply Rmult_eq_reg_l with x.
  rewrite <- h'. rewrite Rmult_0_r. reflexivity.
  exact neq.
Qed.
Hint Resolve Rle_0_sqr Rlt_0_sqr: real.

Lemma Rplus_sqr_eq_0_l : forall r1 r2, Rsqr r1 + Rsqr r2 = 0 -> r1 = 0.
Proof.
  intros x y h.  
  apply Rsqr_0_uniq.
  apply Rplus_eq_0_l with (y²).
  apply Rle_0_sqr.
  apply Rle_0_sqr.
  exact h.
Qed.

Lemma Rplus_sqr_eq_0 :
  forall r1 r2, Rsqr r1 + Rsqr r2 = 0 -> r1 = 0 /\ r2 = 0.
Proof.
  intros x y h.
  split.
  Search (Rsqr _).
  apply Rplus_sqr_eq_0_l with y. exact h.
  apply Rplus_sqr_eq_0_l with x. rewrite Rplus_comm. exact h.
Qed.

Lemma Rlt_0_1 : 0 < 1.
Proof.
  rewrite <- Rmult_1_l.
  fold (Rsqr 1).
  apply Rlt_0_sqr.
  apply R1_neq_R0.
Qed.
Hint Resolve Rlt_0_1: real.

Lemma Rle_0_1 : 0 <= 1.
Proof.
  left.
  exact Rlt_0_1.
Qed.

Lemma Rinv_0_lt_compat : forall r, 0 < r -> 0 < / r.
Proof.
  intros x h.
  apply Rmult_lt_reg_l with x.
  exact h. rewrite Rmult_0_r. rewrite Rinv_r.
  apply Rlt_0_1.
  apply Rgt_not_eq.
  exact h.
Qed.
Hint Resolve Rinv_0_lt_compat: real.

Lemma Rinv_lt_0_compat : forall r, r < 0 -> / r < 0.
Proof.
  intros x h.
  apply Ropp_lt_cancel.
  rewrite Ropp_0.
  rewrite Ropp_inv_permute.
  apply Rinv_0_lt_compat.
  rewrite <- Ropp_0.
  apply Ropp_lt_contravar.
  exact h.
  apply Rlt_not_eq.
  exact h.
Qed.
Hint Resolve Rinv_lt_0_compat: real.

Lemma Rinv_lt_contravar : forall r1 r2, 0 < r1 * r2 -> r1 < r2 -> / r2 < / r1.
Proof.
  intros x y hp hxy.
  apply Rmult_lt_reg_l with (x*y).
  exact hp.
  rewrite Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_r.
  rewrite Rmult_assoc.
  rewrite Rmult_comm with y (/ x).
  rewrite <- Rmult_assoc.
  rewrite Rinv_r.
  rewrite Rmult_1_l.
  exact hxy.
  apply Rlt_not_eq in hp.
  apply not_eq_sym in hp.
  apply Rmult_neq_0_reg in hp.
  apply hp.
  apply Rlt_not_eq in hp.
  apply not_eq_sym in hp.
  apply Rmult_neq_0_reg in hp.
  apply hp.
Qed.

Lemma Rinv_1_lt_contravar : forall r1 r2, 1 <= r1 -> r1 < r2 -> / r2 < / r1.
Proof. (* using asserts would make the proof quite nicer here *)
  intros x y.
  intros hx hxy.
  destruct hx as [lt | eq].
  {
    apply Rmult_lt_reg_l with x.
    apply Rlt_trans with 1.
    apply Rlt_0_1. exact lt.
    rewrite Rinv_r.
    apply Rmult_lt_reg_l with y.
    apply Rlt_trans with 1.
    apply Rlt_0_1.
    apply Rlt_trans with x.
    exact lt.
    exact hxy.
    rewrite Rmult_comm with x (/ y).
    rewrite <- Rmult_assoc.
    rewrite Rinv_r.
    rewrite Rmult_1_l.
    rewrite Rmult_1_r.
    exact hxy.
    apply Rgt_not_eq.
    apply Rgt_trans with x.
    exact hxy.
    apply Rgt_trans with 1.
    exact lt.
    apply Rlt_0_1.
    apply Rgt_not_eq.
    apply Rgt_trans with 1.
    exact lt.
    apply Rlt_0_1.
  }
  {
    subst x.
    apply Rinv_lt_contravar.
    rewrite Rmult_1_l.
    apply Rlt_trans with 1.
    apply Rlt_0_1.
    exact hxy.
    exact hxy.
  }
Qed.
Hint Resolve Rinv_1_lt_contravar: real.

Lemma Rle_lt_0_plus_1 : forall r, 0 <= r -> 0 < r + 1.
Proof.
  intros x h.
  destruct h as [ h | h ].
  apply Rlt_trans with x. exact h.
  pattern x at 1;rewrite <- Rplus_0_r with x.
  apply Rplus_lt_compat_l.
  apply Rlt_0_1.
  subst x. rewrite Rplus_0_l. apply Rlt_0_1.
Qed.
Hint Resolve Rle_lt_0_plus_1: real.

Lemma Rlt_plus_1 : forall r, r < r + 1.
Proof.
  intro x.
  pattern x at 1;rewrite <- Rplus_0_r with x.
  apply Rplus_lt_compat_l.
  apply Rlt_0_1.
Qed.
Hint Resolve Rlt_plus_1: real.

Lemma tech_Rgt_minus : forall r1 r2, 0 < r2 -> r1 > r1 - r2.
Proof.
  intros x y h.
  apply Rlt_gt in h.
  apply Rplus_lt_reg_r with y.
  apply Rgt_lt.
  unfold Rminus.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  apply Rplus_gt_compat_l.
  exact h.
Qed.

Lemma S_INR : forall n:nat, INR (S n) = INR n + 1.
Proof.
  Arguments INR n : simpl nomatch.
  intro n.
  destruct n.
  simpl. rewrite Rplus_0_l. reflexivity.
  simpl. reflexivity.
Qed.

Lemma S_O_plus_INR : forall n:nat, INR (1 + n) = INR 1 + INR n.
Proof.
  intro n.
  simpl.
  rewrite S_INR.
  rewrite Rplus_comm.
  reflexivity.
Qed.


Lemma plus_INR : forall n m:nat, INR (n + m) = INR n + INR m.
Proof.
  intro n.
  induction n as [ | n i ].
  simpl. intro m. rewrite Rplus_0_l. reflexivity.
  intro m.
  rewrite plus_comm.
  rewrite <- plus_n_Sm.
  rewrite S_INR.
  specialize (i m).
  rewrite S_INR.
  rewrite plus_comm.
  rewrite i.
  rewrite Rplus_assoc.
  rewrite Rplus_comm with (INR m) 1.
  rewrite <- Rplus_assoc.
  reflexivity.
Qed.
Hint Resolve plus_INR: real.

Lemma minus_INR : forall n m:nat, (m <= n)%nat -> INR (n - m) = INR n - INR m.
Proof.
  intros n m h.
  unfold Rminus.
  apply Rplus_eq_reg_r with (INR m).
  rewrite Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  rewrite <- plus_INR.
  rewrite Nat.sub_add.
  reflexivity.
  exact h.
Qed.
Hint Resolve minus_INR: real.

Lemma mult_INR : forall n m:nat, INR (n * m) = INR n * INR m.
Proof.
  intros n.
  induction n as [ | n i ].
  intro m. simpl. rewrite Rmult_0_l. reflexivity.
  intro m.
  rewrite Nat.mul_succ_l.
  rewrite plus_INR.
  rewrite S_INR.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  specialize (i m).
  rewrite i.
  reflexivity.
Qed.
Hint Resolve mult_INR: real.

Lemma pow_INR (m n: nat) :  INR (m ^ n) = pow (INR m) n.
Proof.
  generalize dependent m.
  induction n as [ | n i ].
  intro m. simpl. reflexivity.
  intro m. simpl.
  rewrite mult_INR.
  rewrite (i m).
  reflexivity.
Qed.

Lemma lt_0_INR : forall n:nat, (0 < n)%nat -> 0 < INR n.
Proof.
  intro n.
  induction n as [ | n i ].
  { intro h. inversion h. }
  intro h. inversion h as [ zeq | n' le n'eq]; clear h.
  { simpl. apply Rlt_0_1. }
  {
    subst n'.
    apply Rlt_trans with (INR n).
    {
      apply i.
      inversion le as [ w1  | n' le' eq ];clear le.
      { constructor. }
      { constructor. exact le'. }
   }
   { rewrite S_INR. apply Rlt_plus_1. }
  }
Qed.
Hint Resolve lt_0_INR: real.

Lemma lt_INR : forall n m:nat, (n < m)%nat -> INR n < INR m.
Proof.
  intro n.
  induction n as [ | n i ].
  { intros m h. simpl. apply lt_0_INR. exact h. }
  {
    intros m h.
    destruct m as [ | m ].
    { inversion h. }
    {
      rewrite S_INR.
      rewrite S_INR.
      apply Rplus_lt_compat_r.
      apply i.
      apply lt_S_n.
      exact h.
     }
  }
Qed.
Hint Resolve lt_INR: real.

Lemma lt_1_INR : forall n:nat, (1 < n)%nat -> 1 < INR n.
Proof.
  intros n h.
  apply lt_INR in h.
  simpl in h.
  exact h.
Qed.
Hint Resolve lt_1_INR: real.

Lemma pos_INR_nat_of_P : forall p:positive, 0 < INR (Pos.to_nat p).
Proof.
  intro p.
  apply lt_0_INR.
  apply Pos2Nat.is_pos.
Qed.
Hint Resolve pos_INR_nat_of_P: real.


Lemma pos_INR : forall n:nat, 0 <= INR n.
Proof.
  intro n.
  induction n as [ | n i ].
  simpl. right. reflexivity.
  apply Rle_trans with (INR n).
  exact i.
  rewrite S_INR.
  pattern (INR n) at 1;rewrite <- Rplus_0_r with (INR n).
  apply Rplus_le_compat_l.
  left. apply Rlt_0_1.
Qed.
Hint Resolve pos_INR: real.

Lemma INR_lt : forall n m:nat, INR n < INR m -> (n < m)%nat.
Proof.
  induction n as [ | n i ].
  { simpl. intros m h. destruct m.
    { simpl in h. apply Rlt_irrefl in h. elim h. }
    { apply Nat.lt_0_succ. }
  }
  { intros m h. destruct m.
    {
      exfalso.
      apply Rlt_irrefl with (INR 0).
      apply Rlt_trans with (INR (S n)).
      { apply lt_INR. apply Nat.lt_0_succ. }
      { exact h. }
    }
    {
      apply lt_n_S.
      apply i.
      apply Rplus_lt_reg_r with 1.
      rewrite <- S_INR.
      rewrite <- S_INR.
      exact h.
    }
  }
Qed.
Hint Resolve INR_lt: real.

Lemma le_INR : forall n m:nat, (n <= m)%nat -> INR n <= INR m.
Proof.
  intros n m h.
  Search ( _ <= _ -> _ \/ _)%nat.
  apply le_lt_or_eq in h.
  destruct h as [ h | h].
  left. apply lt_INR. exact h.
  subst m. right. reflexivity.
Qed.
Hint Resolve le_INR: real.

Lemma INR_not_0 : forall n:nat, INR n <> 0 -> n <> 0%nat.
Proof.
  intros n h eq.
  apply h.
  rewrite eq.
  simpl. reflexivity.
Qed.
Hint Immediate INR_not_0: real.

Lemma not_0_INR : forall n:nat, n <> 0%nat -> INR n <> 0.
Proof.
  intros n h eq.
  apply h. clear h.
  destruct n.
  { reflexivity. }
  {
    exfalso.
    apply Rlt_irrefl with 0.
    pattern 0 at 2;rewrite <- eq. clear eq.
    apply lt_0_INR.
    apply Nat.lt_0_succ.
  }
Qed.
Hint Resolve not_0_INR: real.

Lemma not_INR : forall n m:nat, n <> m -> INR n <> INR m.
Proof.
  intros n m h.
  generalize dependent n.
  induction m as [ | m i ].
  { intros n h. apply not_0_INR. exact h. }
  {
    intros n h.
    intro eq.
    destruct n.
    {
      clear i h.
      simpl in eq.
      apply Rlt_irrefl with 0.
      pattern 0 at 2;rewrite eq. clear eq.
      apply lt_0_INR.
      apply Nat.lt_0_succ.
    }
    {
      apply i with n;clear i.
      {
        clear eq.
        intro eq.
        apply h. clear h.
        subst m. reflexivity.
      }
      {
        clear h.
        apply Rplus_eq_reg_r with 1.
        rewrite <- S_INR.
        rewrite <- S_INR.
        exact eq.
      }
    }
  }
Qed.
Hint Resolve not_INR: real.

Lemma INR_eq : forall n m:nat, INR n = INR m -> n = m.
Proof.
  intros n.
  induction n as [ | n i ].
  {
    intro m. destruct m.
    { reflexivity. }
    {
      simpl. intro h.
      exfalso. (* this pattern could deserve it's own lemma *)
      apply Rlt_irrefl with 0.
      pattern 0 at 2;rewrite h.
      apply lt_0_INR.
      apply Nat.lt_0_succ.
    }
  }
  {
    intro m. destruct m.
    {
      simpl. intro h. exfalso.
      apply Rlt_irrefl with 0.
      pattern 0 at 2;rewrite <- h.
      apply lt_0_INR.
      apply Nat.lt_0_succ.
    }
    {
      intro h.
      Search ( S _ = S _).
      apply eq_S.
      apply i.
      apply Rplus_eq_reg_r with 1.
      rewrite <- S_INR.
      rewrite <- S_INR.
      exact h.
    }
  }
Qed.
Hint Resolve INR_eq: real.

Lemma INR_le : forall n m:nat, INR n <= INR m -> (n <= m)%nat.
Proof.
  intros n m h.
  destruct h as [ h | h].
  {
    apply Nat.lt_le_incl.
    apply INR_lt.
    exact h.
  }
  {
    apply Nat.eq_le_incl.
    apply INR_eq.
    exact h.
  }
Qed.
Hint Resolve INR_le: real.

Lemma not_1_INR : forall n:nat, n <> 1%nat -> INR n <> 1.
Proof.
  intros n h eq.
  apply h.
  apply INR_eq.
  simpl.
  exact eq.
Qed.
Hint Resolve not_1_INR: real.

Lemma IZN : forall n:Z, (0 <= n)%Z ->  exists m : nat, n = Z.of_nat m.
Proof.
  intros z h.

  destruct z as [  | p | p ].
  {
    exists 0%nat. simpl. reflexivity.
  }
  {
    unfold Z.le in h.
    simpl in h. clear h.
    induction p as [ p i | p i | ] .
    {
      destruct i as [ m eq ].
      rewrite Pos2Z.pos_xI.
      exists (2*m+1)%nat.
      rewrite Nat2Z.inj_add.
      rewrite Nat2Z.inj_mul.
      rewrite <- eq.
      simpl.
      reflexivity.
    }
    {
      rewrite Pos2Z.pos_xO.
      destruct i as [ m eq ].
      exists (2*m)%nat.
      rewrite Nat2Z.inj_mul.
      rewrite <- eq.
      simpl.
      reflexivity.
    }
    {
      exists 1%nat.
      simpl.
      reflexivity.
    }
  }
  {
    unfold Z.le in h.
    simpl in h.
    contradiction.
  }
Qed.

Lemma INR_IPR : forall p, INR (Pos.to_nat p) = IPR p.
Proof.

Qed.

(**********)
Lemma INR_IZR_INZ : forall n:nat, INR n = IZR (Z.of_nat n).
Proof.

Qed.

Lemma plus_IZR_NEG_POS :
  forall p q:positive, IZR (Zpos p + Zneg q) = IZR (Zpos p) + IZR (Zneg q).
Proof.

Qed.

(**********)
Lemma plus_IZR : forall n m:Z, IZR (n + m) = IZR n + IZR m.
Proof.

Qed.

(**********)
Lemma mult_IZR : forall n m:Z, IZR (n * m) = IZR n * IZR m.
Proof.

Qed.

Lemma pow_IZR : forall z n, pow (IZR z) n = IZR (Z.pow z (Z.of_nat n)).
Proof.

Qed.

(**********)
Lemma succ_IZR : forall n:Z, IZR (Z.succ n) = IZR n + 1.
Proof.

Qed.

(**********)
Lemma opp_IZR : forall n:Z, IZR (- n) = - IZR n.
Proof.

Qed.

Definition Ropp_Ropp_IZR := opp_IZR.

Lemma minus_IZR : forall n m:Z, IZR (n - m) = IZR n - IZR m.
Proof.

Qed.

(**********)
Lemma Z_R_minus : forall n m:Z, IZR n - IZR m = IZR (n - m).
Proof.

Qed.

(**********)
Lemma lt_0_IZR : forall n:Z, 0 < IZR n -> (0 < n)%Z.
Proof.

Qed.

(**********)
Lemma lt_IZR : forall n m:Z, IZR n < IZR m -> (n < m)%Z.
Proof.

Qed.

(**********)
Lemma eq_IZR_R0 : forall n:Z, IZR n = 0 -> n = 0%Z.
Proof.

Qed.

(**********)
Lemma eq_IZR : forall n m:Z, IZR n = IZR m -> n = m.
Proof.

Qed.

(**********)
Lemma not_0_IZR : forall n:Z, n <> 0%Z -> IZR n <> 0.
Proof.

Qed.

(*********)
Lemma le_0_IZR : forall n:Z, 0 <= IZR n -> (0 <= n)%Z.
Proof.

Qed.

(**********)
Lemma le_IZR : forall n m:Z, IZR n <= IZR m -> (n <= m)%Z.
Proof.

Qed.

(**********)
Lemma le_IZR_R1 : forall n:Z, IZR n <= 1 -> (n <= 1)%Z.
Proof.

Qed.

(**********)
Lemma IZR_ge : forall n m:Z, (n >= m)%Z -> IZR n >= IZR m.
Proof.

Qed.

Lemma IZR_le : forall n m:Z, (n <= m)%Z -> IZR n <= IZR m.
Proof.

Qed.

Lemma IZR_lt : forall n m:Z, (n < m)%Z -> IZR n < IZR m.
Proof.

Qed.

Lemma IZR_neq : forall z1 z2:Z, z1 <> z2 -> IZR z1 <> IZR z2.
Proof.
intros; red; intro; elim H; apply eq_IZR; assumption.
Qed.

Hint Extern 0 (IZR _ <= IZR _) => apply IZR_le, Zle_bool_imp_le, eq_refl : real.
Hint Extern 0 (IZR _ >= IZR _) => apply Rle_ge, IZR_le, Zle_bool_imp_le, eq_refl : real.
Hint Extern 0 (IZR _ <  IZR _) => apply IZR_lt, eq_refl : real.
Hint Extern 0 (IZR _ >  IZR _) => apply IZR_lt, eq_refl : real.
Hint Extern 0 (IZR _ <> IZR _) => apply IZR_neq, Zeq_bool_neq, eq_refl : real.

Lemma one_IZR_lt1 : forall n:Z, -1 < IZR n < 1 -> n = 0%Z.
Proof.

Qed.

Lemma one_IZR_r_R1 :
  forall r (n m:Z), r < IZR n <= r + 1 -> r < IZR m <= r + 1 -> n = m.
Proof.

Qed.


(**********)
Lemma single_z_r_R1 :
  forall r (n m:Z),
    r < IZR n -> IZR n <= r + 1 -> r < IZR m -> IZR m <= r + 1 -> n = m.
Proof.

Qed.

(**********)
Lemma tech_single_z_r_R1 :
  forall r (n:Z),
    r < IZR n ->
    IZR n <= r + 1 ->
    (exists s : Z, s <> n /\ r < IZR s /\ IZR s <= r + 1) -> False.
Proof.

Qed.

(*********)
Lemma Rmult_le_pos : forall r1 r2, 0 <= r1 -> 0 <= r2 -> 0 <= r1 * r2.
Proof.

Qed.

Lemma Rinv_le_contravar :
  forall x y, 0 < x -> x <= y -> / y <= / x.
Proof.

Qed.

Lemma Rle_Rinv : forall x y:R, 0 < x -> 0 < y -> x <= y -> / y <= / x.
Proof.

Qed.

Lemma Ropp_div : forall x y, -x/y = - (x / y).
Proof.
Qed.

Lemma double : forall r1, 2 * r1 = r1 + r1.
Proof.

Qed.

Lemma double_var : forall r1, r1 = r1 / 2 + r1 / 2.
Proof.

Qed.

Lemma R_rm : ring_morph
  0%R 1%R Rplus Rmult Rminus Ropp eq
  0%Z 1%Z Zplus Zmult Zminus Z.opp Zeq_bool IZR.
Proof.

Qed.

Lemma Zeq_bool_IZR x y :
  IZR x = IZR y -> Zeq_bool x y = true.
Proof.

Qed.

Add Field RField : Rfield
  (completeness Zeq_bool_IZR, morphism R_rm, constants [IZR_tac], power_tac R_power_theory [Rpow_tac]).

Lemma Rmult_ge_0_gt_0_lt_compat :
  forall r1 r2 r3 r4,
    r3 >= 0 -> r2 > 0 -> r1 < r2 -> r3 < r4 -> r1 * r3 < r2 * r4.
Proof.

Qed.

Lemma le_epsilon :
  forall r1 r2, (forall eps:R, 0 < eps -> r1 <= r2 + eps) -> r1 <= r2.
Proof.

Qed.

(**********)
Lemma completeness_weak :
  forall E:R -> Prop,
    bound E -> (exists x : R, E x) ->  exists m : R, is_lub E m.
Proof.

Qed.

Lemma Rdiv_lt_0_compat : forall a b, 0 < a -> 0 < b -> 0 < a/b.
Proof. 

Qed.

Lemma Rdiv_plus_distr : forall a b c, (a + b)/c = a/c + b/c.
Proof.
Qed.

Lemma Rdiv_minus_distr : forall a b c, (a - b)/c = a/c - b/c.
Proof.
Qed.

Lemma Req_EM_T : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.

Qed.


Record nonnegreal : Type := mknonnegreal
  {nonneg :> R; cond_nonneg : 0 <= nonneg}.

Record posreal : Type := mkposreal {pos :> R; cond_pos : 0 < pos}.

Record nonposreal : Type := mknonposreal
  {nonpos :> R; cond_nonpos : nonpos <= 0}.

Record negreal : Type := mknegreal {neg :> R; cond_neg : neg < 0}.

Record nonzeroreal : Type := mknonzeroreal
  {nonzero :> R; cond_nonzero : nonzero <> 0}.

Notation prod_neq_R0 := Rmult_integral_contrapositive_currified (only parsing).
Notation minus_Rgt := Rminus_gt (only parsing).
Notation minus_Rge := Rminus_ge (only parsing).
Notation plus_le_is_le := Rplus_le_reg_pos_r (only parsing).
Notation plus_lt_is_lt := Rplus_lt_reg_pos_r (only parsing).
Notation INR_lt_1 := lt_1_INR (only parsing).
Notation lt_INR_0 := lt_0_INR (only parsing).
Notation not_nm_INR := not_INR (only parsing).
Notation INR_pos := pos_INR_nat_of_P (only parsing).
Notation not_INR_O := INR_not_0 (only parsing).
Notation not_O_INR := not_0_INR (only parsing).
Notation not_O_IZR := not_0_IZR (only parsing).
Notation le_O_IZR := le_0_IZR (only parsing).
Notation lt_O_IZR := lt_0_IZR (only parsing).
