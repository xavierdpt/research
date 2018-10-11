(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import PartSum.
Require Import Omega.
Require Import Setoid Morphisms. 
Local Open Scope R_scope.

Set Implicit Arguments.

Local Open Scope nat_scope.

Lemma plus_S_minus : forall n m : nat, m<=n -> S n = m + S(n - m).
Proof.
  induction n as [ | n i].
  { simpl. intros m le. apply le_n_0_eq in le. subst m. simpl. reflexivity. }
  destruct m.
  { simpl. reflexivity. }
  intros. simpl. rewrite (i m).
  { reflexivity. }
  apply Peano.le_S_n. assumption.
Qed.

Lemma SnPSm_SSnPm : forall n m : nat, S n + S m = S (S n) + m.
Proof.
intros. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.


Lemma nMSm_nMmM1 : forall n m, n - (S m) = (n - m) - 1.
Proof.
induction n as [ | n i ]. simpl. reflexivity.
intro m. destruct m. simpl. reflexivity.
rewrite Nat.sub_succ.
rewrite (i m). clear i.
rewrite Nat.sub_succ.
reflexivity.
Qed.

Local Close Scope nat_scope.



Section Sigma.

  Variable f : nat -> R.

  Definition sigma (low high:nat) : R :=
    sum_f_R0 (fun k:nat => f (low + k)) (high - low).

  Lemma sigma_S_r : forall (low k:nat) , (low <= k)%nat -> sigma low k + f (S k) = sigma low (S k).
  Proof.
    intros low k h. unfold sigma. rewrite <- minus_Sn_m.
    rewrite (@plus_S_minus k low). simpl. reflexivity.
    assumption. assumption.
  Qed.

 

  Lemma specific1 : forall (k m:nat),
    sum_f_R0 (fun x:nat => f (S (S k) + x)) m =
    sum_f_R0 (fun x:nat => f (S k + S x))   m.
  Proof.
    intros k m. apply sum_eq. intros i im. rewrite SnPSm_SSnPm. reflexivity.
  Qed.

  Lemma specific2 : forall (k m:nat),
    sum_f_R0 (fun x:nat => f (S (k + x))) m =
    sum_f_R0 (fun x:nat => f (k + S x))   m.
  Proof.
    intros k m. apply sum_eq. intros i im. rewrite plus_n_Sm. reflexivity.
  Qed.

  Lemma sigma_S_l : forall k high : nat, (S k < high)%nat -> sigma (S k) high = f (S k) + sigma (S (S k)) high.
  Proof.
    intros k high kh.
    unfold sigma.
    rewrite (Nat.sub_succ_r high (S k)).
    rewrite <- Nat.add_0_r at 2.
    rewrite specific1.
    apply decomp_sum.
    apply lt_minus_O_lt.
    assumption.
  Qed.

  Lemma soo : sigma 0 0 = f 0.
  Proof. reflexivity. Qed.

  Lemma snn : forall n : nat, sigma n n = f n.
  Proof.
    intro n.
    unfold sigma.
    rewrite <- minus_n_n.
    simpl.
    rewrite <- plus_n_O.
    reflexivity.
  Qed.

  Lemma sigma_0_sumf : forall high :  nat, sigma 0 high = sum_f_R0 f high.
  Proof. 
    intro high.
    unfold sigma. simpl. rewrite <- minus_n_O.
    reflexivity.
  Qed.

  Definition shift {T:Type} (f:nat->T) := fun n => f (S n).

  Lemma sigma_1_sumf : forall high :  nat, sigma 1 high = sum_f_R0 (shift f) (high-1).
  Proof. 
    intro high.
    unfold sigma. simpl. unfold shift.
    reflexivity.
  Qed.

  Lemma decomp_sum_with_shift : forall (An : nat -> R) (N : nat),
       (0 < N)%nat -> sum_f_R0 An N = An 0%nat + sum_f_R0 (shift An) (Nat.pred N).
  Proof.
    apply decomp_sum.
  Qed.

  Theorem sigma_split :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high = sigma low k + sigma (S k) high.
  Proof.
    intros low high k lk kh.
    induction k as [| k i].
    {
      apply le_n_0_eq in lk. (* x <= 0 -> x = 0 *)
      rewrite <- lk. (* low = 0 *)
      rewrite soo.
      rewrite sigma_0_sumf.
      rewrite sigma_1_sumf.
      rewrite decomp_sum_with_shift. (* sum f n = f 0 + sum f' n *)
      {
        rewrite Nat.sub_1_r. (* n - 1 = pred n *)
        reflexivity.
      }
      assumption.
    }
    apply Compare.le_le_S_eq in lk. (* a <= S b -> S a <= S b \/ a = S b *)
    {
      destruct lk as [lk | lk].
      {
        apply Peano.le_S_n in lk. (* S n <= S m -> n <= m *)
        rewrite <- sigma_S_r. (* sum n (S m) = sum n m  + f(S m) *)
        {
          rewrite Rplus_assoc.
          rewrite <- sigma_S_l. (* f n + sum (S n) m = sum n m *)
          {
            apply i. (* induction hypothesis *)
            { assumption. }
            apply lt_trans with (S k).
            { apply lt_n_Sn. }
            assumption.
          }
          assumption.
        }
        assumption.
      }
      rewrite <- lk. (* low = S k *)
      rewrite snn.
      unfold sigma.
      simpl.
      rewrite Nat.sub_succ_r. (* n - S m = pred (n - m) *)
      rewrite specific2. (* S ( n + m) -> n + S m within abstraction *)
      {
        apply decomp_sum.
        apply lt_minus_O_lt. (* 0 < n -m -> n < m *)
        apply le_lt_trans with (S k).
        {
          rewrite lk.
          apply le_n. (* n <= n *)
        }
        assumption.
      }
    }
  Qed.

  Theorem sigma_diff :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high - sigma low k = sigma (S k) high.
  Proof.
    intros low high k H1 H2; symmetry ; rewrite (sigma_split H1 H2); ring.
  Qed.

  Theorem sigma_diff_neg :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low k - sigma low high = - sigma (S k) high.
  Proof.
    intros low high k H1 H2; rewrite (sigma_split H1 H2); ring.
  Qed.

  Theorem sigma_first :
    forall low high:nat,
      (low < high)%nat -> sigma low high = f low + sigma (S low) high.
  Proof.
    intros low high H1; generalize (lt_le_S low high H1); intro H2;
      generalize (lt_le_weak low high H1); intro H3;
        replace (f low) with (sigma low low).
    apply sigma_split.
    apply le_n.
    assumption.
    unfold sigma; rewrite <- minus_n_n.
    simpl.
    replace (low + 0)%nat with low; [ reflexivity | ring ].
  Qed.

  Theorem sigma_last :
    forall low high:nat,
      (low < high)%nat -> sigma low high = f high + sigma low (pred high).
  Proof.
    intros low high H1; generalize (lt_le_S low high H1); intro H2;
      generalize (lt_le_weak low high H1); intro H3;
        replace (f high) with (sigma high high).
    rewrite Rplus_comm; cut (high = S (pred high)).
    intro; pattern high at 3; rewrite H.
    apply sigma_split.
    apply le_S_n; rewrite <- H; apply lt_le_S; assumption.
    apply lt_pred_n_n; apply le_lt_trans with low; [ apply le_O_n | assumption ].
    apply S_pred with 0%nat; apply le_lt_trans with low;
      [ apply le_O_n | assumption ].
    unfold sigma; rewrite <- minus_n_n; simpl;
      replace (high + 0)%nat with high; [ reflexivity | ring ].
  Qed.

  Theorem sigma_eq_arg : forall low:nat, sigma low low = f low.
  Proof.
    intro; unfold sigma; rewrite <- minus_n_n.
    simpl; replace (low + 0)%nat with low; [ reflexivity | ring ].
  Qed.

End Sigma.
