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

  Theorem sigma_split :
    forall low high k:nat,
      (low <= k)%nat ->
      (k < high)%nat -> sigma low high = sigma low k + sigma (S k) high.
  Proof.
    intros low high k lk kh.
    induction k as [| k i].
    {
      apply le_n_0_eq in lk.
      rewrite <- lk.
      unfold sigma. simpl.
      rewrite <- minus_n_O.
      rewrite decomp_sum.
      {
        rewrite Nat.sub_1_r.
        reflexivity.
      }
      assumption.
    }
    apply Compare.le_le_S_eq in lk.
    {
      destruct lk as [lk | lk].
      {
        apply Peano.le_S_n in lk.
        replace (sigma low (S k)) with (sigma low k + f (S k)).
        {
          rewrite Rplus_assoc.
          replace (f (S k) + sigma (S (S k)) high) with (sigma (S k) high).
          {
            apply i.
            { assumption. }
            apply lt_trans with (S k).
            { apply lt_n_Sn. }
            assumption.
          }
          unfold sigma.
          replace (high - S (S k))%nat with (pred (high - S k)).
          {
            pattern (S k) at 3.
            replace (S k) with (S k + 0)%nat.
            {
              replace (sum_f_R0 (fun k0:nat => f (S (S k) + k0)) (pred (high - S k))) with
              (sum_f_R0 (fun k0:nat => f (S k + S k0)) (pred (high - S k))).
              {
                apply (decomp_sum (fun i:nat => f (S k + i))).
                apply lt_minus_O_lt.
                assumption.
              }
              apply sum_eq. intros.
              replace (S k + S i0)%nat with (S (S k) + i0)%nat.
              { reflexivity. }
              ring.
            }
            ring.
          }
          replace (high - S (S k))%nat with (high - S k - 1)%nat.
          { apply pred_of_minus. }
          omega.
        }
        rewrite titi. reflexivity.
        assumption.
      }
      rewrite <- lk. unfold sigma. rewrite <- minus_n_n. simpl.
      replace (high - S low)%nat with (pred (high - low)).
      {
        replace (sum_f_R0 (fun k0:nat => f (S (low + k0))) (pred (high - low))) with
        (sum_f_R0 (fun k0:nat => f (low + S k0)) (pred (high - low))).
        {
          apply (decomp_sum (fun k0:nat => f (low + k0))).
          apply lt_minus_O_lt.
          apply le_lt_trans with (S k).
          { rewrite lk. apply le_n. }
          assumption.
        }
        apply sum_eq. intros.
        replace (S (low + i0)) with (low + S i0)%nat.
        { reflexivity. }
        ring.
      }
      omega.
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
