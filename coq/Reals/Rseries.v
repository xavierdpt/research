Require Import Rbase.
Require Import Rfunctions.
Require Import Compare.
Local Open Scope R_scope.

Implicit Type r : R.

Remark Rlt_0_half : 0 < / 2.
Proof.
  apply Rinv_0_lt_compat.
  apply Rlt_0_2.
Qed.

Remark Rlt_half_1 : / 2 < 1.
Proof.
  rewrite <- Rinv_1.
  apply Rinv_lt_contravar.
  rewrite Rmult_1_l. apply Rlt_0_2.
  pattern 2;rewrite <- Rmult_1_r. rewrite double.
  pattern 1 at 1;rewrite <- Rplus_0_r. apply Rplus_lt_compat_l.
  apply Rlt_0_1.
Qed.

Remark half_half :/ 2 + / 2 = 1.
Proof.
  pattern (/ 2);rewrite <- Rmult_1_r.
  rewrite <- Rmult_plus_distr_l.
  rewrite <- double.
  rewrite Rmult_1_r.
  rewrite Rinv_l.
  reflexivity.
  intro eq.
  apply Rlt_irrefl with 0.
  pattern 0 at 2;rewrite <- eq.
  apply Rlt_0_2.
Qed.

Lemma Rlt_irrefl_le : forall a b, a < b -> b <= a -> False.
Proof.
  intros a b hab hba.
  destruct hba.
  { apply Rlt_irrefl with a. apply Rlt_trans with b;assumption. }
  { subst b. apply Rlt_irrefl with a. exact hab. }
Qed.

Lemma ex_ex : forall (T:Type) (P:T->Prop) (Q:{ t : T | P t }), exists (t:T), P t.
Proof.
  intros T P h.
  destruct h.
  exists x.
  exact p.
Qed.

Lemma ex_ex_inv : forall (T:Type) (P:T->Prop), (exists (t:T), P t) -> exists (Q:{ t : T | P t }), True.
Proof.
  intros T P h.
  destruct h as [ t pt].
  exists (exist P t pt).
  apply I.
Qed.

Lemma exists_fun : forall {A B : Type} (P:A->B->Prop), (forall a, {b | P a b}) -> exists f, forall a, P a (f a).
Proof.
  intros A B P h.
  exists (fun a => match (h a) with exist _ b _ => b end).
  intros a.
  destruct (h a).
  exact p.
Qed.

Lemma exists_fun' : forall {A B : Type} (P:A->B->Prop), (forall a, {b | P a b}) -> { f | forall a, P a (f a) }.
Proof.
  intros A B P h.
  exists (fun a => match (h a) with exist _ b _ => b end).
  intros a.
  destruct (h a).
  exact p.
Qed.

Lemma Rplus_le_compat_0_l : forall u v, 0 <= v -> u <= u + v.
Proof.
  intros u v h.
  pattern u at 1;rewrite <- Rplus_0_r.
  apply Rplus_le_compat_l.
  exact h.
Qed.

Lemma Rplus_le_compat_0_r : forall u v, 0 <= v -> u <= v + u.
Proof.
  intros u v h.
  rewrite Rplus_comm.
  apply Rplus_le_compat_0_l.
  exact h.
Qed.

Lemma Rplus_lt_compat_l_minus : forall u v w, v < w - u -> u + v < w.
Proof.
  intros u v w h.
  apply Rplus_lt_reg_l with (-u).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite Rplus_comm.
  fold (w-u).
  exact h.
Qed.

Lemma Rplus_lt_compat_r_minus : forall u v w, u < w - v -> u + v < w.
Proof.
  intros u v w h.
  rewrite Rplus_comm.
  apply Rplus_lt_compat_l_minus.
  exact h.
Qed.

Lemma Rplus_le_compat_l_minus : forall u v w, v <= w - u -> u + v <= w.
Proof.
  intros u v w h.
  apply Rplus_le_reg_l with (-u).
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  rewrite Rplus_comm.
  fold (w-u).
  exact h.
Qed.

Lemma Rplus_le_compat_r_minus : forall u v w, u <= w - v -> u + v <= w.
Proof.
  intros u v w h.
  rewrite Rplus_comm.
  apply Rplus_le_compat_l_minus.
  exact h.
Qed.

Lemma Rminus_diag : forall r, r-r=0.
Proof.
  intro r.
  unfold Rminus.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.

Lemma lt_disj : (forall n m, S m < S n -> S m < n \/ S m = n)%nat.
Proof.
  intros n m h.
  apply lt_le_S in h.
  apply le_lt_or_eq in h.
  destruct h as [ h | h ].
  {
    apply lt_S_n in h.
    left. exact h.
  }
  {
    apply eq_add_S in h.
    right. exact h.
  }
Qed.

Lemma sum_pow_neq_0: forall x y n, 0 <= x -> 0 < y -> x + y^n = 0 -> False.
Proof.
  intros x y n hx hy heq.
  apply Rlt_irrefl with 0.
  pattern 0 at 2;rewrite <- heq.
  apply Rle_lt_trans with x.
  { exact hx. }
  {
    pattern x at 1;rewrite <- Rplus_0_r.
    apply Rplus_lt_compat_l.
    apply pow_lt.
    exact hy.
  }
Qed.

(* Duplicate from extension of Rfunctions *)
Lemma Rgen : forall r:R, exists n:nat, INR n >= r.
Proof.
  intro r.
  destruct (archimed r) as [ agt ale ].
  exists (Z.abs_nat (up r)).
  destruct (up r) eqn:upeq.
  { (* up r = 0 *)
    simpl.
    left. exact agt.
  }
  { (* up r = Z.pos p *)
    simpl.
    destruct (Pos.to_nat p) eqn:poseq.
    { (* Pos.to_nat p = 0 *)
      simpl.
      generalize (Pos2Nat.is_pos p);intro hpos.
      rewrite poseq in hpos.
      inversion hpos.
    }
    { (* Pos.to_nat p = S n *)
      (* rewrite S_INR. *)
      left.
      rewrite INR_IZR_INZ.
      rewrite <- poseq.
      rewrite positive_nat_Z.
      exact agt.
    }
  }
  { (* up r = Z.neg p *)
    simpl.
    destruct (Pos.to_nat p) eqn:poseq.
    { (* Pos.to_nat p = 0 *)
      simpl.
      generalize (Pos2Nat.is_pos p);intro hpos.
      rewrite poseq in hpos.
      inversion hpos.
    }
    { (* Pos.to_nat p = S n *)
      left.
      rewrite INR_IZR_INZ.
      rewrite <- poseq.
      rewrite positive_nat_Z.
      apply Rgt_trans with (IZR (Z.neg p)).
      {
        apply Rlt_gt.
        apply IZR_lt.
        apply Pos2Z.neg_lt_pos.
      }
      { exact agt. }
    }
  }
Qed.

Lemma Rgen_two_power :
  forall b:R, exists N : nat, b <= 2 ^ N.
Proof.
  intros.
  destruct (archimed b) as [H0 H1].
  clear H1.
  {
    destruct (Rgen b) as [N H1].
    apply Rge_le in H1.
    exists N.
    unfold IZR. unfold IPR. unfold IPR_2.
    apply Rle_trans with (1 + INR N * 1).
    {
      apply Rle_trans with (INR N).
      { exact H1. }
      {
        apply Rlt_le.
        pattern (INR N) at 1;rewrite <- Rplus_0_l.
        rewrite Rmult_1_r.
        apply Rplus_lt_compat_r.
        apply Rlt_0_1.
      }
    }
    { apply poly. exact Rlt_0_1. }
  }
Qed.

Lemma Neq_2_0 : 2 <> 0.
Proof.
  intro eq. apply Rlt_irrefl with 0. pattern 0 at 2;rewrite <- eq.
  exact Rlt_0_2.
Qed.

Lemma Rgen_half_power :
  forall b:R, 0 < b -> exists N : nat, (/ 2) ^ N <= b.
Proof.
  intros.
  generalize Rgen_two_power;intro gtp.
  specialize (gtp (/ b)).
  destruct gtp as [N h].
  exists N.
  rewrite <- Rinv_pow.
  2:{ exact Neq_2_0. }
  rewrite <- Rinv_involutive with b.
  2:{ apply Rlt_dichotomy_converse. right. exact H. }
  apply Rinv_le_contravar.
  1:{ apply Rinv_0_lt_compat. exact H. }
  exact h.
Qed.

Section sequence.

  Fixpoint Rmax_N (U:nat->R) (n:nat) : R :=
    match n with
      | O => U 0%nat
      | S n => Rmax (U (S n)) (Rmax_N U n)
    end.

  Definition EUn (U:nat->R) (r:R) : Prop :=  exists n : nat, r = U n.

  Definition Un_cv (U:nat->R) (l:R) : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat, (forall n:nat, (n >= N)%nat -> R_dist (U n) l < eps).

  Definition Cauchy_crit (U : nat -> R) : Prop :=
    forall eps:R,
      eps > 0 ->
      exists N : nat,
        (forall n m:nat,
          (n >= N)%nat -> (m >= N)%nat -> R_dist (U n) (U m) < eps).

  Definition Un_growing (U : nat -> R) : Prop := forall n:nat, U n <= U (S n).

  Lemma EUn_noempty : forall (U : nat -> R), exists r : R, EUn U r.
  Proof.
    intro U.
    exists (U 0%nat).
    unfold EUn.
    exists 0%nat.
    reflexivity.
  Qed.

  Lemma Un_in_EUn : forall (U : nat -> R) (n:nat), EUn U (U n).
  Proof.
    intros U n.
    unfold EUn.
    exists n.
    reflexivity.
  Qed.

  Lemma Un_bound_imp :
    forall (U : nat -> R)  (x:R), (forall n:nat, U n <= x) -> is_upper_bound (EUn U) x.
  Proof.
    intros U x H.
    unfold is_upper_bound.
    intros xn [n eq].
    subst xn.
    apply H.
  Qed.

  Lemma growing_prop :
    forall (U : nat -> R) (n m:nat), Un_growing U -> (n >= m)%nat -> U n >= U m.
  Proof.
    intros U n m hu hnm.
    unfold ge in hnm. apply Rle_ge.
    induction hnm as [ | n hmn i ].
    { right. reflexivity. }
    {
      unfold Un_growing in hu.
      apply Rle_trans with (U n).
      { exact i. }
      { apply hu. }
    }
  Qed.

  Remark Hi2pn: forall n, 0 < (/ 2)^n.
  Proof.
    intros n.
    apply pow_lt.
    apply Rinv_0_lt_compat.
    apply IZR_lt.
    constructor.
  Qed.

  Definition Un_partial (u u':nat->R) := forall n, u n = 0 \/ u n = u' n.

  Definition pos (u:nat->R) := forall n, 0 <= u n.

  Lemma posn : forall u n, pos u -> 0 <= u n.
  Proof.
    intros u n hpos.
    apply hpos.
  Qed.

  Lemma pos_partial : forall u u', pos u' -> Un_partial u u' -> pos u.
  Proof.
    intros u u' hpo hpa.
    unfold pos in hpo.
    unfold Un_partial in hpa.
    unfold pos.
    intro n.
    destruct (hpa n) as [ h | h ].
    rewrite h. right. reflexivity.
    rewrite h. apply hpo.
  Qed.

  Lemma partial_le : forall u u' n, Un_partial u u' -> pos u' -> u n <= u' n.
  Proof.
    intros u u' n h hp.
    unfold Un_partial in h.
    destruct (h n) as [ h' | h' ].
    { rewrite h'. apply hp. }
    { rewrite h'. right. reflexivity. }
  Qed.


  Definition u_half_pow (n:nat) := (/ 2)^n.

  Lemma u_half_pow_pos : pos u_half_pow.
  Proof.
    unfold pos.
    intro n.
    unfold u_half_pow.
    apply pow_le.
    left.
    exact Rlt_0_half.
  Qed.

  Fixpoint serie(u:nat->R) (n:nat) := match n with
  | O => 0
  | S n' => u n + (serie u n')
  end.

  Definition s_half_pow := serie u_half_pow.

  Lemma serie_Sn : forall u n, (serie u) (S n) = serie u n + u (S n).
  Proof.
    intros u n.
    simpl.
    rewrite Rplus_comm.
    reflexivity.
  Qed.

  Lemma s_partial_le : forall u u' n, Un_partial u u' -> pos u' -> serie u n <= serie u' n.
  Proof.
    intros u u' n h hp.
    unfold Un_partial in h.
    induction n as [ | n i ].
    {
      simpl. right. reflexivity.
    }
    {
      destruct (h (S n)) as [ h' | h' ].
      {
        rewrite serie_Sn.
        rewrite serie_Sn.
        rewrite h'.
        apply Rplus_le_compat.
        { exact i. }
        { apply hp. }
      }
      {
        rewrite serie_Sn.
        rewrite serie_Sn.
        rewrite h'.
        apply Rplus_le_compat_r.
        exact i.
      }
    }
  Qed.

  Lemma growing_s_half_pow : Un_growing s_half_pow.
  Proof.
    unfold Un_growing.
    intro n.
    unfold s_half_pow.
    simpl.
    apply Rplus_le_compat_0_r.
    unfold u_half_pow.
    apply pow_le.
    left.
    exact Rlt_0_half.
  Qed.

  Lemma s_half_pow_pos : forall n,  0 <= s_half_pow n.
  Proof.
    intro n.
    unfold s_half_pow.
    induction n as [ | n i ].
    { simpl. right. reflexivity. }
    {
      simpl.
      apply Rle_trans with (serie u_half_pow n).
      { exact i. }
      {
        apply Rplus_le_compat_0_r.
        unfold u_half_pow.
        apply pow_le.
        left.
        exact Rlt_0_half.
      }
    }
  Qed.

  Lemma s_half_pow_le_n : forall n,  s_half_pow n <= 1 - (/ 2) ^ n.
  Proof.
    intro n.
    unfold s_half_pow.
    induction n as [ | n i ].
    {
      simpl.
      rewrite Rminus_diag.
      right.
      reflexivity.
    }
    {
      simpl.
      unfold u_half_pow at 1. 
      apply Rplus_le_compat_l_minus.
      simpl.
      pose (hsn:=(/2)^n).
      fold hsn.
      fold hsn in i.
      unfold Rminus.
      rewrite Ropp_mult_distr_r.
      rewrite Rplus_assoc.
      rewrite <- Rmult_plus_distr_r.
      rewrite half_half.
      rewrite Rmult_1_l.
      fold (1-hsn).
      exact i.
    }
  Qed.

  Lemma s_half_pow_lt_1 : forall n,  s_half_pow n < 1.
  Proof.
    intro n.
    apply Rle_lt_trans with (1 - (/2)^n).
    { apply s_half_pow_le_n. }
    {
      unfold Rminus.
      apply Rplus_lt_compat_l_minus.
      rewrite Rminus_diag.
      rewrite <- Ropp_0.
      apply Ropp_lt_contravar.
      apply pow_lt.
      exact Rlt_0_half.
    }
  Qed.

  Lemma growing_s_half_pow_partial : forall u, Un_partial u u_half_pow -> Un_growing (serie u).
  Proof.
    intros u h.
    unfold Un_growing.
    unfold Un_partial in h.
    intro n;destruct n as [ | n ].
    {
      simpl.
      rewrite Rplus_0_r.
      destruct (h 1%nat) as [ h' | h' ].
      { rewrite h'. right. reflexivity. }
      { rewrite h'. unfold u_half_pow. simpl. rewrite Rmult_1_r. left. exact Rlt_0_half. }
    }
    {
      simpl.
      rewrite <- Rplus_assoc.
      rewrite (Rplus_comm _ (u (S n))).
      rewrite Rplus_assoc.
      apply Rplus_le_compat_l.
      apply Rplus_le_compat_0_r.
      destruct (h (S (S n))) as [ h' | h' ].
      { rewrite h'. right. reflexivity. }
      { rewrite h'. unfold u_half_pow. apply pow_le. left. exact Rlt_0_half. }
    }
  Qed.

  Lemma s_half_pow_pos_partial : forall u, Un_partial u u_half_pow ->
    forall n,  0 <= (serie u) n.
  Proof.
    intros u h n.
    unfold Un_partial in h.
    induction n as [ | n i ].
    { simpl. right. reflexivity. }
    { simpl. apply Rle_trans with (serie u n).
      { exact i. }
      { apply Rplus_le_compat_0_r. destruct (h (S n)) as [ h' | h' ].
        { rewrite h'. right. reflexivity. }
        { rewrite h'. unfold u_half_pow. apply pow_le. left. exact Rlt_0_half. }
      }
    }
  Qed.

  Lemma s_half_pow_le_n_partial : forall u, Un_partial u u_half_pow ->
    forall n,  (serie u) n <= 1 - (/ 2) ^ n.
  Proof.
    intros u h n.
    unfold Un_partial in h.
    induction n as [ | n i ].
    { simpl. rewrite Rminus_diag. right. reflexivity. }
    { simpl. destruct (h (S n)) as [ h' | h' ].
      { rewrite h'. rewrite Rplus_0_l. apply Rle_trans with (1 - (/ 2) ^ n).
        { exact i. }
        { unfold Rminus. apply Rplus_le_compat_l. apply Ropp_le_contravar.
          pattern ( (/ 2) ^ n) at 2;rewrite <- Rmult_1_l.
          apply Rmult_le_compat_r.
          apply pow_le. left. exact Rlt_0_half.
          left. exact Rlt_half_1.
        }
      }
      {
        rewrite h'. clear h'.
        apply Rplus_le_compat_l_minus.
        apply Rle_trans with (1 - (/ 2) ^ n).
        { exact i. }
        {
          unfold Rminus.
          rewrite Rplus_assoc.
          apply Rplus_le_compat_l.
          unfold u_half_pow.
          simpl.
          rewrite Ropp_mult_distr_r.
          rewrite <- Rmult_plus_distr_r.
          rewrite half_half.
          rewrite Rmult_1_l.
          right. reflexivity.
        }
      }
    }
  Qed.



  Lemma s_half_pow_lt_1_partial : forall u, Un_partial u u_half_pow ->
    forall n,  (serie u) n <= 1.
  Proof.
    intros u h n.
    apply Rle_trans with (1 - (/2)^n).
    { apply s_half_pow_le_n_partial. exact h. }
    {
      unfold Rminus.
      apply Rplus_le_compat_l_minus.
      rewrite Rminus_diag.
      rewrite <- Ropp_0.
      apply Ropp_le_contravar.
      apply pow_le.
      left.
      exact Rlt_0_half.
    }
  Qed.

  Definition crit_test (u : nat->R ) (l e : R) (n:nat) := if Rle_lt_dec (u n) (l - e) then false else true.

  Fixpoint crit (u : nat->R ) (l e : R) (n:nat) := match n with
    | O => 0
    | S n' => if crit_test u l e n' then (/ 2)^n else 0
    end.

  Lemma crit_partial : forall u l e, Un_partial (crit u l e) u_half_pow.
  Proof.
    intros u l e n.
    destruct n.
    { simpl. left. reflexivity. }
    { simpl. destruct (crit_test u l e n).
      { right. unfold u_half_pow. simpl. reflexivity. }
      { left. reflexivity. }
    }
  Qed.

  Lemma crit_rewrite_l : forall u l e n,
      u n <= l - e -> crit u l e (S n) = 0.
  Proof.
    intros u l e n h.
    simpl.
    unfold crit_test.
    destruct (Rle_lt_dec (u n) (l-e)).
    { reflexivity. }
    { exfalso. eapply Rlt_irrefl_le. exact r. exact h. }
  Qed.

  Lemma crit_rewrite_r : forall u l e n,
      l - e < u n  -> crit u l e (S n) = (/ 2)^(S n).
  Proof.
    intros u l e n h.
    simpl.
    unfold crit_test.
    destruct (Rle_lt_dec (u n) (l-e)).
    { exfalso. eapply Rlt_irrefl_le. exact h. exact r. }
    { reflexivity. }
  Qed.



  Definition s_crit u l e := serie (crit u l e).

  Lemma crit_bound_l : forall (u : nat -> R) (l e : R) (m n : nat),
    s_crit u l e m <= s_crit u l e (m + n).
  Proof.
    intros u l e m.
    induction n as [ | n i ].
    {
      rewrite<- plus_n_O.
      right.
      reflexivity.
    }
    {
      rewrite <- plus_n_Sm.
      apply Rle_trans with (s_crit u l e (m + n)).
      { exact i. }
      {
        clear i.
        unfold s_crit at 2.
        rewrite serie_Sn.
        apply Rplus_le_compat_0_l.
        apply posn.
        apply pos_partial with u_half_pow.
        { exact u_half_pow_pos. }
        { apply crit_partial. }
      }
    }
  Qed.

  Lemma crit_bound_r : forall (u : nat -> R) (l e : R) (m n : nat),
    s_crit u l e (m + n) <= s_crit u l e m + (/ 2) ^ m - (/ 2) ^ (m + n).
  Proof.
    intros u l e m n.
    induction n as [ | n i ].
    {
      rewrite<- plus_n_O.
      unfold Rminus.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_r.
      right.
      reflexivity.
    }
    {
      rewrite <- plus_n_Sm.
      simpl.
      {
        unfold s_crit at 1.
        rewrite serie_Sn.
        apply Rplus_le_compat_r_minus.
        apply Rle_trans with (s_crit u l e m + (/ 2) ^ m - (/ 2) ^ (m + n)).
        { exact i. }
        {
          clear i.
          unfold Rminus.
          repeat (rewrite Rplus_assoc).
          apply Rplus_le_compat_l.
          apply Rplus_le_compat_l.
          rewrite <- Ropp_plus_distr.
          apply Ropp_le_contravar.
          apply Rplus_le_compat_l_minus.
          pose (p:=(/ 2)^(m+n)).
          fold p.
          unfold Rminus.
          pattern p at 1;rewrite <- Rmult_1_l.
          rewrite Ropp_mult_distr_l.
          rewrite <- Rmult_plus_distr_r.
          rewrite <- half_half.
          rewrite Rplus_assoc.
          rewrite Rplus_opp_r.
          rewrite Rplus_0_r.
          unfold p.
          rewrite tech_pow_Rmult.
          fold (u_half_pow (S (m+n))).
          apply partial_le.
          { apply crit_partial. }
          { apply u_half_pow_pos. }
        }
      }
    }
  Qed.

  Lemma s_crit_pos : forall u l e n, 0 <= s_crit u l e n.
  Proof.
    intros u l e n.
    specialize (crit_bound_l u l e 0 n);intro h.
    simpl in h.
    unfold s_crit at 1 in h.
    simpl in h.
    exact h.
  Qed.

  Lemma crit_bound_O_r : forall u l e n, s_crit u l e n <= 1 - (/2)^n.
  Proof.
    intros u l e n.
    specialize (crit_bound_r u l e 0 n);intro h.
    simpl in h.
    unfold s_crit at 2 in h.
    simpl in h.
    rewrite Rplus_0_l in h.
    exact h.
  Qed.

  Definition crit_exist u l e x := exists n : nat, s_crit u l e n  = x.

  Lemma crit_technic_3 : forall (u : nat -> R) (l e : R),
    is_upper_bound (crit_exist u l e) 0 ->
    forall n : nat, s_crit u l e n = 0.
  Proof.
    intros u l e h n.
    unfold is_upper_bound in h.
    apply Rle_antisym.
    { apply h. unfold crit_exist. exists n. reflexivity. }
    { apply s_crit_pos. }
  Qed.

  Lemma crit_0 : forall u l e n,  crit u l e (S n) = 0 -> u n <= l - e.
  Proof.
    intros u l e n h.
    simpl in h.
    unfold crit_test in h.
    destruct (Rle_lt_dec (u n) (l - e)).
    { assumption. }
    {
      exfalso. apply Rlt_irrefl with 0.
      pattern 0 at 2;rewrite <- h.
      rewrite tech_pow_Rmult.
      apply pow_lt.
      exact Rlt_0_half.
    }
  Qed.

  Lemma crit_0_inv : forall u l e n,  u n <= l - e -> crit u l e (S n) = 0.
  Proof.
    intros u l e n h.
    simpl.
    unfold crit_test.
    destruct (Rle_lt_dec (u n) (l - e)).
    { reflexivity. }
    { exfalso. eapply Rlt_irrefl_le. exact r. exact h. }
  Qed.

  Lemma crit_technic_1 : forall (u : nat -> R) (l e : R),
    (forall n : nat, s_crit u l e n = 0) ->
    forall n : nat, u n <= l - e.
  Proof.
    intros u l e h n.
    induction n as [ | n i ].
    {
      specialize (h 1%nat).
      unfold s_crit in h.
      unfold serie in h.
      rewrite Rplus_0_r in h.
      apply crit_0 in h.
      exact h.
    }
    {
      generalize h;intro hsn;specialize (hsn (S n)).
      generalize h;intro hssn;specialize (hssn (S (S n))).
      unfold s_crit in hssn.
      rewrite serie_Sn in hssn.
      fold (s_crit u l e (S n)) in hssn.
      rewrite hsn in hssn.
      rewrite Rplus_0_l in hssn.
      apply crit_0 in hssn.
      exact hssn.
    }
  Qed.

  Lemma crit_lesn_len: forall (u : nat -> R) (l e : R),
    Un_growing u ->
    forall N : nat, u (S N) <= l - e ->
    u N <= l - e.
  Proof.
    intros u l e hu.
    intros n hn.
    unfold Un_growing in hu.
    apply Rle_trans with (u (S n)).
    - apply hu.
    - assumption.
  Qed.


  Lemma Rlt_abs_half_1 : Rabs (/2) < 1.
  Proof.
    rewrite Rabs_pos_eq.
    - apply Rlt_half_1.
    - left.
      apply Rlt_0_half.
  Qed.

  Lemma scrit_le_0 : forall (u : nat -> R) (l e : R) (N:nat),
    Un_growing u ->
    u N <= l - e ->
    s_crit u l e N = 0.
  Proof.
      intros.
      induction N as [ | N i ].
      { unfold s_crit. simpl. reflexivity. }
      {
        simpl.
        unfold s_crit.
        rewrite serie_Sn.
        fold (s_crit u l e N).
        rewrite i.
        {
          rewrite Rplus_0_l.
          apply crit_0_inv.
          apply crit_lesn_len.
          { exact H. }
          { exact H0. }
        }
        {
          apply Rle_trans with (u (S N)).
          { apply H. }
          { exact H0. }
        }
      }
  Qed.

  Lemma crit_bounded : forall u l e, bound (crit_exist u l e).
  Proof.
    intros u l e.
    unfold bound.
    exists 1.
    unfold is_upper_bound.
    intros x h.
    unfold crit_exist in h.
    destruct h as [n h].
    rewrite <- h;clear h.
    apply s_half_pow_lt_1_partial.
    apply crit_partial.
  Qed.

  Lemma crit_before_0 : forall u l e N n,
    Un_growing u ->
    u N <= l - e -> (n <= N)%nat ->
    s_crit u l e n = 0.
  Proof.
    intros u l e N n hg hN hn.
    generalize dependent n.
    intro n;induction n as [ | n i ].
    {
      intros hn.
      unfold s_crit. simpl. reflexivity.
    }
    {
      intros hn.
      unfold s_crit.
      rewrite serie_Sn.
      fold (s_crit u l e n).
      rewrite i.
      {
        rewrite Rplus_0_l.
        apply crit_rewrite_l.
        apply Rle_trans with (u N).
        {
          apply Rge_le.
          apply growing_prop.
          { exact hg. }
          {
            unfold ge.
            apply le_trans with (S n).
            { constructor. constructor. }
            { exact hn. }
          }
        }
        { exact hN. }
      }
      apply le_trans with (S n).
      { constructor. constructor. }
      { exact hn. }
    }
  Qed.

  Lemma le_0_eq : (forall n, n <= 0 -> n = 0)%nat.
  Proof.
    intros n h.
    inversion h.
    subst n.
    reflexivity.
  Qed.

  (* (/ 2)^n can be made as small as we want *)
  Lemma small_half_pow : forall m : R, 0 < m -> exists n : nat, (/ 2) ^ n < m.
  Proof.
    generalize Rgen_half_power;intro rhp.
    intros m hm.
    specialize (rhp m hm).
    destruct rhp as [N h].
    destruct h as [ h | h ].
    { exists N. exact h. }
    {
      subst m.
      exists (S N).
      Search( (/ _)^_).
      rewrite <- Rinv_pow.
      2:exact Neq_2_0.
      rewrite <- Rinv_pow.
      2:exact Neq_2_0.
      apply Rinv_lt_contravar.
      1:{
        rewrite <- pow_add.
        apply pow_lt.
        exact Rlt_0_2.
      }
      apply Rlt_pow.
      1:{
        rewrite <- Rinv_involutive.
        2:{ exact Neq_2_0. }
        rewrite <- Rinv_1.
        apply Rinv_lt_contravar.
        1:{ rewrite Rmult_1_r. exact Rlt_0_half. }
        { exact Rlt_half_1. }
      }
      { unfold lt. constructor. }
    }
  Qed.

  Lemma fill_n : (forall n N, n < N -> exists n', n + n' = N)%nat.
  Proof.
    intros n N h.
    generalize dependent n.
    induction n as [ | n i ].
    {
      intro h.
      simpl.
      exists N.
      reflexivity.
    }
    {
      intros h.
      destruct i as [ n' h' ].
      {
        apply lt_trans with (S n).
        { unfold lt. constructor. }
        { exact h. }
      }
      {
        destruct n'.
        {
          rewrite plus_comm in h'.
          simpl in h'.
          subst N.
          exfalso.
          apply lt_irrefl with n.
          apply lt_trans with (S n).
          { unfold lt. constructor. }
          { exact h. }
        }
        {
          exists n'.
          subst N.
          rewrite <- plus_n_Sm.
          rewrite plus_Sn_m.
          reflexivity.
        }
      }
    }
  Qed.

  (* This proof shows that for any positive m and increasing sequence u, if (/2)^n is smaller than m and
     u n is small enough for crit_exist, then (/2)^n is an upper bound of crit_exist. *)
  Lemma crit_technic_d : forall (u : nat -> R) (l e m : R) (n : nat),
    0 < m ->
    Un_growing u ->
    (/ 2) ^ n < m ->
    u n <= l - e ->
    is_upper_bound (crit_exist u l e) ((/ 2) ^ n).
  Proof.
    intros u l e m n hm hu hn hun.

    (* Goal : (/2)^n is an upper bound of crit_exist *)

    unfold is_upper_bound.
    (* This means that any x satisfying crit_exist is smaller than (/2)^n *) 
    intros x hcrit.
    (* Let x be such that it satisfies crit_exist. Then there is n such that s_crit u l e n = x *)
    destruct hcrit as [ncrit heq].
    subst x.
    (* Because u n <= l - e and u is increasing, s_crit u l e n = 0 *)
    assert (scrit_n_0:s_crit u l e n = 0).
    { apply scrit_le_0. exact hu. exact hun. }
    clear hun.
    
    (* ncrit can be after or before n *)
    destruct (le_or_lt n ncrit) as [hnn|hnn].
    { (* here, ncrit is after n *)
      apply le_lt_or_eq in hnn.
      destruct hnn.
      {
        apply fill_n in H.
        destruct H.
        subst ncrit.
        apply Rle_trans with (s_crit u l e n + (/ 2) ^ n - (/ 2) ^ (n + x)).
        { apply crit_bound_r. }
        {
          rewrite scrit_n_0.
          rewrite Rplus_0_l.
          pattern ((/ 2)^n) at 2;rewrite <- Rplus_0_r.
          apply Rplus_le_compat_l.
          rewrite <- Ropp_0.
          apply Ropp_le_contravar.
          apply pow_le.
          left.
          exact Rlt_0_half.
        }
      }
      {
        subst ncrit.
        rewrite scrit_n_0.
        apply pow_le.
        left.
        exact Rlt_0_half.
      }
    }
    { (* ncrit is before n *)
      (* We go from ncrit to n, then from n to (/2)^n *)
      apply Rle_trans with (s_crit u l e n).
      {
        (* Here, we apply a property of s_crit, which is equivalent to stating that s_crit is increasing *)
        (* We could also prove that because s_crit u l e n = 0 and ncrit < n, then s_crit u l e ncrit = 0 *)
        (* This would be more intuitive *)
        apply fill_n in hnn.
        destruct hnn as [ n' heq ].
        subst n.
        apply crit_bound_l.
      }
      {
        (* 0 <= / 2 *)
        rewrite scrit_n_0.
        apply pow_le.
        left.
        exact Rlt_0_half.
      }
    }
  Qed.

  (* If m is a positive least upper bound of crit_exist and u is increasing, there is N such that u N > l - e *)
  Lemma crit_technic_c : forall (u : nat -> R) (l e m : R),
    Un_growing u ->
    0 < m ->
    is_lub (crit_exist u l e) m ->
    exists N : nat, u N > l - e.
  Proof.
    intros u l e m hu hm hlub.

    (* Because m is positive, we can find N such that (/ 2)^N < m.
       We don't need any hypothesis on crit_exist for that
     *)
    destruct (small_half_pow m) as [N H4].
    { exact hm. }
    exists N.

    unfold is_lub in hlub.
    apply proj2 in hlub.
    (* We will show that (/2)^N is an upper bound of crit_exist *)
    specialize (hlub ((/ 2)^N)).

    (* If x < y, then it is not the case that y <= x *)
    apply Rnot_le_lt.
    (* Therefore, we can assume that if x <= y, we get a contradiction *)
    intro h.
    (* Now, if we have x < y in the hypothesis and we need a contradiction, we can try to prove y <= x *)
    eapply Rlt_not_le.
    exact H4.

    apply hlub.
    (* The actual proof that (/2)^N is an upper bound of crit_exist is done in crit_technic_d. *)
    eapply crit_technic_d.
    exact hm.
    exact hu.
    exact H4.
    exact h.
  Qed.

  (* This lemma show that there is a least upper bound of fcrit1 *)
  Lemma lub_of_crit_exist : forall u l e, exists x, is_lub (crit_exist u l e) x.
  Proof.
    intros u l e.
    (* Here, we don't really construct the least upper bound *)
    (* Instead, we use the completeness axiom which states that if fcrit1 is bounded and satisfied for
       at least one number, then the least upper bound exists *)
    apply ex_ex.
    apply completeness.
    { apply crit_bounded. }
    {
      exists 0.
      unfold crit_exist.
      exists 0%nat.
      constructor.
    }
  Qed.

  Lemma crit_flat : forall u l e, is_upper_bound (crit_exist u l e) 0 -> forall n, s_crit u l e n = 0.
  Proof.
    intros u l e h n.
    unfold is_upper_bound in h.
    apply Rle_antisym.
    { apply h. exists n. reflexivity. }
    { apply s_crit_pos. }
  Qed.

  Lemma crit_lub_pos : forall u l e m,
    is_lub (EUn u) l ->
    e > 0 ->
    is_lub (crit_exist u l e) m ->
    m > 0.
  Proof.
    intros u l e m hlub he h.
    destruct h as [hl hr].
    destruct (Rtotal_order m 0) as [ hm | [ hm | hm ] ].
    { (* m < 0 *)
      exfalso.
      unfold is_upper_bound in hl.
      apply Rlt_not_le in hm.
      apply hm.
      apply hl.
      exists 0%nat.
      unfold s_crit.
      simpl.
      reflexivity.
    }
    { (* m = 0 *)
      subst m.
      exfalso.
      unfold is_lub in hlub.
      destruct hlub as [hlubl hlubr].
      specialize (hlubr (l-e)).
      apply (Rle_not_lt (l-e) l).
      2:{
        pattern l at 2;rewrite <- Rplus_0_r.
        unfold Rminus.
        apply Rplus_lt_compat_l.
        rewrite <- Ropp_0.
        apply Ropp_lt_contravar.
        apply Rgt_lt in he.
        exact he.
      }
      {
        apply hlubr.
        intros x hex.
        destruct hex as [n eq].
        subst x.
        apply crit_technic_1.
        intro n'.
        apply crit_flat.
        exact hl.
      }
    }
    { exact hm. }
  Qed.

  Lemma Un_cv_crit_lub : forall (U : nat -> R) (l:R), Un_growing U -> is_lub (EUn U) l -> Un_cv U l.
  Proof.
    intros u l hu hul.
    unfold Un_cv.
    intros e he.
    unfold R_dist.

    (* crit_exist has a least upper bound *)
    destruct (lub_of_crit_exist u l e) as [ m hlub].

    (* Given an increasing sequence u and a least upper bound of crit_exist,
        there's a N such that u N > l - e *)
    destruct (crit_technic_c u l e m) as [ N hun ].
    { exact hu. }
    { eapply crit_lub_pos. apply hul. apply he. apply hlub. }
    { exact hlub. }

    (* We just need to show that this N satisfies the goal *)

    exists N.
    intros n hnN.
    unfold R_dist.
    rewrite Rabs_left1.
    2:{
      unfold Rminus.
      apply Rplus_le_reg_r with l.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_l.
      rewrite Rplus_0_r.
      unfold is_lub in hul.
      apply proj1 in hul.
      unfold is_upper_bound in hul.
      apply hul.
      apply Un_in_EUn.
    }
    {
      apply Rgt_lt in hun.
      rewrite Ropp_minus_distr.
      apply Rplus_lt_reg_l with (-e).
      unfold Rminus.
      rewrite <- Rplus_assoc.
      rewrite (Rplus_comm (-e)).
      rewrite Rplus_opp_l.
      apply Rplus_lt_reg_r with (u n).
      rewrite Rplus_0_l.
      rewrite Rplus_assoc.
      rewrite Rplus_opp_l.
      rewrite Rplus_0_r.
      unfold Rminus in hun.
      apply Rlt_le_trans with (u N).
      { assumption. }
      {
        apply Rge_le.
        apply growing_prop.
        { assumption. }
        { assumption. }
      }
    }
  Qed.

  Lemma Un_cv_crit : forall u, Un_growing u -> bound (EUn u) ->  exists l : R, Un_cv u l.
  Proof.
    intros u hg hbound.
    destruct (completeness (EUn u)) as [x hlub].
    { exact hbound. }
    { exists (u 0%nat). unfold EUn. exists 0%nat. reflexivity. }
    exists x.
    apply Un_cv_crit_lub.
    { exact hg. }
    { exact hlub. }
  Qed.

  Lemma finite_greater :
    forall (u:nat->R) (N:nat),  exists M : R, (forall n:nat, (n <= N)%nat -> u n <= M).
  Proof.
    intros u N.
    induction N as [ | N i ].
    {
      exists (u 0%nat).
      intros n hn.
      inversion hn. subst n.
      right. reflexivity.
    }
    {
      destruct i as [M h].
      exists (Rmax M (u (S N))).
      intros n hn.
      apply le_lt_or_eq in hn.
      destruct hn as [ hn | hn ].
      { apply Rle_trans with M.
        apply h. unfold lt in hn. apply le_S_n in hn. exact hn.
        apply Rmax_l.
      }
      { subst n. apply Rmax_r. }
    }
  Qed.

  Lemma cauchy_bound : forall u, Cauchy_crit u -> bound (EUn u).
  Proof.
    intro u.
    unfold Cauchy_crit, bound. intros. unfold is_upper_bound.
      unfold Rgt in H. elim (H 1 Rlt_0_1). clear H. intros.
        generalize (H x). intro. generalize (le_dec x). intro.
          elim (finite_greater u x). intros. split with (Rmax x0 (u x + 1)).
            clear H. intros. unfold EUn in H. elim H. clear H.
              intros.
    elim (H1 x2).
    clear H1.
    intro y.
    unfold ge in H0; generalize (H0 x2 (le_n x) y); clear H0; intro;
      rewrite <- H in H0; unfold R_dist in H0; elim (Rabs_def2 (u x - x1) 1 H0);
        clear H0; intros; elim (Rmax_Rle x0 (u x + 1) x1);
          intros; apply H4; clear H3 H4; right; clear H H0 y;
            apply (Rlt_le x1 (u x + 1)); generalize (Rlt_minus (-1) (u x - x1) H1);
              clear H1; intro; apply (Rminus_lt x1 (u x + 1));
                cut (-1 - (u x - x1) = x1 - (u x + 1));
                  [ intro; rewrite H0 in H; assumption | ring ].
    clear H1.
    intro y.
    generalize (H2 x2 y); clear H2 H0; intro; rewrite <- H in H0;
      elim (Rmax_Rle x0 (u x + 1) x1); intros; clear H1;
        apply H2; left; assumption.
  Qed.

End sequence.

(*****************************************************************)
(**  *       Definition of Power Series and properties           *)
(*                                                               *)
(*****************************************************************)

Section Isequence.

(*********)
  Variable An : nat -> R.

(*********)
  Definition Pser (x l:R) : Prop := infinite_sum (fun n:nat => An n * x ^ n) l.

End Isequence.

Lemma GP_infinite :
  forall x:R, Rabs x < 1 -> Pser (fun n:nat => 1) x (/ (1 - x)).
Proof.
  intros; unfold Pser; unfold infinite_sum; intros;
    elim (Req_dec x 0).
  intros; exists 0%nat; intros; rewrite H1; rewrite Rminus_0_r; rewrite Rinv_1;
    cut (sum_f_R0 (fun n0:nat => 1 * 0 ^ n0) n = 1).
  intros; rewrite H3; rewrite R_dist_eq; auto.
  elim n; simpl.
  ring.
  intros; rewrite H3; ring.
  intro; cut (0 < eps * (Rabs (1 - x) * Rabs (/ x))).
  intro; elim (pow_lt_1_zero x H (eps * (Rabs (1 - x) * Rabs (/ x))) H2);
    intro N; intros; exists N; intros;
      cut
        (sum_f_R0 (fun n0:nat => 1 * x ^ n0) n = sum_f_R0 (fun n0:nat => x ^ n0) n).
  intros; rewrite H5;
    apply
      (Rmult_lt_reg_l (Rabs (1 - x))
        (R_dist (sum_f_R0 (fun n0:nat => x ^ n0) n) (/ (1 - x))) eps).
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  unfold R_dist; rewrite <- Rabs_mult.
  rewrite Rmult_minus_distr_l.
  cut
    ((1 - x) * sum_f_R0 (fun n0:nat => x ^ n0) n =
      - (sum_f_R0 (fun n0:nat => x ^ n0) n * (x - 1))).
  intro; rewrite H6.
  rewrite GP_finite.
  rewrite Rinv_r.
  cut (- (x ^ (n + 1) - 1) - 1 = - x ^ (n + 1)).
  intro; rewrite H7.
  rewrite Rabs_Ropp; cut ((n + 1)%nat = S n); auto.
  intro H8; rewrite H8; simpl; rewrite Rabs_mult;
    apply
      (Rlt_le_trans (Rabs x * Rabs (x ^ n))
        (Rabs x * (eps * (Rabs (1 - x) * Rabs (/ x)))) (
          Rabs (1 - x) * eps)).
  apply Rmult_lt_compat_l.
  apply Rabs_pos_lt.
  assumption.
  auto.
  cut
    (Rabs x * (eps * (Rabs (1 - x) * Rabs (/ x))) =
      Rabs x * Rabs (/ x) * (eps * Rabs (1 - x))).
  clear H8; intros; rewrite H8; rewrite <- Rabs_mult; rewrite Rinv_r.
  rewrite Rabs_R1; cut (1 * (eps * Rabs (1 - x)) = Rabs (1 - x) * eps).
  intros; rewrite H9; unfold Rle; right; reflexivity.
  ring.
  assumption.
  ring.
  ring.
  ring.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  ring; ring.
  elim n; simpl.
  ring.
  intros; rewrite H5.
  ring.
  apply Rmult_lt_0_compat.
  auto.
  apply Rmult_lt_0_compat.
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  apply Rlt_dichotomy_converse.
  right; unfold Rgt.
  apply (Rle_lt_trans x (Rabs x) 1).
  apply RRle_abs.
  assumption.
  apply Rabs_pos_lt.
  apply Rinv_neq_0_compat.
  assumption.
Qed.

(* Convergence is preserved after shifting the indices. *)
Lemma CV_shift : 
  forall f k l, Un_cv (fun n => f (n + k)%nat) l -> Un_cv f l.
intros f' k l cvfk eps ep; destruct (cvfk eps ep) as [N Pn].
exists (N + k)%nat; intros n nN; assert (tmp: (n = (n - k) + k)%nat).
 rewrite Nat.sub_add;[ | apply le_trans with (N + k)%nat]; auto with arith.
rewrite tmp; apply Pn; apply Nat.le_add_le_sub_r; assumption.
Qed.

Lemma CV_shift' : 
  forall f k l, Un_cv f l -> Un_cv (fun n => f (n + k)%nat) l.
intros f' k l cvf eps ep; destruct (cvf eps ep) as [N Pn].
exists N; intros n nN; apply Pn; auto with arith.
Qed.

(* Growing property is preserved after shifting the indices (one way only) *)

Lemma Un_growing_shift : 
   forall k un, Un_growing un -> Un_growing (fun n => un (n + k)%nat).
Proof.
intros k un P n; apply P.
Qed.
