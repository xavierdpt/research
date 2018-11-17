Require Import Rbase.
Require Import Rfunctions.
Require Import Rseries.
Require Import Max.
Require Import Omega.
Local Open Scope R_scope.

Definition Un_decreasing (u:nat -> R) : Prop :=
  forall n:nat, u (S n) <= u n.

Definition opp_seq (u:nat -> R) (n:nat) : R := - u n.

Definition has_ub (u:nat -> R) : Prop := bound (EUn u).

Definition has_lb (u:nat -> R) : Prop := bound (EUn (opp_seq u)).

Lemma exists_lub : forall (u:nat->R), bound (EUn u) -> { l | is_lub (EUn u) l }.
Proof.
  intros u hb.
  apply completeness.
  { exact hb. }
  { apply EUn_noempty. }
Qed.

Lemma growing_cv :
  forall u:nat -> R, Un_growing u -> has_ub u -> { l:R | Un_cv u l }.
Proof.
  intros u hg hub.
  unfold has_ub in hub.
  destruct (exists_lub u) as [l hlub].
  { exact hub. }
  {
    exists l.
    apply Un_cv_crit_lub.
    { exact hg. }
    { exact hlub. }
  }
Qed.

Lemma decreasing_growing :
  forall u:nat -> R, Un_decreasing u -> Un_growing (opp_seq u).
Proof.
  intros u hdec.
  unfold Un_decreasing in hdec.
  unfold Un_growing.
  intro n.
  specialize (hdec n).
  unfold opp_seq.
  apply Ropp_le_contravar.
  exact hdec.
Qed.

Lemma decreasing_cv :
  forall u:nat -> R, Un_decreasing u -> has_lb u -> { l:R | Un_cv u l }.
Proof.

  intros u hdec hlb.
  unfold has_lb in hlb.
  
  generalize completeness;intro hc.
  specialize (hc (EUn (opp_seq u))).
  specialize (hc hlb);clear hlb.
  specialize (hc (EUn_noempty (opp_seq u))).
  destruct hc as [l hlub].

  exists (-l).

  generalize Un_cv_crit_lub;intro h.
  specialize (h (opp_seq u)).
  apply decreasing_growing in hdec.
  specialize (h hdec);clear hdec.
  specialize (h l).
  specialize (h hlub);clear hlub.

  unfold Un_cv.
  intros e he.

  unfold Un_cv in h.
  specialize (h e he).

  destruct h as [N h].
  exists N.

  intros n hnn.
  specialize (h n hnn);clear hnn.

  unfold opp_seq in h.
  unfold R_dist in h.
  unfold Rminus in h.
  rewrite <- Ropp_plus_distr in h.
  rewrite Rabs_Ropp in h.

  unfold R_dist.
  unfold Rminus.
  rewrite Ropp_involutive.

  exact h.
Qed.

Lemma ub_to_lub :
  forall u:nat -> R, has_ub u -> { l:R | is_lub (EUn u) l }.
Proof.
  intros u h.
  unfold has_ub in h.
  apply completeness.
  { exact h. }
  { apply EUn_noempty. }
Qed.

Lemma lb_to_glb :
  forall u:nat -> R, has_lb u -> { l:R | is_lub (EUn (opp_seq u)) l }.
Proof.
  intros u h.
  unfold has_lb in h.
  apply completeness.
  { exact h. }
  { apply EUn_noempty. }
Qed.

Definition lub (Un:nat -> R) (pr:has_ub Un) : R :=
  let (a,_) := ub_to_lub Un pr in a.

Definition glb (Un:nat -> R) (pr:has_lb Un) : R :=
  let (a,_) := lb_to_glb Un pr in - a.

Notation maj_sup := ub_to_lub (only parsing).
Notation min_inf := lb_to_glb (only parsing).
Notation majorant := lub (only parsing).
Notation minorant := glb (only parsing).

Lemma maj_ss :
  forall (u:nat -> R) (k:nat),
    has_ub u -> has_ub (fun i:nat => u (k + i)%nat).
Proof.
  intros u k h.
  unfold has_ub.
  unfold has_ub in h.
  unfold bound in h.
  unfold bound.
  destruct h as [ M h ].
  exists M.
  unfold is_upper_bound.
  intros x hx.
  unfold is_upper_bound in h.
  apply h.
  unfold EUn in hx.
  destruct hx as [n eq].
  unfold EUn.
  exists (k+n)%nat.
  exact eq.
Qed.

Lemma min_ss :
  forall (u:nat -> R) (k:nat),
    has_lb u -> has_lb (fun i:nat => u (k + i)%nat).
Proof.
  intros u k.
  unfold has_lb.
  unfold bound.
  unfold is_upper_bound.
  unfold EUn.
  unfold opp_seq.
  intros [M h].
  exists M.
  intros x [n eq].
  apply h.
  exists (k+n)%nat.
  exact eq.
Qed.

Definition sequence_ub (Un:nat -> R) (pr:has_ub Un)
  (i:nat) : R := lub (fun k:nat => Un (i + k)%nat) (maj_ss Un i pr).

Definition sequence_lb (Un:nat -> R) (pr:has_lb Un)
  (i:nat) : R := glb (fun k:nat => Un (i + k)%nat) (min_ss Un i pr).

Notation sequence_majorant := sequence_ub (only parsing).
Notation sequence_minorant := sequence_lb (only parsing).

Lemma lub_is_lub : forall f hb, is_lub (EUn f) (lub f hb).
Proof.
  intros f hb.
  unfold lub.
  destruct (ub_to_lub f hb).
  exact i.
Qed.

Lemma lub_unique : forall p l1 l2, is_lub p l1 -> is_lub p l2 -> l1 = l2.
Proof.
  intros p l1 l2 hl1 hl2.
  destruct hl1 as [up1 min1].
  destruct hl2 as [up2 min2].
  apply Rle_antisym.
  {
    apply min1.
    exact up2.
  }
  {
    apply min2.
    exact up1.
  }
Qed.

Lemma Wn_decreasing :
  forall (Un:nat -> R) (pr:has_ub Un), Un_decreasing (sequence_ub Un pr).
Proof.
  intros Un u_has_ub.
  unfold Un_decreasing.
  intro n.
  unfold sequence_ub.

  (* Introduce variables to improve readability *)

  pose (f:=fun k:nat => Un (S n + k)%nat).
  fold f.

  pose (g:=fun k:nat => Un (n + k)%nat).
  fold g.

  pose (hbf := (maj_ss Un (S n) u_has_ub)).
  fold f in hbf.
  fold hbf.

  pose (hbg := (maj_ss Un n u_has_ub)).
  fold g in hbg.
  fold hbg.

  (* upper bound -> there's a least upper bound *)
  destruct (ub_to_lub f hbf) as [ lf hlubf].
  destruct (ub_to_lub g hbg) as [ lg hlubg].

  assert (eqf : lub f hbf = lf).
  {
    apply (lub_unique (EUn f)).
    - apply lub_is_lub.
    - exact hlubf.
  }

  assert (eqg : lub g hbg = lg).
  {
    apply (lub_unique (EUn g)).
    - apply lub_is_lub.
    - exact hlubg.
  }

  (* Now we can get rid of this lub _ _ thing and simplify even more *)
  rewrite eqf.
  rewrite eqg.
  clear eqf eqg hbf hbg u_has_ub.

  destruct hlubf as [lf_up lf_min];clear lf_up.
  destruct hlubg as [lg_up lg_min];clear lg_min.

  apply lf_min;clear lf_min.

  unfold is_upper_bound.
  intros ubf hubf.
  unfold is_upper_bound in lg_up.
  apply lg_up;clear lg_up.

  destruct hubf as [nubf heq].
  subst ubf.
  unfold EUn.
  unfold f.
  unfold g.

  exists (S nubf).

  rewrite plus_Sn_m.
  rewrite <- plus_n_Sm.

  reflexivity.

Qed.

Lemma Vn_growing :
  forall (Un:nat -> R) (pr:has_lb Un), Un_growing (sequence_lb Un pr).
Proof.

  intros u u_has_lb.
  unfold Un_growing.
  intro n.
  unfold sequence_lb.

  pose (f := fun k : nat => u (n + k)%nat).
  fold f.

  pose (g := fun k : nat => u (S n + k)%nat).
  fold g.

  pose (fss := min_ss u n u_has_lb).
  fold fss.

  pose (gss := min_ss u (S n) u_has_lb).
  fold gss.

  unfold glb.

  destruct (lb_to_glb f fss) as [lubf hlubf].
  destruct (lb_to_glb g gss) as [lubg hlubg].

  apply Ropp_le_contravar.

  destruct hlubf as [hubf hminf].
  destruct hlubg as [hubg hming].

  apply hming.

  unfold is_upper_bound.
  intros x hex.
  unfold EUn in hex.
  destruct hex as [nx heq].
  subst x.
  
  unfold is_upper_bound in hubf.
  apply hubf.

  unfold EUn.
  unfold opp_seq.
  unfold g.
  unfold f.
  exists (S nx).
  rewrite <- plus_n_Sm.
  rewrite plus_Sn_m.

  reflexivity.
Qed.

Lemma lub_opp_glb : forall (U:nat -> R) (hlb: has_lb U) (n:nat)
  (f:=(fun k:nat => U (n + k)%nat)),
  is_lub (EUn (opp_seq f)) (- glb f (min_ss U n hlb)).
Proof.
  intros U hlb n f.
  pose (hbf := (min_ss U n hlb)).
  fold hbf.
  unfold glb.
  destruct (lb_to_glb f hbf) as [ x0 i ].
  rewrite Ropp_involutive.
  exact i.
Qed.

Lemma Vn_Un_Wn_order :
  forall (U:nat -> R) (hub:has_ub U) (hlb:has_lb U)
    (n:nat), sequence_lb U hlb n <= U n <= sequence_ub U hub n.
Proof.
  intros U hub hlb n.

  unfold sequence_ub.
  unfold sequence_lb.

  pose (f := fun k:nat => U (n + k)%nat).
  fold f.

  pose (smin := min_ss U n hlb).
  fold f in smin.
  fold smin.

  pose (smaj := maj_ss U n hub).
  fold f in smaj.
  fold smaj.

  unfold glb.
  unfold lub.

  destruct (lb_to_glb f smin) as [ xmin imin].
  destruct (ub_to_lub f smaj) as [ xmaj imaj].

  destruct imin as [imin1 imin2].
  destruct imaj as [imaj1 imaj2].

  unfold is_upper_bound in imin1, imaj1.

  split.
  {
    apply Ropp_le_cancel.
    rewrite Ropp_involutive.
    apply imin1;clear imin1.
    unfold EUn.
    unfold opp_seq.
    unfold f.
    exists 0%nat.
    rewrite plus_comm.
    simpl.
    reflexivity.
  }
  {
    apply imaj1;clear imaj1.
    unfold EUn.
    unfold f.
    exists 0%nat.
    rewrite plus_comm.
    simpl.
    reflexivity.
  }
Qed.

Lemma min_maj :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_ub (sequence_lb Un pr2).
Proof.

  intros u hub hlb.

  unfold has_ub.
  unfold bound.

  generalize hub;intro hub'.
  unfold has_ub in hub'.
  unfold bound in hub'.
  destruct hub' as [xup hup].

  exists xup.
  unfold is_upper_bound.
  intros xn hn.

  destruct hn as [n heq].
  subst xn.

  apply Rle_trans with (u n).
  {
    apply Vn_Un_Wn_order.
    exact hub.
  }
  {
    unfold is_upper_bound in hup.
    apply hup.
    exists n.
    reflexivity.
  }
Qed.

Lemma maj_min :
  forall (Un:nat -> R) (pr1:has_ub Un) (pr2:has_lb Un),
    has_lb (sequence_ub Un pr1).
Proof.
  intros u hub hlb.
(*  assert (H := Vn_Un_Wn_order Un pr1 pr2). *)

  unfold has_lb.
  unfold bound.

  elim hlb; intros xlb hxlb.

  exists xlb.
  unfold is_upper_bound.
  intros x h.

  unfold is_upper_bound in hxlb.

  elim h; intros n heq.
  rewrite heq.

  apply Rle_trans with (opp_seq u n).
  {
    unfold opp_seq.
    apply Ropp_le_contravar.
    apply Vn_Un_Wn_order.
    exact hlb.
  }
  {
    apply hxlb.
    exists n.
    reflexivity.
  }
Qed.

Lemma cauchy_maj : forall Un:nat -> R, Cauchy_crit Un -> has_ub Un.
Proof.
  intros u h.
  unfold has_ub.
  generalize cauchy_bound;intro hcbound.
  apply cauchy_bound.
  exact h.
Qed.

Lemma cauchy_opp :
  forall Un:nat -> R, Cauchy_crit Un -> Cauchy_crit (opp_seq Un).
Proof.
  intros u h.
  unfold Cauchy_crit.
  intros e he.
  unfold Cauchy_crit in h.
  specialize (h e he).
  destruct h as [N h].
  exists N.
  intros n m hnn hnm.
  specialize (h n m hnn hnm).
  unfold R_dist in h.
  unfold R_dist.
  unfold opp_seq.
  unfold Rminus.
  rewrite <- Ropp_plus_distr.
  rewrite Rabs_Ropp.
  unfold Rminus in h.
  exact h.
Qed.

Lemma cauchy_min : forall Un:nat -> R, Cauchy_crit Un -> has_lb Un.
Proof.
  intros u h.
  unfold has_lb.
  apply cauchy_bound.
  apply cauchy_opp.
  exact h.
Qed.

Lemma maj_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    { l:R | Un_cv (sequence_ub Un (cauchy_maj Un pr)) l }.
Proof.
  intros u h.
  apply decreasing_cv.
  { apply Wn_decreasing. }
  {
    apply maj_min.
    apply cauchy_min.
    exact h.
  }
Qed.

Lemma min_cv :
  forall (Un:nat -> R) (pr:Cauchy_crit Un),
    { l:R | Un_cv (sequence_lb Un (cauchy_min Un pr)) l }.
Proof.
  intros u h.
  apply growing_cv.
  { apply Vn_growing. }
  {
    apply min_maj.
    apply cauchy_maj.
    exact h.
  }
Qed.

Lemma cond_eq_gt : forall x y:R, y < x -> (forall eps:R, 0 < eps -> Rabs (x - y) < eps) -> False.
Proof.
  intros x y hxy h.
  specialize (h (x - y)).
  apply Rlt_irrefl with (x-y).
  assert (hxy' : 0 < x - y).
  {
    unfold Rminus.
    apply Rplus_lt_reg_r with y.
    rewrite Rplus_0_l.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    exact hxy.
  }
  pattern (x-y) at 1; rewrite <- Rabs_right.
  {
    apply h.
    exact hxy'.
  }
  {
    left.
    apply Rlt_gt.
    exact hxy'.
  }
Qed.

Lemma cond_eq :
  forall x y:R, (forall eps:R, 0 < eps -> Rabs (x - y) < eps) -> x = y.
Proof.
  intros x y h.
  destruct (Req_dec x y) as [ heq | hneq ].
  { exact heq. }
  {
    apply Rdichotomy in hneq.
    destruct hneq as [ hlt | hgt ].
    {
      apply cond_eq_gt in hlt.
      { contradiction. }
      {
        intros e he.
        rewrite Rabs_minus_sym.
        apply h.
        exact he.
      }
    }
    {
      apply cond_eq_gt in hgt.
      { contradiction. }
      {
        intros e he.
        apply h.
        exact he.
      }
    }
  }
Qed.

Lemma not_Rlt : forall r1 r2:R, ~ r1 < r2 -> r1 >= r2.
Proof.
  intros x y h.
  apply Rle_ge.
  apply Rnot_gt_le.
  intro h'.
  apply h.
  apply Rgt_lt.
  exact h'.
Qed.

(* stopped here *)

Fixpoint amv u n := match n with
| O => u O
| S n' => if Rle_lt_dec (amv u n') (u n) then u n else amv u n'
end.

Arguments amv : simpl nomatch.

Fixpoint ami u n := match n with
| O => O
| S n' => if Rle_lt_dec (amv u n) (u n) then n else ami u n'
end.


Arguments ami : simpl nomatch.

Lemma amvSnl : forall u n, amv u n <= u (S n) -> amv u (S n) = u (S n).
Proof.
  intros u n.
  unfold amv.
  simpl.
  fold (amv u n).
  destruct (Rle_lt_dec (amv u n)).
  { intro h. reflexivity. }
  { intro h. exfalso. apply Rlt_irrefl with (u (S n)). destruct h as [ h | h ].
    { apply Rlt_trans with (amv u n);assumption. }
    { rewrite h in r. assumption. }
  }
Qed.

Lemma amvSnr : forall u n, u (S n) < amv u n -> amv u (S n) = amv u n.
Proof.
  intros u n.
  unfold amv.
  simpl.
  fold (amv u n).
  destruct (Rle_lt_dec (amv u n)).
  { intro h. exfalso. apply Rlt_irrefl with (u (S n)). destruct r as [ r | r ].
    { apply Rlt_trans with (amv u n);assumption. }
    { rewrite r in h. assumption. }
  }
  { intro h. reflexivity. }
Qed.

Lemma amvSn : forall u n,
  (amv u n <= u (S n) /\ amv u (S n) = u (S n)) \/
  (u (S n) < amv u n /\ amv u (S n) = amv u n).
Proof.
  intros u n.
  destruct (Rle_lt_dec (amv u n) (u (S n))).
  { left. split. assumption. rewrite amvSnl. reflexivity. assumption. }
  { right. split. assumption. rewrite amvSnr. reflexivity. assumption. }
Qed.

Lemma amiSnl : forall u n, amv u (S n) <= u (S n) -> ami u (S n) = S n.
Proof.
  intros u n h.
  unfold ami.
  fold (ami u n).
  destruct (Rle_lt_dec (amv u (S n)) (u (S n))).
  { reflexivity. }
  { exfalso. apply Rlt_irrefl with (u (S n)). destruct h as [ h | h ].
    { apply Rlt_trans with (amv u (S n));assumption. }
    { rewrite h in r. assumption. }
  }
Qed.

Lemma amiSnr : forall u n, u (S n) < amv u (S n) -> ami u (S n) = ami u n.
Proof.
  intros u n h.
  unfold ami.
  fold (ami u n).
  destruct (Rle_lt_dec (amv u (S n)) (u (S n))).
  { exfalso. apply Rlt_irrefl with (u (S n)). destruct r as [ r | r ].
    { apply Rlt_trans with (amv u (S n));assumption. }
    { rewrite r in h. assumption. }
  }
  { reflexivity. }
Qed.

Lemma amiSn : forall u n,
  (amv u (S n) <= u (S n) /\ ami u (S n) = S n) \/
  (u (S n) < amv u (S n) /\ ami u (S n) = ami u n).
Proof.
  intros u n.
  destruct (Rle_lt_dec (amv u (S n)) (u (S n))).
  { left. split. assumption. rewrite amiSnl. reflexivity. assumption. }
  { right. split. assumption. rewrite amiSnr. reflexivity. assumption. }
Qed.

Lemma VUI: forall u n, amv u n = u (ami u n).
Proof.
  induction n as [ | n i ].
  { simpl. reflexivity. }
  {
    destruct (amvSn u n) as [ [ ha eqa ] | [ ha eqa ] ].
    {
      rewrite eqa.
      destruct (amiSn u n) as [ [ hi eqi ] | [ hi eqi ] ].
      {
        rewrite eqi.
        reflexivity.
      }
      {
        exfalso. apply Rlt_irrefl with (u(S n)).
        pattern (u (S n)) at 2;rewrite <- eqa.
        assumption.
      }
    }
    {
      rewrite eqa.
      destruct (amiSn u n) as [ [ hi eqi ] | [ hi eqi ] ].
      {
        exfalso. destruct hi as [ hi | hi ].
        {
          apply Rlt_irrefl with (u (S n)).
          apply Rlt_trans with (amv u n).
          { assumption. }
          {
            rewrite eqa in hi.
            assumption.
          }
        }
        {
          apply Rlt_irrefl with (u (S n)).
          pattern (u (S n)) at 2;rewrite <- hi.
          rewrite eqa.
          exact ha.
        }
      }
      {
        rewrite i;clear i.
        rewrite eqi.
        reflexivity.
      }
    }
  }
Qed.

Lemma HubV : forall u, has_ub u -> has_ub (amv u).
Proof.
  intros u h.
  unfold has_ub in h.
  unfold bound in h.
  destruct h as [ m h ].
  unfold is_upper_bound in h.

  unfold has_ub.
  unfold bound.
  exists m.
  unfold is_upper_bound.
  intros x hn.
  destruct hn as [ n eq ].

  apply h.
  unfold EUn.

  rewrite VUI in eq.
  exists (ami u n).
  exact eq.
Qed.

Lemma HgrV : forall u, Un_growing (amv u).
Proof.
  intros u.
  unfold Un_growing.
  intro n.
  destruct n as [ | n ].
  {
    simpl.
    destruct (amvSn u 0%nat) as [ [ h eq ] | [ h eq ] ].
    { rewrite eq. simpl in h. exact h. }
    { rewrite eq. simpl. right. reflexivity. }
  }
  {
    destruct (amvSn u (S n)) as [ [ h eq ] | [ h eq ] ].
    { rewrite eq. exact h. }
    { rewrite eq. right. reflexivity. }
  }
Qed.

Lemma approx_maj :
  forall (Un:nat -> R) (pr:has_ub Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (lub Un pr - Un k) < eps.
Proof.
  intros Un pr.

  generalize pr;intro pr'.
  apply HubV in pr.
  apply ub_to_lub in pr.
  destruct pr as [ l Hl ].

  unfold lub.

  generalize pr';intro pr.
  apply ub_to_lub in pr'.
  destruct pr' as [ l' Hl' ].

  cut(l=l').
  {
    intros eq eps Heps.
    subst l'.
    destruct (Un_cv_crit_lub (amv Un) (HgrV Un) l Hl eps Heps) as (n, Hn).
    exists ((ami Un) n).
    rewrite <- VUI.
    rewrite Rabs_minus_sym.
    unfold R_dist in Hn.
    destruct (ub_to_lub Un pr).
    cut (x = l).
    {
      intro eq. subst x.
      apply Hn.
      unfold ge.
      constructor.
    }
    {
      eapply lub_unique.
      apply i.
      assumption.
    }
  }
  {
    apply Rle_antisym.
    {
      apply Hl.
      intros n (k, Hk).
      rewrite Hk, VUI.
      apply Hl'.
      now exists ((ami Un) k).
    }
    {
      apply Hl'.
      intros n (k, Hk).
      rewrite Hk.
      apply Rle_trans with ((amv Un) k).
      {
        clear.
        induction k.
        {
          apply Rle_refl.
        }
        {
          simpl.
          destruct (amvSn Un k) as [ [ h eq ] | [ h eq ] ].
          {
            rewrite eq.
            apply Rle_refl.
          }
          {
            rewrite eq.
            now apply Rlt_le.
          }
        }
      }
      {
        apply Hl.
        now exists k.
      }
    }
  }
Qed.

Lemma approx_min :
  forall (Un:nat -> R) (pr:has_lb Un) (eps:R),
    0 < eps ->  exists k : nat, Rabs (glb Un pr - Un k) < eps.
Proof.
  intros Un pr.
  unfold glb.
  destruct lb_to_glb as (lb, Hlb).
  intros eps Heps.
  destruct (approx_maj _ pr eps Heps) as (n, Hn).
  exists n.
  unfold Rminus.
  rewrite <- Ropp_plus_distr, Rabs_Ropp.
  replace lb with (lub (opp_seq Un) pr).
  { now rewrite <- (Ropp_involutive (Un n)). }
  {
    unfold lub.
    destruct ub_to_lub as (ub, Hub).
    apply Rle_antisym.
    { apply Hub. apply Hlb. }
    { apply Hlb. apply Hub. }
  }
Qed.

Lemma UL_sequence :
  forall (Un:nat -> R) (l1 l2:R), Un_cv Un l1 -> Un_cv Un l2 -> l1 = l2.
Proof.
  intros u l l' hl hl'.
  unfold Un_cv in hl, hl'.
  unfold R_dist in hl, hl'.
  apply cond_eq.
  intros eps he.
  cut (0 < eps / 2).
  {
    intro he'.
    specialize (hl (eps / 2) he').
    specialize (hl' (eps / 2) he').
    destruct hl as [N hl].
    destruct hl' as [N' hl'].
    set (M := max N N').
    apply Rle_lt_trans with (Rabs (l - u M) + Rabs (u M - l')).
    {
      replace (l - l') with (l - u M + (u M - l')).
      { apply Rabs_triang. }
      {
        unfold Rminus.
        repeat (rewrite Rplus_assoc).
        apply Rplus_eq_compat_l.
        repeat (rewrite <- Rplus_assoc).
        rewrite Rplus_opp_l.
        rewrite Rplus_0_l.
        reflexivity.
      }
    }
    {
      rewrite (double_var eps).
      apply Rplus_lt_compat.
      {
        rewrite <- Rabs_Ropp.
        rewrite Ropp_minus_distr.
        apply hl.
        unfold ge.
        unfold M.
        apply le_max_l.
      }
      {
        apply hl'.
        unfold ge.
        unfold M.
        apply le_max_r.
      }
    }
  }
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      prove_sup0.
    }
  }
Qed.

Lemma CV_plus :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i + Bn i) (l1 + l2).
Proof.
  intros u v.
  intros lu lv.
  intros hu hv.
  pose (f := fun i : nat => u i + v i).
  fold f.

  unfold Un_cv in hu, hv.
  unfold Un_cv.

  intros e he.
  assert ( he' : e / 2 > 0).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      prove_sup0.
    }
  }

  specialize (hu (e / 2) he').
  specialize (hv (e / 2) he').
  clear he he'.

  destruct hu as [U hu].
  destruct hv as [V hv].

  pose (M := max U V).
  exists M.

  intros n hnM.

  unfold R_dist in hu.
  unfold R_dist in hv.
  unfold R_dist.

  unfold f;clear f.

  unfold Rminus in hu.
  unfold Rminus in hv.

  rewrite double_var.

  generalize Rabs_triang;intro a.
  specialize (a (u n + - lu) (v n + - lv)).

  apply Rle_lt_trans with (Rabs (u n + - lu) + Rabs (v n + - lv)).
  unfold Rminus.
  rewrite Ropp_plus_distr.
  replace  (u n + v n + (- lu + - lv)) with (u n + - lu + (v n + - lv)).
  { exact a. }
  {
    repeat (rewrite Rplus_assoc).
    apply Rplus_eq_compat_l.
    repeat (rewrite <- Rplus_assoc).
    apply Rplus_eq_compat_r.
    rewrite Rplus_comm.
    reflexivity.
  }
  {
    apply Rplus_lt_compat.
    {
      apply hu.
      unfold ge.
      apply le_trans with M.
      {
        unfold M.
        apply le_max_l.
      }
      {
        unfold ge in hnM.
        exact hnM.
      }
    }
    {
      apply hv.
      unfold ge.
      apply le_trans with M.
      {
        unfold M.
        apply le_max_r.
      }
      {
        unfold ge in hnM.
        exact hnM.
      }
    }
  }
Qed.

Lemma cv_cvabs :
  forall (Un:nat -> R) (l:R),
    Un_cv Un l -> Un_cv (fun i:nat => Rabs (Un i)) (Rabs l).
Proof.
  intros u l h.

  pose (f := fun i : nat => Rabs (u i)).
  fold f.

  unfold Un_cv in h.
  unfold Un_cv.

  intros e he.
  specialize (h e he).

  destruct h as [N h].
  exists N.

  intros n hn.
  specialize (h n hn).

  unfold R_dist in h.
  unfold R_dist.
  unfold f.

  apply Rle_lt_trans with (Rabs (u n - l)).
  { apply Rabs_triang_inv2. }
  { exact h. }
Qed.

Lemma CV_Cauchy :
  forall Un:nat -> R, { l:R | Un_cv Un l } -> Cauchy_crit Un.
Proof.

  intros u h.
  destruct h as [ l h ].
  unfold Cauchy_crit.
  intros e he.
  assert ( he' : e / 2 > 0).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      prove_sup0.
    }
  }
  unfold Un_cv in h.
  specialize (h _ he').
  destruct h as [ N h ].
  exists N.
  intros n m hnn hnm.
  unfold R_dist.
  unfold R_dist in h.

  replace (u n - u m) with ( (u n - l) - (u m - l)).
  2:{
    unfold Rminus.
    repeat (rewrite Rplus_assoc).
    apply Rplus_eq_compat_l.
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    rewrite Rplus_comm.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_r.
    rewrite Rplus_0_r.
    reflexivity.
  }
  {
    generalize Rabs_triang;intro a.
    eapply Rle_lt_trans.
    {
      unfold Rminus at 1.
      apply a.
    }
    {
      rewrite double_var.
      apply Rplus_lt_compat.
      {
        apply h.
        exact hnn.
      }
      {
        rewrite Rabs_Ropp.
        apply h.
        exact hnm.
      }
    }
  }
Qed.


Lemma maj_by_pos :
  forall Un:nat -> R,
    { l:R | Un_cv Un l } ->
    exists l : R, 0 < l /\ (forall n:nat, Rabs (Un n) <= l).
Proof.
  intros u h.
  destruct h as [ l h ].

  pose (f := fun k:nat => Rabs (u k)).

  assert (hf : bound (EUn f)).
  {
    apply cauchy_bound.
    apply CV_Cauchy.
    exists (Rabs l).
    apply cv_cvabs.
    exact h.
  }

  destruct hf as [ub hub].

  assert(hpos: 0 <= ub).
  {
    apply Rle_trans with (Rabs (u 0%nat)).
    { apply Rabs_pos. }
    {
      unfold is_upper_bound in hub.
      apply hub.
      exists 0%nat.
      unfold f.
      reflexivity.
    }
  }

  exists (ub + 1).

  split.
  {
    apply Rplus_le_lt_0_compat.
    exact hpos.
    exact Rlt_0_1.
  }
  {
    intros n.
    apply Rle_trans with ub.
    {
      unfold is_upper_bound in hub.
      apply hub.
      exists n.
      unfold f.
      reflexivity.
    }
    {
      pattern ub at 1; rewrite <- Rplus_0_r.
      apply Rplus_le_compat_l.
      left.
      exact Rlt_0_1.
    }
  }
Qed.

Lemma CV_mult : forall (An Bn:nat -> R) (l1 l2:R),
  Un_cv An l1 -> Un_cv Bn l2 ->
  Un_cv (fun i:nat => An i * Bn i) (l1 * l2).
Proof.

  intros u v lu lv hu hv.

  pose (f := fun i : nat => u i * v i).
  fold f.

  assert (X : { l:R | Un_cv u l }).
  {
    exists lu.
    exact hu.
  }

  apply maj_by_pos in X.
  destruct X as [ M [ H3 H4 ] ].

  unfold Un_cv.
  unfold R_dist.
  intros e he.

  assert (he' : 0 < e / (2 * M)).
  {
    unfold Rdiv.
    apply Rmult_lt_0_compat.
    { exact he. }
    {
      apply Rinv_0_lt_compat.
      apply Rmult_lt_0_compat.
      { prove_sup0. }
      { exact H3. }
    }
  }

  destruct (Req_dec lv 0) as [ H7 | H7 ].
  {
    subst lv.
    rewrite Rmult_0_r.
    unfold Rminus.
    rewrite Ropp_0.

    unfold Un_cv in hv.
    unfold R_dist in hv.
    unfold Rminus in hv.
    rewrite Ropp_0 in hv.

    specialize (hv _ he').
    destruct hv as [ Nv hv ].

    exists Nv.
    intros n hn.

    rewrite Rplus_0_r.

    apply Rle_lt_trans with (Rabs (u n * v n) ).
    {
      unfold f.
      right. reflexivity.
    }
    {
      rewrite Rabs_mult.
      apply Rle_lt_trans with (M * Rabs (v n)).
      {
        apply Rmult_le_compat_r.
        { apply Rabs_pos. }
        { apply H4. }
      }
      {
        apply Rmult_lt_reg_l with (/ M).
        {
          apply Rinv_0_lt_compat.
          apply H3.
        }
        {
          rewrite <- Rmult_assoc.
          rewrite <- Rinv_l_sym.
          {
            rewrite Rmult_1_l.
            rewrite Rmult_comm.
            apply Rlt_trans with (e / (2 * M)).
            {
              specialize (hv n hn).
              rewrite Rplus_0_r in hv.
              exact hv.
            }
            {
              unfold Rdiv.
              rewrite Rinv_mult_distr.
              {
                apply Rmult_lt_reg_l with 2.
                { prove_sup0. }
                {
                  rewrite (Rmult_comm e).
                  rewrite Rmult_assoc.
                  rewrite <- Rmult_assoc.
                  rewrite Rinv_r.
                  rewrite (Rmult_comm e).
                  apply Rmult_lt_compat_r.
                  apply Rmult_lt_0_compat.
                  apply Rinv_0_lt_compat.
                  exact H3.
                  exact he.
                  pattern 2;rewrite <- Rmult_1_r.
                  rewrite double.
                  pattern 1 at 1;rewrite <- Rplus_0_l.
                  apply Rplus_lt_compat_r.
                  exact Rlt_0_1.
                  discrR.
                }
              }
              { discrR. }
              {
                apply not_eq_sym.
                apply Rlt_not_eq.
                exact H3.
              }
            }
          }
          {
            apply not_eq_sym.
            apply Rlt_not_eq.
            exact H3.
          }
        }
      }
    }
  }
  {
    cut (0 < e / (2 * Rabs lv)).
    {
      intro H8.
      unfold Un_cv in hu; unfold R_dist in hu; unfold Un_cv in hv;
      unfold R_dist in hv.
      elim (hu (e / (2 * Rabs lv)) H8); intros N1 H9.
      elim (hv (e / (2 * M)) he'); intros N2 H10.
      set (N := max N1 N2).
      exists N; intros.
      apply Rle_lt_trans with
        (Rabs (u n * v n - u n * lv) + Rabs (u n * lv - lu * lv)).
      {
        unfold f.
        replace (u n * v n - lu * lv) with
        (u n * v n - u n * lv + (u n * lv - lu * lv));
        [ apply Rabs_triang | ring ].
      }
      {
        replace (Rabs (u n * v n - u n * lv)) with
        (Rabs (u n) * Rabs (v n - lv)).
        {
          replace (Rabs (u n * lv - lu * lv)) with (Rabs lv * Rabs (u n - lu)).
          {
            rewrite (double_var e); apply Rplus_lt_compat.
            {
              apply Rle_lt_trans with (M * Rabs (v n - lv)).
              {
                do 2 rewrite <- (Rmult_comm (Rabs (v n - lv))).
                apply Rmult_le_compat_l.
                {
                  apply Rabs_pos.
                }
                {
                  apply H4.
                }
              }
              {
                apply Rmult_lt_reg_l with (/ M).
                {
                  apply Rinv_0_lt_compat; apply H3.
                }
                {
                  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
                  {
                    rewrite Rmult_1_l; rewrite (Rmult_comm (/ M)).
                    apply Rlt_le_trans with (e / (2 * M)).
                    {
                      apply H10.
                      unfold ge; apply le_trans with N.
                      {
                        unfold N; apply le_max_r.
                      }
                      {
                        assumption.
                      }
                    }
                    {
                      unfold Rdiv.
                      rewrite Rinv_mult_distr.
                      {
                        right.
                        ring.
                      }
                      { discrR. }
                      {
                        intro H12.
                        subst M.
                        eapply Rlt_irrefl.
                        apply H3.
                      }
                    }
                  }
                  {
                    intro H12.
                    subst M.
                    eapply Rlt_irrefl.
                    apply H3.
                  }
                }
              }
            }
            {
              apply Rmult_lt_reg_l with (/ Rabs lv).
              {
                apply Rinv_0_lt_compat.
                apply Rabs_pos_lt.
                exact H7.
              }
              {
                rewrite <- Rmult_assoc.
                rewrite <- Rinv_l_sym.
                {
                  rewrite Rmult_1_l.
                  apply Rlt_le_trans with (e / (2 * Rabs lv)).
                  {
                    apply H9.
                    unfold ge.
                    apply le_trans with N.
                    {
                      unfold N.
                      apply le_max_l.
                    }
                    {
                      unfold ge in H.
                      exact H.
                    }
                  }
                  {
                    unfold Rdiv.
                    right.
                    rewrite Rinv_mult_distr.
                    { ring. }
                    { discrR. }
                    {
                      apply Rabs_no_R0.
                      exact H7.
                    }
                  }
                }
                {
                  apply Rabs_no_R0.
                  exact H7.
                }
              }
            }
          }
          {
            replace (u n * lv - lu * lv) with (lv * (u n - lu)).
            {
              symmetry.
              apply Rabs_mult.
            }
            { ring. }
          }
        }
        {
          replace (u n * v n - u n * lv) with (u n * (v n - lv)).
          {
            symmetry.
            apply Rabs_mult.
          }
          { ring. }
        }
      }
    }
    {
      unfold Rdiv.
      apply Rmult_lt_0_compat.
      {
        exact he.
      }
      {
        apply Rinv_0_lt_compat.
        apply Rmult_lt_0_compat.
        { prove_sup0. }
        {
          apply Rabs_pos_lt.
          exact H7.
        }
      }
    }
  }
Qed.

Lemma tech9 :
  forall Un:nat -> R,
    Un_growing Un -> forall m n:nat, (m <= n)%nat -> Un m <= Un n.
Proof.
  intros u hg n m h.
  apply Rge_le.
  apply growing_prop.
  { exact hg. }
  { unfold ge. exact h. }
Qed.

Lemma tech13 :
  forall (An:nat -> R) (k:R),
    0 <= k < 1 ->
    Un_cv (fun n:nat => Rabs (An (S n) / An n)) k ->
    exists k0 : R,
      k < k0 < 1 /\
      (exists N : nat,
        (forall n:nat, (N <= n)%nat -> Rabs (An (S n) / An n) < k0)).
Proof.
  intros; exists (k + (1 - k) / 2).
  split.
  split.
  pattern k at 1; rewrite <- Rplus_0_r; apply Rplus_lt_compat_l.
  unfold Rdiv; apply Rmult_lt_0_compat.
  apply Rplus_lt_reg_l with k; rewrite Rplus_0_r; replace (k + (1 - k)) with 1;
    [ elim H; intros; assumption | ring ].
  apply Rinv_0_lt_compat; prove_sup0.
  apply Rmult_lt_reg_l with 2.
  prove_sup0.
  unfold Rdiv; rewrite Rmult_1_r; rewrite Rmult_plus_distr_l;
    pattern 2 at 1; rewrite Rmult_comm; rewrite Rmult_assoc;
      rewrite <- Rinv_l_sym; [ idtac | discrR ]; rewrite Rmult_1_r;
        replace (2 * k + (1 - k)) with (1 + k); [ idtac | ring ].
  elim H; intros.
  apply Rplus_lt_compat_l; assumption.
  unfold Un_cv in H0; cut (0 < (1 - k) / 2).
  intro; elim (H0 ((1 - k) / 2) H1); intros.
  exists x; intros.
  assert (H4 := H2 n H3).
  unfold R_dist in H4; rewrite <- Rabs_Rabsolu;
    replace (Rabs (An (S n) / An n)) with (Rabs (An (S n) / An n) - k + k);
    [ idtac | ring ];
    apply Rle_lt_trans with (Rabs (Rabs (An (S n) / An n) - k) + Rabs k).
  apply Rabs_triang.
  rewrite (Rabs_right k).
  apply Rplus_lt_reg_l with (- k); rewrite <- (Rplus_comm k);
    repeat rewrite <- Rplus_assoc; rewrite Rplus_opp_l;
      repeat rewrite Rplus_0_l; apply H4.
  apply Rle_ge; elim H; intros; assumption.
  unfold Rdiv; apply Rmult_lt_0_compat.
  apply Rplus_lt_reg_l with k; rewrite Rplus_0_r; elim H; intros;
    replace (k + (1 - k)) with 1; [ assumption | ring ].
  apply Rinv_0_lt_compat; prove_sup0.
Qed.

(**********)
Lemma growing_ineq :
  forall (Un:nat -> R) (l:R),
    Un_growing Un -> Un_cv Un l -> forall n:nat, Un n <= l.
Proof.
  intros; destruct (total_order_T (Un n) l) as [[Hlt|Heq]|Hgt].
  left; assumption.
  right; assumption.
  cut (0 < Un n - l).
  intro; unfold Un_cv in H0; unfold R_dist in H0.
  elim (H0 (Un n - l) H1); intros N1 H2.
  set (N := max n N1).
  cut (Un n - l <= Un N - l).
  intro; cut (Un N - l < Un n - l).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H3 H4)).
  apply Rle_lt_trans with (Rabs (Un N - l)).
  apply RRle_abs.
  apply H2.
  unfold ge, N; apply le_max_r.
  unfold Rminus; do 2 rewrite <- (Rplus_comm (- l));
    apply Rplus_le_compat_l.
  apply tech9.
  assumption.
  unfold N; apply le_max_l.
  apply Rplus_lt_reg_l with l.
  rewrite Rplus_0_r.
  replace (l + (Un n - l)) with (Un n); [ assumption | ring ].
Qed.

(** Un->l => (-Un) -> (-l) *)
Lemma CV_opp :
  forall (An:nat -> R) (l:R), Un_cv An l -> Un_cv (opp_seq An) (- l).
Proof.
  intros An l.
  unfold Un_cv; unfold R_dist; intros.
  elim (H eps H0); intros.
  exists x; intros.
  unfold opp_seq; replace (- An n - - l) with (- (An n - l));
    [ rewrite Rabs_Ropp | ring ].
  apply H1; assumption.
Qed.

(**********)
Lemma decreasing_ineq :
  forall (Un:nat -> R) (l:R),
    Un_decreasing Un -> Un_cv Un l -> forall n:nat, l <= Un n.
Proof.
  intros.
  assert (H1 := decreasing_growing _ H).
  assert (H2 := CV_opp _ _ H0).
  assert (H3 := growing_ineq _ _ H1 H2).
  apply Ropp_le_cancel.
  unfold opp_seq in H3; apply H3.
Qed.

(**********)
Lemma CV_minus :
  forall (An Bn:nat -> R) (l1 l2:R),
    Un_cv An l1 -> Un_cv Bn l2 -> Un_cv (fun i:nat => An i - Bn i) (l1 - l2).
Proof.
  intros.
  replace (fun i:nat => An i - Bn i) with (fun i:nat => An i + opp_seq Bn i).
  unfold Rminus; apply CV_plus.
  assumption.
  apply CV_opp; assumption.
  unfold Rminus, opp_seq; reflexivity.
Qed.

(** Un -> +oo *)
Definition cv_infty (Un:nat -> R) : Prop :=
  forall M:R,  exists N : nat, (forall n:nat, (N <= n)%nat -> M < Un n).

(** Un -> +oo => /Un -> O *)
Lemma cv_infty_cv_R0 :
  forall Un:nat -> R,
    (forall n:nat, Un n <> 0) -> cv_infty Un -> Un_cv (fun n:nat => / Un n) 0.
Proof.
  unfold cv_infty, Un_cv; unfold R_dist; intros.
  elim (H0 (/ eps)); intros N0 H2.
  exists N0; intros.
  unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r;
    rewrite (Rabs_Rinv _ (H n)).
  apply Rmult_lt_reg_l with (Rabs (Un n)).
  apply Rabs_pos_lt; apply H.
  rewrite <- Rinv_r_sym.
  apply Rmult_lt_reg_l with (/ eps).
  apply Rinv_0_lt_compat; assumption.
  rewrite Rmult_1_r; rewrite (Rmult_comm (/ eps)); rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; apply Rlt_le_trans with (Un n).
  apply H2; assumption.
  apply RRle_abs.
  red; intro; rewrite H4 in H1; elim (Rlt_irrefl _ H1).
  apply Rabs_no_R0; apply H.
Qed.

(**********)
Lemma decreasing_prop :
  forall (Un:nat -> R) (m n:nat),
    Un_decreasing Un -> (m <= n)%nat -> Un n <= Un m.
Proof.
  unfold Un_decreasing; intros.
  induction  n as [| n Hrecn].
  induction  m as [| m Hrecm].
  right; reflexivity.
  elim (le_Sn_O _ H0).
  cut ((m <= n)%nat \/ m = S n).
  intro; elim H1; intro.
  apply Rle_trans with (Un n).
  apply H.
  apply Hrecn; assumption.
  rewrite H2; right; reflexivity.
  inversion H0; [ right; reflexivity | left; assumption ].
Qed.

(** |x|^n/n! -> 0 *)
Lemma cv_speed_pow_fact :
  forall x:R, Un_cv (fun n:nat => x ^ n / INR (fact n)) 0.
Proof.
  intro;
    cut
      (Un_cv (fun n:nat => Rabs x ^ n / INR (fact n)) 0 ->
        Un_cv (fun n:nat => x ^ n / INR (fact n)) 0).
  intro; apply H.
  unfold Un_cv; unfold R_dist; intros; case (Req_dec x 0);
    intro.
  exists 1%nat; intros.
  rewrite H1; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r;
    rewrite Rabs_R0; rewrite pow_ne_zero;
      [ unfold Rdiv; rewrite Rmult_0_l; rewrite Rabs_R0; assumption
        | red; intro; rewrite H3 in H2; elim (le_Sn_n _ H2) ].
  assert (H2 := Rabs_pos_lt x H1); set (M := up (Rabs x)); cut (0 <= M)%Z.
  intro; elim (IZN M H3); intros M_nat H4.
  set (Un := fun n:nat => Rabs x ^ (M_nat + n) / INR (fact (M_nat + n))).
  cut (Un_cv Un 0); unfold Un_cv; unfold R_dist; intros.
  elim (H5 eps H0); intros N H6.
  exists (M_nat + N)%nat; intros;
    cut (exists p : nat, (p >= N)%nat /\ n = (M_nat + p)%nat).
  intro; elim H8; intros p H9.
  elim H9; intros; rewrite H11; unfold Un in H6; apply H6; assumption.
  exists (n - M_nat)%nat.
  split.
  unfold ge; apply (fun p n m:nat => plus_le_reg_l n m p) with M_nat;
    rewrite <- le_plus_minus.
  assumption.
  apply le_trans with (M_nat + N)%nat.
  apply le_plus_l.
  assumption.
  apply le_plus_minus; apply le_trans with (M_nat + N)%nat;
    [ apply le_plus_l | assumption ].
  set (Vn := fun n:nat => Rabs x * (Un 0%nat / INR (S n))).
  cut (1 <= M_nat)%nat.
  intro; cut (forall n:nat, 0 < Un n).
  intro; cut (Un_decreasing Un).
  intro; cut (forall n:nat, Un (S n) <= Vn n).
  intro; cut (Un_cv Vn 0).
  unfold Un_cv; unfold R_dist; intros.
  elim (H10 eps0 H5); intros N1 H11.
  exists (S N1); intros.
  cut (forall n:nat, 0 < Vn n).
  intro; apply Rle_lt_trans with (Rabs (Vn (pred n) - 0)).
  repeat rewrite Rabs_right.
  unfold Rminus; rewrite Ropp_0; do 2 rewrite Rplus_0_r;
    replace n with (S (pred n)).
  apply H9.
  inversion H12; simpl; reflexivity.
  apply Rle_ge; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r; left;
    apply H13.
  apply Rle_ge; unfold Rminus; rewrite Ropp_0; rewrite Rplus_0_r; left;
    apply H7.
  apply H11; unfold ge; apply le_S_n; replace (S (pred n)) with n;
    [ unfold ge in H12; exact H12 | inversion H12; simpl; reflexivity ].
  intro; apply Rlt_le_trans with (Un (S n0)); [ apply H7 | apply H9 ].
  cut (cv_infty (fun n:nat => INR (S n))).
  intro; cut (Un_cv (fun n:nat => / INR (S n)) 0).
  unfold Un_cv, R_dist; intros; unfold Vn.
  cut (0 < eps1 / (Rabs x * Un 0%nat)).
  intro; elim (H11 _ H13); intros N H14.
  exists N; intros;
    replace (Rabs x * (Un 0%nat / INR (S n)) - 0) with
    (Rabs x * Un 0%nat * (/ INR (S n) - 0));
    [ idtac | unfold Rdiv; ring ].
  rewrite Rabs_mult; apply Rmult_lt_reg_l with (/ Rabs (Rabs x * Un 0%nat)).
  apply Rinv_0_lt_compat; apply Rabs_pos_lt.
  apply prod_neq_R0.
  apply Rabs_no_R0; assumption.
  assert (H16 := H7 0%nat); red; intro; rewrite H17 in H16;
    elim (Rlt_irrefl _ H16).
  rewrite <- Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_l.
  replace (/ Rabs (Rabs x * Un 0%nat) * eps1) with (eps1 / (Rabs x * Un 0%nat)).
  apply H14; assumption.
  unfold Rdiv; rewrite (Rabs_right (Rabs x * Un 0%nat)).
  apply Rmult_comm.
  apply Rle_ge; apply Rmult_le_pos.
  apply Rabs_pos.
  left; apply H7.
  apply Rabs_no_R0.
  apply prod_neq_R0;
    [ apply Rabs_no_R0; assumption
      | assert (H16 := H7 0%nat); red; intro; rewrite H17 in H16;
        elim (Rlt_irrefl _ H16) ].
  unfold Rdiv; apply Rmult_lt_0_compat.
  assumption.
  apply Rinv_0_lt_compat; apply Rmult_lt_0_compat.
  apply Rabs_pos_lt; assumption.
  apply H7.
  apply (cv_infty_cv_R0 (fun n:nat => INR (S n))).
  intro; apply not_O_INR; discriminate.
  assumption.
  unfold cv_infty; intro;
    destruct (total_order_T M0 0) as [[Hlt|Heq]|Hgt].
  exists 0%nat; intros.
  apply Rlt_trans with 0; [ assumption | apply lt_INR_0; apply lt_O_Sn ].
  exists 0%nat; intros; rewrite Heq; apply lt_INR_0; apply lt_O_Sn.
  set (M0_z := up M0).
  assert (H10 := archimed M0).
  cut (0 <= M0_z)%Z.
  intro; elim (IZN _ H11); intros M0_nat H12.
  exists M0_nat; intros.
  apply Rlt_le_trans with (IZR M0_z).
  elim H10; intros; assumption.
  rewrite H12; rewrite <- INR_IZR_INZ; apply le_INR.
  apply le_trans with n; [ assumption | apply le_n_Sn ].
  apply le_IZR; left; simpl; unfold M0_z;
    apply Rlt_trans with M0; [ assumption | elim H10; intros; assumption ].
  intro; apply Rle_trans with (Rabs x * Un n * / INR (S n)).
  unfold Un; replace (M_nat + S n)%nat with (M_nat + n + 1)%nat.
  rewrite pow_add; replace (Rabs x ^ 1) with (Rabs x);
    [ idtac | simpl; ring ].
  unfold Rdiv; rewrite <- (Rmult_comm (Rabs x));
    repeat rewrite Rmult_assoc; repeat apply Rmult_le_compat_l.
  apply Rabs_pos.
  left; apply pow_lt; assumption.
  replace (M_nat + n + 1)%nat with (S (M_nat + n)).
  rewrite fact_simpl; rewrite mult_comm; rewrite mult_INR;
    rewrite Rinv_mult_distr.
  apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt; red;
    intro; assert (H10 := eq_sym H9); elim (fact_neq_0 _ H10).
  left; apply Rinv_lt_contravar.
  apply Rmult_lt_0_compat; apply lt_INR_0; apply lt_O_Sn.
  apply lt_INR; apply lt_n_S.
  pattern n at 1; replace n with (0 + n)%nat; [ idtac | reflexivity ].
  apply plus_lt_compat_r.
  apply lt_le_trans with 1%nat; [ apply lt_O_Sn | assumption ].
  apply INR_fact_neq_0.
  apply not_O_INR; discriminate.
  ring.
  ring.
  unfold Vn; rewrite Rmult_assoc; unfold Rdiv;
    rewrite (Rmult_comm (Un 0%nat)); rewrite (Rmult_comm (Un n)).
  repeat apply Rmult_le_compat_l.
  apply Rabs_pos.
  left; apply Rinv_0_lt_compat; apply lt_INR_0; apply lt_O_Sn.
  apply decreasing_prop; [ assumption | apply le_O_n ].
  unfold Un_decreasing; intro; unfold Un.
  replace (M_nat + S n)%nat with (M_nat + n + 1)%nat.
  rewrite pow_add; unfold Rdiv; rewrite Rmult_assoc;
    apply Rmult_le_compat_l.
  left; apply pow_lt; assumption.
  replace (Rabs x ^ 1) with (Rabs x); [ idtac | simpl; ring ].
  replace (M_nat + n + 1)%nat with (S (M_nat + n)).
  apply Rmult_le_reg_l with (INR (fact (S (M_nat + n)))).
  apply lt_INR_0; apply neq_O_lt; red; intro; assert (H9 := eq_sym H8);
    elim (fact_neq_0 _ H9).
  rewrite (Rmult_comm (Rabs x)); rewrite <- Rmult_assoc; rewrite <- Rinv_r_sym.
  rewrite Rmult_1_l.
  rewrite fact_simpl; rewrite mult_INR; rewrite Rmult_assoc;
    rewrite <- Rinv_r_sym.
  rewrite Rmult_1_r; apply Rle_trans with (INR M_nat).
  left; rewrite INR_IZR_INZ.
  rewrite <- H4; assert (H8 := archimed (Rabs x)); elim H8; intros; assumption.
  apply le_INR; omega.
  apply INR_fact_neq_0.
  apply INR_fact_neq_0.
  ring.
  ring.
  intro; unfold Un; unfold Rdiv; apply Rmult_lt_0_compat.
  apply pow_lt; assumption.
  apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt; red; intro;
    assert (H8 := eq_sym H7); elim (fact_neq_0 _ H8).
  clear Un Vn; apply INR_le; simpl.
  induction  M_nat as [| M_nat HrecM_nat].
  assert (H6 := archimed (Rabs x)); fold M in H6; elim H6; intros.
  rewrite H4 in H7; rewrite <- INR_IZR_INZ in H7.
  simpl in H7; elim (Rlt_irrefl _ (Rlt_trans _ _ _ H2 H7)).
  apply (le_INR 1); apply le_n_S;
    apply le_O_n.
  apply le_IZR; simpl; left; apply Rlt_trans with (Rabs x).
  assumption.
  elim (archimed (Rabs x)); intros; assumption.
  unfold Un_cv; unfold R_dist; intros; elim (H eps H0); intros.
  exists x0; intros;
    apply Rle_lt_trans with (Rabs (Rabs x ^ n / INR (fact n) - 0)).
  unfold Rminus; rewrite Ropp_0; do 2 rewrite Rplus_0_r;
    rewrite (Rabs_right (Rabs x ^ n / INR (fact n))).
  unfold Rdiv; rewrite Rabs_mult; rewrite (Rabs_right (/ INR (fact n))).
  rewrite RPow_abs; right; reflexivity.
  apply Rle_ge; left; apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt;
    red; intro; assert (H4 := eq_sym H3); elim (fact_neq_0 _ H4).
  apply Rle_ge; unfold Rdiv; apply Rmult_le_pos.
  case (Req_dec x 0); intro.
  rewrite H3; rewrite Rabs_R0.
  induction  n as [| n Hrecn];
    [ simpl; left; apply Rlt_0_1
      | simpl; rewrite Rmult_0_l; right; reflexivity ].
  left; apply pow_lt; apply Rabs_pos_lt; assumption.
  left; apply Rinv_0_lt_compat; apply lt_INR_0; apply neq_O_lt; red;
    intro; assert (H4 := eq_sym H3); elim (fact_neq_0 _ H4).
  apply H1; assumption.
Qed.
