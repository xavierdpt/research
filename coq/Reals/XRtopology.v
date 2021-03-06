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
Require Import XRanalysis1.
Require Import XRList.
Require Import Classical_Prop.
Require Import Classical_Pred_Type.
Require Import XRcompleteness.
Local Open Scope XR_scope.

(** * General definitions and propositions *)

Definition included (D1 D2:R -> Prop) : Prop := forall x:R, D1 x -> D2 x.
Definition disc (x:R) (delta:posreal) (y:R) : Prop := Rabs (y - x) < delta.
Definition neighbourhood (V:R -> Prop) (x:R) : Prop :=
  exists delta : posreal, included (disc x delta) V.
Definition open_set (D:R -> Prop) : Prop :=
  forall x:R, D x -> neighbourhood D x.
Definition complementary (D:R -> Prop) (c:R) : Prop := ~ D c.
Definition closed_set (D:R -> Prop) : Prop := open_set (complementary D).
Definition intersection_domain (D1 D2:R -> Prop) (c:R) : Prop := D1 c /\ D2 c.
Definition union_domain (D1 D2:R -> Prop) (c:R) : Prop := D1 c \/ D2 c.
Definition interior (D:R -> Prop) (x:R) : Prop := neighbourhood D x.

Lemma Rminus_diag : forall x, x - x=R0.
Proof.
  intro x.
  unfold Rminus.
  rewrite Rplus_opp_r.
  reflexivity.
Qed.

(* x is in the disc centered at x *)
Lemma disc_center : forall x delta, disc x delta x.
Proof.
  intros x d.
  unfold disc.
  rewrite Rminus_diag.
  rewrite Rabs_R0.
  apply cond_pos.
Qed.
(* Informal proof:
   The distance between x and itself is 0, which is always smaller than the radius, therefore x is in the disc centered at x
*)

Lemma interior_P1 : forall D:R -> Prop, included (interior D) D.
Proof.
  intro D.
  unfold included. (* we must show that forall x, if x is in the interior of D, then x is in D *)
  intros x h.
  unfold interior in h. (* x is in the interior of D iff x is in a neighbourhood of D *)
  unfold neighbourhood in h. (* x is in a neighbourhood of D iff there is a disc around x which is included in D *)
  destruct h as [ delta h ].
  unfold included in h. (* so we know that forall y, if y is in a disc around x, y is in x *)
  apply h. (* this holds in particular fo x *)
  apply disc_center. (* x is obviously in the disc centered at x *)
Qed.
(* If x is in the interior of D, then x is in a disc centered at x and this disc included in D, therefore by transitivity, x is in D *)

(* If D is an open set, then the interior of D is included in D *)
Lemma interior_P2 : forall D:R -> Prop, open_set D -> included D (interior D).
Proof.
  intros D h.
  unfold included.
  intros x hx.
  unfold interior.
  unfold open_set in h.
  apply h.
  exact hx.
Qed.
(* Informal proof
   D is an open set if any point of D is in a neighbourhood of D. This is the definition of the interior of D.
*)

Definition point_adherent (D:R -> Prop) (x:R) : Prop := forall V:R -> Prop,
    neighbourhood V x ->
    exists y : R, intersection_domain V D y.

Definition adherence (D:R -> Prop) (x:R) : Prop := point_adherent D x.

(* D is included in its adherence *)
Lemma adherence_P1 : forall D:R -> Prop, included D (adherence D).
Proof.
  intros D.
  unfold included. (* we must show that if x is in D, then it is in its adherence *)
  intros x hx. (* let x be such a point *)
  unfold adherence.
  unfold point_adherent.
  intros V h. (* let V be a set which contains a neighbourhood of x ; we must show that there is a point which is both in V and in D *)
  unfold neighbourhood in h.
  destruct h as [ delta h]. (* V is included in a disc centered at x *)
  unfold included in h.
  unfold intersection_domain.
  (* We can show that x is both in D and in V *)
  exists x.
  split.
  { (* Since V contains the disc centered at x, x is in V *)
    apply h.
    apply disc_center.
  }
  { (* And we already know that x is in D *)
    exact hx.
  }
Qed.

(* Inclusion is transitive *)
Lemma included_trans : forall D1 D2 D3:R -> Prop,
    included D1 D2 -> included D2 D3 -> included D1 D3.
Proof.
  intros A B C.
  intros hab hbc.
  unfold included.
  intros x ax.
  unfold included in hbc, hab.
  apply hbc.
  apply hab.
  exact ax.
Qed.

(* The interior is an open set *)
Lemma interior_P3 : forall D:R -> Prop, open_set (interior D).
Proof.
  intro D.
  unfold open_set.
  intros x h.

  unfold interior in h.
  unfold neighbourhood in h.
  destruct h as [ delta h ].

  unfold neighbourhood.
  exists delta.
  unfold included.
  intros y hy.

  unfold interior.
  unfold neighbourhood.
  unfold disc in hy.

  set (exp := delta - Rabs (y - x)).

  assert ( hpos : R0 < exp).
  {
    unfold exp.
    unfold Rminus.
    eapply Rplus_lt_reg_r.
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_l, Rplus_0_r.
    exact hy.
  }

  set (delta' := mkposreal _ hpos).
  exists delta'.

  unfold included.
  intros z hz.
  unfold disc in hz.
  subst delta'. simpl in hz.
  subst exp.

  unfold included in h.
  unfold disc in h.

  apply h. clear h.

  unfold Rminus.
  pattern z;rewrite <- Rplus_0_r.
  rewrite <- (Rplus_opp_l y).
  repeat rewrite Rplus_assoc.
  rewrite <- (Rplus_assoc z).
  eapply Rle_lt_trans.
  apply Rabs_triang.
  eapply Rplus_lt_reg_r.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  exact hz.
Qed.


Lemma complementary_P1 : forall D:R -> Prop,
    ~ (exists y : R, intersection_domain D (complementary D) y).
Proof.
  intros D h.
  destruct h as [ y h ].
  unfold intersection_domain in h.
  destruct h as [hy h].
  unfold complementary in h.
  apply h.
  exact hy.
Qed.

(* If D is closed, then D contains its adherence *)
Lemma adherence_P2 :
  forall D:R -> Prop, closed_set D -> included (adherence D) D.
Proof.
  intros D hclosed.
  unfold included.
  intros x h.
  (* x is either in x or in its complement *)
  destruct (classic (D x)) as [ hdx | hdx ].
  { exact hdx. }
  {
    (* x is in the complement of x *)
    (* We must show that because x is in the adherence of D and D is closed, this cannot be the case *)
    exfalso.
    unfold adherence in h.
    unfold point_adherent in h.
    unfold intersection_domain in h.
    specialize (h (complementary D)).
    (* Hypotheseses allow us to assert that if x is in a neighbourhood of the complementary, then there's a point which is both in D and in its complementary *)
    destruct h as [ y [ l r ] ].
    {
      unfold closed_set in hclosed.
      (* Because D it's closed, it's complementary is open *)
      unfold open_set in hclosed.
      (* this means that if x is in the comlementary of x, then x is in a neighbourhood of the complementary, which is what we want to show *)
      apply hclosed.
      unfold complementary.
      (* and x is in the complementary indeed *)
      exact hdx.
    }
    {
      (* we found a point which is both in D and in its complementary, which is impossible *)
      unfold complementary in l.
      apply l. exact r.
    }
  }
Qed.



Lemma Rabs_reg : forall x y z, Rabs (x-z) <= Rabs (x-y)+Rabs(y-z).
Proof.
  intros x y z.
  eapply Rle_trans.
  2:apply Rabs_triang.
  unfold Rminus.
  repeat rewrite Rplus_assoc.
  repeat rewrite (Rplus_comm x).
  repeat rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l, Rplus_0_l.
  right.
  reflexivity.
Qed.

Lemma adherence_P3 : forall D:R -> Prop, closed_set (adherence D).
Proof.
  intro D.

  unfold closed_set.
  unfold open_set.
  intros x h.

  unfold complementary in h.
  unfold adherence in h.
  unfold point_adherent in h.
  apply not_all_ex_not in h.
  destruct h as [ V h].
  apply imply_to_and in h.
  destruct h as [ hx h ].

  unfold neighbourhood.
  unfold neighbourhood in hx.
  destruct hx as [ delta hx ].
  exists delta.

  unfold included.
  intros y hy.
  unfold disc in hy.

  unfold complementary.
  intro hadh.
  unfold adherence in hadh.
  unfold point_adherent in hadh.
  specialize (hadh V).

  apply h. clear h.
  apply hadh. clear hadh.
  unfold neighbourhood.

  assert ( hpos : R0 < delta - Rabs (y - x)).
  {
    eapply Rplus_lt_reg_r.
    unfold Rminus.
    rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
    apply hy.
  }

  set (del := mkposreal _ hpos).
  exists del.
  unfold included.
  unfold disc.
  subst del.
  simpl.

  intros z hz.
  unfold included in hx.
  apply hx. clear hx.
  unfold disc.

  eapply Rle_lt_trans.
  eapply Rabs_reg.
  eapply Rplus_lt_reg_r.
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r.
  apply hz.
Qed.

Definition eq_Dom (D1 D2:R -> Prop) : Prop :=
  included D1 D2 /\ included D2 D1.

Infix "=_D" := eq_Dom (at level 70, no associativity).

Lemma open_set_P1 : forall D:R -> Prop, open_set D <-> D =_D interior D.
Proof.
  unfold eq_Dom.
  intro D.
  split.
  {
    intro h.
    unfold open_set in h.
    split.
    {
      unfold included.
      intros x hx.
      unfold interior.
      apply h.
      exact hx.
    }
    {
      unfold included.
      intros x hx.
      unfold interior in hx.
      unfold neighbourhood in hx.
      destruct hx as [ delta hx ].
      unfold included in hx.
      apply hx.
      unfold disc.
      unfold Rminus.
      rewrite Rplus_opp_r, Rabs_R0.
      apply cond_pos.
    }
  }
  {
    intros [ hr hl ].
    unfold open_set.
    intros x hx.
    unfold included in hr, hl.
    unfold interior in hr, hl.
    apply hr.
    exact hx.
  }
Qed.

Lemma closed_set_P1 : forall D:R -> Prop, closed_set D <-> D =_D adherence D.
Proof.
  intro D.
  split.
  {
    intro H.
    unfold eq_Dom.
    split.
    { apply adherence_P1. }
    {
      apply adherence_P2.
      assumption.
    }
  }
  {
    unfold eq_Dom.
    unfold included.
    intros H.
    assert (H0 := adherence_P3 D).
    unfold closed_set in H0.
    unfold closed_set.
    unfold open_set.
    unfold open_set in H0.
    intros x H1.
    assert (H2 : complementary (adherence D) x).
    {
      unfold complementary.
      unfold complementary in H1.
      intro H2.
      elim H. clear H. intros _ H.
      elim H1. apply (H _ H2).
    }
    {
      assert (H3 := H0 _ H2).
      unfold neighbourhood.
      unfold neighbourhood in H3.
      elim H3.
      intros x0 H4.
      exists x0.
      unfold included.
      unfold included in H4.
      intros x1 H5.
      assert (H6 := H4 _ H5).
      unfold complementary in H6.
      unfold complementary.
      intro H7.
      elim H.
      clear H.
      intros H _.
      elim H6.
      apply (H _ H7).
    }
  }
Qed.

Lemma neighbourhood_P1 : forall (D1 D2:R -> Prop) (x:R),
    included D1 D2 -> neighbourhood D1 x -> neighbourhood D2 x.
Proof.
  intros A B x.
  intros hAB hax.
  unfold included in hAB.
  unfold neighbourhood.
  unfold neighbourhood in hax.
  destruct hax as [ delta hax ].
  exists delta.
  unfold included.
  unfold included in hax.
  unfold disc.
  unfold disc in hax.
  intros y hy.
  apply hAB.
  apply hax.
  exact hy.
Qed.

Lemma open_set_P2 :
  forall D1 D2:R -> Prop,
    open_set D1 -> open_set D2 -> open_set (union_domain D1 D2).
Proof.
  intros A B hA hB.
  unfold open_set.
  intros x hu.
  unfold union_domain in hu.
  unfold neighbourhood.
  unfold open_set in hA.
  unfold open_set in hB.
  specialize (hA x).
  specialize (hB x).
  destruct hu as [ hu | hu ].
  {
    specialize (hA hu).
    unfold neighbourhood in hA.
    destruct hA as [ delta hA ].
    exists delta.
    unfold included.
    unfold disc.
    intros y hy.
    unfold union_domain.
    unfold included in hA.
    unfold disc in hA.
    left.
    apply hA.
    exact hy.
  }
  {
    specialize (hB hu).
    unfold neighbourhood in hB.
    destruct hB as [ delta hB ].
    exists delta.
    unfold included.
    unfold disc.
    intros y hy.
    unfold union_domain.
    unfold included in hB.
    unfold disc in hB.
    right.
    apply hB.
    exact hy.
  }
Qed.

Lemma open_set_P3 :
  forall D1 D2:R -> Prop,
    open_set D1 -> open_set D2 -> open_set (intersection_domain D1 D2).
Proof.
  intros A B hA hB.
  unfold open_set.
  intros x hAB.
  unfold intersection_domain in hAB.
  destruct hAB as [ hax hbx ].
  unfold neighbourhood.
  unfold open_set in hA.
  unfold open_set in hB.
  specialize (hA x hax).
  specialize (hB x hbx).
  unfold neighbourhood in hA, hB.
  unfold included in hA, hB.
  unfold disc in hA, hB.
  destruct hA as [ dA hA ].
  destruct hB as [ dB hB ].
  unfold included.
  unfold disc.
  unfold intersection_domain.
  set (delta := Rmin dA dB).
  assert (hpos : R0 < delta).
  {
    unfold delta.
    apply Rmin_pos;apply cond_pos.
  }
  set (d := mkposreal _ hpos).
  exists d.
  subst d. simpl.
  intros y hy.
  split.
  {
    apply hA.
    eapply Rlt_le_trans.
    apply hy.
    unfold delta.
    apply Rmin_l.
  }
  {
    apply hB.
    eapply Rlt_le_trans.
    apply hy.
    unfold delta.
    apply Rmin_r.
  }
Qed.

Lemma open_set_P4 : open_set (fun x:R => False).
Proof.
  unfold open_set.
  intros x f.
  contradiction.
Qed.

Lemma open_set_P5 : open_set (fun x:R => True).
Proof.
  unfold open_set.
  intros x _.
  unfold neighbourhood.
  exists (mkposreal R1 Rlt_0_1).
  unfold included.
  intros _ _.
  exact I.
Qed.

Lemma disc_P1 : forall (x:R) (del:posreal), open_set (disc x del).
Proof.
  intros x delta.
  unfold open_set.
  intros y hy.
  unfold neighbourhood.
  unfold disc in hy.
  set (d:=delta - Rabs (y - x)).
  assert (hpos : R0 < d).
  {
    unfold d.
    unfold Rminus.
    eapply Rplus_lt_reg_r.
    rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
    exact hy.
  }
  set (delta' := mkposreal _ hpos).
  exists delta'.
  unfold included.
  unfold disc.
  subst delta'.
  simpl.
  intros z hz.
  eapply Rle_lt_trans.
  eapply Rabs_reg.
  unfold d in hz.
  eapply Rplus_lt_reg_r.
  rewrite Rplus_assoc.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  apply hz.
Qed.

Lemma continuity_P1 : forall (f:R -> R) (x:R),
  continuity_pt f x <-> (forall W:R -> Prop,
    neighbourhood W (f x) -> exists V : R -> Prop,
    neighbourhood V x /\ (forall y:R, V y -> W (f y))).
Proof.
  intros f x.
  split.
  {
    intros hc D hn.
    unfold neighbourhood in hn.
    destruct hn as [ delta hn ].
    unfold continuity_pt in hc.
    unfold continue_in in hc.
    unfold limit1_in in hc.
    unfold limit_in in hc.
    simpl in hc.
    unfold R_dist in hc.
    assert (H2 := hc delta (cond_pos delta)).
    elim H2.
    intros del2 H3.
    elim H3.
    intros H4 H5.
    exists (disc x (mkposreal del2 H4)).
    unfold included in hn.
    split.
    {
      unfold neighbourhood, disc.
      exists (mkposreal del2 H4).
      unfold included.
      intros x0 H6.
      simpl in *.
      exact H6.
    }
    {
      intros y H6.
      apply hn.
      unfold disc.
      case (Req_dec y x).
      {
        intro H7.
        rewrite H7.
        unfold Rminus.
        rewrite Rplus_opp_r.
        rewrite Rabs_R0.
        apply (cond_pos delta).
      }
      {
        intros H7.
        apply H5.
        split.
        {
          unfold D_x.
          unfold no_cond.
          split.
          { exact I. }
          {
            apply (not_eq_sym (A:=R)).
            apply H7.
          }
        }
        {
          unfold disc in H6.
          apply H6.
        }
      }
    }
  }
  {
    intros H.
    unfold continuity_pt.
    unfold continue_in.
    unfold limit1_in.
    unfold limit_in.
    intros eps H0.
    assert (H1 := H (disc (f x) (mkposreal eps H0))).
    cut (neighbourhood (disc (f x) (mkposreal eps H0)) (f x)).
    {
      intro H2.
      assert (H3 := H1 H2).
      elim H3.
      intros D H4.
      elim H4.
      intros H5 H6.
      unfold neighbourhood in H5.
      elim H5.
      intros del1 H7.
      exists (pos del1).
      split.
      {
        apply (cond_pos del1).
      }
      {
        intros x0 H8.
        elim H8.
        intros H9 H10.
        simpl in H10.
        unfold R_dist in H10.
        simpl.
        unfold R_dist.
        apply (H6 _ (H7 _ H10)).
      }
    }
    {
      unfold neighbourhood.
      unfold disc.
      exists (mkposreal eps H0).
      unfold included.
      intros x0 H2.
      simpl in *.
      exact H2.
    }
  }
Qed.

Definition image_rec (f:R -> R) (D:R -> Prop) (x:R) : Prop := D (f x).

(**********)
Lemma continuity_P2 :
  forall (f:R -> R) (D:R -> Prop),
    continuity f -> open_set D -> open_set (image_rec f D).
Proof.
  intros f D.
  intro hc.
  unfold continuity in hc.
  intro ho.
  unfold open_set in ho.
  unfold open_set.
  intros x hi.
  unfold image_rec in hi.

  destruct (continuity_P1 f x) as [ hp _ ].

  specialize (hc x).
  specialize (hp hc).
  specialize (hp D).
  specialize (ho (f x)).
  specialize (ho hi).
  specialize (hp ho).
  destruct hp as [ V [ hn hp ] ].
  unfold neighbourhood in hn.
  destruct hn as [ delta hn ].
  unfold neighbourhood.
  exists delta.
  unfold included in hn.
  unfold included.
  intros y hy.
  unfold image_rec.
  apply hp.
  apply hn.
  exact hy.
Qed.

Lemma continuity_P3 :
  forall f:R -> R,
    continuity f <->
    (forall D:R -> Prop, open_set D -> open_set (image_rec f D)).
Proof.
  intros f.
  split.
  {
    intros hc D ho.
    apply continuity_P2.
    exact hc.
    exact ho.
  }
  {
    intros h.
    unfold continuity.
    unfold continuity_pt.
    unfold continue_in.
    unfold limit1_in.
    unfold limit_in.
    simpl.
    unfold R_dist.
    intros x e he.

    set (pe := (mkposreal _ he)).
    assert (eq:e=pe). { auto. }
    clearbody pe.

    assert ( ho : open_set (disc (f x) pe)).
    { apply disc_P1. }
    specialize (h _ ho).
    clear ho.

    unfold open_set in h.
    unfold image_rec at 1 in h.

    assert (hd : disc (f x) pe (f x)).
    {
      unfold disc.
      unfold Rminus.
      rewrite Rplus_opp_r.
      rewrite Rabs_R0.
      apply cond_pos.
    }

    specialize (h _ hd).
    unfold neighbourhood in h.
    destruct h as [ delta h ].
    exists delta.
    split.
    1:apply cond_pos.
    intros y hy.
    destruct hy as [ _ hy ].
    unfold included in h.
    unfold image_rec in h.
    unfold disc at 2 in h.
    rewrite eq.
    apply h.
    unfold disc.
    exact hy.
  }
Qed.

(**********)
Theorem Rsepare :
  forall x y:R,
    x <> y ->
    exists V : R -> Prop,
      (exists W : R -> Prop,
        neighbourhood V x /\
        neighbourhood W y /\ ~ (exists y : R, intersection_domain V W y)).
Proof.
  intros x y hneq.

  set (e := (Rabs (x-y)/R2)).
  assert (he : R0 < e).
  {
    unfold e.
    apply half_pos.
    apply Rabs_pos_lt.
    intro eq.
    apply hneq.
    apply Rplus_eq_reg_r with (-y).
    rewrite Rplus_opp_r.
    exact eq.
  }
  set (ep := mkposreal e he).
  assert (eq : e = ep). { auto. }
  clearbody ep.

  exists (disc x ep).
  exists (disc y ep).

  repeat (try split).

  unfold neighbourhood.
  exists ep.
  unfold included.
  intros z hz.
  exact hz.

  unfold neighbourhood.
  exists ep.
  unfold included.
  intros z hz.
  exact hz.

  intro hnot.
  destruct hnot as [ z hnot ].
  unfold intersection_domain in hnot.
  destruct hnot as [hxz hyz].
  unfold disc in hxz, hyz.
  rewrite <- eq in hxz, hyz.
  unfold e in hxz, hyz, he.
  clear eq ep e.

  generalize Rabs_reg;intro rr.
  specialize (rr x z y).

  eapply Rlt_irrefl.
  eapply Rle_lt_trans.
  apply rr;clear rr.

  rewrite <- (split_2 (Rabs (x - y))).
  apply Rplus_lt_compat.

  rewrite (Rabs_minus_sym x z).
  exact hxz.

  exact hyz.
Qed.


Record family : Type := mkfamily {
  ind : R -> Prop;
  f :> R -> R -> Prop;
  cond_fam : forall x:R, (exists y : R, f x y) -> ind x
}.

Definition family_open_set (f:family) : Prop := forall x:R, open_set (f x).

Definition domain_finite (D:R -> Prop) : Prop :=
  exists l : Rlist, (forall x:R, D x <-> In x l).

Definition family_finite (f:family) : Prop := domain_finite (ind f).

Definition covering (D:R -> Prop) (f:family) : Prop :=
  forall x:R, D x ->  exists y : R, f y x.

Definition covering_open_set (D:R -> Prop) (f:family) : Prop :=
  covering D f /\ family_open_set f.

Definition covering_finite (D:R -> Prop) (f:family) : Prop :=
  covering D f /\ family_finite f.

Lemma restriction_family : forall (f:family) (D:R -> Prop) (x:R),
  (exists y : R,f x y /\ D x) ->
  intersection_domain (ind f) D x.
Proof.
  intros f D x h.
  unfold intersection_domain.
  (*
    f is a family, D is a subset of R, x is a real number
    and there is y such that y is in the family indexed by x
    and x is in D
  *)
  (*
    we want to show that x is an index of f and x is in D
  *)
  destruct h as [ y [ hxy hx ] ].
  split.
  {
    (* to show taht x is an index of f, we need to show that the set (f x) is not empty *)
    apply cond_fam.
    (* and it is the case, because y is in (f x) *)
    exists y.
    exact hxy.
  }
  { (* the fact that x is in D is in the hypotheses *)
    exact hx.
  }
Qed.

Definition RF (f:family) D x y := f x y /\ D x.

(* restriction_family allows to define the notion of subfamily *)
(* a subfamily is a family projected on D, i.e. the index is restricted to elements of D, and if (f x y) holds only for those x which are in D *)
Definition subfamily (f:family) (D:R -> Prop) : family := mkfamily
  (intersection_domain (ind f) D)
  (RF f D)
  (restriction_family f D).

Goal forall (f:family) (D:R->Prop), covering D (subfamily f D) -> covering D f.
Proof.
intros fam D hcov.
(* We want to show that if fam restricted on D covers D, then fam covers D *)
unfold covering.
(* fam covers D if for all x in D, there is a subset (f y) in fam such that x is in that subset *)
intros x dx.
unfold covering in hcov.
(* We know that for all x in D, there's a subset in the subfamily of fam restricted to D such that x is in that subset *)
simpl in hcov. unfold RF in hcov.
specialize (hcov x dx).
destruct hcov as [ i [ hfam _ ] ].
(* Let i be the index of the subset in the subfamily which contains x. Then because this subset is also in the family, we can use it to show that it contains x too *)
exists i.
exact hfam.
Qed.

(* The index set of a subfamily is included in the index set of the family *)
Goal forall (f:family) (D:R->Prop), included (ind (subfamily f D)) (ind f).
Proof.
intros f D.
simpl.
unfold included.
unfold intersection_domain.
intros x [ h _ ].
exact h.
Qed.

(* The index set of a subfamily is included in the index set of the family *)
Goal forall (f:family) (D:R->Prop) (i:R), included ((subfamily f D) i) (f i).
Proof.
intros f D i.
simpl.
unfold included.
unfold RF.
intros x [ hfix _ ].
exact hfix.
Qed.

Definition empty_set (x:R) := False.

Goal forall (f:family) (D:R->Prop) (i:R), ((subfamily f D) i) =_D (f i) \/ ((subfamily f D) i) =_D empty_set.
Proof.
  intros f D i.
  simpl.
  unfold "=_D".
  unfold included.
  unfold RF.
  unfold empty_set.
  destruct (classic (D i)) as [ di | ndi ].
  {
    left.
    split.
    {
      intros x [ hfix _ ].
      exact hfix.
    }
    {
      intros x hfix.
      split.
      { exact hfix. }
      { exact di. }
    }
  }
  {
    right.
    split.
    {
      intros x [ hfix di ].
      apply ndi.
      exact di.
    }
    {
      intros x false.
      destruct false.
    }
  }
Qed.


Definition is_family (I:R->Prop) (M:R->R->Prop) := forall x, (exists y, M x y) -> I x.

Definition restrict (I:R->Prop) (M:R->R->Prop) (x y:R) := M x y /\ I x.

Lemma yyy : forall  (I I':R->Prop) (M:R->R->Prop), is_family I M -> is_family (intersection_domain I I') (restrict I' M).
Proof.
  intros I I' M h.
  unfold is_family.
  unfold intersection_domain.
  unfold is_family in h.
  intros x h'.
  destruct h' as [ y h' ].
  unfold restrict in h'.
  destruct h' as [ hm hi ].
  specialize (h x).
  split.
  apply h.
  exists y. exact hm.
  exact hi.
Qed.

(* A set X is compact if for every family f which covers X with open sets, there is set D such that the subfamily of f restricted to D covers X
   with finitely many sets *)
Definition compact (X:R -> Prop) : Prop := forall f:family,
    covering_open_set X f ->
    exists D : R -> Prop,
      covering_finite X (subfamily f D).

(* Subfamilies of open sets are families of open sets *)
Lemma family_P1 : forall (f:family) (D:R -> Prop),
  family_open_set f ->
  family_open_set (subfamily f D).
Proof.
  intros f D h.
  unfold family_open_set.
  intros i.
  (* we must show that every set index by i in the subfamily of D is open *)
  unfold family_open_set in h.
  specialize (h i).
  (* we know that every set indexed by i in the family is open *)
  simpl.
  unfold open_set.
  unfold RF at 1.
  unfold open_set in h.
  (*
    We know that every for every x in (f i), x is in a neighbourhood of (f i).
    We must show that for every x such that x is both in (f i) and D, x is a neighbourhood of the set indexed by i in the subfamily.
  *)
  intros x [ hfix di ].
  specialize (h x hfix).
  unfold neighbourhood.
  unfold neighbourhood in h.
  (*
    We know that (f i) is included in a disc centered at x.
    We must show that the set indexed by i in the subfamily is included in a disc centered at x
  *)
  destruct h as [ delta h ].
  exists delta.
  unfold included.
  unfold RF.
  unfold included in h.
  (*
    We know that if y is in the disc centered at x, then y is in the is in (f i).
    We must show that if y is in the disc centered at x, then y is in (f i) and also i is in D.
  *)
  intros y hy.
  specialize (h y hy).
  split.
  { exact h. }
  { exact di. }
Qed.

Definition bounded (D:R -> Prop) : Prop :=
  exists m : R, (exists M : R, (forall x:R, D x -> m <= x <= M)).

Lemma open_set_P6 :
  forall D1 D2:R -> Prop, open_set D1 -> D1 =_D D2 -> open_set D2.
Proof.
  unfold eq_Dom.
  intros A B.
  intros ha hi.
  destruct hi as [hab hba].
  unfold included in hab, hba.
  unfold open_set.
  intros x hx.
  unfold neighbourhood.
  unfold open_set in ha.
  specialize (ha x).
  unfold neighbourhood in ha.
  destruct ha as [ delta ha ].
  apply hba. exact hx.
  exists delta.
  unfold included.
  intros y hy.
  unfold included in ha.
  specialize (ha y hy).
  apply hab.
  exact ha.
Qed.

Lemma family_exists : exists (f:family), True.
Proof.
  assert (forall x : R, (exists _ : R, True) -> no_cond x).
  { unfold no_cond. intros _ _. exact I. }
  exists (mkfamily no_cond (fun _ _ => True) H).
  exact I.
Qed.

Lemma posreal_exists : exists (p:posreal), True.
Proof.
  exists (mkposreal R1 Rlt_0_1).
  exact I.
Qed.

Lemma exists_real : exists x:R, True. 
Proof.
exists R0. exact I.
Qed.

Lemma exists_real_pos : exists x:R, R0 < x.
Proof.
exists R1. exact Rlt_0_1.
Qed.

Lemma posreal_pos : forall x:R, R0 < x -> exists p:posreal, x = p.
Proof.
  intros x hx.
  exists (mkposreal x hx).
  simpl.
  reflexivity.
Qed.

Definition disc_x x y := Rabs y < x.

Lemma disc_x_cond_fam : forall x:R, (exists y, disc_x x y) -> True.
Proof.
  intros x _.
  exact I.
Qed.

Definition disc_fam := mkfamily no_cond disc_x disc_x_cond_fam.

Lemma disc_fam_cover : forall (X:R->Prop), covering X disc_fam.
Proof.
  intros X.
  unfold covering.
  intros x hx.
  simpl.
  unfold disc_x.
  destruct exists_real_pos as [ e he ].
  exists (Rabs x + e).
  pattern (Rabs x) at 1;rewrite <- Rplus_0_r.
  apply Rplus_lt_compat_l.
  exact he.
Qed.

Lemma disc_fam_open_cover : forall (X:R->Prop), covering_open_set X disc_fam.
Proof.
  intros X.
  unfold covering_open_set.
  split.
  { apply disc_fam_cover. }
  {
    unfold family_open_set.
    intro i.
    unfold open_set.
    intro x.
    simpl.
    unfold disc_x at 1.
    intros hxi.
    unfold neighbourhood.

    assert (hpos : R0 < i - Rabs x).
    {
      unfold Rminus.
      eapply Rplus_lt_reg_r.
      rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
      exact hxi.
    }

    destruct (posreal_pos _ hpos) as [ p heq ].
    exists p.
    unfold included.
    intros y.
    unfold disc.
    intro h.
    unfold disc_x.
    rewrite <- heq in *.
    clear heq p.
    apply Rplus_lt_reg_r with (- Rabs x).
    eapply Rle_lt_trans.
    apply Rabs_triang_inv.
    exact h.
  }
Qed.

Lemma max_rlist : forall l : Rlist, exists x, forall y, In y l -> y <= x.
Proof.
  intro l.
  exists (MaxRlist l).
  intros y hy.
  apply MaxRlist_P1.
  exact hy.
Qed.

Lemma compact_P1 : forall X:R -> Prop, compact X -> bounded X.
Proof.
  intros X hc.
  unfold compact in hc.
  specialize (hc disc_fam).
  specialize (hc (disc_fam_open_cover _ )).

  (* This means there is a finite subset D such that f0 restricted to D covers X *)
  destruct hc as [ D hc ].

  unfold covering_finite in hc.
  destruct hc as [ hcov hfam ].
  (* f0|D covers X and f0|D is a finite family *)
  unfold family_finite in hfam.
  unfold domain_finite in hfam.
  (* there's a list such that every indices of f0|D is in the list *)
  destruct hfam as [ l hfam ].

  simpl in *.
  unfold intersection_domain in hfam.
  unfold no_cond in hfam.
  unfold covering in hcov.
  simpl in hcov.
  unfold RF in hcov.
  simpl in hcov.
  unfold disc_x in hcov.

  unfold bounded.

  destruct (max_rlist l) as [r hr].

  exists (- r).
  exists r.
  intros x hx.

  specialize (hcov _ hx).
  destruct hcov as [ y hy ].
  destruct hy as [ hyx hy ].
  specialize (hfam y).

  assert (hid : True /\ D y).
  {
    split.
    { exact I. }
    { exact hy. }
  }

  destruct hfam as [ hfaml _ ].
  specialize (hfaml hid).

  split.
  {
    apply Rabs_def2 in hyx.
    destruct hyx as [ hxy hyx ].
    apply Rle_trans with (-y).
    apply Ropp_le_contravar.
    apply hr.
    exact hfaml.
    left.
    exact hyx.
  }
  {
    apply Rle_trans with y.
    2:{ apply hr. exact hfaml. }
    apply Rle_trans with (Rabs x).
    apply RRle_abs.
    left.
    exact hyx.
  }
Qed.

Definition cP2_fn X x y z := Rabs (y - z) < Rabs (y - x) / R2 /\ X y.

Lemma cP2_cond_fam : forall X x y, (exists z , (cP2_fn X x) y z) -> X y.
Proof.
  intros X x y hy.
  destruct hy as [ z hyz ].
  unfold cP2_fn in hyz.
  destruct hyz as [ _ hy ].
  exact hy.
Qed.

Definition cP2_fam X x := mkfamily X (cP2_fn X x) (cP2_cond_fam X x).

Lemma cP2_tech : forall (X : R -> Prop) (x : R),
  ~ X x -> forall y : R, X y -> R0 < Rabs (y - x) / R2.
Proof.
  intros X x hx y hy.
  apply half_pos.
  apply Rabs_pos_lt.
  apply Rminus_eq_contra.
  intro eq.
  subst y.
  apply hx.
  exact hy.
Qed.

Lemma cP2_open_covering : forall (X : R -> Prop) (x : R),
  ~ X x ->
  covering_open_set X (cP2_fam X x).
Proof.
  intros X x h.
  unfold covering_open_set.
  split.
  {
    unfold covering.
    intros y hy.
    exists y.
    simpl.
    unfold cP2_fn.
    split.
    {
      unfold Rminus.
      rewrite Rplus_opp_r.
      rewrite Rabs_R0.
      eapply cP2_tech.
      apply h.
      exact hy.
    }
    { exact hy. }
  }
  {
    unfold family_open_set.
    simpl.
    intro y.
    destruct  (classic (X y)) as [ hy | hy ].
    {
      assert (h':=cP2_tech).
      specialize (h' _ _ h _ hy).

      set ( ep := mkposreal _ h' ).
      set ( e := pos ep).
      simpl in e.
      assert (eq : e = ep).
      reflexivity.
      clearbody ep.

      apply open_set_P6 with (disc y ep).
      { apply disc_P1. }
      {
        unfold eq_Dom.
        split.
        {
          unfold included.
          unfold disc.
          intros z hzy.
          unfold cP2_fn.
          split.
          {
            fold e.
            rewrite Rabs_minus_sym.
            rewrite eq.
            exact hzy.
          }
          { exact hy. }
        }
        {
          unfold included.
          unfold disc.
          intros z hzy.
          unfold cP2_fn in hzy.
          destruct hzy as [ hzy _ ].
          rewrite Rabs_minus_sym.
          fold e in hzy.
          rewrite eq in hzy.
          exact hzy.
        }
      }
    }
    {
      apply open_set_P6 with empty_set.
      { exact open_set_P4. }
      {
        unfold eq_Dom.
        split.
        {
          unfold included.
          intros z hz.
          unfold empty_set in hz.
          contradiction.
        }
        {
          unfold included.
          intros z hz.
          unfold cP2_fn in hz.
          destruct hz as [ _ hy' ].
          unfold empty_set.
          apply hy.
          exact hy'.
        }
      }
    }
  }
Qed.

Lemma compact_P2 : forall X:R -> Prop, compact X -> closed_set X.
Proof.
  intros X hc.
  apply closed_set_P1.
  unfold eq_Dom.
  split.
  { apply adherence_P1. }
  {
    unfold included.
    unfold adherence.
    unfold point_adherent.
    intros x h.
    unfold compact in hc.
    destruct (classic (X x)) as [ hx | hx ].
    { exact hx. }
    {
      assert ( H2 : forall y:R, X y -> R0 < Rabs (y - x) / R2).
      {
        apply cP2_tech.
        exact hx.
      }

      specialize (hc (cP2_fam X x)).

      assert ( H5 : covering_open_set X (cP2_fam X x)).
      {
        apply cP2_open_covering.
        exact hx.
      }

      specialize (hc H5).
      destruct hc as [ D hc ].
      unfold covering_finite in hc.
      destruct hc as [ hcov hfam ].

      unfold covering in hcov.
      simpl in hcov.

      unfold family_finite in hfam.
      simpl in hfam.

      unfold domain_finite in hfam.
      destruct hfam as [ l hfam ].

      set (m := MinRlist (AbsList l x)).


      assert ( hm : R0 < m).
      {
        clear - H2 hfam.
        unfold m.
        apply MinRlist_P2.
        intros y hy.
        assert (hy' := AbsList_P2 _ _ _ hy).
        destruct hy' as [ z hz ].
        destruct hz as [ hzl heq ].
        subst y.
        apply H2.
        destruct (hfam z) as [ hfaml hfamr ].
        specialize (hfamr hzl).
        unfold intersection_domain in hfaml, hfamr.
        destruct hfamr as [ hxz hdz ].
        exact hxz.
      }

      set( mp := mkposreal _ hm).
      assert ( eqm : m = mp). { reflexivity. }
      clearbody mp.

      specialize (h (disc x mp)).

      assert ( H11 : neighbourhood (disc x mp) x).
      {
        clear.
        unfold neighbourhood.
        exists mp.
        unfold included.
        intros y h.
        exact h.
      }

      specialize (h H11).
      destruct h as [ y h ].
      unfold intersection_domain in h.
      destruct h as [ hxy hy ].

      specialize (hcov _ hy).
      destruct hcov as [ z hcov ].
      unfold RF in hcov.
      destruct hcov as [ hzy hdz ].
      simpl in hzy.
      unfold cP2_fn in hzy.
      destruct hzy as [ hzy hxz ].

      unfold disc in hxy.

      exfalso.
      apply Rlt_irrefl with (Rabs (z-x)).


      apply Rle_lt_trans with (Rabs (z - y) + Rabs (y - x)).
      { apply Rabs_reg. }
      {
        rewrite (double_var (Rabs (z - x))).
        apply Rplus_lt_compat.
        { exact hzy. }
        {
          eapply Rlt_le_trans.
          { apply hxy. }
          {
            rewrite <- eqm.
            apply MinRlist_P1.
            apply AbsList_P1.
            specialize (hfam z).
            destruct hfam as [ hfaml hfamr ].
            apply hfaml.
            unfold intersection_domain.
            split.
            { exact hxz. }
            { exact hdz. }
          }
        }
      }
    }
  }
Qed.

Lemma compact_EMP : compact empty_set.
Proof.
  unfold compact.
  intros f h.
  unfold covering_open_set in h.
  destruct h as [hcov hfam].
  exists empty_set.
  unfold covering_finite.
  split.
  {
    unfold covering.
    unfold empty_set.
    intros x false.
    destruct false.
  }
  {
    unfold family_finite.
    unfold domain_finite.
    simpl.
    exists nil.
    intro x.
    split.
    {
      intro h.
      unfold intersection_domain in h.
      destruct h as [ _ false ].
      unfold empty_set in false.
      destruct false.
    }
    {
      intro h.
      inversion h.
    }
  }
Qed.

Lemma compact_eqDom :
  forall X1 X2:R -> Prop, compact X1 -> X1 =_D X2 -> compact X2.
Proof.
  intros A B.
  intros hA heq.
  unfold eq_Dom in heq.

  destruct heq as [ hiab hiba ].
  unfold included in hiab, hiba.
  unfold compact in hA.
  unfold compact.
  intros f hf.
  specialize (hA f).
  destruct hA as [ D hcovf ].
  unfold covering_open_set.
  unfold covering_open_set in hf.
  destruct hf as [ hcov hfam ].
  {
    split.
    {
      unfold covering.
      intros x ax.
      unfold covering in hcov.
      apply hiab in ax.
      specialize (hcov _ ax).
      destruct hcov as [ y hy ].
      exists y.
      exact hy.
    }
    { exact hfam. }
  }
  {
    exists D.
    unfold covering_finite.
    unfold covering_finite in hcovf.
    destruct hcovf as [ hl hr ].
    split.
    {
      unfold covering.
      simpl.
      intros x bx.
      apply hiba in bx.
      unfold covering in hl.
      specialize (hl _ bx).
      destruct hl as [ y hy ].
      exists y.
      simpl in hy.
      exact hy.
    }
    { exact hr. }
  }
Qed.

Definition closed_interval a b c := a <= c <= b.

Definition AP3 a b fa x := a <= x <= b /\
  (exists D : R -> Prop,
      covering_finite (closed_interval a x) (subfamily fa D)
  ).

Lemma ab_aab : forall a b, a <= b -> a <= a <= b.
Proof.
  intros a b h.
  split.
  { right. reflexivity. }
  { exact h. }
Qed.

Lemma aab_ab : forall a b, a <= a <= b -> a <= b .
Proof.
  intros a b h.
  destruct h;assumption.
Qed.

Definition complete A := {m : R | is_lub A m }.

(* Borel-Lebesgue lemma *)
Lemma compact_P3 : forall a b:R, compact (closed_interval a b).
Proof.
  intros a b.

  destruct (Rle_dec a b) as [ hab | hab ].
  { (* a <= b *)
    unfold compact.
    intros fam h.
    unfold covering_open_set in h.
    destruct h as [ hcov hfam ].

    unfold covering in hcov.
    unfold closed_interval in hcov.

    set (A := AP3 a b fam).
    unfold AP3 in A.

    assert (haa: A a).
    {
      clear - hab hcov.
      unfold A. clear A.
      split.
      { apply ab_aab. exact hab. }
      {
        apply ab_aab in hab.
        specialize (hcov _ hab). clear hab.

        destruct hcov as [ x hx ].
        set (D := eq x).
        exists D.
        unfold covering_finite.
        split.
        {
          unfold covering.
          simpl.
          unfold D.
          clear D.
          unfold closed_interval.
          intros y hy.
          assert( H4 :  y = a).
          {
            clear - hy.
            destruct hy as [ hay hya ].
            apply Rle_antisym;assumption.
          }
          subst y. clear hy.
          exists x.
          split.
          { exact hx. }
          { reflexivity. }
        }
        {
          unfold family_finite.
          simpl.
          unfold domain_finite.
          unfold intersection_domain.
          unfold D.
          clear D.
          exists (cons x nil).
          simpl.
          intro y.
          split.
          {
            intros [_ eq].
            subst y.
            left.
            reflexivity.
          }
          {
            intros [ eq | false ].
            {
              subst y.
              split.
              {
                apply cond_fam.
                exists a.
                exact hx.
              }
              { reflexivity. }
            }
            { destruct false. }
          }
        }
      }
    }

    assert (hcomplete : complete A).
    {
      apply completeness.
      {
        clear.
        unfold bound.
        exists b.
        unfold is_upper_bound.
        intros x h.
        unfold A in h.
        destruct h as [ [ _ h ] _ ].
        exact h.
      }
      { exists a. exact haa. }
    }

    destruct hcomplete as [ m hlub ].

    unfold is_lub in hlub.
    destruct hlub as [ hub hubl ].

    assert ( hm : a <= m <= b).
    {
      clear - hub hubl haa.
      unfold is_upper_bound in hub.
      split.
      {
        apply hub.
        exact haa.
      }
      {
        apply hubl.
        unfold is_upper_bound.
        intros x hax.
        unfold A in hax.
        destruct hax as [ [ _ hax ] _ ].
        exact hax.
      }
    }

    specialize (hcov _ hm).
    destruct hcov as [xm hxm].

    unfold family_open_set in hfam.
    unfold open_set in hfam.
    specialize (hfam _ _ hxm).
    unfold neighbourhood in hfam.
    destruct hfam as [ delta hfam ].

    assert (h : exists x : R, A x /\ m - delta < x <= m).
    {
      clear - hub hubl.
      destruct (classic (exists x : R, A x /\ m - delta < x <= m)) as [ H9 | H9 ].
      { exact H9. }
      {
        assert (H12 : is_upper_bound A (m - delta)).
        {
          clear - H9 hub hubl.
          set (P := fun n:R => A n /\ m - delta < n <= m).
          fold P in H9.

          unfold is_upper_bound.
          intros x H13.

          (* === apply H12 in H9 === *)
          assert( H12 := not_ex_all_not).
          specialize (H12 _ P H9).
          clear H9. rename H12 into H9.

          specialize (H9 x).
          apply not_and_or in H9.
          destruct H9 as [ H15 | H15 ].
          {
            exfalso.
            apply H15.
            exact H13.
          }
          {
            apply not_and_or in H15.
            destruct H15 as [H15|H15].
            {
              destruct (Rle_dec x (m - delta)) as [H17|H17].
              { exact H17. }
              {
                exfalso.
                apply H15.
                apply Rnot_le_lt.
                exact H17.
              }
            }
            {
              unfold is_upper_bound in hub.
              specialize (hub _ H13).
              exfalso.
              apply H15.
              exact hub.
            }
          }
        }

        specialize (hubl _ H12).

        exfalso.
        eapply Rlt_irrefl.
        eapply Rle_lt_trans.
        { exact hubl. }
        {
          pattern m at 2; rewrite <- Rplus_0_r.
          unfold Rminus.
          apply Rplus_lt_compat_l.
          apply Ropp_lt_cancel.
          rewrite Ropp_involutive.
          rewrite Ropp_0.
          apply cond_pos.
        }
      }
    }

    destruct h as [ x [ hax [ Hltx _ ] ] ].
    unfold A in hax.
    destruct hax as [ H9 [ Dx hcovf ] ].
    unfold covering_finite in hcovf.
    destruct hcovf as [ H12 H13 ].

    destruct (Req_dec m b) as [ hmb | hmb ].
    {
      subst m.
      set (Db := fun x:R => Dx x \/ x = xm).
      exists Db.
      unfold covering_finite.
      split.
      {
        unfold covering.
        intros x0 (H14,H18).
        unfold covering in H12.
        destruct (Rle_dec x0 x) as [Hle'|Hnle'].
        {
          assert (H15 : a <= x0 <= x).
          {
            split.
            { exact H14. }
            { exact Hle'. }
          }

          specialize (H12 _ H15).
          simpl in H12.
          destruct H12 as [ x1 [ H16 H17 ] ].
          exists x1.
          simpl.
          unfold Db.
          split.
          { apply H16. }
          {
            left.
            apply H17.
          }
        }
        {
          exists xm.
          simpl.
          split.
          {
            apply hfam.
            unfold disc.
            rewrite <- Rabs_Ropp, Ropp_minus_distr, Rabs_right.
            {
              apply Rlt_trans with (b - x).
              {
                unfold Rminus.
                apply Rplus_lt_compat_l.
                apply Ropp_lt_contravar.
                apply Rnot_le_lt.
                exact Hnle'.
              }
              {
                apply Rplus_lt_reg_l with (x - delta).
                replace (x - delta + (b - x)) with (b - delta).
                {
                  unfold Rminus.
                  rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                  apply Hltx.
                }
                {
                  unfold Rminus.
                  symmetry.
                  rewrite Rplus_comm.
                  repeat rewrite <- Rplus_assoc.
                  apply Rplus_eq_compat_r.
                  rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                  reflexivity.
                }
              }
            }
            {
              unfold Rminus.
              eapply Rplus_le_reg_r.
              rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
              exact H18.
            }
          }
          {
            unfold Db.
            right.
            reflexivity.
          }
        }
      }
      {
        unfold family_finite.
        unfold domain_finite.
        unfold family_finite in H13.
        unfold domain_finite in H13.
        destruct H13 as (l,H13).
        exists (cons xm l).
        intro x0.
        split.
        {
          intro H14.
          simpl in H14.
          unfold intersection_domain in H14.
          specialize H13 with x0.
          destruct H13 as [ H13 H15].
          destruct (Req_dec x0 xm) as [ H16 | H16 ].
          {
            simpl.
            left.
            apply H16.
          }
          {
            simpl.
            right.
            apply H13.
            simpl.
            unfold intersection_domain.
            unfold Db in H14.
            destruct H14 as [ H7 [ H11 | H11 ] ].
            {
              split.
              { exact H7. }
              { exact H11. }
            }
            {
              exfalso.
              apply H16.
              exact H11.
            }
          }
        }
      {
        intro H14.
        simpl in H14.
        destruct H14 as [ H15 | H15 ].
        {
          simpl.
          unfold intersection_domain.
          {
            split.
            {
              apply cond_fam.
              rewrite H15.
              exists b.
              apply hxm.
            }
            {
              unfold Db.
              right.
              exact H15.
            }
          }
        }
        {
          simpl.
          unfold intersection_domain.
          specialize (H13 x0).
          destruct H13 as [ _ H16 ].
          specialize (H16 H15).
          simpl in H16.
          unfold intersection_domain in H16.
          split.
          { apply H16. }
          {
            unfold Db.
            left.
            apply H16.
          }
        }
      }
    }
  }
  {
  set (m' := Rmin (m + delta / R2) b).
  cut (A m').
  {
    intro H7.
    unfold is_upper_bound in hub.
    {
      specialize (hub _ H7).
      cut (m < m').
      {
        intro H17.
        exfalso.
        eapply Rlt_irrefl.
        eapply Rle_lt_trans.
        { exact hub. }
        { exact H17. }
      }
      {
        unfold m'.
        unfold Rmin.
        destruct (Rle_dec (m + delta / R2) b) as [Hle'|Hnle'].
        {
          pattern m at 1; rewrite <- Rplus_0_r.
          apply Rplus_lt_compat_l.
          unfold Rdiv.
          apply Rmult_lt_0_compat.
          { apply cond_pos. }
          {
            apply Rinv_0_lt_compat.
            exact Rlt_0_2.
          }
        }
        {
          destruct hm as [ _  [ H4 | H4 ] ].
          { exact H4. }
          {
            exfalso.
            apply hmb.
            exact H4.
          }
        }
      }
    }
  }
  {
    unfold A.
    split.
    {
      split.
      {
        apply Rle_trans with m.
        { apply hm. }
        {
          unfold m'.
          unfold Rmin.
          destruct (Rle_dec (m + delta / R2) b) as [ r | _ ].
          {
            pattern m at 1; rewrite <- Rplus_0_r.
            apply Rplus_le_compat_l.
            left.
            unfold Rdiv.
            apply Rmult_lt_0_compat.
            {
              apply cond_pos.
            }
            {
              apply Rinv_0_lt_compat.
              exact Rlt_0_2.
            }
          }
          { apply hm. }
        }
      }
      {
        unfold m'.
        apply Rmin_r.
      }
    }
    {
      set (Db := fun x:R => Dx x \/ x = xm).
      exists Db.
      unfold covering_finite.
      split.
      {
        unfold covering.
        intros x0 [H14 H18].
        unfold covering in H12.
        destruct (Rle_dec x0 x) as [Hle'|Hnle'].
        {
          cut (a <= x0 <= x).
          {
            intro H15.
            pose proof (H12 x0 H15) as (x1 & H16 & H17).
            exists x1.
            simpl.
            unfold Db.
            split.
            { apply H16. }
            {
              left.
              apply H17.
            }
          }
          {
            split.
            { exact H14. }
            { exact Hle'. }
          }
        }
        {
          exists xm.
          simpl.
          split.
          {
            apply hfam.
            unfold disc.
            unfold Rabs.
            destruct (Rcase_abs (x0 - m)) as [Hlt|Hge].
            {
              rewrite Ropp_minus_distr.
              apply Rlt_trans with (m - x).
              {
                unfold Rminus.
                apply Rplus_lt_compat_l.
                apply Ropp_lt_contravar.
                apply Rnot_le_lt.
                exact Hnle'.
              }
              {
                apply Rplus_lt_reg_l with (x - delta).
                replace (x - delta + (m - x)) with (m - delta).
                {
                  replace (x - delta + delta) with x.
                  {
                    exact Hltx.
                  }
                  {
                    unfold Rminus.
                    rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                    reflexivity.
                  }
                }
                {
                  unfold Rminus.
                  symmetry.
                  rewrite Rplus_comm.
                  repeat rewrite <- Rplus_assoc.
                  apply Rplus_eq_compat_r.
                  rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                  reflexivity.
                }
              }
            }
            {
              apply Rle_lt_trans with (m' - m).
              {
                unfold Rminus.
                do 2 rewrite <- (Rplus_comm (- m)).
                apply Rplus_le_compat_l.
                exact H18.
              }
              {
                apply Rplus_lt_reg_l with m.
                replace (m + (m' - m)) with m'.
                {
                  apply Rle_lt_trans with (m + delta / R2).
                  {
                    unfold m'.
                    apply Rmin_l.
                  }
                  {
                    apply Rplus_lt_compat_l; apply Rmult_lt_reg_l with R2.
                    {
                      exact Rlt_0_2.
                    }
                    {
                      unfold Rdiv.
                      rewrite <- (Rmult_comm (/ R2)).
                      rewrite <- Rmult_assoc.
                      rewrite <- Rinv_r_sym.
                      {
                        rewrite Rmult_1_l.
                        pattern (pos delta) at 1; rewrite <- Rplus_0_r.
                        rewrite double.
                        apply Rplus_lt_compat_l.
                        apply cond_pos.
                      }
                      { exact Neq_2_0. }
                    }
                  }
                }
                {
                  rewrite Rplus_comm.
                  unfold Rminus.
                  rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
                  reflexivity.
                }
              }
            }
          }
          {
            unfold Db.
            right.
            reflexivity.
          }
        }
      }
      {
        unfold family_finite.
        unfold domain_finite.
        unfold family_finite in H13.
        unfold domain_finite in H13.
        destruct H13 as (l,H13).
        exists (cons xm l).
        intro x0.
        split.
        {
          intro H14.
          simpl in H14.
          unfold intersection_domain in H14.
          specialize (H13 x0).
          destruct H13 as [H13 H15].
          destruct (Req_dec x0 xm) as [Heq|Hneq].
          {
            simpl.
            left.
            apply Heq.
          }
          {
            simpl.
            right.
            apply H13.
            simpl.
            unfold intersection_domain.
            unfold Db in H14.
            decompose [and or] H14.
            {
              split.
              { exact H. }
              { exact H1. }
            }
            {
              exfalso.
              apply Hneq.
              exact H1.
            }
          }
        }
        {
          intros [ H15 | H15 ].
          {
            split.
            {
              apply cond_fam.
              rewrite H15.
              exists m.
              exact hxm.
            }
            {
              unfold Db.
              right.
              exact H15.
            }
          }
          {
            specialize (H13 x0).
            destruct H13 as [ _ H16 ].
            {
              assert (H17 := H16 H15).
              simpl in H17.
              unfold intersection_domain in H17.
              split.
              {
                destruct H17 as [H7 H10].
                exact H7.
              }
              {
                unfold Db.
                left.
                elim H17.
                intros H7 H10.
                exact H10.
              }
            }
          }
        }
      }
    }
  }
}
}

  {
    apply compact_eqDom with empty_set.
    { exact compact_EMP. }
    {
      unfold eq_Dom.
      unfold included.
      unfold empty_set.
      split.
      {
        intros x false.
        destruct false.
      }
      {
        intro x.
        unfold closed_interval.
        intros [ hax hxb ].
        apply hab.
        eapply Rle_trans.
        { exact hax. }
        { exact hxb. }
      }
    }
  }
Qed.

Definition cond_fam_gen (D:R->Prop) (f:R->R->Prop) := forall x, (exists y, f x y) -> D x.

Definition fun_P4 (f0:family) (F:R->Prop) (x y:R) := f0 x y \/ complementary F y /\ (ind f0) x.

Lemma cond_fam_P4 : forall (f0:family) (F:R->Prop) , cond_fam_gen (ind f0) (fun_P4 f0 F).
Proof.
  intros f0 F.
  unfold cond_fam_gen.
  intros x h.
  destruct h as [ y h ].
  unfold fun_P4 in h.
  destruct h as [ h | h ].
  {
    apply cond_fam.
    exists y.
    exact h.
  }
  {
    destruct h as [ _ h ].
    exact h.
  }
Qed.

Definition fam_P4 f0 F := mkfamily
  (ind f0)
  (fun_P4 f0 F)
  (cond_fam_P4 f0 F).

Lemma lem_P4 : 
forall X F : R -> Prop,
open_set (complementary F) ->
forall f0 : family,
covering_open_set F f0 ->
(exists z : R, F z) ->
covering_open_set X (fam_P4 f0 F).
Proof.
  intros X F.
  intros hco fam hcov hnot_empty.
  unfold covering_open_set.
  unfold covering_open_set in hcov.
  destruct hcov as [ H2 H4 ].
  split.
  {
    clear - H2 hnot_empty.
    unfold covering.
    unfold covering in H2.
    intros x H5.
    destruct (classic (F x)) as [ H6 | H6 ].
    {
      clear - H2 H6.
      specialize (H2 _ H6).
      destruct H2 as [y0 H7].
      exists y0.
      simpl.
      unfold fun_P4.
      left.
      exact H7.
    }
    {
      cut (exists z : R, (ind fam) z).
      {
        clear - H6.
        intro H7.
        destruct H7 as [x0 H7].
        exists x0.
        simpl.
        unfold fun_P4.
        right.
        split.
        {
          clear - H6.
          unfold complementary.
          exact H6.
        }
        {
          clear - H7.
          exact H7.
        }
      }
      {
        clear - hnot_empty H2.
        destruct hnot_empty as [z0 H7].
        specialize (H2 _ H7).
        destruct H2 as [ t H8 ].
        exists t.
        apply cond_fam.
        exists z0.
        exact H8.
      }
    }
  }
  {
    clear - hco H4.
    unfold family_open_set.
    intro x.
    simpl.
    unfold fun_P4.
    destruct (classic ((ind fam) x)) as [ H5 | H5].
    {
      clear - hco H4 H5.
      apply open_set_P6 with (union_domain (fam x) (complementary F)).
      {
        clear - hco H4.
        apply open_set_P2.
        {
          clear - H4.
          unfold family_open_set in H4.
          apply H4.
        }
        {
          clear - hco.
          exact hco.
        }
      }
      {
        clear - H5.
        unfold eq_Dom.
        unfold included.
        unfold union_domain.
        unfold complementary.
        split.
        {
          clear - H5.
          intros y h.
          destruct h as [ h | h ].
          {
            left.
            exact h.
          }
          {
            right.
            split.
            { exact h. }
            { exact H5. }
          }
        }
        {
          clear.
          intros y h.
          destruct h as [ h | h ].
          {
            left.
            apply h.
          }
          {
            right.
            destruct h as [ h _ ].
            exact h.
          }
        }
      }
    }
    {
      clear - H4 H5.
      apply open_set_P6 with (fam x).
      {
        clear - H4.
        unfold family_open_set in H4.
        apply H4.
      }
      {
        clear - H5.
        unfold eq_Dom.
        split.
        {
          clear.
          unfold included.
          unfold complementary.
          intros y hfxy.
          left.
          exact hfxy.
        }
        {
          clear - H5.
          unfold included.
          unfold complementary.
          intros x0 H6.
          destruct H6 as [ H7 | H7 ].
          {
            clear - H7.
            apply H7.
          }
          {
            clear - H7 H5.
            destruct H7 as [ _ H7 ].
            exfalso.
            apply H5.
            exact H7.
          }
        }
      }
    }
  }
Qed.


Lemma compact_P4 :
  forall X F:R -> Prop, compact X -> closed_set F -> included F X -> compact F.
Proof.
  unfold compact.
  intros X F H H0 H1 f0 H2.
  destruct (classic (exists z : R, F z)) as [ Hyp_F_NE | Hyp_F_NE ].
  {
    set (D := ind f0).
    set (g := f f0).

    unfold closed_set in H0.
    set (g' := fun x y:R => f0 x y \/ complementary F y /\ D x).
    cut (forall x:R, (exists y : R, g' x y) -> D x).
    {
      intro H3.

      set (f' := mkfamily D g' H3).

      cut (covering_open_set X f').
      {
        intro H4. clear H4.
        assert( lp := lem_P4).
        specialize (lp X F).
        specialize (lp H0).
        specialize (lp f0).
        specialize (lp H2).
        specialize (lp Hyp_F_NE).
        clear - H H1 lp.
        specialize (H _ lp).
        clear lp.
        destruct H as [ DX H5 ].
        exists DX.
        unfold covering_finite.
        unfold covering_finite in H5.
        destruct H5 as [ H H5 ].
        split.
        {
          clear - H H1.
          unfold covering.
          unfold covering in H.
          intros x H7.
          specialize (H1 _ H7).
          specialize (H _ H1).
          destruct H as [ y0 H8 ].
          exists y0.
          simpl in H8.
          unfold RF in H8.
          simpl in H8.
          simpl.
          destruct H8 as [ H8 H5 ].
          split.
          {
            clear - H7 H8.
            unfold fun_P4 in H8.
            destruct H8 as [ H10 | H10 ].
            {
              clear - H10.
              exact H10.
            }
            {
              clear - H10 H7.
              destruct H10 as [ H11 _ ].
              unfold complementary in H11.
              exfalso.
              apply H11.
              exact H7.
            }
          }
          {
            clear - H5.
            exact H5.
          }
        }
        {
          clear - H5.
          unfold family_finite.
          unfold domain_finite.
          unfold family_finite in H5.
          unfold domain_finite in H5.
          destruct H5 as [ l H6 ].
          exists l.
          intro x.
          specialize (H6 x).
          destruct H6 as [ H7 H8 ].
          split.
          {
            clear - H7.
            intro H9.
            apply H7.
            simpl.
            unfold intersection_domain.
            simpl in H9.
            unfold intersection_domain in H9.
            apply H9.
          }
          {
            clear - H8.
            intro H9.
            assert (H10 := H8 H9).
            simpl in H10.
            unfold intersection_domain in H10.
            simpl.
            unfold intersection_domain.
            apply H10.
          }
        }
      }
      {
        clear - H2 Hyp_F_NE H0.

        revert f'.
        revert H3.
        revert g'.
        revert D.
        revert Hyp_F_NE.
        revert H2.
        revert f0.
        revert H0.
        revert F.
        revert X.

        intros X F H0 f0 H2 Hyp_F_NE D g' H3 f'.

        unfold covering_open_set.
        unfold covering_open_set in H2.
        destruct H2 as [ H2 H4 ].
        split.
        {
          clear - H2 Hyp_F_NE.
          unfold covering.
          unfold covering in H2.
          intros x H5.
          destruct (classic (F x)) as [ H6 | H6 ].
          {
            clear - H2 H6.
            specialize (H2 _ H6).
            destruct H2 as [y0 H7].
            exists y0.
            simpl.
            unfold g'.
            left.
            exact H7.
          }
          {
            cut (exists z : R, D z).
            {
              clear - H6.
              intro H7.
              destruct H7 as [x0 H7].
              exists x0.
              simpl.
              unfold g'.
              right.
              split.
              {
                clear - H6.
                unfold complementary.
                exact H6.
              }
              {
                clear - H7.
                exact H7.
              }
            }
            {
              clear - Hyp_F_NE H2.
              destruct Hyp_F_NE as [z0 H7].
              specialize (H2 _ H7).
              destruct H2 as [ t H8 ].
              exists t.
              apply cond_fam.
              exists z0.
              exact H8.
            }
          }
        }
        {
          clear - H0 H4.
          unfold family_open_set.
          intro x.
          simpl.
          unfold g'.
          destruct (classic (D x)) as [ H5 | H5].
          {
            clear - H0 H4 H5.
            apply open_set_P6 with (union_domain (f0 x) (complementary F)).
            {
              clear - H0 H4.
              apply open_set_P2.
              {
                clear - H4.
                unfold family_open_set in H4.
                apply H4.
              }
              {
                clear - H0.
                exact H0.
              }
            }
            {
              clear - H5.
              unfold eq_Dom.
              unfold included.
              unfold union_domain.
              unfold complementary.
              split.
              {
                clear - H5.
                intros y h.
                destruct h as [ h | h ].
                {
                  left.
                  exact h.
                }
                {
                  right.
                  split.
                  { exact h. }
                  { exact H5. }
                }
              }
              {
                clear.
                intros y h.
                destruct h as [ h | h ].
                {
                  left.
                  apply h.
                }
                {
                  right.
                  destruct h as [ h _ ].
                  exact h.
                }
              }
            }
          }
          {
            clear - H4 H5.
            apply open_set_P6 with (f0 x).
            {
              clear - H4.
              unfold family_open_set in H4.
              apply H4.
            }
            {
              clear - H5.
              unfold eq_Dom.
              split.
              {
                clear.
                unfold included.
                unfold complementary.
                intros y hfxy.
                left.
                exact hfxy.
              }
              {
                clear - H5.
                unfold included.
                unfold complementary.
                intros x0 H6.
                destruct H6 as [ H7 | H7 ].
                {
                  clear - H7.
                  apply H7.
                }
                {
                  clear - H7 H5.
                  destruct H7 as [ _ H7 ].
                  exfalso.
                  apply H5.
                  exact H7.
                }
              }
            }
          }
        }
      }
    }
    {
      clear.
      intros x hex.
      destruct hex as [y hy].
      unfold g' in hy.
      destruct hy as [ hy | hy ].
      {
        clear - hy.
        apply cond_fam.
        exists y.
        exact hy.
      }
      {
        clear - hy.
        destruct hy as [ _ hy ].
        unfold D.
        exact hy.
      }
    }
  }
  {
    clear - H2 Hyp_F_NE.
    cut (compact F).
    {
      clear - H2.
      intro hcompact.
      unfold compact in hcompact.
      apply hcompact.
      exact H2.
    }
    {
      clear - Hyp_F_NE.
      apply compact_eqDom with empty_set.
      {
        clear.
        apply compact_EMP.
      }
      {
        clear - Hyp_F_NE.
        unfold eq_Dom.
        split.
        {
          clear.
          unfold included.
          intros x empty.
          unfold empty_set in empty.
          destruct empty.
        }
        {
          clear - Hyp_F_NE.
          assert (H3 := not_ex_all_not _ _ Hyp_F_NE) ; clear Hyp_F_NE ; rename H3 into Hyp_F_NE.
          unfold included.
          intros x hfx.
          unfold empty_set.
          apply Hyp_F_NE with x.
          exact hfx.
        }
      }
    }
  }
Qed.

(**********)
Lemma compact_P5 : forall X:R -> Prop, closed_set X -> bounded X -> compact X.
Proof.
  intros; unfold bounded in H0.
  elim H0; clear H0; intros m H0.
  elim H0; clear H0; intros M H0.
  assert (H1 := compact_P3 m M).
  apply (compact_P4 (fun c:R => m <= c <= M) X H1 H H0).
Qed.

(**********)
Lemma compact_carac :
  forall X:R -> Prop, compact X <-> closed_set X /\ bounded X.
Proof.
  intro; split.
  intro; split; [ apply (compact_P2 _ H) | apply (compact_P1 _ H) ].
  intro; elim H; clear H; intros; apply (compact_P5 _ H H0).
Qed.

Definition image_dir (f:R -> R) (D:R -> Prop) (x:R) : Prop :=
  exists y : R, x = f y /\ D y.

(**********)
Lemma continuity_compact :
  forall (f:R -> R) (X:R -> Prop),
    (forall x:R, continuity_pt f x) -> compact X -> compact (image_dir f X).
Proof.
  unfold compact; intros; unfold covering_open_set in H1.
  elim H1; clear H1; intros.
  set (D := ind f1).
  set (g := fun x y:R => image_rec f0 (f1 x) y).
  cut (forall x:R, (exists y : R, g x y) -> D x).
  intro; set (f' := mkfamily D g H3).
  cut (covering_open_set X f').
  intro; elim (H0 f' H4); intros D' H5; exists D'.
  unfold covering_finite in H5; elim H5; clear H5; intros;
    unfold covering_finite; split.
  unfold covering, image_dir; simpl; unfold covering in H5;
    intros; elim H7; intros y H8; elim H8; intros; assert (H11 := H5 _ H10);
      simpl in H11; elim H11; intros z H12; exists z; unfold g in H12;
        unfold image_rec in H12; rewrite H9; apply H12.
  unfold family_finite in H6; unfold domain_finite in H6;
    unfold family_finite; unfold domain_finite;
      elim H6; intros l H7; exists l; intro; elim (H7 x);
        intros; split; intro.
  apply H8; simpl in H10; simpl; apply H10.
  apply (H9 H10).
  unfold covering_open_set; split.
  unfold covering; intros; simpl; unfold covering in H1;
    unfold image_dir in H1; unfold g; unfold image_rec;
      apply H1.
  exists x; split; [ reflexivity | apply H4 ].
  unfold family_open_set; unfold family_open_set in H2; intro;
    simpl; unfold g;
      cut ((fun y:R => image_rec f0 (f1 x) y) = image_rec f0 (f1 x)).
  intro; rewrite H4.
  apply (continuity_P2 f0 (f1 x) H (H2 x)).
  reflexivity.
  intros; apply (cond_fam f1); unfold g in H3; unfold image_rec in H3; elim H3;
    intros; exists (f0 x0); apply H4.
Qed.

Lemma prolongement_C0 :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall c:R, a <= c <= b -> continuity_pt f c) ->
    exists g : R -> R,
      continuity g /\ (forall c:R, a <= c <= b -> g c = f c).
Proof.
  intros; elim H; intro.
  set
    (h :=
      fun x:R =>
        match Rle_dec x a with
          | left _ => f0 a
          | right _ =>
            match Rle_dec x b with
              | left _ => f0 x
              | right _ => f0 b
            end
        end).
  assert (H2 : R0 < b - a).
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
assumption.
  exists h; split.
  unfold continuity; intro; case (Rtotal_order x a); intro.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      simpl; unfold R_dist; intros; exists (a - x);
        split.
  change (R0 < a - x).
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
assumption.
  intros; elim H5; clear H5; intros _ H5; unfold h.
  case (Rle_dec x a) as [|[]].
  case (Rle_dec x0 a) as [|[]].
  unfold Rminus; rewrite Rplus_opp_r, Rabs_R0; assumption.
  left; apply Rplus_lt_reg_l with (- x);
    do 2 rewrite (Rplus_comm (- x)); apply Rle_lt_trans with (Rabs (x0 - x)).
  apply RRle_abs.
  assumption.
  left; assumption.
  elim H3; intro.
  assert (H5 : a <= a <= b).
  split; [ right; reflexivity | left; assumption ].
  assert (H6 := H0 _ H5); unfold continuity_pt in H6; unfold continue_in in H6;
    unfold limit1_in in H6; unfold limit_in in H6; simpl in H6;
      unfold R_dist in H6; unfold continuity_pt;
        unfold continue_in; unfold limit1_in;
          unfold limit_in; simpl; unfold R_dist;
            intros; elim (H6 _ H7); intros; exists (Rmin x0 (b - a));
              split.
  unfold Rmin; case (Rle_dec x0 (b - a)); intro.
  elim H8; intros; assumption.
  change (R0 < b - a).
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
assumption.
  intros; elim H9; clear H9; intros _ H9; cut (x1 < b).
  intro; unfold h; case (Rle_dec x a) as [|[]].
  case (Rle_dec x1 a) as [Hlta|Hnlea].
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
  case (Rle_dec x1 b) as [Hleb|[]].
  elim H8; intros; apply H12; split.
  unfold D_x, no_cond; split.
  trivial.
  red; intro; elim Hnlea; right; symmetry ; assumption.
  apply Rlt_le_trans with (Rmin x0 (b - a)).
  rewrite H4 in H9; apply H9.
  apply Rmin_l.
  left; assumption.
  right; assumption.
  apply Rplus_lt_reg_l with (- a); do 2 rewrite (Rplus_comm (- a));
    rewrite H4 in H9; apply Rle_lt_trans with (Rabs (x1 - a)).
  apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (b - a)).
  assumption.
  apply Rmin_r.
  case (Rtotal_order x b); intro.
  assert (H6 : a <= x <= b).
  split; left; assumption.
  assert (H7 := H0 _ H6); unfold continuity_pt in H7; unfold continue_in in H7;
    unfold limit1_in in H7; unfold limit_in in H7; simpl in H7;
      unfold R_dist in H7; unfold continuity_pt;
        unfold continue_in; unfold limit1_in;
          unfold limit_in; simpl; unfold R_dist;
            intros; elim (H7 _ H8); intros; elim H9; clear H9;
              intros.
  assert (H11 : R0 < x - a).
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
assumption.
  assert (H12 : R0 < b - x).
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
assumption.
  exists (Rmin x0 (Rmin (x - a) (b - x))); split.
  unfold Rmin; case (Rle_dec (x - a) (b - x)) as [Hle|Hnle].
  case (Rle_dec x0 (x - a)) as [Hlea|Hnlea].
  assumption.
  assumption.
  case (Rle_dec x0 (b - x)) as [Hleb|Hnleb].
  assumption.
  assumption.
  intros x1 (H13,H14); cut (a < x1 < b).
  intro; elim H15; clear H15; intros; unfold h; case (Rle_dec x a) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle H4)).
  case (Rle_dec x b) as [|[]].
  case (Rle_dec x1 a) as [Hle0|].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle0 H15)).
  case (Rle_dec x1 b) as [|[]].
  apply H10; split.
  assumption.
  apply Rlt_le_trans with (Rmin x0 (Rmin (x - a) (b - x))).
  assumption.
  apply Rmin_l.
  left; assumption.
  left; assumption.
  split.
  apply Ropp_lt_cancel; apply Rplus_lt_reg_l with x;
    apply Rle_lt_trans with (Rabs (x1 - x)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (Rmin (x - a) (b - x))).
  assumption.
  apply Rle_trans with (Rmin (x - a) (b - x)).
  apply Rmin_r.
  apply Rmin_l.
  apply Rplus_lt_reg_l with (- x); do 2 rewrite (Rplus_comm (- x));
    apply Rle_lt_trans with (Rabs (x1 - x)).
  apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (Rmin (x - a) (b - x))).
  assumption.
  apply Rle_trans with (Rmin (x - a) (b - x)); apply Rmin_r.
  elim H5; intro.
  assert (H7 : a <= b <= b).
  split; [ left; assumption | right; reflexivity ].
  assert (H8 := H0 _ H7); unfold continuity_pt in H8; unfold continue_in in H8;
    unfold limit1_in in H8; unfold limit_in in H8; simpl in H8;
      unfold R_dist in H8; unfold continuity_pt;
        unfold continue_in; unfold limit1_in;
          unfold limit_in; simpl; unfold R_dist;
            intros; elim (H8 _ H9); intros; exists (Rmin x0 (b - a));
              split.
  unfold Rmin; case (Rle_dec x0 (b - a)); intro.
  elim H10; intros; assumption.
  change (R0 < b - a).
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
assumption.
  intros; elim H11; clear H11; intros _ H11; cut (a < x1).
  intro; unfold h; case (Rle_dec x a) as [Hlea|Hnlea].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hlea H4)).
  case (Rle_dec x1 a) as [Hlea'|Hnlea'].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hlea' H12)).
  case (Rle_dec x b) as [Hleb|Hnleb].
  case (Rle_dec x1 b) as [Hleb'|Hnleb'].
  rewrite H6; elim H10; intros; destruct Hleb'.
  apply H14; split.
  unfold D_x, no_cond; split.
  trivial.
  red; intro; rewrite <- H16 in H15; elim (Rlt_irrefl _ H15).
  rewrite H6 in H11; apply Rlt_le_trans with (Rmin x0 (b - a)).
  apply H11.
  apply Rmin_l.
  rewrite H15; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    assumption.
  rewrite H6; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    assumption.
  elim Hnleb; right; assumption.
  rewrite H6 in H11; apply Ropp_lt_cancel; apply Rplus_lt_reg_l with b;
    apply Rle_lt_trans with (Rabs (x1 - b)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply RRle_abs.
  apply Rlt_le_trans with (Rmin x0 (b - a)).
  assumption.
  apply Rmin_r.
  unfold continuity_pt; unfold continue_in;
    unfold limit1_in; unfold limit_in;
      simpl; unfold R_dist; intros; exists (x - b);
        split.
  change (R0 < x - b).
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
assumption.
  intros; elim H8; clear H8; intros.
  assert (H10 : b < x0).
  apply Ropp_lt_cancel; apply Rplus_lt_reg_l with x;
    apply Rle_lt_trans with (Rabs (x0 - x)).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply RRle_abs.
  assumption.
  unfold h; case (Rle_dec x a) as [Hle|Hnle].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hle H4)).
  case (Rle_dec x b) as [Hleb|Hnleb].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hleb H6)).
  case (Rle_dec x0 a) as [Hlea'|Hnlea'].
  elim (Rlt_irrefl _ (Rlt_trans _ _ _ H1 (Rlt_le_trans _ _ _ H10 Hlea'))).
  case (Rle_dec x0 b) as [Hleb'|Hnleb'].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ Hleb' H10)).
  unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0; assumption.
  intros; elim H3; intros; unfold h; case (Rle_dec c a) as [[|]|].
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H4 H6)).
  rewrite H6; reflexivity.
  case (Rle_dec c b) as [|[]].
  reflexivity.
  assumption.
  exists (fun _:R => f0 a); split.
  apply derivable_continuous; apply (derivable_const (f0 a)).
  intros; elim H2; intros; rewrite H1 in H3; cut (b = c).
  intro; rewrite <- H5; rewrite H1; reflexivity.
  apply Rle_antisym; assumption.
Qed.

(**********)
Lemma continuity_ab_maj :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall c:R, a <= c <= b -> continuity_pt f c) ->
    exists Mx : R, (forall c:R, a <= c <= b -> f c <= f Mx) /\ a <= Mx <= b.
Proof.
  intros;
    cut
      (exists g : R -> R,
        continuity g /\ (forall c:R, a <= c <= b -> g c = f0 c)).
  intro HypProl.
  elim HypProl; intros g Hcont_eq.
  elim Hcont_eq; clear Hcont_eq; intros Hcont Heq.
  assert (H1 := compact_P3 a b).
  assert (H2 := continuity_compact g (fun c:R => a <= c <= b) Hcont H1).
  assert (H3 := compact_P2 _ H2).
  assert (H4 := compact_P1 _ H2).
  cut (bound (image_dir g (fun c:R => a <= c <= b))).
  cut (exists x : R, image_dir g (fun c:R => a <= c <= b) x).
  intros; assert (H7 := completeness _ H6 H5).
  elim H7; clear H7; intros M H7; cut (image_dir g (fun c:R => a <= c <= b) M).
  intro; unfold image_dir in H8; elim H8; clear H8; intros Mxx H8; elim H8;
    clear H8; intros; exists Mxx; split.
  intros; rewrite <- (Heq c H10); rewrite <- (Heq Mxx H9); intros;
    rewrite <- H8; unfold is_lub in H7; elim H7; clear H7;
      intros H7 _; unfold is_upper_bound in H7; apply H7;
        unfold image_dir; exists c; split; [ reflexivity | apply H10 ].
  apply H9.
  elim (classic (image_dir g (fun c:R => a <= c <= b) M)); intro.
  assumption.
  cut
    (exists eps : posreal,
      (forall y:R,
        ~
        intersection_domain (disc M eps)
        (image_dir g (fun c:R => a <= c <= b)) y)).
  intro; elim H9; clear H9; intros eps H9; unfold is_lub in H7; elim H7;
    clear H7; intros;
      cut (is_upper_bound (image_dir g (fun c:R => a <= c <= b)) (M - eps)).
  intro; assert (H12 := H10 _ H11); cut (M - eps < M).
  intro; elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ H12 H13)).
  pattern M at 2; rewrite <- Rplus_0_r; unfold Rminus;
    apply Rplus_lt_compat_l; apply Ropp_lt_cancel; rewrite Ropp_0;
      rewrite Ropp_involutive; apply (cond_pos eps).
  unfold is_upper_bound, image_dir; intros; cut (x <= M).
  intro; destruct (Rle_dec x (M - eps)) as [H13|].
  apply H13.
  elim (H9 x); unfold intersection_domain, disc, image_dir; split.
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; rewrite Rabs_right.
  apply Rplus_lt_reg_l with (x - eps);
    replace (x - eps + (M - x)) with (M - eps).
  replace (x - eps + eps) with x.
  auto with real.
unfold Rminus.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r. reflexivity.
symmetry. unfold Rminus.
rewrite Rplus_comm.
repeat rewrite <- Rplus_assoc.
apply Rplus_eq_compat_r.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r. reflexivity.
unfold Rminus. eapply Rplus_le_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
  apply H12.
  apply H11.
  apply H7; apply H11.
  cut
    (exists V : R -> Prop,
      neighbourhood V M /\
      (forall y:R,
        ~ intersection_domain V (image_dir g (fun c:R => a <= c <= b)) y)).
  intro; elim H9; intros V H10; elim H10; clear H10; intros.
  unfold neighbourhood in H10; elim H10; intros del H12; exists del; intros;
    red; intro; elim (H11 y).
  unfold intersection_domain; unfold intersection_domain in H13;
    elim H13; clear H13; intros; split.
  apply (H12 _ H13).
  apply H14.
  cut (~ point_adherent (image_dir g (fun c:R => a <= c <= b)) M).
  intro; unfold point_adherent in H9.
  assert
    (H10 :=
      not_all_ex_not _
      (fun V:R -> Prop =>
        neighbourhood V M ->
        exists y : R,
          intersection_domain V (image_dir g (fun c:R => a <= c <= b)) y) H9).
  elim H10; intros V0 H11; exists V0; assert (H12 := imply_to_and _ _ H11);
    elim H12; clear H12; intros.
  split.
  apply H12.
  apply (not_ex_all_not _ _ H13).
  red; intro; cut (adherence (image_dir g (fun c:R => a <= c <= b)) M).
  intro; elim (closed_set_P1 (image_dir g (fun c:R => a <= c <= b)));
    intros H11 _; assert (H12 := H11 H3).
  elim H8.
  unfold eq_Dom in H12; elim H12; clear H12; intros.
  apply (H13 _ H10).
  apply H9.
  exists (g a); unfold image_dir; exists a; split.
  reflexivity.
  split; [ right; reflexivity | apply H ].
  unfold bound; unfold bounded in H4; elim H4; clear H4; intros m H4;
    elim H4; clear H4; intros M H4; exists M; unfold is_upper_bound;
      intros; elim (H4 _ H5); intros _ H6; apply H6.
  apply prolongement_C0; assumption.
Qed.

(**********)
Lemma continuity_ab_min :
  forall (f:R -> R) (a b:R),
    a <= b ->
    (forall c:R, a <= c <= b -> continuity_pt f c) ->
    exists mx : R, (forall c:R, a <= c <= b -> f mx <= f c) /\ a <= mx <= b.
Proof.
  intros.
  cut (forall c:R, a <= c <= b -> continuity_pt (- f0) c).
  intro; assert (H2 := continuity_ab_maj (- f0)%F a b H H1); elim H2;
    intros x0 H3; exists x0; intros; split.
  intros; rewrite <- (Ropp_involutive (f0 x0));
    rewrite <- (Ropp_involutive (f0 c)); apply Ropp_le_contravar;
      elim H3; intros; unfold opp_fct in H5; apply H5; apply H4.
  elim H3; intros; assumption.
  intros.
  assert (H2 := H0 _ H1).
  apply (continuity_pt_opp _ _ H2).
Qed.


(********************************************************)
(** *      Proof of Bolzano-Weierstrass theorem         *)
(********************************************************)

Definition ValAdh (un:nat -> R) (x:R) : Prop :=
  forall (V:R -> Prop) (N:nat),
    neighbourhood V x ->  exists p : nat, (N <= p)%nat /\ V (un p).

Definition intersection_family (f:family) (x:R) : Prop :=
  forall y:R, ind f y -> f y x.

Lemma ValAdh_un_exists :
  forall (un:nat -> R) (D:=fun x:R =>  exists n : nat, x = INR n)
    (f:=
      fun x:R =>
        adherence
        (fun y:R => (exists p : nat, y = un p /\ x <= INR p) /\ D x))
    (x:R), (exists y : R, f x y) -> D x.
Proof.
  intros; elim H; intros; unfold f in H0; unfold adherence in H0;
    unfold point_adherent in H0;
      assert (H1 : neighbourhood (disc x0 (mkposreal _ Rlt_0_1)) x0).
  unfold neighbourhood, disc; exists (mkposreal _ Rlt_0_1);
    unfold included; trivial.
  elim (H0 _ H1); intros; unfold intersection_domain in H2; elim H2; intros;
    elim H4; intros; apply H6.
Qed.

Definition ValAdh_un (un:nat -> R) : R -> Prop :=
  let D := fun x:R =>  exists n : nat, x = INR n in
    let f :=
      fun x:R =>
        adherence
        (fun y:R => (exists p : nat, y = un p /\ x <= INR p) /\ D x) in
        intersection_family (mkfamily D f (ValAdh_un_exists un)).

Lemma ValAdh_un_prop :
  forall (un:nat -> R) (x:R), ValAdh un x <-> ValAdh_un un x.
Proof.
  intros; split; intro.
  unfold ValAdh in H; unfold ValAdh_un;
    unfold intersection_family; simpl;
      intros; elim H0; intros N H1; unfold adherence;
        unfold point_adherent; intros; elim (H V N H2);
          intros; exists (un x0); unfold intersection_domain;
            elim H3; clear H3; intros; split.
  assumption.
  split.
  exists x0; split; [ reflexivity | rewrite H1; apply (le_INR _ _ H3) ].
  exists N; assumption.
  unfold ValAdh; intros; unfold ValAdh_un in H;
    unfold intersection_family in H; simpl in H;
      assert
        (H1 :
          adherence
          (fun y0:R =>
            (exists p : nat, y0 = un p /\ INR N <= INR p) /\
            (exists n : nat, INR N = INR n)) x).
  apply H; exists N; reflexivity.
  unfold adherence in H1; unfold point_adherent in H1; assert (H2 := H1 _ H0);
    elim H2; intros; unfold intersection_domain in H3;
      elim H3; clear H3; intros; elim H4; clear H4; intros;
        elim H4; clear H4; intros; elim H4; clear H4; intros;
          exists x1; split.
  apply (INR_le _ _ H6).
  rewrite H4 in H3; apply H3.
Qed.

Lemma adherence_P4 :
  forall F G:R -> Prop, included F G -> included (adherence F) (adherence G).
Proof.
  unfold adherence, included; unfold point_adherent; intros;
    elim (H0 _ H1); unfold intersection_domain;
      intros; elim H2; clear H2; intros; exists x0; split;
        [ assumption | apply (H _ H3) ].
Qed.

Definition family_closed_set (f:family) : Prop :=
  forall x:R, closed_set (f x).

Definition intersection_vide_in (D:R -> Prop) (f:family) : Prop :=
  forall x:R,
    (ind f x -> included (f x) D) /\
    ~ (exists y : R, intersection_family f y).

Definition intersection_vide_finite_in (D:R -> Prop)
  (f:family) : Prop := intersection_vide_in D f /\ family_finite f.

(**********)
Lemma compact_P6 :
  forall X:R -> Prop,
    compact X ->
    (exists z : R, X z) ->
    forall g:family,
      family_closed_set g ->
      intersection_vide_in X g ->
      exists D : R -> Prop, intersection_vide_finite_in X (subfamily g D).
Proof.
  intros X H Hyp g H0 H1.
  set (D' := ind g).
  set (f' := fun x y:R => complementary (g x) y /\ D' x).
  assert (H2 : forall x:R, (exists y : R, f' x y) -> D' x).
  intros; elim H2; intros; unfold f' in H3; elim H3; intros; assumption.
  set (f0 := mkfamily D' f' H2).
  unfold compact in H; assert (H3 : covering_open_set X f0).
  unfold covering_open_set; split.
  unfold covering; intros; unfold intersection_vide_in in H1;
    elim (H1 x); intros; unfold intersection_family in H5;
      assert
        (H6 := not_ex_all_not _ (fun y:R => forall y0:R, ind g y0 -> g y0 y) H5 x);
        assert (H7 := not_all_ex_not _ (fun y0:R => ind g y0 -> g y0 x) H6);
          elim H7; intros; exists x0; elim (imply_to_and _ _ H8);
            intros; unfold f0; simpl; unfold f';
              split; [ apply H10 | apply H9 ].
  unfold family_open_set; intro; elim (classic (D' x)); intro.
  apply open_set_P6 with (complementary (g x)).
  unfold family_closed_set in H0; unfold closed_set in H0; apply H0.
  unfold f0; simpl; unfold f'; unfold eq_Dom;
    split.
  unfold included; intros; split; [ apply H4 | apply H3 ].
  unfold included; intros; elim H4; intros; assumption.
  apply open_set_P6 with (fun _:R => False).
  apply open_set_P4.
  unfold eq_Dom; unfold included; split; intros;
    [ elim H4
      | simpl in H4; unfold f' in H4; elim H4; intros; elim H3; assumption ].
  elim (H _ H3); intros SF H4; exists SF;
    unfold intersection_vide_finite_in; split.
  unfold intersection_vide_in; simpl; intros; split.
  intros; unfold included; intros; unfold intersection_vide_in in H1;
    elim (H1 x); intros; elim H6; intros; apply H7.
  unfold intersection_domain in H5; elim H5; intros; assumption.
  assumption.
  elim (classic (exists y : R, intersection_domain (ind g) SF y)); intro Hyp'.
  red; intro; elim H5; intros; unfold intersection_family in H6;
    simpl in H6.
  cut (X x0).
  intro; unfold covering_finite in H4; elim H4; clear H4; intros H4 _;
    unfold covering in H4; elim (H4 x0 H7); intros; simpl in H8;
      unfold intersection_domain in H6; cut (ind g x1 /\ SF x1).
  intro; assert (H10 := H6 x1 H9); elim H10; clear H10; intros H10 _; elim H8;
    clear H8; intros H8 _; unfold f' in H8; unfold complementary in H8;
      elim H8; clear H8; intros H8 _; elim H8; assumption.
  split.
  apply (cond_fam f0).
  exists x0; elim H8; intros; assumption.
  elim H8; intros; assumption.
  unfold intersection_vide_in in H1; elim Hyp'; intros; assert (H8 := H6 _ H7);
    elim H8; intros; cut (ind g x1).
  intro; elim (H1 x1); intros; apply H12.
  apply H11.
  apply H9.
  apply (cond_fam g); exists x0; assumption.
  unfold covering_finite in H4; elim H4; clear H4; intros H4 _;
    cut (exists z : R, X z).
  intro; elim H5; clear H5; intros; unfold covering in H4; elim (H4 x0 H5);
    intros; simpl in H6; elim Hyp'; exists x1; elim H6;
      intros; unfold intersection_domain; split.
  apply (cond_fam f0); exists x0; apply H7.
  apply H8.
  apply Hyp.
  unfold covering_finite in H4; elim H4; clear H4; intros;
    unfold family_finite in H5; unfold domain_finite in H5;
      unfold family_finite; unfold domain_finite;
        elim H5; clear H5; intros l H5; exists l; intro; elim (H5 x);
          intros; split; intro;
            [ apply H6; simpl; simpl in H8; apply H8 | apply (H7 H8) ].
Qed.

Theorem Bolzano_Weierstrass :
  forall (un:nat -> R) (X:R -> Prop),
    compact X -> (forall n:nat, X (un n)) ->  exists l : R, ValAdh un l.
Proof.
  intros; cut (exists l : R, ValAdh_un un l).
  intro; elim H1; intros; exists x; elim (ValAdh_un_prop un x); intros;
    apply (H4 H2).
  assert (H1 :  exists z : R, X z).
  exists (un 0%nat); apply H0.
  set (D := fun x:R =>  exists n : nat, x = INR n).
  set
    (g :=
      fun x:R =>
        adherence (fun y:R => (exists p : nat, y = un p /\ x <= INR p) /\ D x)).
  assert (H2 : forall x:R, (exists y : R, g x y) -> D x).
  intros; elim H2; intros; unfold g in H3; unfold adherence in H3;
    unfold point_adherent in H3.
  assert (H4 : neighbourhood (disc x0 (mkposreal _ Rlt_0_1)) x0).
  unfold neighbourhood; exists (mkposreal _ Rlt_0_1);
    unfold included; trivial.
  elim (H3 _ H4); intros; unfold intersection_domain in H5; decompose [and] H5;
    assumption.
  set (f0 := mkfamily D g H2).
  assert (H3 := compact_P6 X H H1 f0).
  elim (classic (exists l : R, ValAdh_un un l)); intro.
  assumption.
  cut (family_closed_set f0).
  intro; cut (intersection_vide_in X f0).
  intro; assert (H7 := H3 H5 H6).
  elim H7; intros SF H8; unfold intersection_vide_finite_in in H8; elim H8;
    clear H8; intros; unfold intersection_vide_in in H8;
      elim (H8 R0); intros _ H10; elim H10; unfold family_finite in H9;
        unfold domain_finite in H9; elim H9; clear H9; intros l H9;
          set (r := MaxRlist l); cut (D r).
  intro; unfold D in H11; elim H11; intros; exists (un x);
    unfold intersection_family; simpl;
      unfold intersection_domain; intros; split.
  unfold g; apply adherence_P1; split.
  exists x; split;
    [ reflexivity
      | rewrite <- H12; unfold r; apply MaxRlist_P1; elim (H9 y); intros;
        apply H14; simpl; apply H13 ].
  elim H13; intros; assumption.
  elim H13; intros; assumption.
  elim (H9 r); intros.
  simpl in H12; unfold intersection_domain in H12; cut (In r l).
  intro; elim (H12 H13); intros; assumption.
  unfold r; apply MaxRlist_P2;
    cut (exists z : R, intersection_domain (ind f0) SF z).
  intro; elim H13; intros; elim (H9 x); intros; simpl in H15;
    assert (H17 := H15 H14); exists x; apply H17.
  elim (classic (exists z : R, intersection_domain (ind f0) SF z)); intro.
  assumption.
  elim (H8 R0); intros _ H14; elim H1; intros;
    assert
      (H16 :=
        not_ex_all_not _ (fun y:R => intersection_family (subfamily f0 SF) y) H14);
      assert
        (H17 :=
          not_ex_all_not _ (fun z:R => intersection_domain (ind f0) SF z) H13);
        assert (H18 := H16 x); unfold intersection_family in H18;
          simpl in H18;
            assert
              (H19 :=
                not_all_ex_not _ (fun y:R => intersection_domain D SF y -> g y x /\ SF y)
                H18); elim H19; intros; assert (H21 := imply_to_and _ _ H20);
              elim (H17 x0); elim H21; intros; assumption.
  unfold intersection_vide_in; intros; split.
  intro; simpl in H6; unfold f0; simpl; unfold g;
    apply included_trans with (adherence X).
  apply adherence_P4.
  unfold included; intros; elim H7; intros; elim H8; intros; elim H10;
    intros; rewrite H11; apply H0.
  apply adherence_P2; apply compact_P2; assumption.
  apply H4.
  unfold family_closed_set; unfold f0; simpl;
    unfold g; intro; apply adherence_P3.
Qed.

(********************************************************)
(** *            Proof of Heine's theorem               *)
(********************************************************)

Definition uniform_continuity (f:R -> R) (X:R -> Prop) : Prop :=
  forall eps:posreal,
    exists delta : posreal,
      (forall x y:R,
        X x -> X y -> Rabs (x - y) < delta -> Rabs (f x - f y) < eps).

Lemma is_lub_u :
  forall (E:R -> Prop) (x y:R), is_lub E x -> is_lub E y -> x = y.
Proof.
  unfold is_lub; intros; elim H; elim H0; intros; apply Rle_antisym;
    [ apply (H4 _ H1) | apply (H2 _ H3) ].
Qed.

Lemma domain_P1 :
  forall X:R -> Prop,
    ~ (exists y : R, X y) \/
    (exists y : R, X y /\ (forall x:R, X x -> x = y)) \/
    (exists x : R, (exists y : R, X x /\ X y /\ x <> y)).
Proof.
  intro; elim (classic (exists y : R, X y)); intro.
  right; elim H; intros; elim (classic (exists y : R, X y /\ y <> x)); intro.
  right; elim H1; intros; elim H2; intros; exists x; exists x0; intros.
  split;
    [ assumption
      | split; [ assumption | apply (not_eq_sym (A:=R)); assumption ] ].
  left; exists x; split.
  assumption.
  intros; case (Req_dec x0 x); intro.
  assumption.
  elim H1; exists x0; split; assumption.
  left; assumption.
Qed.

Theorem Heine :
  forall (f:R -> R) (X:R -> Prop),
    compact X ->
    (forall x:R, X x -> continuity_pt f x) -> uniform_continuity f X.
Proof.
  intros f0 X H0 H; elim (domain_P1 X); intro Hyp.
(* X is empty *)
  unfold uniform_continuity; intros; exists (mkposreal _ Rlt_0_1);
    intros; elim Hyp; exists x; assumption.
  elim Hyp; clear Hyp; intro Hyp.
(* X has only one element *)
  unfold uniform_continuity; intros; exists (mkposreal _ Rlt_0_1);
    intros; elim Hyp; clear Hyp; intros; elim H4; clear H4;
      intros; assert (H6 := H5 _ H1); assert (H7 := H5 _ H2);
        rewrite H6; rewrite H7; unfold Rminus; rewrite Rplus_opp_r;
          rewrite Rabs_R0; apply (cond_pos eps).
(* X has at least two distinct elements *)
  assert
    (X_enc :
      exists m : R, (exists M : R, (forall x:R, X x -> m <= x <= M) /\ m < M)).
  assert (H1 := compact_P1 X H0); unfold bounded in H1; elim H1; intros;
    elim H2; intros; exists x; exists x0; split.
  apply H3.
  elim Hyp; intros; elim H4; intros; decompose [and] H5;
    assert (H10 := H3 _ H6); assert (H11 := H3 _ H8);
      elim H10; intros; elim H11; intros;
      destruct (total_order_T x x0) as [[|H15]|H15].
  assumption.
  rewrite H15 in H13, H7; elim H9; apply Rle_antisym;
    apply Rle_trans with x0; assumption.
  elim (Rlt_irrefl _ (Rle_lt_trans _ _ _ (Rle_trans _ _ _ H13 H14) H15)).
  elim X_enc; clear X_enc; intros m X_enc; elim X_enc; clear X_enc;
    intros M X_enc; elim X_enc; clear X_enc Hyp; intros X_enc Hyp;
      unfold uniform_continuity; intro;
        assert (H1 : forall t:posreal, R0 < t / R2).
  intro; unfold Rdiv; apply Rmult_lt_0_compat;
    [ apply (cond_pos t) | apply Rinv_0_lt_compat; exact Rlt_0_2 ].
  set
    (g :=
      fun x y:R =>
        X x /\
        (exists del : posreal,
          (forall z:R, Rabs (z - x) < del -> Rabs (f0 z - f0 x) < eps / R2) /\
          is_lub
          (fun zeta:R =>
            R0 < zeta <= M - m /\
            (forall z:R, Rabs (z - x) < zeta -> Rabs (f0 z - f0 x) < eps / R2))
          del /\ disc x (mkposreal (del / R2) (H1 del)) y)).
  assert (H2 : forall x:R, (exists y : R, g x y) -> X x).
  intros; elim H2; intros; unfold g in H3; elim H3; clear H3; intros H3 _;
    apply H3.
  set (f' := mkfamily X g H2); unfold compact in H0;
    assert (H3 : covering_open_set X f').
  unfold covering_open_set; split.
  unfold covering; intros; exists x; simpl; unfold g;
    split.
  assumption.
  assert (H4 := H _ H3); unfold continuity_pt in H4; unfold continue_in in H4;
    unfold limit1_in in H4; unfold limit_in in H4; simpl in H4;
      unfold R_dist in H4; elim (H4 (eps / R2) (H1 eps));
        intros;
          set
            (E :=
              fun zeta:R =>
                R0 < zeta <= M - m /\
                (forall z:R, Rabs (z - x) < zeta -> Rabs (f0 z - f0 x) < eps / R2));
            assert (H6 : bound E).
  unfold bound; exists (M - m); unfold is_upper_bound;
    unfold E; intros; elim H6; clear H6; intros H6 _;
      elim H6; clear H6; intros _ H6; apply H6.
  assert (H7 :  exists x : R, E x).
  elim H5; clear H5; intros; exists (Rmin x0 (M - m)); unfold E; intros;
    split.
  split.
  unfold Rmin; case (Rle_dec x0 (M - m)); intro.
  apply H5.
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
apply Hyp.
  apply Rmin_r.
  intros; case (Req_dec x z); intro.
  rewrite H9; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply (H1 eps).
  apply H7; split.
  unfold D_x, no_cond; split; [ trivial | assumption ].
  apply Rlt_le_trans with (Rmin x0 (M - m)); [ apply H8 | apply Rmin_l ].
  destruct (completeness _ H6 H7) as (x1,p).
    cut (R0 < x1 <= M - m).
  intros (H8,H9); exists (mkposreal _ H8); split.
  intros; cut (exists alp : R, Rabs (z - x) < alp <= x1 /\ E alp).
  intros; elim H11; intros; elim H12; clear H12; intros; unfold E in H13;
    elim H13; intros; apply H15.
  elim H12; intros; assumption.
  elim (classic (exists alp : R, Rabs (z - x) < alp <= x1 /\ E alp)); intro.
  assumption.
  assert
    (H12 :=
      not_ex_all_not _ (fun alp:R => Rabs (z - x) < alp <= x1 /\ E alp) H11);
    unfold is_lub in p; elim p; intros; cut (is_upper_bound E (Rabs (z - x))).
  intro; assert (H16 := H14 _ H15);
    elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H10 H16)).
  unfold is_upper_bound; intros; unfold is_upper_bound in H13;
    assert (H16 := H13 _ H15); case (Rle_dec x2 (Rabs (z - x)));
      intro.
  assumption.
  elim (H12 x2); split; [ split; [ auto with real | assumption ] | assumption ].
  split.
  apply p.
  unfold disc; unfold Rminus; rewrite Rplus_opp_r;
    rewrite Rabs_R0; simpl; unfold Rdiv;
      apply Rmult_lt_0_compat; [ apply H8 | apply Rinv_0_lt_compat; exact Rlt_0_2 ].
  elim H7; intros; unfold E in H8; elim H8; intros H9 _; elim H9; intros H10 _;
    unfold is_lub in p; elim p; intros; unfold is_upper_bound in H12;
      unfold is_upper_bound in H11; split.
  apply Rlt_le_trans with x2; [ assumption | apply (H11 _ H8) ].
  apply H12; intros; unfold E in H13; elim H13; intros; elim H14; intros;
    assumption.
  unfold family_open_set; intro; simpl; elim (classic (X x));
    intro.
  unfold g; unfold open_set; intros; elim H4; clear H4;
    intros _ H4; elim H4; clear H4; intros; elim H4; clear H4;
      intros; unfold neighbourhood; case (Req_dec x x0);
        intro.
  exists (mkposreal _ (H1 x1)); rewrite <- H6; unfold included; intros;
    split.
  assumption.
  exists x1; split.
  apply H4.
  split.
  elim H5; intros; apply H8.
  apply H7.
  set (d := x1 / R2 - Rabs (x0 - x)); assert (H7 : R0 < d).
  unfold d.
unfold Rminus. eapply Rplus_lt_reg_r. rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l.
elim H5; clear H5; intros;
    unfold disc in H7; apply H7.
  exists (mkposreal _ H7); unfold included; intros; split.
  assumption.
  exists x1; split.
  apply H4.
  elim H5; intros; split.
  assumption.
  unfold disc in H8; simpl in H8; unfold disc; simpl;
    unfold disc in H10; simpl in H10;
      apply Rle_lt_trans with (Rabs (x2 - x0) + Rabs (x0 - x)).
  replace (x2 - x) with (x2 - x0 + (x0 - x)); [ apply Rabs_triang | idtac ].
unfold Rminus. repeat rewrite <- Rplus_assoc.
apply Rplus_eq_compat_r.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
reflexivity.
  replace (x1 / R2) with (d + Rabs (x0 - x)); [ idtac | unfold d ].
2:{
unfold Rminus.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r. reflexivity.
}
  do 2 rewrite <- (Rplus_comm (Rabs (x0 - x))); apply Rplus_lt_compat_l;
    apply H8.
  apply open_set_P6 with (fun _:R => False).
  apply open_set_P4.
  unfold eq_Dom; unfold included; intros; split.
  intros; elim H4.
  intros; unfold g in H4; elim H4; clear H4; intros H4 _; elim H3; apply H4.
  elim (H0 _ H3); intros DF H4; unfold covering_finite in H4; elim H4; clear H4;
    intros; unfold family_finite in H5; unfold domain_finite in H5;
      unfold covering in H4; simpl in H4; simpl in H5; elim H5;
        clear H5; intros l H5; unfold intersection_domain in H5;
          cut
            (forall x:R,
              In x l ->
              exists del : R,
                R0 < del /\
                (forall z:R, Rabs (z - x) < del -> Rabs (f0 z - f0 x) < eps / R2) /\
                included (g x) (fun z:R => Rabs (z - x) < del / R2)).
  intros;
    assert
      (H7 :=
        Rlist_P1 l
        (fun x del:R =>
          R0 < del /\
          (forall z:R, Rabs (z - x) < del -> Rabs (f0 z - f0 x) < eps / R2) /\
          included (g x) (fun z:R => Rabs (z - x) < del / R2)) H6);
      elim H7; clear H7; intros l' H7; elim H7; clear H7;
        intros; set (D := MinRlist l'); cut (R0 < D / R2).
  intro; exists (mkposreal _ H9); intros; assert (H13 := H4 _ H10); elim H13;
    clear H13; intros xi H13; assert (H14 : In xi l).
{
  unfold RF in H13. decompose [and] H13. elim (H5 xi). intros. clear H5. apply H16. split.
{

  unfold f' in *.
  simpl in *.
  unfold g in H14.
  apply H14.

} assumption.
}
  elim (pos_Rl_P2 l xi); intros H15 _; elim (H15 H14); intros i H16; elim H16;
    intros; apply Rle_lt_trans with (Rabs (f0 x - f0 xi) + Rabs (f0 xi - f0 y)).
  replace (f0 x - f0 y) with (f0 x - f0 xi + (f0 xi - f0 y));
  [ apply Rabs_triang | idtac ].
{ clear. unfold Rminus.
repeat rewrite <- Rplus_assoc. apply Rplus_eq_compat_r.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r. reflexivity.
}
  rewrite (double_var eps); apply Rplus_lt_compat.
  assert (H19 := H8 i H17); elim H19; clear H19; intros; rewrite <- H18 in H20;
    elim H20; clear H20; intros; apply H20; unfold included in H21;
      apply Rlt_trans with (pos_Rl l' i / R2).
  apply H21.
  elim H13; clear H13; intros; assumption.
  unfold Rdiv; apply Rmult_lt_reg_l with R2.
  exact Rlt_0_2.
  rewrite Rmult_comm; rewrite Rmult_assoc; rewrite <- Rinv_l_sym.
  rewrite Rmult_1_r; pattern (pos_Rl l' i) at 1; rewrite <- Rplus_0_r;
    rewrite double; apply Rplus_lt_compat_l; apply H19.
  exact Neq_2_0.
  assert (H19 := H8 i H17); elim H19; clear H19; intros; rewrite <- H18 in H20;
    elim H20; clear H20; intros; rewrite <- Rabs_Ropp;
      rewrite Ropp_minus_distr; apply H20; unfold included in H21;
        elim H13; intros; assert (H24 := H21 x H22);
          apply Rle_lt_trans with (Rabs (y - x) + Rabs (x - xi)).
  replace (y - xi) with (y - x + (x - xi)); [ apply Rabs_triang | idtac ].
{
unfold Rminus. repeat rewrite <- Rplus_assoc. apply Rplus_eq_compat_r.
rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r.
reflexivity.
}
  rewrite (double_var (pos_Rl l' i)); apply Rplus_lt_compat.
  apply Rlt_le_trans with (D / R2).
  rewrite <- Rabs_Ropp; rewrite Ropp_minus_distr; apply H12.
  unfold Rdiv; do 2 rewrite <- (Rmult_comm (/ R2));
    apply Rmult_le_compat_l.
  left; apply Rinv_0_lt_compat; exact Rlt_0_2.
  unfold D; apply MinRlist_P1; elim (pos_Rl_P2 l' (pos_Rl l' i));
    intros; apply H26; exists i; split;
      [ rewrite <- H7; assumption | reflexivity ].
  assumption.
  unfold Rdiv; apply Rmult_lt_0_compat;
    [ unfold D; apply MinRlist_P2; intros; elim (pos_Rl_P2 l' y); intros;
      elim (H10 H9); intros; elim H12; intros; rewrite H14;
        rewrite <- H7 in H13; elim (H8 x H13); intros;
          apply H15
      | apply Rinv_0_lt_compat; exact Rlt_0_2 ].
  intros; elim (H5 x); intros; elim (H8 H6); intros;
    set
      (E :=
        fun zeta:R =>
          R0 < zeta <= M - m /\
          (forall z:R, Rabs (z - x) < zeta -> Rabs (f0 z - f0 x) < eps / R2));
      assert (H11 : bound E).
  unfold bound; exists (M - m); unfold is_upper_bound;
    unfold E; intros; elim H11; clear H11; intros H11 _;
      elim H11; clear H11; intros _ H11; apply H11.
  assert (H12 :  exists x : R, E x).
  assert (H13 := H _ H9); unfold continuity_pt in H13;
    unfold continue_in in H13; unfold limit1_in in H13;
      unfold limit_in in H13; simpl in H13; unfold R_dist in H13;
        elim (H13 _ (H1 eps)); intros; elim H12; clear H12;
          intros; exists (Rmin x0 (M - m)); unfold E;
            intros; split.
  split;
    [ unfold Rmin; case (Rle_dec x0 (M - m)); intro;
      [ apply H12 | unfold Rminus; eapply Rplus_lt_reg_r; rewrite Rplus_assoc, Rplus_opp_l, Rplus_0_r, Rplus_0_l; apply Hyp ]
      | apply Rmin_r ].
  intros; case (Req_dec x z); intro.
  rewrite H16; unfold Rminus; rewrite Rplus_opp_r; rewrite Rabs_R0;
    apply (H1 eps).
  apply H14; split;
    [ unfold D_x, no_cond; split; [ trivial | assumption ]
      | apply Rlt_le_trans with (Rmin x0 (M - m)); [ apply H15 | apply Rmin_l ] ].
  destruct (completeness _ H11 H12) as (x0,p).
    cut (R0 < x0 <= M - m).
  intro; elim H13; clear H13; intros; exists x0; split.
  assumption.
  split.
  intros; cut (exists alp : R, Rabs (z - x) < alp <= x0 /\ E alp).
  intros; elim H16; intros; elim H17; clear H17; intros; unfold E in H18;
    elim H18; intros; apply H20; elim H17; intros; assumption.
  elim (classic (exists alp : R, Rabs (z - x) < alp <= x0 /\ E alp)); intro.
  assumption.
  assert
    (H17 :=
      not_ex_all_not _ (fun alp:R => Rabs (z - x) < alp <= x0 /\ E alp) H16);
    unfold is_lub in p; elim p; intros; cut (is_upper_bound E (Rabs (z - x))).
  intro; assert (H21 := H19 _ H20);
    elim (Rlt_irrefl _ (Rlt_le_trans _ _ _ H15 H21)).
  unfold is_upper_bound; intros; unfold is_upper_bound in H18;
    assert (H21 := H18 _ H20); case (Rle_dec x1 (Rabs (z - x)));
      intro.
  assumption.
  elim (H17 x1); split.
  split; [ auto with real | assumption ].
  assumption.
  unfold included, g; intros; elim H15; intros; elim H17; intros;
    decompose [and] H18; cut (x0 = x2).
  intro; rewrite H20; apply H22.
  unfold E in p; eapply is_lub_u.
  apply p.
  apply H21.
  elim H12; intros; unfold E in H13; elim H13; intros H14 _; elim H14;
    intros H15 _; unfold is_lub in p; elim p; intros;
      unfold is_upper_bound in H16; unfold is_upper_bound in H17;
        split.
  apply Rlt_le_trans with x1; [ assumption | apply (H16 _ H13) ].
  apply H17; intros; unfold E in H18; elim H18; intros; elim H19; intros;
    assumption.
Qed.
