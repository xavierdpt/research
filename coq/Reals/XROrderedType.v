Require Import XRbase Equalities Orders OrdersTac.

Local Open Scope R_scope.

Lemma Req_dec : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros x y.
  destruct (total_order_T x y) as [ [hlt | heq ] | hgt].
  right. apply Rlt_dichotomy_converse. left. assumption.
  left. assumption.
  right. apply Rlt_dichotomy_converse. right. assumption.
Qed.

Definition Reqb r1 r2 := if Req_dec r1 r2 then true else false.

Lemma Reqb_eq : forall r1 r2, Reqb r1 r2 = true <-> r1=r2.
Proof.
 intros x y. split.
 {
   intro h. unfold Reqb in h. destruct (Req_dec x y).
   { assumption. }
   { inversion h. }
 }
 {
   intro eq. subst y.
   unfold Reqb. destruct (Req_dec x x).
   { reflexivity. }
   { elim n. reflexivity. }
 }
Qed.

Module R_as_UBE <: UsualBoolEq.
 Definition t := R.
 Definition eq := @eq R.
 Definition eqb := Reqb.
 Definition eqb_eq := Reqb_eq.
End R_as_UBE.

Module R_as_DT <: UsualDecidableTypeFull := Make_UDTF R_as_UBE.

Definition Rcompare x y :=
 match total_order_T x y with
  | inleft (left _) => Lt
  | inleft (right _) => Eq
  | inright _ => Gt
 end.

Lemma Rcompare_spec : forall x y, CompareSpec (x=y) (x<y) (y<x) (Rcompare x y).
Proof.
 intros x y.
 unfold Rcompare.
 destruct (total_order_T x y) as [[H|H]|H].
 constructor. assumption.
 constructor. assumption.
 constructor. assumption.
Qed.

Module R_as_OT <: OrderedTypeFull.
 Include R_as_DT.
 Definition lt := Rlt.
 Definition le := Rle.
 Definition compare := Rcompare.

 Instance lt_strorder : StrictOrder Rlt.
 Proof.
   split.
   {
     unfold Irreflexive. unfold Reflexive.
     apply Rlt_irrefl.
   }
   {
     unfold Transitive.
     apply Rlt_trans.
   }
Qed.

 Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) Rlt.
 Proof.
   unfold Proper.
   unfold respectful.
   intros x y eq x' y' eq'.
   subst y y'.
   split;intros;assumption.
 Qed.

 Lemma le_lteq : forall x y, x <= y <-> x < y \/ x = y.
 Proof.
   unfold Rle.
   intros x y.
   split;intro;assumption.
 Qed.

 Definition compare_spec := Rcompare_spec.

End R_as_OT.

Module ROrder := OTF_to_OrderTac R_as_OT.
Ltac r_order := ROrder.order.
