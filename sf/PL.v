Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match nil EmptyStr
| MChar : forall x, exp_match (cons x nil) (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (app s1 s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match nil (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).


Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => nil
  | S n' => app l (napp n' l)
  end.


Lemma list_dec : forall {T:Type} (l:list T), l = nil \/ l <> nil.
Proof.
destruct l. left;reflexivity. right. intro h. inversion h.
Qed.

Lemma app_assoc : forall T (l m n : list T), app (app l m) n = app l (app m n).
Proof.
induction l.
simpl. reflexivity.
simpl. intros. rewrite IHl. reflexivity.
Qed.

Theorem pumping_lemma : forall T (re : @reg_exp T) s,
  exp_match s re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = app s1 (app s2 s3) /\
    s2 <> nil /\
    forall m, exp_match (app s1 (app (napp m s2) s3)) re.
Proof.
intros T r s m.
induction m as [
(* empty *)
| (* char *) ch
| (* app *) sa ra sb rb ram ia rbm ib
| (* union left *) sl rl rr ml il
| (* union right *) sr rl rr mr ir
| (* star empty *) r
| (* star next *) sr srs R mr ir mrs irs
];simpl.
{ (* Empty *)
  intro l. inversion l.
}
{ (* Char *)
  intro l. apply Nat.nle_succ_diag_l in l. contradiction.
}
{ (* App *)
  intro l. 
  rewrite app_length in l.
  apply Nat.add_le_cases in l.
  inversion_clear l as [ ha | hb ].
  {
    specialize (ia ha). clear ib.
    inversion ia as [ ta [ tb [ tc [ hx [ hy hz ]]]]].
    exists ta, tb, (tc++sb).
    split. subst sa. repeat (rewrite app_assoc). reflexivity.
    split. assumption.
    intro m.
    assert (eq: ta++napp m tb ++ tc ++ sb = (ta++napp m tb ++ tc) ++ sb).
    repeat (rewrite app_assoc). reflexivity.
    rewrite eq. constructor. apply hz. assumption.
  }
  {
    specialize (ib hb). clear ia.
    inversion ib as [ ta [ tb [ tc [ hx [ hy hz ]]]]].
    exists (sa++ta), tb, tc.
    split. subst sb. repeat (rewrite app_assoc). reflexivity.
    split. assumption.
    intro m.
    assert (eq: (sa++ta)++napp m tb ++ tc = sa++(ta++napp m tb ++ tc)).
    repeat (rewrite app_assoc). reflexivity.
    rewrite eq. constructor. assumption. apply hz.
  }
}
{ (* Union left *)
  intro l.
  induction (pumping_constant rr) as [ | pc ipc].
  {
    rewrite plus_comm in l. simpl in l. specialize (il l).
    inversion il as [ ta [ tb [ tc [ hx [ hy hz ]]]]].
    exists ta, tb, tc. split. assumption. split. assumption.
    intro m. apply MUnionL. apply hz.
  }
  {
    rewrite plus_comm in l. simpl in l. apply le_Sn_le in l. rewrite plus_comm in l.
    specialize (ipc l).
    inversion ipc as [ ta [ tb [ tc [ hx [ hy hz ]]]]].
    exists ta, tb, tc.
    split. assumption. split. assumption.
    assumption.
  }
}
{ (* Union right *)
  intro l. induction (pumping_constant sr) as [ | pc ipc ].
  {
    simpl in l. specialize (ir l).
    inversion ir as [ ta [ tb [ tc [ hx [ hy hz ]]]]].
    exists ta, tb, tc. split. assumption. split. assumption.
    intro m. apply MUnionR. apply hz.
  }
  {
    simpl in l. apply le_Sn_le in l. specialize (ipc l).
    inversion ipc as [ ta [ tb [ tc [ hx [ hy hz ]]]]].
    exists ta, tb, tc. split. assumption. split. assumption.
    assumption.
  }
}
{ (* Star none *)
  intro h. inversion h.
}
{ (* Star some *)
  intro l.
  simpl in irs.
  elim (list_dec sr);simpl.
  {
    intro h. subst sr. simpl in l. specialize (irs l).
    inversion irs as [ ta [ tb [ tc [ hx [ hy hz ]]]]].
    exists ta, tb, tc;simpl.
    split. assumption. split. assumption.
    assumption.
  }
  {
    intro neq.
    exists nil, sr, srs. simpl.
    split. reflexivity. split. assumption.
    simpl. induction m as [ | m im ];simpl.
    - assumption.
    - rewrite app_assoc. constructor.
      + assumption.
      + assumption.
  }
}
Qed.

