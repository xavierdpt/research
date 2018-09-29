Require Import Coq.Lists.List.

Fixpoint nthR {A:Type} (l:list A) (n:nat) (a:A) :=
match l with
| nil => False
| cons h t =>
  match n with
  | O => h=a
  | S n' => nthR t n' a
  end
end.

Theorem pigeon : forall (l:list nat) (m:nat),
length l >= 2 ->
length l = S m ->
(forall (i v:nat), nthR l i v -> v < m) ->
exists (i j vi vj:nat), i<>j /\ (nthR l i vi -> nthR l j vj -> vi=vj). 

intros l m.

destruct l. intro h. simpl in h. inversion h.
destruct l. intro h. simpl in h. inversion h. inversion H0.
generalize dependent l.
intro l.

destruct m.
intros hge heq hiv. specialize (hiv 0 n). simpl in hiv.
specialize (hiv eq_refl). inversion hiv.

intros hge hl.
intro hiv.

clear hge.

generalize dependent m.
induction l.

intros. exists 0, 1, n, n0. simpl in hl. inversion hl. subst m.
split. auto. simpl.
clear hl. intros. clear H H0.
remember (hiv 0 n) as ha.
remember (hiv 1 n0) as hb.
clear Heqhb Heqha hiv.
simpl in ha, hb.
specialize (ha eq_refl).
specialize (hb eq_refl).
unfold lt in ha, hb.
inversion ha. inversion hb. clear ha hb. reflexivity. inversion H1. inversion H0.

intros.
simpl in hl.
inversion hl.
assert (exists x, m= S x).
destruct m. inversion H0. exists m. reflexivity.
inversion_clear H. subst m.
inversion H1. clear H1.
specialize (IHl x).
apply eq_S in H0.
apply eq_S in H0.
specialize (IHl H0).
clear hl. inversion H0. clear H0.
rewrite H1 in hiv.
rename a into a'.
rename n into a.
rename n0 into b.
rename a' into c.

assert (youpi:forall i v : nat, nthR(a::b::l) i v -> v < S(S x)).
intros i v h.
destruct i.
apply (hiv 0). simpl in h. simpl. assumption.
destruct i. apply (hiv 1). simpl in h. simpl. assumption.
apply (hiv (S (S (S i)))).
simpl. simpl in h. assumption.

(* Stuck :( *)

