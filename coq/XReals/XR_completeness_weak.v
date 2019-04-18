Require Export XR_completeness.

Local Open Scope R_scope.

Lemma completeness_weak : forall E:R -> Prop,
  bound E ->
  (exists x : R, E x) ->
  exists m : R, is_lub E m.
Proof.
  intros E hE hex.
  assert (completeness := completeness).
  specialize (completeness E hE hex).
  destruct completeness as [ m hm].
  exists m.
  exact hm.
Qed.