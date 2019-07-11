Variable Scissors : Type.
Variable Fabric : Type.
Variable cut : Scissors -> Fabric -> Prop.

Definition magic_statement :=
(exists magic_scissors, forall fabric, cut magic_scissors fabric) ->
(forall fabric, exists scissors, cut scissors fabric).

Theorem magic : magic_statement.
Proof.
unfold magic_statement.
intro hmagic.
destruct hmagic as [ magic_scissors hmagic ].
intro fabric.
exists magic_scissors.
specialize (hmagic fabric).
exact hmagic.
Qed.

Theorem ex_inv : forall A B (P:A->B->Prop),
(exists a, forall b, P a b) ->
(forall b, exists a, P a b).
Proof.
intros A B P.
intro hex.
destruct hex as [ a h ].
intro b.
exists a.
specialize (h b).
exact h.
Qed.

Theorem magic_power : magic_statement.
Proof.
unfold magic_statement.
apply ex_inv.
Qed.
