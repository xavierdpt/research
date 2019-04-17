Require Export ZArith.

Lemma IZN : forall n:Z,
  (0 <= n)%Z ->
  exists m : nat,
  n = Z.of_nat m.
Proof.
  intros z hz.
  exists (Z.to_nat z).
  rewrite Z2Nat.id.
  { reflexivity. }
  { exact hz. }
Qed.
