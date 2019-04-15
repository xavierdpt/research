Require Export XR_R.
Require Export XR_Rle.

Implicit Type r : R.
Local Open Scope R_scope.

Lemma Req_le_sym : forall r1 r2, r2 = r1 -> r1 <= r2.
Proof.
  intros x y heq.
  subst y.
  unfold "<=".
  right.
  reflexivity.
Qed.
