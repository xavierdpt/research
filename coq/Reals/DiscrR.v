Require Import RIneq.
Require Import Omega.
Local Open Scope R_scope.

Lemma Rlt_R0_R2 : 0 < 2.
Proof.
  (* map 2%R into nat *)
  change 2%R with (INR 2%nat).
  (* switch the comparison to nat *)
  apply lt_INR_0.
  (* apply the theorem from nat *)
  apply lt_O_Sn.
Qed.

Notation Rplus_lt_pos := Rplus_lt_0_compat (only parsing).

Lemma IZR_eq : forall z1 z2:Z, z1 = z2 -> IZR z1 = IZR z2.
Proof.
intros x y. intro eq. subst y. reflexivity.
Qed.

Ltac discrR :=
  try
   match goal with
   |  |- (?X1 <> ?X2) =>
       repeat
         rewrite <- plus_IZR ||
           rewrite <- mult_IZR ||
           rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus;
       apply IZR_neq; try discriminate
   end.

Ltac prove_sup0 :=
  match goal with
  |  |- (0 < 1) => apply Rlt_0_1
  |  |- (0 < ?X1) =>
      repeat
       (apply Rmult_lt_0_compat || apply Rplus_lt_pos;
         try apply Rlt_0_1 || apply Rlt_R0_R2)
  |  |- (?X1 > 0) => change (0 < X1); prove_sup0
  end.

Ltac omega_sup :=
  repeat
    rewrite <- plus_IZR ||
      rewrite <- mult_IZR || rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus;
  apply IZR_lt; omega.

Ltac prove_sup :=
  match goal with
  |  |- (?X1 > ?X2) => change (X2 < X1); prove_sup
  |  |- (0 < ?X1) => prove_sup0
  |  |- (- ?X1 < 0) => rewrite <- Ropp_0; prove_sup
  |  |- (- ?X1 < - ?X2) => apply Ropp_lt_gt_contravar; prove_sup
  |  |- (- ?X1 < ?X2) => apply Rlt_trans with 0; prove_sup
  |  |- (?X1 < ?X2) => omega_sup
  | _ => idtac
  end.

Ltac Rcompute :=
  repeat
    rewrite <- plus_IZR ||
      rewrite <- mult_IZR || rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus;
  apply IZR_eq; try reflexivity.
