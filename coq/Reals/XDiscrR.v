Require Import XRIneq.
Require Import Omega.
Local Open Scope XR_scope.

Lemma Rlt_R0_R2 : R0 < IZR 2.
Proof.
  change (IZR 2) with (INR 2%nat).
  apply lt_INR_0.
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

Ltac Rcompute :=
  repeat
    rewrite <- plus_IZR ||
      rewrite <- mult_IZR || rewrite <- Ropp_Ropp_IZR || rewrite Z_R_minus;
  apply IZR_eq; try reflexivity.