(* Automatic differentiation over the rationals *)

From Stdlib Require Import QArith Qcanon Ring Field.
From DArith Require Import Dual QcDual AD.

Module QcAD := GDualAD QcField.
Import QcAD Dual.

Add Ring Qc_base_ring : QcField.rt.
Add Field S_qc_field : QcField.ft.

Open Scope Qc_scope.

(* Test cases *)

(* f(x) = x^2 *)
Definition sq : Expr := Mul Var Var.

(* f(x) = x^2 + 3x + 2 *)
Definition poly : Expr :=
    Add (Add (Mul Var Var) (Mul (Const (Q2Qc 3)) Var)) (Const (Q2Qc 2)).

(* f(x) = 1 / x *)
Definition recip : Expr := Div (Const 1) Var.

(* f(x) = x / (x + 1) *)
Definition frac : Expr := Div Var (Add Var (Const 1)).

Lemma Q2Qc_2 : Q2Qc 2 = (1 + 1)%S.
Proof. reflexivity. Qed.

Lemma Q2Qc_3 : Q2Qc 3 = (1 + 1 + 1)%S.
Proof. reflexivity. Qed.

(* Symbolic derivatives *)

(* d/dx x^2 = 2x. *)
Example deriv_sq :
    forall a, du (eval_dual sq ((a, 1%S : S) : D)) = (Q2Qc 2 * a)%S.
Proof.
    intro a.
    assert (Hdef : defined_at sq a) by (cbn; tauto).
    destruct (eval_dual_correct sq a Hdef) as [_ Hd].
    change S with Qc in *. rewrite Hd, Q2Qc_2. cbn.
    unfold one in *. ring.
Qed.

Add Field Qc_field : Qcft.

(* d/dx (x^2 + 3x + 2) = 2x + 3. *)
Example deriv_poly :
    forall a, du (eval_dual poly (a, 1%S : S)) = (Q2Qc 2 * a + Q2Qc 3)%S.
Proof.
    intro a.
    assert (Hdef : defined_at poly a) by (cbn; tauto).
    destruct (eval_dual_correct poly a Hdef) as [_ Hd].
    rewrite Hd. cbn.
    rewrite Q2Qc_2, Q2Qc_3.
    change S with Qc in *.
    change QcField.add with Qcplus. change QcField.mul with Qcmult.
    unfold zero, one. rewrite Qcmult_0_l, Qcplus_0_l, Qcplus_0_r.
    ring.
Qed.

(* d/dx (1/x) = -1/x^2, where x <> 0. *)
Example deriv_recip :
    forall a, (a <> 0)%S ->
        du (eval_dual recip (a, 1%S)) = (- Qcinv (a * a))%S.
Proof.
    intros a Ha.
    assert (Hdef : defined_at recip a) by (cbn; tauto).
    destruct (eval_dual_correct recip a Hdef) as [_ Hd].
    change S with Qc in *. rewrite Hd. cbn.
    unfold one, zero in *.
    change QcField.add with Qcplus. change QcField.mul with Qcmult.
    change QcField.sub with Qcminus. change QcField.opp with Qcopp.
    unfold div.
    now field.
Qed.

(* d/dx (x/(x+1)) = 1/(x+1)^2, where x + 1 <> 0. *)
Example deriv_frac :
    forall a, ((a + 1) <> 0)%S ->
        du (eval_dual frac (a, 1%S)) = Qcinv ((a + 1) * (a + 1)).
Proof.
    intros a Ha.
    assert (Hdef : defined_at frac a) by (cbn; tauto).
    destruct (eval_dual_correct frac a Hdef) as [_ Hd].
    change S with Qc in *. rewrite Hd. cbn.
    unfold one, zero in *.
    change QcField.add with Qcplus. change QcField.mul with Qcmult.
    change QcField.sub with Qcminus. change QcField.opp with Qcopp.
    unfold div. now field.
Qed.

(* f(x) = x^2 + 3x + 2 at x = 5:  value 42, derivative 13. *)
Example poly_at_5_value :
    real (eval_dual poly (Q2Qc 5, 1%S)) = Q2Qc 42.
Proof. reflexivity. Qed.

Example poly_at_5_deriv :
    du (eval_dual poly (Q2Qc 5, 1%S)) = Q2Qc 13.
Proof. reflexivity. Qed.

(* f(x) = 1/x at x = 2:  value 1/2, derivative -1/4. *)
Example recip_at_2_value :
    real (eval_dual recip (Q2Qc 2, 1%S)) = Q2Qc (1 # 2).
Proof. reflexivity. Qed.

Example recip_at_2_deriv :
    du (eval_dual recip (Q2Qc 2, 1%S)) = Q2Qc (- (1 # 4)).
Proof. reflexivity. Qed.

(* f(x) = x/(x+1) at x = 3:  value 3/4, derivative 1/16. *)
Example frac_at_3_value :
    real (eval_dual frac (Q2Qc 3, 1%S)) = Q2Qc (3 # 4).
Proof. reflexivity. Qed.

Example frac_at_3_deriv :
    du (eval_dual frac (Q2Qc 3, 1%S)) = Q2Qc (1 # 16).
Proof. apply Qceq_alt. reflexivity. Qed.
