(* Automatic differentiation over the rationals *)

From Stdlib Require Import QArith Qcanon Ring Field.
From DArith Require Import Dual QcDual AD.

Module QcAD := GDualAD QcField.
Import QcAD Dual.

Add Ring Qc_base_ring : QcField.rt.
Add Field Qc_base_field : QcField.ft.

Open Scope Qc_scope.

(* Seed 1 at variable i, 0 elsewhere; dual environment at point a *)
Definition seed (i : nat) : nat -> S := fun j => if Nat.eqb j i then 1%S else 0%S.
Definition env_at (a : nat -> S) (i : nat) : nat -> D := fun j => (a j, seed i j).

(* Single-variable point: variable 0 at a, seed 1 *)
Definition pt (a : S) : nat -> D := fun _ => (a, 1%S).

Notation X := (Var 0).
Notation Y := (Var 1).

Lemma Q2Qc_1 : Q2Qc 1 = 1%S.
Proof. reflexivity. Qed.

Lemma Q2Qc_2 : Q2Qc 2 = (1 + 1)%S.
Proof. reflexivity. Qed.

Lemma Q2Qc_3 : Q2Qc 3 = (1 + 1 + 1)%S.
Proof. reflexivity. Qed.

(* Test cases *)

(* f(x) = x^2 *)
Definition sq : Expr := Mul X X.

(* f(x) = x^2 + 3x + 2 *)
Definition poly : Expr :=
    Add (Add (Mul X X) (Mul (Const (Q2Qc 3)) X)) (Const (Q2Qc 2)).

(* f(x) = 1 / x *)
Definition recip : Expr := Div (Const 1) X.

(* f(x) = x / (x + 1) *)
Definition frac : Expr := Div X (Add X (Const 1)).

(* Symbolic derivatives *)

(* d/dx x^2 = 2x *)
Example deriv_sq :
    forall a, du (eval_dual sq (pt a)) = (Q2Qc 2 * a)%S.
Proof.
    intro a.
    assert (Hdef : defined_at sq (fun _ => a)) by (cbn; tauto).
    destruct (eval_dual_correct sq (fun _ => a) (fun _ => 1%S) Hdef) as [_ Hd].
    unfold pt. change S with Qc in *. rewrite Hd, Q2Qc_2. cbn.
    unfold one in *. ring.
Qed.

(* d/dx (x^2 + 3x + 2) = 2x + 3 *)
Example deriv_poly :
    forall a, du (eval_dual poly (pt a)) = (Q2Qc 2 * a + Q2Qc 3)%S.
Proof.
    intro a.
    assert (Hdef : defined_at poly (fun _ => a)) by (cbn; tauto).
    destruct (eval_dual_correct poly (fun _ => a) (fun _ => 1%S) Hdef) as [_ Hd].
    unfold pt.
    change QcField.add with Qcplus.
    change S with Qc in *. rewrite Hd. cbn. rewrite Q2Qc_2, Q2Qc_3.
    change Qcplus with QcField.add.
    change Qcmult with QcField.mul.
    rewrite Q2Qc_1. ring.
Qed.

(* d/dx (1/x) = -1/x^2, where x <> 0 *)
Example deriv_recip :
    forall a, (a <> 0)%S ->
        du (eval_dual recip (pt a)) = (- Qcinv (a * a))%S.
Proof.
    
    intros a Ha.
    assert (Hdef : defined_at recip (fun _ => a)) by (cbn; tauto).
    destruct (eval_dual_correct recip (fun _ => a) (fun _ => 1%S) Hdef) as [_ Hd].
    unfold pt.
    change S with Qc in *. rewrite Hd. cbn.
    unfold one, zero in *.
    change QcField.add with Qcplus. change QcField.mul with Qcmult.
    change QcField.sub with Qcminus. change QcField.opp with Qcopp.
    unfold div.
    Add Field Qc_raw_field : Qcft. now field.
Qed.

(* d/dx (x/(x+1)) = 1/(x+1)^2, where x + 1 <> 0 *)
Example deriv_frac :
    forall a, ((a + 1) <> 0)%S ->
        du (eval_dual frac (pt a)) = Qcinv ((a + 1) * (a + 1)).
Proof.
    intros a Ha.
    assert (Hdef : defined_at frac (fun _ => a)) by (cbn; tauto).
    destruct (eval_dual_correct frac (fun _ => a) (fun _ => 1%S) Hdef) as [_ Hd].
    unfold pt. change S with Qc in *. rewrite Hd. cbn.
    unfold one, zero in *.
    change QcField.add with Qcplus. change QcField.mul with Qcmult.
    change QcField.sub with Qcminus. change QcField.opp with Qcopp.
    unfold div. now field.
Qed.

(* f(x) = x^2 + 3x + 2 at x = 5:  value 42, derivative 13 *)
Example poly_at_5_value :
    real (eval_dual poly (pt (Q2Qc 5))) = Q2Qc 42.
Proof. reflexivity. Qed.

Example poly_at_5_deriv :
    du (eval_dual poly (pt (Q2Qc 5))) = Q2Qc 13.
Proof. reflexivity. Qed.

(* f(x) = 1/x at x = 2:  value 1/2, derivative -1/4 *)
Example recip_at_2_value :
    real (eval_dual recip (pt (Q2Qc 2))) = Q2Qc (1 # 2).
Proof. reflexivity. Qed.

Example recip_at_2_deriv :
    du (eval_dual recip (pt (Q2Qc 2))) = Q2Qc (- (1 # 4)).
Proof. reflexivity. Qed.

(* f(x) = x/(x+1) at x = 3:  value 3/4, derivative 1/16 *)
Example frac_at_3_value :
    real (eval_dual frac (pt (Q2Qc 3))) = Q2Qc (3 # 4).
Proof. reflexivity. Qed.

Example frac_at_3_deriv :
    du (eval_dual frac (pt (Q2Qc 3))) = Q2Qc (1 # 16).
Proof. apply Qceq_alt. reflexivity. Qed.

(* Multivariate *)

(* g(x, y) = x * y *)
Definition prod_xy : Expr := Mul X Y.

(* h(x, y) = x^2 * y + y *)
Definition hxy : Expr := Add (Mul (Mul X X) Y) Y.

(* Point (x, y) = (3, 4) *)
Definition pt2 : nat -> S :=
    fun j => match j with 0%nat => Q2Qc 3 | 1%nat => Q2Qc 4 | _ => 0%S end.

(* g(3,4) = 12 *)
Example prod_value :
    real (eval_dual prod_xy (env_at pt2 0)) = Q2Qc 12.
Proof. reflexivity. Qed.

(* d/dx (x*y) = y = 4 *)
Example prod_dx :
    du (eval_dual prod_xy (env_at pt2 0)) = Q2Qc 4.
Proof. reflexivity. Qed.

(* d/dy (x*y) = x = 3 *)
Example prod_dy :
    du (eval_dual prod_xy (env_at pt2 1)) = Q2Qc 3.
Proof. reflexivity. Qed.

(* h(3,4) = 40 *)
Example hxy_value :
    real (eval_dual hxy (env_at pt2 0)) = Q2Qc 40.
Proof. reflexivity. Qed.

(* d/dx (x^2 y + y) = 2xy = 24 *)
Example hxy_dx :
    du (eval_dual hxy (env_at pt2 0)) = Q2Qc 24.
Proof. reflexivity. Qed.

(* d/dy (x^2 y + y) = x^2 + 1 = 10 *)
Example hxy_dy :
    du (eval_dual hxy (env_at pt2 1)) = Q2Qc 10.
Proof. reflexivity. Qed.
