(* Automatic Differentiation using duals *)
From Stdlib Require Import Ring Ring_theory Field Field_theory.
From DArith Require Import Dual.

Module GDualAD (DF : DField).
Export DF.

Module Dual := GDual DF.
Import Dual.

Add Ring S_ad : rt.
Add Field S_field : ft.

(* Dual inversion and division

   For a dual [y = (p, q)] with [p <> 0],
       1 / (p + q e) = 1/p - (q / p^2) e,
   since (p + q e)(1/p - (q/p^2) e) = 1 + (q/p - q/p) e = 1. *)

Definition Dinv (y : D) : D :=
    (inv (real y), (- (du y * inv (real y) * inv (real y)))%S).

Definition Ddiv (x y : D) : D := mul x (Dinv y).

Theorem real_Dinv : forall y, real (Dinv y) = inv (real y).
Proof. intros. now destruct y. Qed.

Theorem du_Dinv :
    forall y, du (Dinv y) = (- (du y * inv (real y) * inv (real y)))%S.
Proof. intros. now destruct y. Qed.

Theorem real_Ddiv :
    forall x y, real (Ddiv x y) = (real x * inv (real y))%S.
Proof. intros. unfold Ddiv. rewrite real_mul, real_Dinv. reflexivity. Qed.

(* Single-variable expression language *)
Inductive Expr : Set :=
| Const (s : S)
| Var   (i : nat)
| Add   (e1 e2 : Expr)
| Sub   (e1 e2 : Expr)
| Mul   (e1 e2 : Expr)
| Opp   (e : Expr)
| Div   (e1 e2 : Expr).

(* Evaluation over the base field *)
Fixpoint eval (e : Expr) (x : nat -> S) : S :=
    match e with
    | Const c   => c
    | Var i     => x i
    | Add e1 e2 => (eval e1 x + eval e2 x)%S
    | Sub e1 e2 => (eval e1 x - eval e2 x)%S
    | Mul e1 e2 => (eval e1 x * eval e2 x)%S
    | Opp e1    => (- eval e1 x)%S
    | Div e1 e2 => (eval e1 x / eval e2 x)%S
    end.

(* Evaluation over the duals *)
Fixpoint eval_dual (e : Expr) (x : nat -> D) : D :=
    match e with
    | Const c   => inj c
    | Var i     => x i
    | Add e1 e2 => Dual.add (eval_dual e1 x) (eval_dual e2 x)
    | Sub e1 e2 => Dual.sub (eval_dual e1 x) (eval_dual e2 x)
    | Mul e1 e2 => Dual.mul (eval_dual e1 x) (eval_dual e2 x)
    | Opp e1    => Dual.opp (eval_dual e1 x)
    | Div e1 e2 => Ddiv (eval_dual e1 x) (eval_dual e2 x)
    end.

(* Symbolic derivative *)
(* Inductive derivative : Expr -> Expr -> Prop :=
| DConst x    : derivative (Const x) (Const 0%S)
| DVar        : derivative Var (Const 1%S)
| DAdd e1  e2
      de1 de2 :
    derivative e1 de1 ->
    derivative e2 de2 ->
    derivative (Add e1 e2) (Add de1 de2)
| DSub e1  e2
      de1 de2 :
    derivative e1 de1 ->
    derivative e2 de2 ->
    derivative (Sub e1 e2) (Sub de1 de2)
| DMul e1  e2
      de1 de2 :
    derivative e1 de1 ->
    derivative e2 de2 ->
    derivative (Mul e1 e2) (Add (Mul de1 e2) (Mul e1 de2))
| DOpp e1 de1 :
    derivative e1 de1 ->
    derivative (Opp e1) (Opp de1)
| DDiv e1  e2
      de1 de2 :
    derivative e1 de1 ->
    derivative e2 de2 ->
    (forall x, eval e2 x <> 0%S) ->
    derivative (Div e1 e2)
        (Div (Sub (Mul de1 e2) (Mul e1 de2)) (Mul e2 e2)). *)

Fixpoint deriv (e : Expr) (v : nat -> S) : Expr :=
    match e with
    | Const _   => Const 0%S
    | Var j     => Const (v j)
    | Add e1 e2 => Add (deriv e1 v) (deriv e2 v)
    | Sub e1 e2 => Sub (deriv e1 v) (deriv e2 v)
    | Mul e1 e2 => Add (Mul (deriv e1 v) e2) (Mul e1 (deriv e2 v))
    | Opp e1    => Opp (deriv e1 v)
    | Div e1 e2 =>
        (* (e1' e2 - e1 e2') / e2^2 *)
        Div (Sub (Mul (deriv e1 v) e2) (Mul e1 (deriv e2 v)))
            (Mul e2 e2)
    end.

(* Well-definedness: Every denominator is nonzero *)
Fixpoint defined_at (e : Expr) (x : nat -> S) : Prop :=
    match e with
    | Const _   => True
    | Var _     => True
    | Add e1 e2 => defined_at e1 x /\ defined_at e2 x
    | Sub e1 e2 => defined_at e1 x /\ defined_at e2 x
    | Mul e1 e2 => defined_at e1 x /\ defined_at e2 x
    | Opp e1    => defined_at e1 x
    | Div e1 e2 => defined_at e1 x /\ defined_at e2 x /\ (eval e2 x <> 0)%S
    end.

(* Correctness

   Evaluating an expression [e] over multivariate dual numbers gives two results:
   1. The real part is the standard evaluation of the expression
   2. The dual part is the partial derivative with respect to variable [i]. *)
Theorem eval_dual_correct :
    forall (e : Expr) (a : nat -> S) (v : nat -> S),
        let env : nat -> D := fun j => (a j, v j) in
        defined_at e a ->
        real (eval_dual e env) = eval e a /\
        du (eval_dual e env)   = eval (deriv e v) a.
Proof.
    induction e; cbv zeta; intros a v Hdef; cbn in Hdef.
    - (* Const c *)
      cbn. unfold inj. now split.
    - (* Var *)
      cbn. now split.
    - (* Add e1 e2 *)
      destruct Hdef as [H1 H2].
      destruct (IHe1 a v H1) as [Hr1 Hd1].
      destruct (IHe2 a v H2) as [Hr2 Hd2].
      cbn. rewrite Hr1, Hr2, Hd1, Hd2. now split.
    - (* Sub e1 e2 *)
      destruct Hdef as [H1 H2].
      destruct (IHe1 a v H1) as [Hr1 Hd1].
      destruct (IHe2 a v H2) as [Hr2 Hd2].
      cbn. unfold Dual.sub.
      rewrite Hr1, Hr2, Hd1, Hd2.
      split; ring.
    - (* Mul e1 e2 *)
      destruct Hdef as [H1 H2].
      destruct (IHe1 a v H1) as [Hr1 Hd1].
      destruct (IHe2 a v H2) as [Hr2 Hd2].
      cbn. rewrite Hr1, Hr2, Hd1, Hd2.
      split; ring.
    - (* Opp e1 *)
      destruct (IHe a v Hdef) as [Hr Hd].
      cbn. rewrite Hr, Hd. split; ring.
    - (* Div e1 e2 *)
      destruct Hdef as [H1 [H2 Hnz]].
      destruct (IHe1 a v H1) as [Hr1 Hd1].
      destruct (IHe2 a v H2) as [Hr2 Hd2].
      cbn. split.
      + rewrite Hr1, Hr2.
        symmetry. apply div_def.
      + unfold Ddiv. rewrite Hr1, Hd1, Hr2, Hd2.
        rewrite div_def.
        field. apply Hnz.
Qed.

End GDualAD.
