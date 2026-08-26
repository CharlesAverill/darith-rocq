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

(* Expression language *)
Inductive Expr : Set :=
| Const (s : S)
| Var   (i : nat)
| Add   (e1 e2 : Expr)
| Sub   (e1 e2 : Expr)
| Mul   (e1 e2 : Expr)
| Opp   (e : Expr)
| Div   (e1 e2 : Expr)
| Pow   (e : Expr) (n : nat).

Notation Sq e    := (Mul e e).
Notation Cube e  := (Mul e (Mul e e)).
Notation Recip e := (Div (Const 1%S) e).

(* Power on the base field *)
Fixpoint S_pow (b : S) (n : nat) : S :=
    match n with
    | O    => 1%S
    | Datatypes.S k  => (b * S_pow b k)%S
    end.

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
    | Pow e1 n  => S_pow (eval e1 x) n
    end.

(* Evaluation over the duals *)
Fixpoint Dpow (b : D) (n : nat) : D :=
    match n with
    | O    => inj 1%S
    | Datatypes.S k  => Dual.mul b (Dpow b k)
    end.

Fixpoint eval_dual (e : Expr) (x : nat -> D) : D :=
    match e with
    | Const c   => inj c
    | Var i     => x i
    | Add e1 e2 => Dual.add (eval_dual e1 x) (eval_dual e2 x)
    | Sub e1 e2 => Dual.sub (eval_dual e1 x) (eval_dual e2 x)
    | Mul e1 e2 => Dual.mul (eval_dual e1 x) (eval_dual e2 x)
    | Opp e1    => Dual.opp (eval_dual e1 x)
    | Div e1 e2 => Ddiv (eval_dual e1 x) (eval_dual e2 x)
    | Pow e1 n  => Dpow (eval_dual e1 x) n
    end.

(* Derivative of a power by recursion on the exponent
     (e^{k+1})' = e' * e^k + e * (e^k)' *)
Fixpoint deriv_pow (de1 e1 : Expr) (n : nat) : Expr :=
    match n with
    | O    => Const 0%S
    | Datatypes.S k => Add (Mul de1 (Pow e1 k)) (Mul e1 (deriv_pow de1 e1 k))
    end.

(* Symbolic derivative *)
Reserved Notation "'d/dx' e '@' v" (at level 0).
Fixpoint deriv (e : Expr) (v : nat -> S) : Expr :=
    match e with
    | Const _   => Const 0%S
    | Var j     => Const (v j)
    | Add e1 e2 => Add (d/dx e1 @ v) (d/dx e2 @ v)
    | Sub e1 e2 => Sub (d/dx e1 @ v) (d/dx e2 @ v)
    | Mul e1 e2 => Add (Mul (d/dx e1 @ v) e2) (Mul e1 (d/dx e2 @ v))
    | Opp e1    => Opp (d/dx e1 @ v)
    | Div e1 e2 =>
        (* (e1' e2 - e1 e2') / e2^2 *)
        Div (Sub (Mul (d/dx e1 @ v) e2) (Mul e1 (d/dx e2 @ v)))
            (Mul e2 e2)
    | Pow e1 n => deriv_pow (d/dx e1 @ v) e1 n
    end
where "'d/dx' e '@' v" := (deriv e v).

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
    | Pow e1 _  => defined_at e1 x
    end.

Lemma real_Dpow :
    forall (d : D) (n : nat),
        real (Dpow d n) = S_pow (real d) n.
Proof.
    intros d n. induction n as [| k IH].
    - cbn. reflexivity.
    - cbn. now rewrite <- real_mul, <- IH.
Qed.

(* Correctness

   Evaluating an expression [e] over multivariate dual numbers gives two
   results:
   1. The real part is the standard evaluation of the expression.
   2. The dual part is the seeded derivative [eval (d/dx e @ v) a]. *)
Theorem eval_dual_correct :
    forall (e : Expr) (a : nat -> S) (v : nat -> S),
        let env : nat -> D := fun j => (a j, v j) in
        defined_at e a ->
        real (eval_dual e env) = eval e a /\
        du (eval_dual e env)   = eval (d/dx e @ v) a.
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
    - (* Pow e1 n *)
      destruct (IHe a v Hdef) as [Hr1 Hd1].
      split.
      + cbn [eval_dual eval]. rewrite real_Dpow, Hr1. reflexivity.
      + induction n as [| k IHk].
        * reflexivity.
        * cbn [eval_dual Dpow deriv deriv_pow eval] in *.
          rewrite du_mul, Hr1, Hd1, real_Dpow, Hr1, IHk.
          ring.
Qed.

End GDualAD.
