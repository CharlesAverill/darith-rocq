(** General dual number ring *)
From Stdlib Require Import Ring.
From Stdlib Require Import Ring_theory.

Module Type DRing.
    Parameter S : Set.
    Parameter zero one : S.
    Parameter add mul sub : S -> S -> S.

    Declare Scope S_scope.
    Delimit Scope S_scope with S.
    Notation "0" := zero : S_scope.
    Notation "1" := one : S_scope.
    Infix "+" := add (at level 50, left associativity) : S_scope.
    Infix "-" := sub (at level 50, left associativity) : S_scope.
    Infix "*" := mul (at level 40, left associativity) : S_scope.

    (* Additive inverse *)
    Parameter opp : S -> S.
    Notation "- x" := (opp x) (at level 35, right associativity) : S_scope.

    (* Equality is decidable *)
    Parameter eqb : S -> S -> bool.
    Infix "=?" := eqb (at level 100, no associativity) : S_scope.
    Parameter eqb_eq :
        forall (s1 s2 : S),
            reflect (s1 = s2) (s1 =? s2)%S.

    Parameter rt : ring_theory
        zero one add mul sub opp eq.
    Parameter srt : semi_ring_theory
        zero one add mul eq.
    Parameter zero_neq_one : (0 <> 1)%S.
    Parameter opp_nonzero : forall x, (-x <> 0 <-> x <> 0)%S.
End DRing.

Module GDual (DR : DRing).
Export DR.

(* 'ring' tactic now works on S goals *)
Add Ring S : rt.
Add Ring Ss : srt.

(* Dual numbers are of the form a + be, where
   a, b \in S and e is a new value such that
   e^2 = 0 and e <> 0 *)
Definition D : Set := S * S.

(* S component of a dual *)
Definition real (d : D) := fst d.

(* Non-S component of a dual *)
Definition du (d : D) := snd d.

(* Constants *)
Definition D0 : D := (0, 0)%S.
Definition D1 : D := (1, 0)%S.
Definition eps : D := (0, 1)%S.

Declare Scope D_scope.
Delimit Scope D_scope with D.
Open Scope D_scope.

Notation "0" := D0 : D_scope.
Notation "1" := D1 : D_scope.
Notation "\e" := eps : D_scope.

(* Operations *)
Definition add (x y : D) : D :=
    (real x + real y, du x + du y)%S.
Infix "+" := add (at level 50, left associativity) : D_scope.

Definition opp (x : D) : D :=
    (- real x, - du x)%S.
Notation "- x" := (opp x) (at level 35, right associativity) : D_scope.

Definition sub (x y : D) : D :=
    x + (- y).
Infix "-" := sub (at level 50, left associativity) : D_scope.

(* (a + be)(c + de) = ac + (ad + bc)e *)
Definition mul (x y : D) : D :=
    (real x * real y,
     real x * du y + du x * real y)%S.
Infix "*" := mul (at level 40, left associativity) : D_scope.

(* Declare D as a ring *)
Lemma D_ring_theory : ring_theory 0 1 add mul sub opp eq.
Proof.
    constructor; intros;
    repeat unfold add, opp, sub, mul, D0 in *;
    destruct x; try destruct y; try destruct z;
    simpl; f_equal; try ring;
    now destruct rt.
Qed.

Add Ring D : D_ring_theory.

Theorem add_0_l : forall x, 0 + x = x.
Proof. now destruct D_ring_theory. Qed.

Theorem add_comm : forall x y, x + y = y + x.
Proof. now destruct D_ring_theory. Qed.

Theorem add_assoc : forall x y z, x + (y + z) = x + y + z.
Proof. now destruct D_ring_theory. Qed.

Theorem mul_1_l : forall x, 1 * x = x.
Proof. now destruct D_ring_theory. Qed.

Theorem mul_comm : forall x y, x * y = y * x.
Proof. now destruct D_ring_theory. Qed.

Theorem mul_assoc : forall x y z, x * (y * z) = x * y * z.
Proof. now destruct D_ring_theory. Qed.

Theorem distr_l : forall x y z, (x + y) * z = (x * z) + (y * z).
Proof. now destruct D_ring_theory. Qed.

Theorem sub_def : forall x y, x - y = x + (- y).
Proof. now destruct D_ring_theory. Qed.

Theorem opp_def : forall x, x + (- x) = 0.
Proof. now destruct D_ring_theory. Qed.

(* Declare D as a semiring *)
Lemma D_semi_ring_theory : semi_ring_theory 0 1 add mul eq.
Proof.
    constructor; destruct D_ring_theory; auto.
    intros. unfold mul, D0. simpl.
    f_equal; ring.
Qed.
Add Ring Ds : D_semi_ring_theory.

Theorem mul_0_l : forall x, 0 * x = 0.
Proof.
    intros. destruct x. unfold D0, mul. simpl.
    f_equal; ring.
Qed.

Definition eqb (x y : D) : bool :=
    (andb (real x =? real y) (du x =? du y))%S.
Infix "=?" := eqb (at level 100, no associativity) : D_scope.

Theorem eqb_eq : forall (x y : D),
    reflect (x = y) (x =? y).
Proof.
    intros. destruct (x =? y) eqn:E.
    - apply ReflectT. destruct x, y. unfold eqb in E.
      simpl in E. destruct (s =? s1)%S eqn:E0, (s0 =? s2)%S eqn:E1;
        try discriminate.
      apply (Bool.reflect_iff _ _ (eqb_eq _ _)) in E0.
      apply (Bool.reflect_iff _ _ (eqb_eq _ _)) in E1.
      now subst.
    - apply ReflectF. destruct x, y. unfold eqb in E.
      simpl in E. destruct (s =? s1)%S eqn:E0, (s0 =? s2)%S eqn:E1;
        try discriminate; intro Contra; inversion Contra; subst; clear Contra;
        clear E.
      + assert (s2 = s2) by reflexivity.
        apply (Bool.reflect_iff _ _ (eqb_eq _ _)) in H.
        now rewrite H in E1.
      + assert (s1 = s1) by reflexivity.
        apply (Bool.reflect_iff _ _ (eqb_eq _ _)) in H.
        now rewrite H in E0.
      + assert (s2 = s2) by reflexivity.
        apply (Bool.reflect_iff _ _ (eqb_eq _ _)) in H.
        now rewrite H in E1.
Qed.

(* The sum of two strict duals need not be a strict dual *)
Theorem strict_sum_not_strict:
    exists d1 d2 d3,
        (real d1 <> 0 /\ real d2 <> 0 /\
        du d1 <> 0 /\ du d2 <> 0)%S /\
        d1 + d2 = d3 /\
        (real d3 = 0 \/ du d3 = 0)%S.
Proof.
    exists (1, 1)%S. exists (- one, one)%S.
    eexists. repeat split; simpl; try symmetry;
    try apply zero_neq_one.
    - symmetry. rewrite opp_nonzero.
      symmetry. apply zero_neq_one.
    - left. destruct rt. now rewrite Ropp_def.
Qed.
      
End GDual.
