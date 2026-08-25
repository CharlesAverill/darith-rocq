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
    Infix "=?" := eqb (at level 70, no associativity) : S_scope.
    Parameter eqb_eq :
        forall (s1 s2 : S),
            reflect (s1 = s2) (s1 =? s2)%S.

    Parameter rt : ring_theory
        zero one add mul sub opp eq.
    Parameter srt : semi_ring_theory
        zero one add mul eq.
    Parameter zero_neq_one : (0 <> 1)%S.
    Parameter opp_nonzero : forall x, (-x <> 0 <-> x <> 0)%S.
    Parameter mul_nonzero : forall x y, (x <> 0 -> y <> 0 -> x * y <> 0)%S.
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

(* Notation "0" := D0 : D_scope.
Notation "1" := D1 : D_scope. *)
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
Lemma D_ring_theory : ring_theory D0 D1 add mul sub opp eq.
Proof.
    constructor; intros;
    repeat unfold add, opp, sub, mul, D0 in *;
    destruct x; try destruct y; try destruct z;
    cbn; f_equal; try ring;
    now destruct rt.
Qed.

Add Ring D : D_ring_theory.

Theorem add_0_l : forall x, D0 + x = x.
Proof. now destruct D_ring_theory. Qed.

Theorem add_comm : forall x y, x + y = y + x.
Proof. now destruct D_ring_theory. Qed.

Theorem add_assoc : forall x y z, x + (y + z) = x + y + z.
Proof. now destruct D_ring_theory. Qed.

Theorem mul_1_l : forall x, D1 * x = x.
Proof. now destruct D_ring_theory. Qed.

Theorem mul_comm : forall x y, x * y = y * x.
Proof. now destruct D_ring_theory. Qed.

Theorem mul_assoc : forall x y z, x * (y * z) = x * y * z.
Proof. now destruct D_ring_theory. Qed.

Theorem distr_l : forall x y z, (x + y) * z = (x * z) + (y * z).
Proof. now destruct D_ring_theory. Qed.

Theorem sub_def : forall x y, x - y = x + (- y).
Proof. now destruct D_ring_theory. Qed.

Theorem opp_def : forall x, x + (- x) = D0.
Proof. now destruct D_ring_theory. Qed.

(* Declare D as a semiring *)
Lemma D_semi_ring_theory : semi_ring_theory D0 D1 add mul eq.
Proof.
    constructor; destruct D_ring_theory; auto.
    intros. unfold mul, D0. cbn.
    f_equal; ring.
Qed.
Add Ring Ds : D_semi_ring_theory.

Theorem mul_0_l : forall x, D0 * x = D0.
Proof.
    intros. destruct x. unfold D0, mul. cbn.
    f_equal; ring.
Qed.

Theorem real_add : forall x y, real (x + y) = (real x + real y)%S.
Proof. intros. now destruct x, y. Qed.

Theorem du_add : forall x y, du (x + y) = (du x + du y)%S.
Proof. intros. now destruct x, y. Qed.

Theorem real_mul : forall x y, real (x * y) = (real x * real y)%S.
Proof. intros. now destruct x, y. Qed.

Theorem du_mul :
    forall x y, du (x * y) = (real x * du y + du x * real y)%S.
Proof. intros. now destruct x, y. Qed.

Theorem real_opp : forall x, real (- x) = (- real x)%S.
Proof. intros. now destruct x. Qed.

Theorem du_opp : forall x, du (- x) = (- du x)%S.
Proof. intros. now destruct x. Qed.

Definition eqb (x y : D) : bool :=
    (andb (real x =? real y) (du x =? du y))%S.
Infix "=?" := eqb (at level 70, no associativity) : D_scope.

Theorem eqb_eq : forall (x y : D),
    reflect (x = y) (x =? y).
Proof.
    intros. destruct (x =? y) eqn:E.
    - apply ReflectT. destruct x, y. unfold eqb in E.
      cbn in E. destruct (s =? s1)%S eqn:E0, (s0 =? s2)%S eqn:E1;
        try discriminate.
      apply (Bool.reflect_iff _ _ (eqb_eq _ _)) in E0.
      apply (Bool.reflect_iff _ _ (eqb_eq _ _)) in E1.
      now subst.
    - apply ReflectF. destruct x, y. unfold eqb in E.
      cbn in E. destruct (s =? s1)%S eqn:E0, (s0 =? s2)%S eqn:E1;
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
Example strict_sum_not_strict:
    exists d1 d2,
        ((real d1 <> 0)%S /\ (real d2 <> 0)%S /\
         (du d1 <> 0)%S /\ (du d2 <> 0)%S) /\
        (real (d1 + d2)%D = 0)%S.
Proof.
    exists (1, 1)%S. exists (- one, one)%S.
    repeat split; cbn; symmetry;
    try apply zero_neq_one.
    - symmetry. rewrite opp_nonzero.
      symmetry. apply zero_neq_one.
    - destruct rt. now rewrite Ropp_def.
Qed.

Example strict_sum_du_zero :
    exists d1 d2,
        ((real d1 <> 0)%S /\ (real d2 <> 0)%S /\
         (du d1 <> 0)%S /\ (du d2 <> 0)%S) /\
        du (d1 + d2) = 0%S.
Proof.
    exists (1, 1)%S, (one, - one)%S.
    repeat split; cbn; symmetry; try apply zero_neq_one.
    - symmetry. rewrite opp_nonzero. symmetry. apply zero_neq_one.
    - symmetry. destruct rt. apply Ropp_def.
Qed.

Example strict_sum_zero :
    exists d1 d2,
        ((real d1 <> 0)%S /\ (real d2 <> 0)%S /\
         (du d1 <> 0)%S /\ (du d2 <> 0)%S) /\
        d1 + d2 = D0.
Proof.
    exists (1, 1)%S, (- one, - one)%S.
    repeat split; cbn;
      try (symmetry; apply zero_neq_one);
      try (rewrite opp_nonzero; symmetry; apply zero_neq_one);
    unfold add, D0; cbn; f_equal;
      destruct rt; now rewrite Ropp_def.
Qed.

Theorem strict_prod_strict :
    forall d1 d2,
        real d1 <> 0%S ->
        real d2 <> 0%S ->
        du d1 <> 0%S ->
        du d2 <> 0%S ->
        (du d1 * real d2 + real d1 * du d2 <> 0)%S ->
        real (d1 * d2) <> 0%S /\ du (d1 * d2) <> 0%S.
Proof.
    intros d1 d2 Hanz Hbnz Hxnz Hdnz Habxd.
    split.
    - unfold real, mul. cbn. now apply mul_nonzero.
    - unfold du, mul. cbn.
      intro Hz. apply Habxd.
      destruct rt. now rewrite Radd_comm.
Qed.

Theorem eps_sq_zero : \e * \e = D0.
Proof. unfold eps, mul, D0. cbn. f_equal; ring. Qed.

Theorem eps_nonzero : \e <> D0.
Proof.
    unfold eps, D0. intro H. inversion H.
    now apply zero_neq_one.
Qed.

Definition inj (a : S) : D := (a, 0%S).
Coercion inj : S >-> D.

Theorem inj_zero : inj 0%S = D0.
Proof. reflexivity. Qed.

Theorem inj_one : inj 1%S = D1.
Proof. reflexivity. Qed.

Theorem inj_add : forall a b, inj (a + b)%S = inj a + inj b.
Proof. intros. unfold inj, add. cbn. f_equal; ring. Qed.

Theorem inj_mul : forall a b, inj (a * b)%S = inj a * inj b.
Proof. intros. unfold inj, mul. cbn. f_equal; ring. Qed.

Theorem inj_opp : forall a, inj (- a)%S = - inj a.
Proof.
    intros. unfold inj, opp. cbn. f_equal.
    destruct rt.
    now rewrite <- (Radd_0_l (- 0)%S), Ropp_def.
Qed.

Theorem inj_injective : forall a b, inj a = inj b -> a = b.
Proof. intros a b H. now inversion H. Qed.

Theorem dual_decomp :
    forall d, d = inj (real d) + inj (du d) * \e.
Proof.
    intros [a b]. unfold inj, eps, add, mul, real, du. cbn.
    f_equal; ring.
Qed.

Theorem D_not_domain :
    exists x y, x <> D0 /\ y <> D0 /\ x * y = D0.
Proof.
    exists \e, \e. repeat split;
    [ apply eps_nonzero | apply eps_nonzero | apply eps_sq_zero ].
Qed.

Theorem strict_prod_iff :
    forall d1 d2,
        real d1 <> 0%S ->
        real d2 <> 0%S ->
        du d1 <> 0%S ->
        du d2 <> 0%S ->
        ( (real (d1 * d2) <> 0%S /\ du (d1 * d2) <> 0%S)
          <->
          (du d1 * real d2 + real d1 * du d2 <> 0)%S ).
Proof.
    intros d1 d2 Hanz Hbnz Hxnz Hdnz. split.
    - intros [_ Hdu]. rewrite du_mul in Hdu.
      intro Hz. apply Hdu.
      destruct rt. now rewrite Radd_comm.
    - intro Hcross.
      now apply strict_prod_strict.
Qed.

End GDual.
