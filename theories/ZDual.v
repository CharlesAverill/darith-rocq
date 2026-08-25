From Stdlib Require Import ZArith Zbool Lia.
From DArith Require Import Dual.
Open Scope Z_scope.

Module ZRing <: DRing.
    Definition S := Z.
    Definition zero := 0.
    Definition one := 1.
    Definition add := Z.add.
    Definition mul := Z.mul.
    Definition sub := Z.sub.
    Definition opp := Z.opp.

    Declare Scope S_scope.
    Delimit Scope S_scope with S.
    Notation "0" := zero : S_scope.
    Notation "1" := one : S_scope.
    Infix "+" := add (at level 50, left associativity) : S_scope.
    Infix "-" := sub (at level 50, left associativity) : S_scope.
    Infix "*" := mul (at level 40, left associativity) : S_scope.
    Notation "- x" := (opp x) (at level 35, right associativity) : S_scope.

    Definition eqb := Z.eqb.

    Lemma eqb_eq : forall s1 s2 : S, reflect (s1 = s2) (s1 =? s2)%S.
    Proof. intros. apply Z.eqb_spec. Qed.

    Lemma rt : ring_theory zero one add mul sub opp eq.
    Proof.
        constructor; intros;
        unfold add, mul, sub, opp, zero, one; ring.
    Qed.

    Lemma srt : semi_ring_theory zero one add mul eq.
    Proof.
        constructor; intros;
        unfold add, mul, zero, one; lia.
    Qed.

    Lemma zero_neq_one : (0 <> 1)%S.
    Proof. unfold zero, one. discriminate. Qed.

    Lemma opp_nonzero : forall x, (- x <> 0 <-> x <> 0)%S.
    Proof.
        intros x. unfold opp, zero. lia.
    Qed.

    Lemma mul_nonzero : forall x y, (x <> 0 -> y <> 0 -> x * y <> 0)%S.
    Proof.
        intros x y Hx Hy. unfold mul, zero.
        intro H. apply Z.mul_eq_0 in H. now destruct H.
    Qed.
End ZRing.

Module ZDual := GDual ZRing.
