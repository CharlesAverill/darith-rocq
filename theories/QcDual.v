From Stdlib Require Import QArith Qcanon Ring.
From DArith Require Import Dual.

Module QcRing <: DRing.
    Definition S := Qc.
    Definition zero := 0%Qc.
    Definition one := 1%Qc.
    Definition add := Qcplus.
    Definition mul := Qcmult.
    Definition sub := Qcminus.
    Definition opp := Qcopp.

    Declare Scope S_scope.
    Delimit Scope S_scope with S.
    Notation "0" := zero : S_scope.
    Notation "1" := one : S_scope.
    Infix "+" := add (at level 50, left associativity) : S_scope.
    Infix "-" := sub (at level 50, left associativity) : S_scope.
    Infix "*" := mul (at level 40, left associativity) : S_scope.
    Notation "- x" := (opp x) (at level 35, right associativity) : S_scope.

    Definition eqb (x y : Qc) : bool :=
        if Qc_eq_dec x y then true else false.

    Lemma eqb_eq : forall s1 s2 : S, reflect (s1 = s2) (eqb s1 s2).
    Proof.
        intros. unfold eqb. destruct (Qc_eq_dec s1 s2).
        - now apply ReflectT.
        - now apply ReflectF.
    Qed.

    Lemma rt : ring_theory zero one add mul sub opp eq.
    Proof. constructor; intros; unfold add,mul,sub,opp,zero,one; ring. Qed.

    Lemma srt : semi_ring_theory zero one add mul eq.
    Proof. constructor; intros; unfold add,mul,zero,one; ring. Qed.

    Lemma zero_neq_one : (0 <> 1)%S.
    Proof. unfold zero, one. discriminate. Qed.

    Lemma opp_nonzero : forall x, (- x <> 0 <-> x <> 0)%S.
    Proof.
        intros x. unfold opp, zero. split; intro H; intro Hx.
        - apply H. rewrite Hx. ring.
        - apply H. rewrite <- (Qcopp_involutive x), Hx. ring.
    Qed.

    Lemma mul_nonzero : forall x y, (x <> 0 -> y <> 0 -> x * y <> 0)%S.
    Proof.
        intros x y Hx Hy. unfold mul, zero. intro H.
        apply Qcmult_integral in H. destruct H; contradiction.
    Qed.
End QcRing.

Module QcDual := GDual QcRing.
