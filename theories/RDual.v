From Stdlib Require Import Reals Ring Lra.
From DArith Require Import Dual.
Open Scope R_scope.

Module RRing <: DRing.
    Definition S := R.
    Definition zero := 0%R.
    Definition one := 1%R.
    Definition add := Rplus.
    Definition mul := Rmult.
    Definition sub := Rminus.
    Definition opp := Ropp.

    Declare Scope S_scope.
    Delimit Scope S_scope with S.
    Notation "0" := zero : S_scope.
    Notation "1" := one : S_scope.
    Infix "+" := add (at level 50, left associativity) : S_scope.
    Infix "-" := sub (at level 50, left associativity) : S_scope.
    Infix "*" := mul (at level 40, left associativity) : S_scope.
    Notation "- x" := (opp x) (at level 35, right associativity) : S_scope.

    (* Decidability of R equality is classical - noncomputable *)
    Definition eqb (x y : R) : bool :=
        if Req_EM_T x y then true else false.

    Lemma eqb_eq : forall s1 s2 : S, reflect (s1 = s2) (eqb s1 s2).
    Proof.
        intros. unfold eqb. destruct (Req_EM_T s1 s2).
        - now apply ReflectT.
        - now apply ReflectF.
    Qed.

    Lemma rt : ring_theory zero one add mul sub opp eq.
    Proof. constructor; intros; unfold add,mul,sub,opp,zero,one; ring. Qed.

    Lemma srt : semi_ring_theory zero one add mul eq.
    Proof. constructor; intros; unfold add,mul,zero,one; ring. Qed.

    Lemma zero_neq_one : (0 <> 1)%S.
    Proof. unfold zero, one. apply not_eq_sym. exact R1_neq_R0. Qed.

    Lemma opp_nonzero : forall x, (- x <> 0 <-> x <> 0)%S.
    Proof.
        intros x. unfold opp, zero. split; intros H Hx.
        - apply H. rewrite Hx. ring.
        - apply H. lra.
    Qed.

    Lemma mul_nonzero : forall x y, (x <> 0 -> y <> 0 -> x * y <> 0)%S.
    Proof.
        intros x y Hx Hy. unfold mul, zero. intro H.
        apply Rmult_integral in H. destruct H; contradiction.
    Qed.
End RRing.

Module RDual := GDual RRing.
