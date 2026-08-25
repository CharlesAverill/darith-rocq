From DArith Require Import ZDual.
Import ZDual.
From Stdlib Require Import Lia.
Open Scope Z_scope.
Open Scope D_scope.

Example ex_2_7_real_cancels :
    (5, 8) + (-5, 9) = (0, 17).
Proof. reflexivity. Qed.

Example ex_2_7_eqb :
    (5, 8) + (-5, 9) =? (0, 17) = true.
Proof. reflexivity. Qed.

Example ex_2_7_summands_strict :
    real (5, 8) <> 0 /\ du (5, 8) <> 0 /\
    real (-5, 9) <> 0 /\ du (-5, 9) <> 0.
Proof. cbn. repeat split; try discriminate; lia. Qed.

Example ex_du_cancels :
    (12, 15) + (-3, -15) = (9, 0).
Proof. reflexivity. Qed.

Example ex_sum_zero :
    (1, 1) + (-1, -1) = D0.
Proof. reflexivity. Qed.

Example ex_2_3_product :
    (2, 3) * (4, 5) = (8, 22).
Proof. reflexivity. Qed.

Example ex_2_3_product_strict :
    real ((2, 3) * (4, 5)) <> 0 /\
    du   ((2, 3) * (4, 5)) <> 0.
Proof. cbn. split; discriminate. Qed.

Example ex_eps_sq :
    \e * \e = D0.
Proof. reflexivity. Qed.

Example ex_eps_nonzero :
    \e <> D0.
Proof. discriminate. Qed.
