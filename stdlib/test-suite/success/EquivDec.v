From Stdlib Require Import EquivDec.

Example test_None_eqb_None: None ==b None = true. Proof. reflexivity. Qed.
Example test_None_eqb_Some: None ==b Some true = false. Proof. reflexivity. Qed.
Example test_Some_eqb_Some: Some 1 ==b Some 1 = true. Proof. reflexivity. Qed.
Example test_Some_neqb_Some: Some 0 ==b Some 1 = false. Proof. reflexivity. Qed.
