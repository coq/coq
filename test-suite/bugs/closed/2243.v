Inductive is_nul: nat -> Prop := X: is_nul 0.
Section O.
Variable u: nat.
Variable H: is_nul u.
Goal True.
Proof.
destruct H.
Undo.
revert H; intro H; destruct H.
