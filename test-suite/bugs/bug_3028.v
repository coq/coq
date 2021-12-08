Class WT (A : Type) := inhabited : A.
Instance nat_WT : WT nat := O.
Inductive dumb (B : Type) {B_WT : WT B} := cons : dumb nat -> dumb B.
