Require Export PrimInt63.
Require Import Uint63Axioms.

Declare Scope sint63_scope.
Delimit Scope sint63_scope with sint63.
Definition printer (x : int_wrapper) : pos_neg_int63 :=
  if (ltb (int_wrap x) 4611686018427387904)%uint63 then (* 2^62 *)
    Pos (int_wrap x)
  else
    Neg (add (lxor (int_wrap x) max_int) 1)%uint63.
Definition parser (x : pos_neg_int63) : option int :=
  match x with
  | Pos p => if (ltb p 4611686018427387904)%uint63 then Some p else None
  | Neg n => if (leb n 4611686018427387904)%uint63
             then Some (lxor (sub n 1) max_int)%uint63 else None
  end.
Number Notation int parser printer : sint63_scope.
