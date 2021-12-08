Set Primitive Projections.
Set Implicit Arguments.
Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Definition eta_sigma {A} {P : A -> Type} (u : sigT P)
  : existT _ (projT1 u) (projT2 u) = u
  := match u with existT _ x y => eq_refl end. (* Toplevel input, characters 0-139:
Error: Pattern-matching expression on an object of inductive type sigT
has invalid information. *)
Definition sum_of_sigT A B (x : sigT (fun b : bool => if b then A else B))
: A + B
  := match x with
       | existT _ true a => inl a
       | existT _ false b => inr b
     end. (* Toplevel input, characters 0-182:
Error: Pattern-matching expression on an object of inductive type sigT
has invalid information. *)
