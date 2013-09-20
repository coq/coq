(* This example (found by coqchk) checks that an inductive cannot be
   polymorphic if its constructors induce upper universe constraints.
   Here: I cannot be polymorphic because its type is less than the
   type of the argument of impl. *)

Definition Type1 := Type.
Definition Type3 : Type1 := Type.                       (* Type3 < Type1 *)
Definition Type4 := Type.
Definition impl (A B:Type3) : Type4 := A->B.           (* Type3 <= Type4 *)
Inductive I (B:Type (*6*)) := C : B -> impl Prop (I B).
    (* Type(6) <= Type(7)     because I contains, via C, elements in B
       Type(7) <=  Type3      because (I B) is argument of impl
       Type(4) <=  Type(7)    because type of C less than I (see remark below)

       where Type(7) is the auxiliary level used to infer the type of I
*)

(* We cannot enforce Type1 < Type(6) while we already have
   Type(6) <= Type(7) < Type3 < Type1 *)
Fail Definition J := I Type1.

(* Open question: should the type of an inductive be the max of the
   types of the _arguments_ of its constructors (here B and Prop,
   after unfolding of impl), or of the max of types of the
   constructors itself (here B -> impl Prop (I B)), as done above. *)
