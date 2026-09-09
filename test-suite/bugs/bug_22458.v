(* The canonical name a resolver records must itself be canonical.

   [F]'s body aliases its parameter, so [R] records the module equivalence
   [R.Inner ↦ P] and the name of its field is derived from it by the prefix
   rule, which answers [P.n] and stops there. That is not canonical: [P] is
   built by [Include M0], so [P.n] is an alias of [M0.n].

   The equivalence [P.n ↦ M0.n] was there to be transferred, but [Parameter
   Inline] had it shadowed by the inlined body, and [subset_prefixed_by] --
   which is how [Mod_subst.subst_mp_delta] carries the fields of the target of
   an alias under the alias key -- dropped inline data wholesale, losing the
   name with it.

   Nothing rejects such a program: both views agree on the intermediate name, so
   conversion and the kernel's check on names are satisfied. It shows where
   canonical names are compared syntactically, as [Constr.equal] does. *)

Module M0. Definition n := true. End M0.
Module Type TI. Parameter Inline n : bool. End TI.
Module F (X : TI). Module Inner := X. End F.
Module P. Include M0. End P.
Module R := F P.

Goal R.Inner.n = M0.n.
Proof.
  match goal with [ |- M0.n = M0.n ] => idtac end.
  reflexivity.
Qed.
