(* An inline body must survive the merge of two resolvers.

   Applying [F] to [P] gives one field two independent descriptions: the
   functor's resolver names it, [Mod_subst.join] having carried the
   equivalence [P] gets from [Include M0], and the application's substitution
   gives it the body [Parameter Inline] asked for. [add_delta_resolver] merges
   the two. While a resolver held both kinds of statement in a single map, the
   name overwrote the body, and the field stopped being inlined.

   As in resolver_inline_alias.v, the symptom is that the objects attached to
   the field are not replayed: [R.u] loses the argument scope [M0.u] has, so
   [1] is read in the ambient scope -- as [true] -- instead of [nat_scope]. *)

Module Type TI. Parameter Inline t : Type. Parameter u : t -> t. End TI.
Module M0. Definition t := nat. Definition u (x : nat) := x. End M0.
Module P. Include M0. End P.
Module F (X : TI) := X.
Module R := F P.
Notation "1" := true.
Check R.u 1.
