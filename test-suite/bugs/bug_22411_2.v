(* Subtyping between two functors must be performed in a single name space.

   As [Subtyping.check_modtypes] descends into a functor, [subst1] renames the
   implementation's bound parameter into the signature's one. The
   implementation's delta-resolver has to follow, both where it is used
   directly (the environment given to the conversion checks, and [reso1] in
   [check_signatures]) and where it is used indirectly, as the resolver carried
   by [subst2] for [mp2]. Otherwise the canonical names computed on the
   signature side mention the implementation's parameter while the ones
   computed on the implementation side mention the signature's, and the two can
   never be recognised as equal. Inductive types have no delta-rule, so unlike
   constants they cannot recover by unfolding: the check below used to fail
   with

     Signature components for field G.I do not match:
     types given to constructor c differ:
       expected "Ind(MA.G.I,0)" but found "Ind(MA.G.I,0)"

   (the two inductives print the same because only their canonical parts
   differ), and printing that message used to raise
   Anomaly "Uncaught exception Not_found." because it mentions a bound modpath
   that is not in the environment.

   Here [G] is moreover a *functor* field of the module being sealed, so the
   binding [subst2] inherits is the one of the enclosing [MA], whose resolver
   knows nothing about [MA.G]: [mod_global_delta] is [None] on functors, hence
   a functor field's resolver is never merged into its parent. *)

Module Type T. Parameter n : bool. Inductive I : Prop := c : I. End T.
Module Q0. Definition n := true. Inductive I : Prop := c : I. End Q0.
Module Type TQ0. Include Q0. End TQ0.

Module F (X : T) <: T.
  Module Sub := X.
  Include X.
End F.

Module Type PS (X : TQ0).
  Parameter n : bool.
  Inductive I : Prop := c : I.
  Declare Module Sub : TQ0.
End PS.

Module Type MF. Declare Module G : PS. End MF.

Module MA : MF.
  Module G := F.
End MA.
