(* A delta-resolver binding on a modpath records either the canonical form of
   that path, or a marker saying that the prefix rule must not be extrapolated
   into it ([Mod_subst.lift_mp_delta_resolver], recorded by
   [Modops.strengthen_and_subst_struct] for every functor field and every module
   type field of the module it builds).

   The two transport differently -- a canonical name is left alone, a marker
   travels with its key -- and while both were spelled [p -> p] they were
   indistinguishable, so α-renaming a resolver turned a marker into a genuine
   alias to the source. The two directions of the equivalence check that
   [Subtyping.check_signatures] runs on a module type field then disagreed on
   the canonical name of the inductive declared inside it, and the sealing below
   was rejected with an error that could not even be printed. *)

Module Type HasS. Module Type S. Inductive I := c. End S. End HasS.
Module Type T. Declare Module M : HasS. End T.

Module B.
  Module Type S. Inductive I := c. End S.
End B.

Module C := B. (* first hop: marks C.S *)

Module D : T.
  Module M := C. (* second hop: used to lose the mark *)
End D.

(* The same shape with a functor field rather than a module type field, the
   other kind of field [strengthen_and_subst_struct] marks. It takes a
   [with Module] to make the parameter type's [M] be [B'] itself, so that the
   two sides of the check compare the resolver of [B'] with the ambient one;
   sealing against a module type that merely declares a functor field of the
   same shape gives them nothing in common to disagree about. The parameter type
   of [Fn] must have content, for the same reason.

   On its own this no longer trips anything -- the [subst_mp_delta] fix of
   #22445 is enough for it -- so it is kept as a guard on the marker of a
   functor field, not as a reproducer. *)

Module Type Any. End Any.
Module Type TAny. Declare Module M : Any. End TAny.

Module Type WithI. Inductive I := c. End WithI.

Module B'.
  Module Fn (X : WithI) := X.
End B'.

Module D' : TAny with Module M := B'.
  Module M := B'.
End D'.

(* Another funky test. *)

Module Other.

Module A.
  Module E. Definition n := false. End E.
  Module B.
    Module P. Include A.E. End P.
  End B.
  Include B.
End A.

Include A.

Definition p := P.n.

End Other.
