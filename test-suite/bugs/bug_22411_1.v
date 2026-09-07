(* Minimal spurious rejection caused by the unsubstituted [mod_delta mtb1]
   in Subtyping.check_modtypes. *)
Module Type T.
  Inductive I : Prop := c : I.
End T.

Module F (X : T) <: T.
  Include X.
End F.

Module Type PS (X : T).
  Include X.
End PS.

Module H (K : PS) (X : T).
  Module Res := K X.
End H.

Module Q. Inductive I : Prop := c : I. End Q.

(* [F] is compared against [PS], a functor-vs-functor subtyping check. *)
Module R := H F Q.
(* <in exception printer>: Anomaly "Uncaught exception Not_found." *)
(* <original exception>: Uncaught exception Modops.ModuleTypingError(_). *)
