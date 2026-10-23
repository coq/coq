Require (safe) CMorphisms. (* depends on CRelationClasses *)

(* no implicit arguments, but can be used *)
Type CRelationClasses.flip.
About CRelationClasses.flip.
Print CRelationClasses.flip.

(* universe-polymorphic constant: instances can be given explicitly *)
Check CRelationClasses.flip@{Set Set Set}.

(* a monomorphic Type-former from the same library, showing its universes
   were (the application typechecks) *)
Check CRelationClasses.arrow.
Check (CRelationClasses.arrow nat nat).

(* Print Assumptions on an opaque (Qed) proof exercises the lazy opaque table
   under safe loading *)
Print Assumptions CRelationClasses.complement_inverse.

(* Inductive types and their constructors are available qualified by (at
   least) the name of the file that defines them, as with plain Require;
   bare short names are not available. *)
Require (safe) Corelib.Numbers.BinNums.

Fail Check positive.
Check BinNums.positive.
About BinNums.xI.
Locate BinNums.positive.
Locate BinNums.xH.

(* pattern-matching / unification with a safe-required inductive typechecks *)
Check (fun p : BinNums.positive =>
         match p with
         | BinNums.xI q => q
         | BinNums.xO q => q
         | BinNums.xH => BinNums.xH
         end).

(* Nested modules: PosDef contains an inner module [Pos] with its own
   inductive [mask]. Constants and constructors resolve through the inner
   module path, and the module itself can be located and printed even though
   module names are only pushed at the Synterp stage. *)
Require (safe) Corelib.BinNums.PosDef.

Check Corelib.BinNums.PosDef.Pos.mask.
About Corelib.BinNums.PosDef.Pos.IsPos.
Check Corelib.BinNums.PosDef.Pos.succ.
Locate Module Corelib.BinNums.PosDef.Pos.
Print Module Type Corelib.BinNums.PosDef.Pos.

(* Module types are resolved too. ssrunder declares a [Module Type UNDER_REL]
   and a [Module Under_rel]. *)
Require (safe) Corelib.ssr.ssrunder.

Locate Corelib.ssr.ssrunder.UNDER_REL.
Locate Module Corelib.ssr.ssrunder.Under_rel.

(* could do a full require of safe-required deps instead but needs more work *)
Fail Require SetoidTactics.
