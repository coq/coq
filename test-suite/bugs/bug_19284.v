Require Export Corelib.Program.Tactics.

Set Printing Universes.

Polymorphic Class Countable A := { encode : A }.
Axiom NonExpansive : Prop.
Axiom gmapURF : forall K {_ : Countable K} , NonExpansive.

Local Obligation Tactic := idtac.

Program Definition gmapRF K {_ : Countable K} : NonExpansive := _.

Solve Obligations with apply gmapURF.
(* Next Obligation. apply gmapURF. Qed. *)
(*
Error: Illegal application:
The term "gmapRF_obligation_1" of type
 "forall K : Type@{gmapURF.u0}, Countable@{gmapURF.u0} K -> NonExpansive"
cannot be applied to the terms
 "K" : "Type@{gmapRF_obligation_1.u0}"
 "c" : "Countable@{gmapRF_obligation_1.u0} K"
The 1st term has type "Type@{gmapRF_obligation_1.u0}" which should be a subtype of
 "Type@{gmapURF.u0}".
*)
