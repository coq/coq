(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Univ
open Term
open Declarations
open Environ
open Typeops
(*i*)


(*s The different kinds of errors that may result of a malformed inductive
  definition. *)

type inductive_error =
  (* These are errors related to inductive constructions in this module *)
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | SameNamesOverlap of identifier list
  | NotAnArity of identifier
  | BadEntry
  (* These are errors related to recursors building in Indrec *)
  | NotAllowedCaseAnalysis of bool * sorts * inductive
  | BadInduction of bool * identifier * sorts
  | NotMutualInScheme

exception InductiveError of inductive_error

(*s Declaration of inductive types. *)

(* Assume the following definition in concrete syntax:
\begin{verbatim}
Inductive I1 [x1:X1;...;xn:Xn] : A1 := c11 : T11 | ... | c1n1 : T1n1
...
with  Ip [x1:X1;...;xn:Xn] : Ap := cp1 : Tp1 | ... | cpnp : Tpnp.
\end{verbatim}
then, in $i^{th}$ block, [mind_entry_params] is [[xn:Xn;...;x1:X1]];
[mind_entry_arity] is [Ai], defined in context [[[x1:X1;...;xn:Xn]];
[mind_entry_lc] is [Ti1;...;Tini], defined in context [[A'1;...;A'p;x1:X1;...;xn:Xn]] where [A'i] is [Ai] generalized over [[x1:X1;...;xn:Xn]].
*)

type one_inductive_entry = {
  mind_entry_params : (identifier * local_entry) list;
  mind_entry_typename : identifier;
  mind_entry_arity : constr;
  mind_entry_consnames : identifier list;
  mind_entry_lc : constr list }

type mutual_inductive_entry = {
  mind_entry_finite : bool;
  mind_entry_inds : one_inductive_entry list }

(*s The following function does checks on inductive declarations. *)

val check_inductive :
  env -> mutual_inductive_entry -> mutual_inductive_body
