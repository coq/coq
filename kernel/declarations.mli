(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Identifier
open Names
open Univ
open Term
open Sign
(*i*)

(* This module defines the types of global declarations. This includes
   global constants/axioms and mutual inductive definitions.
   [*_body] is the information kept in the environment, while
   [*_entry] is the information provided by the user to be typechecked *)

(*s Constants (internal representation) (Definition/Axiom) *)

type constant_body = {
  const_body : constr option;
  const_type : types;
  const_hyps : section_context; (* New: younger hyp at top *)
  const_constraints : constraints;
  mutable const_opaque : bool }

val is_defined : constant_body -> bool

val is_opaque : constant_body -> bool

(*s Global and local constant declaration. *)

type constant_entry = {
  const_entry_body : constr option;
  const_entry_type : constr option }

type local_entry =
  | LocalDef of constr
  | LocalAssum of constr

(*s Inductive types (internal representation). *)

type recarg = 
  | Param of int 
  | Norec 
  | Mrec of int 
  | Imbr of inductive_path * (recarg list)

(* [mind_typename] is the name of the inductive; [mind_arity] is
   the arity generalized over global parameters; [mind_lc] is the list
   of types of constructors generalized over global parameters and
   relative to the global context enriched with the arities of the
   inductives *) 

type one_inductive_body = {
  mind_consnames : label array;
  mind_typename : label;
  mind_nf_lc : types array; (* constrs and arity with pre-expanded ccl *)
  mind_nf_arity : types;
  mind_user_lc : types array option;
  mind_user_arity : types option;
  mind_sort : sorts;
  mind_nrealargs : int;
  mind_kelim : sorts list;
  mind_listrec : (recarg list) array;
  mind_finite : bool;
  mind_nparams : int;
  mind_params_ctxt : rel_context }

type mutual_inductive_body = {
  mind_ntypes : int;
  mind_hyps : section_context;
  mind_packets : one_inductive_body array;
  mind_constraints : constraints }

val mind_type_finite : mutual_inductive_body -> int -> bool
val mind_user_lc : one_inductive_body -> types array
val mind_user_arity : one_inductive_body -> types
val mind_nth_type_packet : mutual_inductive_body -> int -> one_inductive_body

val mind_arities_context : mutual_inductive_body -> rel_declaration list

(*s Declaration of inductive types. *)

(* Assume the following definition in concrete syntax:
\begin{verbatim}
Inductive I1 [x1:X1;...;xn:Xn] : A1 := c11 : T11 | ... | c1n1 : T1n1
...
with  Ip [x1:X1;...;xn:Xn] : Ap := cp1 : Tp1 | ... | cpnp : Tpnp.
\end{verbatim}
then, in $i^{th}$ block, [mind_entry_params] is [[xn:Xn;...;x1:X1]];
[mind_entry_arity] is [Ai], defined in context [[x1:X1;...;xn:Xn]];
[mind_entry_lc] is [Ti1;...;Tini], defined in context [[A'1;...;A'p;x1:X1;...;xn:Xn]] where [A'i] is [Ai] generalized over [[x1:X1;...;xn:Xn]].
Note, that contexts are stacks rather than lists, so that is why 
[mind_entry_params] seems reversed.
*)

type one_inductive_entry = {
  mind_entry_nparams : int;
  mind_entry_params : (identifier * local_entry) list;
  mind_entry_typename : label;
  mind_entry_arity : constr;
  mind_entry_consnames : label list;
  mind_entry_lc : constr list }

type mutual_inductive_entry = {
  mind_entry_finite : bool;
  mind_entry_inds : one_inductive_entry list }


