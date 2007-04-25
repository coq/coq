(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Univ
open Term
open Sign
(*i*)

(* This module defines the entry types for global declarations. This
   information is entered in the environments. This includes global
   constants/axioms, mutual inductive definitions, modules and module
   types *)


(*s Local entries *)

type local_entry =
  | LocalDef of constr
  | LocalAssum of constr


(*s Declaration of inductive types. *)

(* Assume the following definition in concrete syntax:
\begin{verbatim}
Inductive I1 (x1:X1) ... (xn:Xn) : A1 := c11 : T11 | ... | c1n1 : T1n1
...
with      Ip (x1:X1) ... (xn:Xn) : Ap := cp1 : Tp1 | ... | cpnp : Tpnp.
\end{verbatim}
then, in $i^{th}$ block, [mind_entry_params] is [[xn:Xn;...;x1:X1]];
[mind_entry_arity] is [Ai], defined in context [[[x1:X1;...;xn:Xn]];
[mind_entry_lc] is [Ti1;...;Tini], defined in context [[A'1;...;A'p;x1:X1;...;xn:Xn]] where [A'i] is [Ai] generalized over [[x1:X1;...;xn:Xn]].
*)

type one_inductive_entry = {
  mind_entry_typename : identifier;
  mind_entry_arity : constr;
  mind_entry_consnames : identifier list;
  mind_entry_lc : constr list }

type mutual_inductive_entry = {
  mind_entry_record : bool;
  mind_entry_finite : bool;
  mind_entry_params : (identifier * local_entry) list;
  mind_entry_inds : one_inductive_entry list }


(*s Constants (Definition/Axiom) *)

type definition_entry = {
  const_entry_body   : constr;
  const_entry_type   : types option;
  const_entry_opaque : bool;
  const_entry_boxed  : bool}

type parameter_entry = types*bool

type constant_entry = 
  | DefinitionEntry of definition_entry
  | ParameterEntry of parameter_entry

(*s Modules *)

type specification_entry = 
    SPEconst of constant_entry
  | SPEmind of mutual_inductive_entry
  | SPEmodule of module_entry
  | SPEmodtype of module_type_entry

and module_type_entry = 
    MTEident of kernel_name
  | MTEfunsig of mod_bound_id * module_type_entry * module_type_entry
  | MTEwith of module_type_entry * with_declaration

and module_signature_entry = (label * specification_entry) list

and with_declaration = 
    With_Module of identifier list * module_path
  | With_Definition of identifier list * constr

and module_expr = 
    MEident of module_path
  | MEfunctor of mod_bound_id * module_type_entry * module_expr
  | MEapply of module_expr * module_expr

and module_structure = (label * specification_entry) list


and module_entry = 
    { mod_entry_type : module_type_entry option;
      mod_entry_expr : module_expr option}

