(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

open Names
open Term

(* Maps fron \em{unshared} [constr] to ['a]. *)
module CicHash =
 Hashtbl.Make
  (struct
    type t = Term.constr
    let equal = (==)
    let hash = Hashtbl.hash
   end)
;;

type id = string  (* the type of the (annotated) node identifiers *)
type uri = string

type 'constr context_entry =
   Decl of 'constr             (* Declaration *)
 | Def  of 'constr * 'constr   (* Definition; the second argument (the type) *)
                               (* is not present in the DTD, but is needed   *)
                               (* to use Coq functions during exportation.   *)

type 'constr hypothesis = identifier * 'constr context_entry
type context = constr hypothesis list

type conjecture = existential_key * context * constr
type metasenv = conjecture list

(* list of couples section path -- variables defined in that section *)
type params = (string * uri list) list

type obj =
   Constant of string *                            (* id,           *)
    constr option * constr *                       (*  value, type, *)
    params                                         (*  parameters   *)
 | Variable of
    string * constr option * constr *              (* name, body, type *)
    params                                         (*  parameters   *)
 | CurrentProof of
    string * metasenv *                            (*  name, conjectures, *)
    constr * constr                                (*  value, type        *)
 | InductiveDefinition of
    inductiveType list *                           (* inductive types ,      *)
    params * int                                   (*  parameters,n ind. pars*)
and inductiveType =
 identifier * bool * constr *                 (* typename, inductive, arity *)
  constructor list                            (*  constructors              *)
and constructor =
 identifier * constr                          (* id, type *)

type aconstr =
  | ARel       of id * int * id * identifier
  | AVar       of id * uri
  | AEvar      of id * existential_key * aconstr list
  | ASort      of id * sorts
  | ACast      of id * aconstr * aconstr
  | AProds     of (id * name * aconstr) list * aconstr
  | ALambdas   of (id * name * aconstr) list * aconstr
  | ALetIns    of (id * name * aconstr) list * aconstr
  | AApp       of id * aconstr list
  | AConst     of id * explicit_named_substitution * uri
  | AInd       of id * explicit_named_substitution * uri * int
  | AConstruct of id * explicit_named_substitution * uri * int * int
  | ACase      of id * uri * int * aconstr * aconstr * aconstr list
  | AFix       of id * int * ainductivefun list
  | ACoFix     of id * int * acoinductivefun list
and ainductivefun =
 id * identifier * int * aconstr * aconstr
and acoinductivefun =
 id * identifier * aconstr * aconstr
and explicit_named_substitution = id option * (uri * aconstr) list

type acontext = (id * aconstr hypothesis) list
type aconjecture = id * existential_key * acontext * aconstr
type ametasenv = aconjecture list

type aobj =
   AConstant of id * string *                      (* id,           *)
    aconstr option * aconstr *                     (*  value, type, *)
    params                                         (*  parameters   *)
 | AVariable of id *
    string * aconstr option * aconstr *            (* name, body, type *)
    params                                         (*  parameters   *)
 | ACurrentProof of id *
    string * ametasenv *                           (*  name, conjectures, *)
    aconstr * aconstr                              (*  value, type        *)
 | AInductiveDefinition of id *
    anninductiveType list *                        (* inductive types ,      *)
    params * int                                   (*  parameters,n ind. pars*)
and anninductiveType =
 id * identifier * bool * aconstr *           (* typename, inductive, arity *)
  annconstructor list                         (*  constructors              *)
and annconstructor =
 identifier * aconstr                         (* id, type *)
