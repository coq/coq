(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Names
open Term
open Miniml

(*s Special identifiers. [prop_name] is to be used for propositions
    and will be printed as [_] in concrete (Caml) code. *)

val anonymous : identifier
val prop_name : identifier

(* Utility functions over ML types. [update_args sp vl t] puts [vl]
   as arguments behind every inductive types [(sp,_)]. *)

val update_args : section_path -> ml_type list -> ml_type -> ml_type

(*s Utility functions over ML terms. [occurs n t] checks whether [Rel
    n] occurs (freely) in [t]. [ml_lift] is de Bruijn
    lifting. [ml_subst e t] substitutes [e] for [Rel 1] in [t]. *)

val occurs : int -> ml_ast -> bool

val ml_lift : int -> ml_ast -> ml_ast

val ml_subst : ml_ast -> ml_ast -> ml_ast

(* Simplification of singleton inductive types: one contructor
   with one argument is isomorphic to identity *)

val elim_singleton : ml_decl list -> ml_decl list

(*s Some transformations of ML terms. [betared_ast] and [betared_ecl] reduce
    all beta redexes (when the argument does not occur, it is just
    thrown away; when it occurs exactly once it is substituted; otherwise
    a let in redex is created for clarity) *)

val betared_ast : ml_ast -> ml_ast
val betared_decl : ml_decl -> ml_decl

val uncurrify_ast : ml_ast -> ml_ast
val uncurrify_decl : ml_decl -> ml_decl

(*s Optimization. *)

module Refset : Set.S with type elt = global_reference

type extraction_params = {
  modular : bool;       (* modular extraction *)
  optimization : bool;  (* we need optimization *)
  to_keep : Refset.t;   (* globals to keep *)
  to_expand : Refset.t; (* globals to expand *)
}

val optimize : extraction_params -> ml_decl list -> ml_decl list

(*s Table for direct extractions to ML values. *)

val is_ml_extraction : global_reference -> bool
val find_ml_extraction : global_reference -> string

val ml_extractions : unit -> Refset.t
