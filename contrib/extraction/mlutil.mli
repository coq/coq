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
open Nametab

(*s Special identifiers. [prop_name] is to be used for propositions
    and will be printed as [_] in concrete (Caml) code. *)

val anonymous : identifier
val prop_name : identifier

(* Utility functions over ML types. [update_args sp vl t] puts [vl]
   as arguments behind every inductive types [(sp,_)]. *)

val update_args : section_path -> ml_type list -> ml_type -> ml_type

exception Found_sp

val sp_of_r : global_reference -> section_path

val parse_ml_type : section_path -> ml_type -> unit

(*s Utility functions over ML terms. [occurs n t] checks whether [Rel
    n] occurs (freely) in [t]. [ml_lift] is de Bruijn
    lifting. [ml_subst e t] substitutes [e] for [Rel 1] in [t]. *)

val occurs : int -> ml_ast -> bool

val ml_lift : int -> ml_ast -> ml_ast

val ml_subst : ml_ast -> ml_ast -> ml_ast

val subst_glob_ast : global_reference -> ml_ast -> ml_ast -> ml_ast

(*s [collect_lambda MLlam(id1,...MLlam(idn,t)...)] returns
    the list [idn;...;id1] and the term [t]. *)

val collect_lams : ml_ast -> identifier list * ml_ast

(* [named_abstract] is the converse of [collect_lambda]. *)

val named_lams : ml_ast -> identifier list -> ml_ast

val anonym_lams : ml_ast -> int -> ml_ast


(*s Some transformations of ML terms. [normalize] and [normalize_decl] reduce
    all beta redexes (when the argument does not occur, it is just
    thrown away; when it occurs exactly once it is substituted; otherwise
    a let in redex is created for clarity) and iota redexes, plus some other
    optimizations. *)  (* TO UPDATE *)

val normalize : ml_ast -> ml_ast
val normalize_decl : ml_decl -> ml_decl

(*s Optimization. *)

val add_ml_decls : 
  extraction_params -> ml_decl list -> ml_decl list

val optimize : 
  extraction_params -> ml_decl list -> ml_decl list

