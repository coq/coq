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
open Term
open Classops
open Libobject
open Library
(*i*)

val nbimpl : int ref
val nbpathc : int ref
val nbcoer : int ref
val nbstruc : int ref
val nbimplstruc : int ref
val compter : bool ref

type struc_typ = {
  s_CONST : identifier; 
  s_PARAM : int;
  s_PROJ : long_name option list }

val add_new_struc : 
  inductive_path * identifier * int * long_name option list -> unit

(* [find_structure isp] returns the infos associated to inductive path
   [isp] if it corresponds to a structure, otherwise fails with [Not_found] *)
val find_structure : inductive_path -> struc_typ

type obj_typ = {
  o_DEF : constr;
  o_TABS : constr list; (* dans l'ordre *)
  o_TPARAMS : constr list; (* dans l'ordre *)
  o_TCOMPS : constr list } (* dans l'ordre *)
               
val objdef_info : (global_reference * global_reference) -> obj_typ
val add_new_objdef : 
  (global_reference * global_reference) * Term.constr * Term.constr list *
  Term.constr list * Term.constr list -> unit


val inStruc : inductive_path * struc_typ -> obj
val outStruc : obj -> inductive_path * struc_typ
val inObjDef1 : long_name -> obj
val outObjDef1 : obj -> long_name

val add_new_objdef1 : ((global_reference * global_reference) * obj_typ) -> unit
