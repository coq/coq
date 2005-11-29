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
open Nametab
open Term
open Libnames
open Classops
open Libobject
open Library
(*i*)

type struc_typ = {
  s_CONST : identifier; 
  s_PARAM : int;
  s_PROJ : constant option list }

val add_new_struc : 
  inductive * identifier * int * constant option list -> unit

(* [find_structure isp] returns the infos associated to inductive path
   [isp] if it corresponds to a structure, otherwise fails with [Not_found] *)
val find_structure : inductive -> struc_typ

(* raise [Not_found] if not a projection *)
val find_projection_nparams : global_reference -> int

type obj_typ = {
  o_DEF : constr;
  o_TABS : constr list; (* dans l'ordre *)
  o_TPARAMS : constr list; (* dans l'ordre *)
  o_TCOMPS : constr list } (* dans l'ordre *)
               
val objdef_info : (global_reference * global_reference) -> obj_typ
val add_new_objdef : 
  (global_reference * global_reference) * Term.constr * Term.constr list *
  Term.constr list * Term.constr list -> unit


val inStruc : inductive * struc_typ -> obj
val outStruc : obj -> inductive * struc_typ
val inObjDef1 : kernel_name -> obj
val outObjDef1 : obj -> kernel_name
