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

(*s A structure S is a non recursive inductive type with a single
   constructor (the name of which defaults to Build_S) *)

val declare_structure : 
  inductive * identifier * bool list * constant option list -> unit

(* [lookup_projections isp] returns the projections associated to the
   inductive path [isp] if it corresponds to a structure, otherwise
   it fails with [Not_found] *)
val lookup_projections : inductive -> constant option list

(* raise [Not_found] if not a projection *)
val find_projection_nparams : global_reference -> int

(*s A canonical structure declares "canonical" conversion hints between *)
(*  the effective components of a structure and the projections of the  *)
(*  structure *)

type cs_pattern =
    Const_cs of global_reference
  | Prod_cs 
  | Sort_cs of sorts_family
  | Default_cs

type obj_typ = {
  o_DEF : constr;
  o_INJ : int;      (* position of trivial argument *)
  o_TABS : constr list;    (* ordered *)
  o_TPARAMS : constr list; (* ordered *)
  o_TCOMPS : constr list } (* ordered *)

val cs_pattern_of_constr : constr -> cs_pattern * int * constr list
 
val lookup_canonical_conversion : (global_reference * cs_pattern) -> obj_typ
val declare_canonical_structure : global_reference -> unit
val is_canonical_projection : constr -> bool
val canonical_projections : unit -> 
  ((global_reference * cs_pattern) * obj_typ) list
