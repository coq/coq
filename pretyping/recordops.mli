
(* $Id$ *)

(*i*)
open Names
open Term
open Generic
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
  s_PROJ : section_path option list }

val add_new_struc : Names.section_path * Names.identifier * int *
    Names.section_path option list -> unit
val struc_info : Names.section_path -> struc_typ

type obj_typ = {
  o_DEF : constr;
  o_TABS : constr list; (* dans l'ordre *)
  o_TPARAMS : constr list; (* dans l'ordre *)
  o_TCOMPS : constr list } (* dans l'ordre *)
               
val oBJDEFS : ((cte_typ*cte_typ) * obj_typ) list ref
val sTRUCS : (section_path * struc_typ) list ref

val objdef_info : (cte_typ*cte_typ) -> obj_typ
val add_new_objdef : (Classops.cte_typ * Classops.cte_typ) * Term.constr * Term.constr list *
    Term.constr list * Term.constr list -> unit


val inStruc : section_path*struc_typ -> obj
val outStruc : obj -> section_path*struc_typ
val inObjDef1 : section_path -> obj
val outObjDef1 : obj -> section_path

val add_new_objdef1 : ((cte_typ*cte_typ) * obj_typ) -> unit
