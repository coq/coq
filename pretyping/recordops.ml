(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Pp
open Identifier
open Names
open Term
open Typeops
open Libobject
open Library
open Classops

let nbimpl = ref 0
let nbpathc = ref 0
let nbcoer = ref 0
let nbstruc = ref 0
let nbimplstruc = ref 0

let compter = ref false


(*** table des structures: section_path du struc donne l'id du constructeur,
     le nombre de parame`tres et ses projection valides ***)

type struc_typ = {
  s_CONST : identifier; 
  s_PARAM : int;
  s_PROJ : long_name option list }

let sTRUCS = (ref [] : (inductive_path * struc_typ) list ref)

let add_new_struc1 x = sTRUCS:=x::(!sTRUCS)

let cache_structure (_,x) = add_new_struc1 x

let (inStruc,outStruc) =
  declare_object ("STRUCTURE",
                  { load_function = (fun _ -> ());
                    cache_function = cache_structure;
		    open_function = cache_structure;
                    export_function = (function x -> Some x) })

let add_new_struc (s,c,n,l) = 
  Lib.add_anonymous_leaf (inStruc (s,{s_CONST=c;s_PARAM=n;s_PROJ=l}))

let find_structure indsp = List.assoc indsp !sTRUCS

(*** table des definitions "object" : pour chaque object c,
c := [x1:B1]...[xk:Bk](R_Cons a1...am t1...t_n)
 avec ti=(ci ui1...uir)
      
Pour tout ci, et Li correspondant (du record)
     o_DEF = c
     o_TABS = B1...Bk
     o_PARAMS = a1...am
     o_TCOMP = ui1...uir
***)

type obj_typ = {
  o_DEF : constr;
  o_TABS : constr list;    (* dans l'ordre *)
  o_TPARAMS : constr list; (* dans l'ordre *)
  o_TCOMPS : constr list } (* dans l'ordre *)

let oBJDEFS =
  (ref [] : ((global_reference * global_reference) * obj_typ) list ref)

let add_new_objdef1 x = oBJDEFS:=x::(!oBJDEFS)

let cache_obj (_,x) = add_new_objdef1 x

let (inObjDef,outObjDef) =
  declare_object ("OBJDEF",
                  { load_function = (fun _ -> ());
		    open_function = cache_obj;
                    cache_function = cache_obj;
                    export_function = (function x -> Some x)})

let add_new_objdef (o,c,la,lp,l) =
  try 
    let _ = List.assoc o !oBJDEFS in ()
  with Not_found -> 
    Lib.add_anonymous_leaf
      (inObjDef (o,{o_DEF=c;o_TABS=la;o_TPARAMS=lp;o_TCOMPS=l}))

let cache_objdef1 (_,sp) = ()

let ((inObjDef1 : long_name -> obj),(outObjDef1 : obj -> long_name)) =
  declare_object ("OBJDEF1",
                  { load_function = (fun _ -> ());
		    open_function = cache_objdef1;
                    cache_function = cache_objdef1;
                    export_function = (function x -> Some x)})

let objdef_info o = List.assoc o !oBJDEFS

let freeze () = !sTRUCS,!oBJDEFS

let unfreeze (s,o) = sTRUCS := s; oBJDEFS := o

let init () = sTRUCS:=[];oBJDEFS:=[]

let _ = init()

let _ = 
  Summary.declare_summary "objdefs"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }
