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
open Names
open Nametab
open Term
open Termops
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

(*s Une structure S est un type inductif non récursif à un seul
   constructeur (de nom par défaut Build_S) *)

(* Table des structures: le nom de la structure (un [inductive]) donne
   le nom du constructeur, le nombre de paramètres et pour chaque
   argument réels du constructeur, le noms de la projection
   correspondante, si valide *)

type struc_typ = {
  s_CONST : identifier; 
  s_PARAM : int;
  s_PROJ : constant option list }

let structure_table = (ref [] : (inductive * struc_typ) list ref)

let cache_structure (_,x) = structure_table := x :: (!structure_table)

let (inStruc,outStruc) =
  declare_object
    ("STRUCTURE", {
       load_function = (fun _ -> ());
       cache_function = cache_structure;
       open_function = cache_structure;
       export_function = (function x -> Some x)
     })

let add_new_struc (s,c,n,l) = 
  Lib.add_anonymous_leaf (inStruc (s,{s_CONST=c;s_PARAM=n;s_PROJ=l}))

let find_structure indsp = List.assoc indsp !structure_table

(*s Un "object" est une fonction construisant une instance d'une structure *)

(* Table des definitions "object" : pour chaque object c,

  c := [x1:B1]...[xk:Bk](Build_R a1...am t1...t_n)

  avec ti = (ci ui1...uir)

  Pour tout ci, et Li, la ième projection de la structure R (si
  définie), on déclare une "coercion"

    o_DEF = c
    o_TABS = B1...Bk
    o_PARAMS = a1...am
    o_TCOMP = ui1...uir
*)

type obj_typ = {
  o_DEF : constr;
  o_TABS : constr list;    (* dans l'ordre *)
  o_TPARAMS : constr list; (* dans l'ordre *)
  o_TCOMPS : constr list } (* dans l'ordre *)

let object_table =
  (ref [] : ((global_reference * global_reference) * obj_typ) list ref)

let cache_object (_,x) = object_table := x :: (!object_table)

let (inObjDef, outObjDef) =
  declare_object
    ("OBJDEF", {
       load_function = (fun _ -> ());
       open_function = cache_object;
       cache_function = cache_object;
       export_function = (function x -> Some x)
     })

let add_new_objdef (o,c,la,lp,l) =
  try 
    let _ = List.assoc o !object_table in ()
  with Not_found -> 
    Lib.add_anonymous_leaf
      (inObjDef (o,{o_DEF=c;o_TABS=la;o_TPARAMS=lp;o_TCOMPS=l}))

let cache_objdef1 (_,sp) = ()

let (inObjDef1, outObjDef1) =
  declare_object
    ("OBJDEF1", {
       load_function = (fun _ -> ());
       open_function = cache_objdef1;
       cache_function = cache_objdef1;
       export_function = (function x -> Some x)
     })

let objdef_info o = List.assoc o !object_table

let freeze () = !structure_table, !object_table

let unfreeze (s,o) = structure_table := s; object_table := o

let init () = structure_table := []; object_table:=[]

let _ = init()

let _ = 
  Summary.declare_summary "objdefs"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }
