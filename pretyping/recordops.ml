
(* $Id$ *)

open Util
open Pp
open Names
open Typeops
open Vartab
open Libobject
open Library
open Term
open Pp_control
open Generic
open Initial
open Classops

let nbimpl = ref 0
let nbpathc = ref 0
let nbcoer = ref 0
let nbstruc = ref 0
let nbimplstruc = ref 0

let compter = ref false


(*** table des structures: section_path du struc donne l'id du constructeur,
     le nombre de parame`tres et ses projection valides ***)

type struc_typ = {s_CONST : identifier; 
                  s_PARAM : int;
                  s_PROJ : section_path option list}

let sTRUCS = (ref [] : (section_path * struc_typ) list ref)

let add_new_struc1 x = sTRUCS:=x::(!sTRUCS)


let (inStruc,outStruc) =
    declare_object ("STRUCTURE",
                    {load_function = (fun _ -> ());
                     cache_function = (function  (_,x) -> add_new_struc1 x);
                     specification_function = (function x -> x)})

let add_new_struc (s,c,n,l) = 
add_anonymous_object (inStruc (s,{s_CONST=c;s_PARAM=n;s_PROJ=l}))


let struc_info s = assoc s !sTRUCS


(*** table des definitions "object" : pour chaque object c,
c := [x1:B1]...[xk:Bk](R_Cons a1...am t1...t_n)
 avec ti=(ci ui1...uir)
      
Pour tout ci, et Li correspondant (du record)
     o_DEF = c
     o_TABS = B1...Bk
     o_PARAMS = a1...am
     o_TCOMP = ui1...uir
***)

type obj_typ = {o_DEF : constr;
                o_TABS : constr list; (* dans l'ordre *)
                o_TPARAMS : constr list; (* dans l'ordre *)
                o_TCOMPS : constr list (* dans l'ordre *)
               }

let oBJDEFS = (ref [] : ((cte_typ*cte_typ) * obj_typ) list ref)

let add_new_objdef1 x = oBJDEFS:=x::(!oBJDEFS)


let (inObjDef,outObjDef) =
    declare_object ("OBJDEF",
                    {load_function = (fun _ -> ());
                     cache_function = (function  (_,x) -> add_new_objdef1 x);
                     specification_function = (function x -> x)})

let add_new_objdef (o,c,la,lp,l) =
  try let _ = assoc o !oBJDEFS in ()
  with Not_found -> 
    add_anonymous_object 
      (inObjDef (o,{o_DEF=c;o_TABS=la;o_TPARAMS=lp;o_TCOMPS=l}))



let ((inObjDef1:section_path -> obj),(outObjDef1:obj -> section_path)) =
    declare_object ("OBJDEF1",
                    {load_function = (fun _ -> ());
                     cache_function = (function  (_,sp) -> ());
                     specification_function = (function x -> x)})


(* let objdef_info (o1,o2) = 
  let rec aux = function [] -> raise Not_found 
                       | (x,y)::l -> if (o1,o2) = x then Left(y)
                                     else if (o2,o1) = x then Right(y)
                                          else aux l
  in aux !oBJDEFS

*)

let objdef_info o = assoc o !oBJDEFS

let freeze () = !sTRUCS,!oBJDEFS


let unfreeze (s,o) = sTRUCS:=s;oBJDEFS:=o


let init () = sTRUCS:=[];oBJDEFS:=[]

let _ = init()

let _ = 
  Library.declare_summary "objdefs"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }
