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
open Options
open Names
open Nametab
open Environ
open Libobject
open Library
open Declare
open Term
open Termops
open Rawterm

(* usage qque peu general: utilise aussi dans record *)

type cl_typ = 
  | CL_SORT 
  | CL_FUN
  | CL_SECVAR of variable
  | CL_CONST of constant
  | CL_IND of inductive

type cl_info_typ = {
  cl_strength : strength;
  cl_param : int }

type coe_typ = global_reference

type coe_info_typ = {
  coe_value : unsafe_judgment;
  coe_strength : strength;
  coe_is_identity : bool;
  coe_param : int;
  mutable coe_hide : bool }

type cl_index = int
type coe_index = int

type inheritance_path = coe_index list


(* table des classes, des coercions et graphe d'heritage *)

let class_tab =
  (ref [] : (cl_index * (cl_typ * cl_info_typ)) list ref)

let coercion_tab =
  (ref [] : (coe_index * (coe_typ * coe_info_typ)) list ref)

let inheritance_graph =
  (ref [] : ((cl_index * cl_index) * inheritance_path) list ref) 

let freeze () = (!class_tab, !coercion_tab, !inheritance_graph)

let unfreeze (fcl,fco,fig) = 
  class_tab:=fcl;
  coercion_tab:=fco;
  inheritance_graph:=fig

(* ajout de nouveaux "objets" *)

let newNum_class = 
 let num = ref 0 in
 function () -> (num:=!num+1;!num)

let newNum_coercion = 
 let num = ref 0 in
 function () -> (num:=!num+1;!num)

let add_new_class_num (n,(cl,s)) = 
  class_tab := (n,(cl,s))::(!class_tab)

let add_new_class (cl,s) = 
  add_new_class_num (newNum_class(),(cl,s))

let add_new_coercion_num (n,(coe,s)) = 
  coercion_tab := (n,(coe,s))::(!coercion_tab)

let add_new_coercion (coe,s) = 
  let n = newNum_coercion() in 
  add_new_coercion_num (n,(coe,s));n

let add_new_path x =
  inheritance_graph := x::!inheritance_graph

let init () =
  class_tab:= []; 
  add_new_class (CL_FUN,  { cl_param = 0; cl_strength = NeverDischarge });
  add_new_class (CL_SORT, { cl_param = 0; cl_strength = NeverDischarge });
  coercion_tab:= [];
  inheritance_graph:= []

let _ = init()

(* fonction de recherche *)

let search_info x l = 
  let rec aux = function 
    | [] -> raise Not_found
    | (n,(x1,r))::l -> if x=x1 then (n,r) else aux l
  in 
  aux l

(* class_info : cl_typ -> int * cl_info_typ *)

let class_info cl = search_info cl (!class_tab)

let class_exists cl =
  try let _ = class_info cl in true
  with Not_found -> false

(* class_info_from_index : int -> cl_typ * cl_info_typ *)

let class_info_from_index i = List.assoc i !class_tab

(* coercion_info : coe_typ -> int * coe_info_typ *)

let coercion_info coe = search_info coe !coercion_tab

let coercion_exists coe =
  try let _ = coercion_info coe in true
  with Not_found -> false

let coe_of_reference x = x

let hide_coercion coe =
  let _,coe_info = coercion_info coe in
  if coe_info.coe_hide then Some coe_info.coe_param else None

let set_coercion_visibility b coe =
  let _,coe_info = coercion_info coe in
  coe_info.coe_hide <- not b

let is_coercion_visible coe = 
  let _,coe_info = coercion_info coe in
  not coe_info.coe_hide

let coercion_params coe_info = coe_info.coe_param

(* coercion_info_from_index : int -> coe_typ * coe_info_typ *)

let coercion_info_from_index i = 
  List.assoc i !coercion_tab

let lookup_path_between (s,t) =
  List.assoc (s,t) !inheritance_graph

let lookup_path_to_fun_from s = 
  lookup_path_between (s,fst(class_info CL_FUN))

let lookup_path_to_sort_from s = 
  lookup_path_between (s,fst(class_info CL_SORT))

(* library, summary *)

(*val inClass : (cl_typ * cl_info_typ) -> Libobject.object = <fun>
 val outClass : Libobject.object -> (cl_typ * cl_info_typ) = <fun> *)

let cache_class (_,x) = add_new_class x

let (inClass,outClass) =
  declare_object ("CLASS",
                  { load_function = (fun _ -> ());
		    open_function = cache_class;
                    cache_function = cache_class;
                    export_function = (function x -> Some x) })

let declare_class (cl,stre,p) = 
  Lib.add_anonymous_leaf (inClass ((cl,{ cl_strength = stre; cl_param = p })))
   
let _ = 
  Summary.declare_summary "inh_graph"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init;
      Summary.survive_section = false }

(* classe d'un terme *)

(* constructor_at_head : constr -> cl_typ * int *)

let constructor_at_head t = 
  let rec aux t' = match kind_of_term t' with
    | Var id -> CL_SECVAR id,0
    | Const sp -> CL_CONST sp,0
    | Ind ind_sp -> CL_IND ind_sp,0
    | Prod (_,_,c) -> CL_FUN,0
    | LetIn (_,_,_,c) -> aux c
    | Sort _ -> CL_SORT,0
    | Cast (c,_) -> aux (collapse_appl c)
    | App (f,args) -> let c,_ = aux f in c, Array.length args
    |  _ -> raise Not_found
  in 
  aux (collapse_appl t)

(* class_of : Term.constr -> int *)

let class_of env sigma t = 
  let t,n,n1,i = 
    (try 
       let (cl,n) = constructor_at_head t in
       let (i,{cl_param=n1}) = class_info cl in
       t,n,n1,i              
     with _ -> 
       let t = Tacred.hnf_constr env sigma t in
       let (cl,n) = constructor_at_head t in
       let (i,{cl_param=n1}) = class_info cl in
       t,n,n1,i) 
  in
  if n = n1 then t,i else raise Not_found

let class_args_of c = snd (decompose_app c)

let strength_of_cl = function 
  | CL_CONST sp -> constant_or_parameter_strength sp
  | CL_SECVAR sp -> variable_strength sp
  | _ -> NeverDischarge

let string_of_class = function
  | CL_FUN -> "FUNCLASS"
  | CL_SORT -> "SORTCLASS" 
  | CL_CONST sp -> string_of_id (id_of_global (Global.env()) (ConstRef sp))
  | CL_IND sp -> string_of_id (id_of_global (Global.env()) (IndRef sp))
  | CL_SECVAR sp -> string_of_id (id_of_global (Global.env()) (VarRef sp))

(* coercion_value : int -> unsafe_judgment * bool *)

let coercion_value i = 
  let { coe_value = j; coe_is_identity = b } = snd (coercion_info_from_index i)
  in (j,b)

(* pretty-print functions are now in Pretty *)
(* rajouter une coercion dans le graphe *)

let path_printer = ref (fun _ -> [< 'sTR "<a class path>" >] 
                        : (int * int) * inheritance_path -> std_ppcmds)

let install_path_printer f = path_printer := f
 
let print_path x = !path_printer x

let message_ambig l = 
  [< 'sTR"Ambiguous paths:"; 'sPC;
     prlist_with_sep pr_fnl (fun ijp -> print_path ijp) l >]

(* add_coercion_in_graph : coe_index * cl_index * cl_index -> unit 
                         coercion,source,target *)

let add_coercion_in_graph (ic,source,target) =
  let old_inheritance_graph = !inheritance_graph in
  let ambig_paths =
    (ref [] : ((cl_index * cl_index) * inheritance_path) list ref) in
  let try_add_new_path (p,i,j) =
    try 
      if i=j then begin
	if (snd (class_info_from_index i)).cl_param > 0 then begin
	  let _ = lookup_path_between (i,j) in
          ambig_paths := ((i,j),p)::!ambig_paths
	end
      end else begin
        let _ = lookup_path_between (i,j) in
        ambig_paths := ((i,j),p)::!ambig_paths
      end;
      false
    with Not_found -> begin
      add_new_path ((i,j),p);
      true
    end
  in
  let try_add_new_path1 (p,i,j) = 
    let _ = try_add_new_path (p,i,j) in () 
  in
  if try_add_new_path ([ic],source,target) then begin
    List.iter 
      (fun ((s,t),p) ->
         if s<>t then begin
	   if t = source then begin
             try_add_new_path1 (p @ [ ic ],s,target);
             List.iter 
	       (fun ((u,v),q) ->
                  if u<>v & (u = target) & (p <> q) then 
		    try_add_new_path1 (p @ [ ic ] @ q,s,v))
               old_inheritance_graph
           end;
           if s = target then try_add_new_path1 (ic::p,source,t)
	 end)
      old_inheritance_graph 
  end;
  if (!ambig_paths <> []) && is_verbose () && is_mes_ambig() then 
    pPNL (message_ambig !ambig_paths)

type coercion = (coe_typ * coe_info_typ) * cl_typ * cl_typ

let cache_coercion (_,((coe,xf),cls,clt)) =
  let is,_ = class_info cls in
  let it,_ = class_info clt in
  let jf = add_new_coercion (coe,xf) in
  add_coercion_in_graph (jf,is,it)

(* val inCoercion : (coe_typ * coe_info_typ) * cl_typ * cl_typ  ->
                    -> Libobject.object 
   val outCoercion : Libobject.object -> (coe_typ * coe_info_typ) 
                         * cl_typ * cl_typ *)

let (inCoercion,outCoercion) =
  declare_object ("COERCION",
                  { load_function = (fun _ -> ());
		    open_function = cache_coercion;
                    cache_function = cache_coercion;
                    export_function = (function x -> Some x) })

let declare_coercion coef v stre isid cls clt ps =
  Lib.add_anonymous_leaf
    (inCoercion
       ((coef,
	 { coe_value = v;
	   coe_strength = stre;
	   coe_is_identity = isid;
	   coe_param = ps;
	   coe_hide = true }),
	cls, clt))

let coercion_strength v = v.coe_strength
let coercion_identity v = v.coe_is_identity

(* For printing purpose *)
let get_coercion_value v = v.coe_value.uj_val

let classes () = !class_tab
let coercions () = !coercion_tab
let inheritance_graph () = !inheritance_graph
