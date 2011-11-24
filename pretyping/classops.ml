(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Flags
open Names
open Libnames
open Nametab
open Environ
open Libobject
open Library
open Term
open Termops
open Glob_term
open Decl_kinds
open Mod_subst

(* usage qque peu general: utilise aussi dans record *)

(* A class is a type constructor, its type is an arity whose number of
   arguments is cl_param (0 for CL_SORT and CL_FUN) *)

type cl_typ =
  | CL_SORT
  | CL_FUN
  | CL_SECVAR of variable
  | CL_CONST of constant
  | CL_IND of inductive

type cl_info_typ = {
  cl_param : int
}

type coe_typ = global_reference

type coe_info_typ = {
  coe_value : constr;
  coe_type : types;
  coe_strength : locality;
  coe_is_identity : bool;
  coe_param : int }

let coe_info_typ_equal c1 c2 =
  eq_constr c1.coe_value c2.coe_value &&
    eq_constr c1.coe_type c2.coe_type &&
    c1.coe_strength = c2.coe_strength &&
    c1.coe_is_identity = c2.coe_is_identity &&
    c1.coe_param = c2.coe_param

type cl_index = int

type coe_index = coe_info_typ

type inheritance_path = coe_index list

(* table des classes, des coercions et graphe d'heritage *)

module Bijint = struct
  type ('a,'b) t = { v : ('a * 'b) array; s : int; inv : ('a,int) Gmap.t }
  let empty = { v = [||]; s = 0; inv = Gmap.empty }
  let mem y b = Gmap.mem y b.inv
  let map x b = if 0 <= x & x < b.s then b.v.(x) else raise Not_found
  let revmap y b = let n = Gmap.find y b.inv in (n, snd (b.v.(n)))
  let add x y b =
    let v =
      if b.s = Array.length b.v then
	(let v = Array.make (b.s + 8) (x,y) in Array.blit b.v 0 v 0 b.s; v)
      else b.v in
    v.(b.s) <- (x,y); { v = v; s = b.s+1; inv = Gmap.add x b.s b.inv }
  let dom b = Gmap.dom b.inv
end

let class_tab =
  ref (Bijint.empty : (cl_typ, cl_info_typ) Bijint.t)

let coercion_tab =
  ref (Gmap.empty : (coe_typ, coe_info_typ) Gmap.t)

let inheritance_graph =
  ref (Gmap.empty : (cl_index * cl_index, inheritance_path) Gmap.t)

let freeze () = (!class_tab, !coercion_tab, !inheritance_graph)

let unfreeze (fcl,fco,fig) =
  class_tab:=fcl;
  coercion_tab:=fco;
  inheritance_graph:=fig

(* ajout de nouveaux "objets" *)

let add_new_class cl s =
  if not (Bijint.mem cl !class_tab) then
    class_tab := Bijint.add cl s !class_tab

let add_new_coercion coe s =
  coercion_tab := Gmap.add coe s !coercion_tab

let add_new_path x y =
  inheritance_graph := Gmap.add x y !inheritance_graph

let init () =
  class_tab:= Bijint.empty;
  add_new_class CL_FUN  { cl_param = 0 };
  add_new_class CL_SORT { cl_param = 0 };
  coercion_tab:= Gmap.empty;
  inheritance_graph:= Gmap.empty

let _ =
  Summary.declare_summary "inh_graph"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let _ = init()

(* class_info : cl_typ -> int * cl_info_typ *)

let class_info cl = Bijint.revmap cl !class_tab

let class_exists cl = Bijint.mem cl !class_tab

(* class_info_from_index : int -> cl_typ * cl_info_typ *)

let class_info_from_index i = Bijint.map i !class_tab

let cl_fun_index = fst(class_info CL_FUN)

let cl_sort_index = fst(class_info CL_SORT)

(* coercion_info : coe_typ -> coe_info_typ *)

let coercion_info coe = Gmap.find coe !coercion_tab

let coercion_exists coe = Gmap.mem coe !coercion_tab

(* find_class_type : evar_map -> constr -> cl_typ * constr list *)

let find_class_type sigma t =
  let t', args = Reductionops.whd_betaiotazeta_stack sigma t in
  match kind_of_term t' with
    | Var id -> CL_SECVAR id, args
    | Const sp -> CL_CONST sp, args
    | Ind ind_sp -> CL_IND ind_sp, args
    | Prod (_,_,_) -> CL_FUN, []
    | Sort _ -> CL_SORT, []
    |  _ -> raise Not_found


let subst_cl_typ subst ct = match ct with
    CL_SORT
  | CL_FUN
  | CL_SECVAR _ -> ct
  | CL_CONST kn ->
      let kn',t = subst_con subst kn in
	if kn' == kn then ct else
         fst (find_class_type Evd.empty t)
  | CL_IND (kn,i) ->
      let kn' = subst_ind subst kn in
	if kn' == kn then ct else
	  CL_IND (kn',i)

(*CSC: here we should change the datatype for coercions: it should be possible
       to declare any term as a coercion *)
let subst_coe_typ subst t = fst (subst_global subst t)

(* class_of : Term.constr -> int *)

let class_of env sigma t =
  let (t, n1, i, args) =
    try
      let (cl,args) = find_class_type sigma t in
      let (i, { cl_param = n1 } ) = class_info cl in
      (t, n1, i, args)
    with Not_found ->
      let t = Tacred.hnf_constr env sigma t in
      let (cl, args) = find_class_type sigma t in
      let (i, { cl_param = n1 } ) = class_info cl in
      (t, n1, i, args)
  in
  if List.length args = n1 then t, i else raise Not_found

let inductive_class_of ind = fst (class_info (CL_IND ind))

let class_args_of env sigma c = snd (find_class_type sigma c)

let string_of_class = function
  | CL_FUN -> "Funclass"
  | CL_SORT -> "Sortclass"
  | CL_CONST sp ->
      string_of_qualid (shortest_qualid_of_global Idset.empty (ConstRef sp))
  | CL_IND sp ->
      string_of_qualid (shortest_qualid_of_global Idset.empty (IndRef sp))
  | CL_SECVAR sp ->
      string_of_qualid (shortest_qualid_of_global Idset.empty (VarRef sp))

let pr_class x = str (string_of_class x)

(* lookup paths *)

let lookup_path_between_class (s,t) =
  Gmap.find (s,t) !inheritance_graph

let lookup_path_to_fun_from_class s =
  lookup_path_between_class (s,cl_fun_index)

let lookup_path_to_sort_from_class s =
  lookup_path_between_class (s,cl_sort_index)

(* advanced path lookup *)

let apply_on_class_of env sigma t cont =
  try
    let (cl,args) = find_class_type sigma t in
    let (i, { cl_param = n1 } ) = class_info cl in
    if List.length args <> n1 then raise Not_found;
    t, cont i
  with Not_found ->
    (* Is it worth to be more incremental on the delta steps? *)
    let t = Tacred.hnf_constr env sigma t in
    let (cl, args) = find_class_type sigma t in
    let (i, { cl_param = n1 } ) = class_info cl in
    if List.length args <> n1 then raise Not_found;
    t, cont i

let lookup_path_between env sigma (s,t) =
  let (s,(t,p)) =
    apply_on_class_of env sigma s (fun i ->
      apply_on_class_of env sigma t (fun j ->
	lookup_path_between_class (i,j))) in
  (s,t,p)

let lookup_path_to_fun_from env sigma s =
  apply_on_class_of env sigma s lookup_path_to_fun_from_class

let lookup_path_to_sort_from env sigma s =
  apply_on_class_of env sigma s lookup_path_to_sort_from_class

let get_coercion_constructor coe =
  let c, _ =
    Reductionops.whd_betadeltaiota_stack (Global.env()) Evd.empty coe.coe_value
  in
  match kind_of_term c with
  | Construct cstr ->
      (cstr, Inductiveops.constructor_nrealargs (Global.env()) cstr -1)
  | _ ->
      raise Not_found

let lookup_pattern_path_between (s,t) =
  let i = inductive_class_of s in
  let j = inductive_class_of t in
  List.map get_coercion_constructor (Gmap.find (i,j) !inheritance_graph)

(* coercion_value : coe_index -> unsafe_judgment * bool *)

let coercion_value { coe_value = c; coe_type = t; coe_is_identity = b } =
  (make_judge c t, b)

(* pretty-print functions are now in Pretty *)
(* rajouter une coercion dans le graphe *)

let path_printer = ref (fun _ -> str "<a class path>"
                        : (int * int) * inheritance_path -> std_ppcmds)

let install_path_printer f = path_printer := f

let print_path x = !path_printer x

let message_ambig l =
  (str"Ambiguous paths:" ++ spc () ++
   prlist_with_sep pr_fnl (fun ijp -> print_path ijp) l)

(* add_coercion_in_graph : coe_index * cl_index * cl_index -> unit
                         coercion,source,target *)

let different_class_params i j =
  (snd (class_info_from_index i)).cl_param > 0

let add_coercion_in_graph (ic,source,target) =
  let old_inheritance_graph = !inheritance_graph in
  let ambig_paths =
    (ref [] : ((cl_index * cl_index) * inheritance_path) list ref) in
  let try_add_new_path (i,j as ij) p =
    try
      if i=j then begin
	if different_class_params i j then begin
	  let _ = lookup_path_between_class ij in
          ambig_paths := (ij,p)::!ambig_paths
	end
      end else begin
        let _ = lookup_path_between_class (i,j) in
        ambig_paths := (ij,p)::!ambig_paths
      end;
      false
    with Not_found -> begin
      add_new_path ij p;
      true
    end
  in
  let try_add_new_path1 ij p =
    let _ = try_add_new_path ij p in ()
  in
  if try_add_new_path (source,target) [ic] then begin
    Gmap.iter
      (fun (s,t) p ->
         if s<>t then begin
	   if t = source then begin
             try_add_new_path1 (s,target) (p@[ic]);
             Gmap.iter
	       (fun (u,v) q ->
                  if u<>v & u = target &&  not (list_equal coe_info_typ_equal p q) then
		    try_add_new_path1 (s,v) (p@[ic]@q))
               old_inheritance_graph
           end;
           if s = target then try_add_new_path1 (source,t) (ic::p)
	 end)
      old_inheritance_graph
  end;
  if (!ambig_paths <> []) && is_verbose () then
    ppnl (message_ambig !ambig_paths)

type coercion = coe_typ * locality * bool * cl_typ * cl_typ * int

(* Calcul de l'arité d'une classe *)

let reference_arity_length ref =
  let t = Global.type_of_global ref in
  List.length (fst (Reductionops.splay_arity (Global.env()) Evd.empty t))

let class_params = function
  | CL_FUN | CL_SORT -> 0
  | CL_CONST sp -> reference_arity_length (ConstRef sp)
  | CL_SECVAR sp -> reference_arity_length (VarRef sp)
  | CL_IND sp  -> reference_arity_length (IndRef sp)

(* add_class : cl_typ -> locality_flag option -> bool -> unit *)

let add_class cl =
  add_new_class cl { cl_param = class_params cl }

let automatically_import_coercions = ref false

open Goptions
let _ =
  declare_bool_option
    { optsync  = true;
      optdepr  = false;
      optname  = "automatic import of coercions";
      optkey   = ["Automatic";"Coercions";"Import"];
      optread  = (fun () -> !automatically_import_coercions);
      optwrite = (:=) automatically_import_coercions }

let cache_coercion (_,(coe,stre,isid,cls,clt,ps)) =
  add_class cls;
  add_class clt;
  let is,_ = class_info cls in
  let it,_ = class_info clt in
  let xf =
    { coe_value = constr_of_global coe;
      coe_type = Global.type_of_global coe;
      coe_strength = stre;
      coe_is_identity = isid;
      coe_param = ps } in
  add_new_coercion coe xf;
  add_coercion_in_graph (xf,is,it)

let load_coercion _ o =
  if
    !automatically_import_coercions || Flags.version_less_or_equal Flags.V8_2
  then
    cache_coercion o

let open_coercion _ o =
  if not
    (!automatically_import_coercions || Flags.version_less_or_equal Flags.V8_2)
  then
    cache_coercion o

let subst_coercion (subst,(coe,stre,isid,cls,clt,ps as obj)) =
  let coe' = subst_coe_typ subst coe in
  let cls' = subst_cl_typ subst cls in
  let clt' = subst_cl_typ subst clt in
    if coe' == coe && cls' == cls & clt' == clt then obj else
      (coe',stre,isid,cls',clt',ps)

let discharge_cl = function
  | CL_CONST kn -> CL_CONST (Lib.discharge_con kn)
  | CL_IND ind -> CL_IND (Lib.discharge_inductive ind)
  | cl -> cl

let discharge_coercion (_,(coe,stre,isid,cls,clt,ps)) =
  if stre = Local then None else
    let n = try Array.length (Lib.section_instance coe) with Not_found -> 0 in
    Some (Lib.discharge_global coe,
          stre,
	  isid,
          discharge_cl cls,
	  discharge_cl clt,
          n + ps)

let classify_coercion (coe,stre,isid,cls,clt,ps as obj) =
  if stre = Local then Dispose else Substitute obj

type coercion_obj =
  coe_typ * Decl_kinds.locality * bool * cl_typ * cl_typ * int

let inCoercion : coercion_obj -> obj =
  declare_object {(default_object "COERCION") with
    open_function = open_coercion;
    load_function = load_coercion;
    cache_function = cache_coercion;
    subst_function = subst_coercion;
    classify_function = classify_coercion;
    discharge_function = discharge_coercion }

let declare_coercion coef stre ~isid ~src:cls ~target:clt ~params:ps =
  Lib.add_anonymous_leaf (inCoercion (coef,stre,isid,cls,clt,ps))

(* For printing purpose *)
let get_coercion_value v = v.coe_value

let pr_cl_index n = int n

let classes () = Bijint.dom !class_tab
let coercions () = Gmap.rng !coercion_tab
let inheritance_graph () = Gmap.to_list !inheritance_graph

let coercion_of_reference r =
  let ref = Nametab.global r in
  if not (coercion_exists ref) then
    errorlabstrm "try_add_coercion"
      (Nametab.pr_global_env Idset.empty ref ++ str" is not a coercion.");
  ref

module CoercionPrinting =
  struct
    type t = coe_typ
    let encode = coercion_of_reference
    let subst = subst_coe_typ
    let printer x = pr_global_env Idset.empty x
    let key = ["Printing";"Coercion"]
    let title = "Explicitly printed coercions: "
    let member_message x b =
      str "Explicit printing of coercion " ++ printer x ++
      str (if b then " is set" else " is unset")
    let synchronous = true
  end

module PrintingCoercion  = Goptions.MakeRefTable(CoercionPrinting)

let hide_coercion coe =
  if not (PrintingCoercion.active coe) then
    let coe_info = coercion_info coe in
    Some coe_info.coe_param
  else None
