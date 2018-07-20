(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp
open Names
open Constr
open Libnames
open Globnames
open Nametab
open Environ
open Libobject
open Mod_subst

(* usage qque peu general: utilise aussi dans record *)

(* A class is a type constructor, its type is an arity whose number of
   arguments is cl_param (0 for CL_SORT and CL_FUN) *)

type cl_typ =
  | CL_SORT
  | CL_FUN
  | CL_SECVAR of variable
  | CL_CONST of Constant.t
  | CL_IND of inductive
  | CL_PROJ of Projection.Repr.t

type cl_info_typ = {
  cl_param : int
}

type coe_typ = GlobRef.t

module CoeTypMap = Refmap_env

type coe_info_typ = {
  coe_value : GlobRef.t;
  coe_local : bool;
  coe_is_identity : bool;
  coe_is_projection : Projection.Repr.t option;
  coe_param : int;
}

let coe_info_typ_equal c1 c2 =
  GlobRef.equal c1.coe_value c2.coe_value &&
    c1.coe_local == c2.coe_local &&
    c1.coe_is_identity == c2.coe_is_identity &&
    c1.coe_is_projection == c2.coe_is_projection &&
    Int.equal c1.coe_param c2.coe_param

let cl_typ_ord t1 t2 = match t1, t2 with
  | CL_SECVAR v1, CL_SECVAR v2 -> Id.compare v1 v2
  | CL_CONST c1, CL_CONST c2 -> Constant.CanOrd.compare c1 c2
  | CL_PROJ c1, CL_PROJ c2 -> Projection.Repr.CanOrd.compare c1 c2
  | CL_IND i1, CL_IND i2 -> ind_ord i1 i2
  | _ -> Pervasives.compare t1 t2 (** OK *)

module ClTyp = struct
  type t = cl_typ
  let compare = cl_typ_ord
end

module ClTypMap = Map.Make(ClTyp)

module IntMap = Map.Make(Int)

let cl_typ_eq t1 t2 = Int.equal (cl_typ_ord t1 t2) 0

type inheritance_path = coe_info_typ list

(* table des classes, des coercions et graphe d'heritage *)

module Bijint :
sig
  module Index :
  sig
    type t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val print : t -> Pp.t
  end
  type 'a t
  val empty : 'a t
  val mem : cl_typ -> 'a t -> bool
  val map : Index.t -> 'a t -> cl_typ * 'a
  val revmap : cl_typ -> 'a t -> Index.t * 'a
  val add : cl_typ -> 'a -> 'a t -> 'a t
  val dom : 'a t -> cl_typ list
end
=
struct

  module Index = struct include Int let print = Pp.int end

  type 'a t = { v : (cl_typ * 'a) IntMap.t; s : int; inv : int ClTypMap.t }
  let empty = { v = IntMap.empty; s = 0; inv = ClTypMap.empty }
  let mem y b = ClTypMap.mem y b.inv
  let map x b = IntMap.find x b.v
  let revmap y b = let n = ClTypMap.find y b.inv in (n, snd (IntMap.find n b.v))
  let add x y b =
    { v = IntMap.add b.s (x,y) b.v; s = b.s+1; inv = ClTypMap.add x b.s b.inv }
  let dom b = List.rev (ClTypMap.fold (fun x _ acc -> x::acc) b.inv [])
end

type cl_index = Bijint.Index.t

let class_tab =
  ref (Bijint.empty : cl_info_typ Bijint.t)

let coercion_tab =
  ref (CoeTypMap.empty : coe_info_typ CoeTypMap.t)

let coercions_in_scope =
  ref Refset_env.empty

module ClPairOrd =
struct
  type t = cl_index * cl_index
  let compare (i1, j1) (i2, j2) =
    let c = Bijint.Index.compare i1 i2 in
    if Int.equal c 0 then Bijint.Index.compare j1 j2 else c
end

module ClPairMap = Map.Make(ClPairOrd)

let inheritance_graph =
  ref (ClPairMap.empty : inheritance_path ClPairMap.t)

let freeze _ = (!class_tab, !coercion_tab, !inheritance_graph, !coercions_in_scope)

let unfreeze (fcl,fco,fig,in_scope) =
  class_tab:=fcl;
  coercion_tab:=fco;
  inheritance_graph:=fig;
  coercions_in_scope:=in_scope

(* ajout de nouveaux "objets" *)

let add_new_class cl s =
  if not (Bijint.mem cl !class_tab) then
    class_tab := Bijint.add cl s !class_tab

let add_new_coercion coe s =
  coercion_tab := CoeTypMap.add coe s !coercion_tab

let add_new_path x y =
  inheritance_graph := ClPairMap.add x y !inheritance_graph

let init () =
  class_tab:= Bijint.empty;
  add_new_class CL_FUN  { cl_param = 0 };
  add_new_class CL_SORT { cl_param = 0 };
  coercion_tab:= CoeTypMap.empty;
  inheritance_graph:= ClPairMap.empty

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

let coercion_info coe = CoeTypMap.find coe !coercion_tab

let coercion_exists coe = CoeTypMap.mem coe !coercion_tab

(* find_class_type : evar_map -> constr -> cl_typ * universe_list * constr list *)

let find_class_type sigma t =
  let open EConstr in
  let t', args = Reductionops.whd_betaiotazeta_stack sigma t in
  match EConstr.kind sigma t' with
    | Var id -> CL_SECVAR id, EInstance.empty, args
    | Const (sp,u) -> CL_CONST sp, u, args
    | Proj (p, c) when not (Projection.unfolded p) ->
      CL_PROJ (Projection.repr p), EInstance.empty, (c :: args)
    | Ind (ind_sp,u) -> CL_IND ind_sp, u, args
    | Prod (_,_,_) -> CL_FUN, EInstance.empty, []
    | Sort _ -> CL_SORT, EInstance.empty, []
    |  _ -> raise Not_found


let subst_cl_typ subst ct = match ct with
    CL_SORT
  | CL_FUN
  | CL_SECVAR _ -> ct
  | CL_PROJ c ->
    let c' = subst_proj_repr subst c in
      if c' == c then ct else CL_PROJ c'
  | CL_CONST c ->
      let c',t = subst_con_kn subst c in
	if c' == c then ct else
         pi1 (find_class_type Evd.empty (EConstr.of_constr t))
  | CL_IND i ->
      let i' = subst_ind subst i in
	if i' == i then ct else CL_IND i'

(*CSC: here we should change the datatype for coercions: it should be possible
       to declare any term as a coercion *)
let subst_coe_typ subst t = subst_global_reference subst t

(* class_of : Term.constr -> int *)

let class_of env sigma t =
  let (t, n1, i, u, args) =
    try
      let (cl, u, args) = find_class_type sigma t in
      let (i, { cl_param = n1 } ) = class_info cl in
      (t, n1, i, u, args)
    with Not_found ->
      let t = Tacred.hnf_constr env sigma t in
      let (cl, u, args) = find_class_type sigma t in
      let (i, { cl_param = n1 } ) = class_info cl in
      (t, n1, i, u, args)
  in
  if Int.equal (List.length args) n1 then t, i else raise Not_found

let inductive_class_of ind = fst (class_info (CL_IND ind))

let class_args_of env sigma c = pi3 (find_class_type sigma c)

let string_of_class = function
  | CL_FUN -> "Funclass"
  | CL_SORT -> "Sortclass"
  | CL_CONST sp ->
    string_of_qualid (shortest_qualid_of_global Id.Set.empty (ConstRef sp))
  | CL_PROJ sp ->
    let sp = Projection.Repr.constant sp in
    string_of_qualid (shortest_qualid_of_global Id.Set.empty (ConstRef sp))
  | CL_IND sp ->
      string_of_qualid (shortest_qualid_of_global Id.Set.empty (IndRef sp))
  | CL_SECVAR sp ->
      string_of_qualid (shortest_qualid_of_global Id.Set.empty (VarRef sp))

let pr_class x = str (string_of_class x)

(* lookup paths *)

let lookup_path_between_class (s,t) =
  ClPairMap.find (s,t) !inheritance_graph

let lookup_path_to_fun_from_class s =
  lookup_path_between_class (s,cl_fun_index)

let lookup_path_to_sort_from_class s =
  lookup_path_between_class (s,cl_sort_index)

(* advanced path lookup *)

let apply_on_class_of env sigma t cont =
  try
    let (cl,u,args) = find_class_type sigma t in
    let (i, { cl_param = n1 } ) = class_info cl in
    if not (Int.equal (List.length args) n1) then raise Not_found;
    t, cont i
  with Not_found ->
    (* Is it worth to be more incremental on the delta steps? *)
    let t = Tacred.hnf_constr env sigma t in
    let (cl, u, args) = find_class_type sigma t in
    let (i, { cl_param = n1 } ) = class_info cl in
    if not (Int.equal (List.length args) n1) then raise Not_found;
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

let mkNamed = function
  | GlobRef.ConstRef c -> EConstr.mkConst c
  | VarRef v -> EConstr.mkVar v
  | ConstructRef c -> EConstr.mkConstruct c
  | IndRef i -> EConstr.mkInd i

let get_coercion_constructor env coe =
  let evd = Evd.from_env env in
  let red x = fst (Reductionops.whd_all_stack env evd x) in
  match EConstr.kind evd (red (mkNamed coe.coe_value)) with
  | Constr.Construct (c, _) ->
      c, Inductiveops.constructor_nrealargs c -1
  | _ -> raise Not_found

let lookup_pattern_path_between env (s,t) =
  let i = inductive_class_of s in
  let j = inductive_class_of t in
  List.map (get_coercion_constructor env) (ClPairMap.find (i,j) !inheritance_graph)

(* rajouter une coercion dans le graphe *)

let path_printer : (env -> Evd.evar_map -> (Bijint.Index.t * Bijint.Index.t) * inheritance_path -> Pp.t) ref =
  ref (fun _ _ _ -> str "<a class path>")

let install_path_printer f = path_printer := f

let print_path env sigma x = !path_printer env sigma x

let message_ambig env sigma l =
  str"Ambiguous paths:" ++ spc () ++
  prlist_with_sep fnl (fun ijp -> print_path env sigma ijp) l

(* add_coercion_in_graph : coe_index * cl_index * cl_index -> unit
                         coercion,source,target *)

let different_class_params i =
  let ci = class_info_from_index i in
    if (snd ci).cl_param > 0 then true
    else 
      match fst ci with
      | CL_IND i -> Global.is_polymorphic (IndRef i)
      | CL_CONST c -> Global.is_polymorphic (ConstRef c)
      | _ -> false

let add_coercion_in_graph env sigma (ic,source,target) =
  let old_inheritance_graph = !inheritance_graph in
  let ambig_paths =
    (ref [] : ((cl_index * cl_index) * inheritance_path) list ref) in
  let try_add_new_path (i,j as ij) p =
    try
      if Bijint.Index.equal i j then begin
	if different_class_params i then begin
	  let _ = lookup_path_between_class ij in
          ambig_paths := (ij,p)::!ambig_paths
	end
      end else begin
        let _ = lookup_path_between_class ij in
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
    ClPairMap.iter
      (fun (s,t) p ->
         if not (Bijint.Index.equal s t) then begin
	   if Bijint.Index.equal t source then begin
             try_add_new_path1 (s,target) (p@[ic]);
             ClPairMap.iter
	       (fun (u,v) q ->
                  if not (Bijint.Index.equal u v) && Bijint.Index.equal u target &&  not (List.equal coe_info_typ_equal p q) then
		    try_add_new_path1 (s,v) (p@[ic]@q))
               old_inheritance_graph
           end;
           if Bijint.Index.equal s target then try_add_new_path1 (source,t) (ic::p)
	 end)
      old_inheritance_graph
  end;
  let is_ambig = match !ambig_paths with [] -> false | _ -> true in
  if is_ambig && not !Flags.quiet then
    Feedback.msg_info (message_ambig env sigma !ambig_paths)

type coercion = {
  coercion_type   : coe_typ;
  coercion_local  : bool;
  coercion_is_id  : bool;
  coercion_is_proj  : Projection.Repr.t option;
  coercion_source : cl_typ;
  coercion_target : cl_typ;
  coercion_params : int;
}

(* Computation of the class arity *)

let reference_arity_length ref =
  let t, _ = Global.type_of_global_in_context (Global.env ()) ref in
  List.length (fst (Reductionops.splay_arity (Global.env()) Evd.empty (EConstr.of_constr t))) (** FIXME *)

let projection_arity_length p =
  let len = reference_arity_length (ConstRef (Projection.Repr.constant p)) in
  len - Projection.Repr.npars p

let class_params = function
  | CL_FUN | CL_SORT -> 0
  | CL_CONST sp -> reference_arity_length (ConstRef sp)
  | CL_PROJ sp -> projection_arity_length sp
  | CL_SECVAR sp -> reference_arity_length (VarRef sp)
  | CL_IND sp  -> reference_arity_length (IndRef sp)

(* add_class : cl_typ -> locality_flag option -> bool -> unit *)

let add_class cl =
  add_new_class cl { cl_param = class_params cl }

let automatically_import_coercions = ref false

open Goptions
let _ =
  declare_bool_option
    { optdepr  = true; (* remove in 8.8 *)
      optname  = "automatic import of coercions";
      optkey   = ["Automatic";"Coercions";"Import"];
      optread  = (fun () -> !automatically_import_coercions);
      optwrite = (:=) automatically_import_coercions }

let cache_coercion env sigma (_, c) =
  let () = add_class c.coercion_source in
  let () = add_class c.coercion_target in
  let is, _ = class_info c.coercion_source in
  let it, _ = class_info c.coercion_target in
  let xf =
    { coe_value = c.coercion_type;
      coe_local = c.coercion_local;
      coe_is_identity = c.coercion_is_id;
      coe_is_projection = c.coercion_is_proj;
      coe_param = c.coercion_params;
    } in
  let () = add_new_coercion c.coercion_type xf in
  add_coercion_in_graph env sigma (xf,is,it)

let load_coercion _ o =
  if !automatically_import_coercions then
    cache_coercion (Global.env ()) Evd.empty o

let set_coercion_in_scope (_, c) =
  let r = c.coercion_type in
  coercions_in_scope := Refset_env.add r !coercions_in_scope

let open_coercion i o =
  if Int.equal i 1 then begin
    set_coercion_in_scope o;
    if not !automatically_import_coercions then
      cache_coercion (Global.env ()) Evd.empty o
  end

let subst_coercion (subst, c) =
  let coe = subst_coe_typ subst c.coercion_type in
  let cls = subst_cl_typ subst c.coercion_source in
  let clt = subst_cl_typ subst c.coercion_target in
  let clp = Option.Smart.map (subst_proj_repr subst) c.coercion_is_proj in
  if c.coercion_type == coe && c.coercion_source == cls &&
     c.coercion_target == clt && c.coercion_is_proj == clp
  then c
  else { c with coercion_type = coe; coercion_source = cls;
                coercion_target = clt; coercion_is_proj = clp; }

let discharge_cl = function
  | CL_CONST kn -> CL_CONST (Lib.discharge_con kn)
  | CL_IND ind -> CL_IND (Lib.discharge_inductive ind)
  | CL_PROJ p -> CL_PROJ (Lib.discharge_proj_repr p)
  | cl -> cl

let discharge_coercion (_, c) =
  if c.coercion_local then None
  else
    let n =
      try
        let ins = Lib.section_instance c.coercion_type in
        Array.length (snd ins)
      with Not_found -> 0
    in
    let nc = { c with
      coercion_type = Lib.discharge_global c.coercion_type;
      coercion_source = discharge_cl c.coercion_source;
      coercion_target = discharge_cl c.coercion_target;
      coercion_params = n + c.coercion_params;
      coercion_is_proj = Option.map Lib.discharge_proj_repr c.coercion_is_proj;
    } in
    Some nc

let classify_coercion obj =
  if obj.coercion_local then Dispose else Substitute obj

let inCoercion : coercion -> obj =
  declare_object {(default_object "COERCION") with
    open_function = open_coercion;
    load_function = load_coercion;
    cache_function = (fun objn ->
        let env = Global.env () in
        set_coercion_in_scope objn;
        cache_coercion env Evd.empty objn
      );
    subst_function = subst_coercion;
    classify_function = classify_coercion;
    discharge_function = discharge_coercion }

let declare_coercion coef ?(local = false) ~isid ~src:cls ~target:clt ~params:ps =
  let isproj = 
    match coef with
    | ConstRef c -> Recordops.find_primitive_projection c
    | _ -> None
  in
  let c = {
    coercion_type = coef;
    coercion_local = local;
    coercion_is_id = isid;
    coercion_is_proj = isproj;
    coercion_source = cls;
    coercion_target = clt;
    coercion_params = ps;
  } in
  Lib.add_anonymous_leaf (inCoercion c)

(* For printing purpose *)
let pr_cl_index = Bijint.Index.print

let classes () = Bijint.dom !class_tab
let coercions () =
  List.rev (CoeTypMap.fold (fun _ y acc -> y::acc) !coercion_tab [])

let inheritance_graph () =
  ClPairMap.bindings !inheritance_graph

let coercion_of_reference r =
  let ref = Nametab.global r in
  if not (coercion_exists ref) then
    user_err ~hdr:"try_add_coercion"
      (Nametab.pr_global_env Id.Set.empty ref ++ str" is not a coercion.");
  ref

module CoercionPrinting =
  struct
    type t = coe_typ
    let compare = RefOrdered.compare
    let encode = coercion_of_reference
    let subst = subst_coe_typ
    let printer x = pr_global_env Id.Set.empty x
    let key = ["Printing";"Coercion"]
    let title = "Explicitly printed coercions: "
    let member_message x b =
      str "Explicit printing of coercion " ++ printer x ++
      str (if b then " is set" else " is unset")
  end

module PrintingCoercion  = Goptions.MakeRefTable(CoercionPrinting)

let hide_coercion coe =
  if not (PrintingCoercion.active coe) then
    let coe_info = coercion_info coe in
    Some coe_info.coe_param
  else None

let is_coercion_in_scope r =
  Refset_env.mem r !coercions_in_scope
