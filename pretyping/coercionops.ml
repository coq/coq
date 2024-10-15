(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
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

let cl_typ_ord t1 t2 = match t1, t2 with
  | CL_SECVAR v1, CL_SECVAR v2 -> Id.compare v1 v2
  | CL_CONST c1, CL_CONST c2 -> Constant.CanOrd.compare c1 c2
  | CL_PROJ c1, CL_PROJ c2 -> Projection.Repr.CanOrd.compare c1 c2
  | CL_IND i1, CL_IND i2 -> Ind.CanOrd.compare i1 i2
  | _ -> Stdlib.compare t1 t2 (** OK *)

let cl_typ_eq t1 t2 = Int.equal (cl_typ_ord t1 t2) 0

module ClTyp = struct
  type t = cl_typ
  let compare = cl_typ_ord
end

module ClTypSet = Set.Make(ClTyp)
module ClTypMap = Map.Make(ClTyp)

type cl_info_typ = {
  (* The number of parameters of the coercion class. *)
  cl_param : int;
  (* The sets of coercion classes respectively reachable from and to the
     coercion class. *)
  cl_reachable_from : ClTypSet.t;
  cl_reachable_to : ClTypSet.t;
  (* The representative class of the strongly connected component. *)
  cl_repr : cl_typ;
}

type coe_typ = GlobRef.t

module CoeTypMap = GlobRef.Map_env

type coe_info_typ = {
  coe_value : GlobRef.t;
  coe_local : bool;
  coe_reversible : bool;
  coe_is_identity : bool;
  coe_is_projection : Projection.Repr.t option;
  coe_source : cl_typ;
  coe_target : cl_typ;
  coe_param : int;
}

type inheritance_path = coe_info_typ list

let init_class_tab =
  let open ClTypMap in
  let cl_info params cl =
    let cl_singleton = ClTypSet.singleton cl in
    { cl_param = params;
      cl_reachable_from = cl_singleton;
      cl_reachable_to = cl_singleton;
      cl_repr = cl }
  in
  add CL_FUN (cl_info 0 CL_FUN) (add CL_SORT (cl_info 0 CL_SORT) empty)

let class_tab =
  Summary.ref ~name:"class_tab" (init_class_tab : cl_info_typ ClTypMap.t)

let coercion_tab =
  Summary.ref ~name:"coercion_tab" (CoeTypMap.empty : coe_info_typ CoeTypMap.t)

let reachable_from cl =
  try (ClTypMap.find cl !class_tab).cl_reachable_from
  with Not_found -> ClTypSet.empty

module ClGraph :
sig
  type t
  val empty : t
  val add : cl_typ -> cl_typ -> inheritance_path -> t -> t
  val find : cl_typ -> cl_typ -> t -> inheritance_path
  val src : cl_typ -> t -> inheritance_path ClTypMap.t
  val dst : cl_typ -> t -> inheritance_path ClTypMap.t
  val bindings : t -> ((cl_typ * cl_typ) * inheritance_path) list
end =
struct
  type map = inheritance_path ClTypMap.t ClTypMap.t
  type t = map * map
  (* Doubly-indexed map in both directions *)
  let empty = ClTypMap.empty, ClTypMap.empty
  let add0 x y p m =
    let n = try ClTypMap.find x m with Not_found -> ClTypMap.empty in
    ClTypMap.add x (ClTypMap.add y p n) m
  let add x y p (ml, mr) = (add0 x y p ml, add0 y x p mr)
  let find x y (m, _) = ClTypMap.find y (ClTypMap.find x m)
  let src x (m, _) = try ClTypMap.find x m with Not_found -> ClTypMap.empty
  let dst x (_, m) = try ClTypMap.find x m with Not_found -> ClTypMap.empty

  let bindings (m, _) =
    let fold s n accu =
      let fold t p accu = ((s, t), p) :: accu in
      ClTypMap.fold fold n accu
    in
    List.rev (ClTypMap.fold fold m [])
end

let inheritance_graph =
  Summary.ref ~name:"inheritance_graph" ClGraph.empty

(* ajout de nouveaux "objets" *)

let add_new_class cl s =
  class_tab := ClTypMap.add cl s !class_tab

let add_coercion coe s =
  coercion_tab := CoeTypMap.add coe s !coercion_tab

let add_path (x, y) p =
  inheritance_graph := ClGraph.add x y p !inheritance_graph

(* class_info : cl_typ -> int * cl_info_typ *)

let class_info cl = ClTypMap.find cl !class_tab

let class_nparams cl = (class_info cl).cl_param

let class_exists cl = ClTypMap.mem cl !class_tab

let coercion_info coe = CoeTypMap.find coe !coercion_tab

let coercion_type env sigma (coe,u) =
  Retyping.get_type_of env sigma (EConstr.mkRef (coe.coe_value,u))

let coercion_exists coe = CoeTypMap.mem coe !coercion_tab

(* find_class_type : evar_map -> constr -> cl_typ * universe_list * constr list *)

let find_class_type env sigma t =
  let open EConstr in
  let t', args = Reductionops.whd_betaiotazeta_stack env sigma t in
  match EConstr.kind sigma t' with
    | Var id -> CL_SECVAR id, EInstance.empty, args
    | Const (sp,u) -> CL_CONST sp, u, args
    | Proj (p, _, c) when not (Projection.unfolded p) ->
      let revparams =
        let open Inductiveops in
        let t = Retyping.get_type_of env sigma c in
        let IndType (fam,_) = find_rectype env sigma t in
        let _, params = dest_ind_family fam in
        List.rev params
      in
      CL_PROJ (Projection.repr p), EInstance.empty, (List.rev_append revparams (c :: args))
    | Ind (ind_sp,u) -> CL_IND ind_sp, u, args
    | Prod _ -> CL_FUN, EInstance.empty, []
    | Sort _ -> CL_SORT, EInstance.empty, []
    |  _ -> raise Not_found

let class_of_global_reference = function
  | GlobRef.VarRef id -> CL_SECVAR id
  | GlobRef.ConstRef kn -> CL_CONST kn
  | GlobRef.IndRef ind -> CL_IND ind
  | GlobRef.ConstructRef _ -> raise Not_found

let find_class_glob_type c = match DAst.get c with
  | Glob_term.GRef (ref,_) -> class_of_global_reference ref
  | Glob_term.GProd _ -> CL_FUN
  | Glob_term.GSort _ -> CL_SORT
  |  _ -> raise Not_found

let subst_cl_typ env subst ct = match ct with
    CL_SORT
  | CL_FUN
  | CL_SECVAR _ -> ct
  | CL_PROJ c ->
    let c' = subst_proj_repr subst c in
      if c' == c then ct else CL_PROJ c'
  | CL_CONST c ->
      let c',t = subst_con subst c in
      if c' == c then ct else (match t with
          | None -> CL_CONST c'
          | Some t ->
            pi1 (find_class_type env Evd.empty (EConstr.of_constr t.UVars.univ_abstracted_value)))
  | CL_IND i ->
      let i' = subst_ind subst i in
        if i' == i then ct else CL_IND i'

(*CSC: here we should change the datatype for coercions: it should be possible
       to declare any term as a coercion *)
let subst_coe_typ subst t = subst_global_reference subst t

(* class_of : Term.constr -> int *)

let class_of env sigma t =
  let (t, n1, cl, u, args) =
    try
      let (cl, u, args) = find_class_type env sigma t in
      let { cl_param = n1 } = class_info cl in
      (t, n1, cl, u, args)
    with Not_found ->
      let t = Tacred.hnf_constr env sigma t in
      let (cl, u, args) = find_class_type env sigma t in
      let { cl_param = n1 } = class_info cl in
      (t, n1, cl, u, args)
  in
  if Int.equal (List.length args) n1 then t, cl else raise Not_found

let class_args_of env sigma c = pi3 (find_class_type env sigma c)

let string_of_class = function
  | CL_FUN -> "Funclass"
  | CL_SORT -> "Sortclass"
  | CL_CONST sp ->
    string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.ConstRef sp))
  | CL_PROJ sp ->
    let sp = Projection.Repr.constant sp in
    string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.ConstRef sp))
  | CL_IND sp ->
      string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.IndRef sp))
  | CL_SECVAR sp ->
      string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty (GlobRef.VarRef sp))

let pr_class x = str (string_of_class x)

(* lookup paths *)

let lookup_path_between_class (s,t) =
  ClGraph.find s t !inheritance_graph

let lookup_path_to_fun_from_class s =
  lookup_path_between_class (s, CL_FUN)

let lookup_path_to_sort_from_class s =
  lookup_path_between_class (s, CL_SORT)

(* advanced path lookup *)

let apply_on_class_of env sigma t cont =
  try
    let (cl,u,args) = find_class_type env sigma t in
    let { cl_param = n1 } = class_info cl in
    if not (Int.equal (List.length args) n1) then raise Not_found;
    cont cl
  with Not_found ->
    (* Is it worth to be more incremental on the delta steps? *)
    let t = Tacred.hnf_constr env sigma t in
    let (cl, u, args) = find_class_type env sigma t in
    let { cl_param = n1 } = class_info cl in
    if not (Int.equal (List.length args) n1) then raise Not_found;
    cont cl

let lookup_path_between env sigma ~src:s ~tgt:t =
  apply_on_class_of env sigma s (fun i ->
      apply_on_class_of env sigma t (fun j ->
          lookup_path_between_class (i,j)))

let lookup_path_to_fun_from env sigma s =
  apply_on_class_of env sigma s lookup_path_to_fun_from_class

let lookup_path_to_sort_from env sigma s =
  apply_on_class_of env sigma s lookup_path_to_sort_from_class

let get_coercion_constructor env coe =
  let evd = Evd.from_env env in
  let evd, c = Evd.fresh_global env evd coe.coe_value in
  let c = fst (Reductionops.whd_all_stack env evd c) in
  match EConstr.kind evd c with
  | Constr.Construct (c, _) ->
    (* we don't return the modified evd as we drop the universes *)
    c, Inductiveops.constructor_nrealargs env c -1
  | _ -> raise Not_found

let lookup_pattern_path_between env (s,t) =
  List.map (get_coercion_constructor env)
    (ClGraph.find (CL_IND s) (CL_IND t) !inheritance_graph)

let path_is_reversible p =
  List.for_all (fun c -> c.coe_reversible) p

(* rajouter une coercion dans le graphe *)

let path_printer : ((cl_typ * cl_typ) * inheritance_path -> Pp.t) ref =
  ref (fun _ -> str "<a class path>")

let install_path_printer f = path_printer := f

let print_path x = !path_printer x

let path_comparator :
  (Environ.env -> Evd.evar_map -> cl_typ -> inheritance_path -> inheritance_path -> bool) ref =
  ref (fun _ _ _ _ _ -> false)

let install_path_comparator f = path_comparator := f

let compare_path env sigma cl p q = !path_comparator env sigma cl p q

let warning_ambiguous_path = "ambiguous-paths"

let warn_ambiguous_path =
  CWarnings.create ~name:warning_ambiguous_path ~category:CWarnings.CoreCategories.coercions
    (fun l -> prlist_with_sep fnl (fun (c,p,q) ->
         str"New coercion path " ++ print_path (c,p) ++
         if List.is_empty q then
           str" is not definitionally an identity function."
         else
           str" is ambiguous with existing " ++ print_path (c, q) ++ str".") l)

(* add_coercion_in_graph : coe_index * cl_typ * cl_typ -> unit
                         coercion,source,target *)

let different_class_params env ci =
  if (class_info ci).cl_param > 0 then true
  else
    match ci with
    | CL_IND i -> Environ.is_polymorphic env (GlobRef.IndRef i)
    | CL_CONST c -> Environ.is_polymorphic env (GlobRef.ConstRef c)
    | _ -> false

let add_coercion_in_graph env sigma ?(update=false) ic =
  let source = ic.coe_source in
  let target = ic.coe_target in
  let source_info = class_info source in
  let target_info = class_info target in
  let old_inheritance_graph = !inheritance_graph in
  let ambig_paths :
    ((cl_typ * cl_typ) * inheritance_path * inheritance_path) list ref =
    ref [] in
  let warn = match CWarnings.get_warning warning_ambiguous_path with
  | There w ->
    begin match CWarnings.warning_status w with
    | Disabled -> false
    | Enabled | AsError -> true
    end
  | NotThere | OtherType -> assert false
  in
  let check_coherence (i, j as ij) p q =
    if warn then
    let i_info = class_info i in
    let j_info = class_info j in
    let between_ij = ClTypSet.inter i_info.cl_reachable_from j_info.cl_reachable_to in
    if cl_typ_eq i_info.cl_repr i &&
       cl_typ_eq j_info.cl_repr j &&
       ClTypSet.is_empty
         (ClTypSet.diff (ClTypSet.inter between_ij source_info.cl_reachable_to)
            i_info.cl_reachable_to) &&
       ClTypSet.is_empty
         (ClTypSet.diff
            (ClTypSet.inter between_ij target_info.cl_reachable_from)
            j_info.cl_reachable_from) &&
       not (compare_path env sigma i p q)
    then
      ambig_paths := (ij, p, q) :: !ambig_paths
  in
  let try_add_new_path (i,j as ij) p =
    let () = if cl_typ_eq i j then check_coherence ij p [] in
    if not (cl_typ_eq i j) || different_class_params env i then
      if update then let () = add_path ij p in true else
        match lookup_path_between_class ij with
        | q -> (if not (cl_typ_eq i j) then check_coherence ij p q); false
        | exception Not_found -> add_path ij p; true
    else
      false
  in
  if try_add_new_path (source, target) [ic] then begin
    let rev = ClGraph.dst source old_inheritance_graph in
    let dir = ClGraph.src target old_inheritance_graph in
    let iter s p =
      if not (cl_typ_eq s source) then
        let _ = try_add_new_path (s, target) (p@[ic]) in
        let iter v q =
          if not (cl_typ_eq target v) then
            ignore (try_add_new_path (s,v) (p@[ic]@q))
        in
        ClTypMap.iter iter dir
    in
    let () = ClTypMap.iter iter rev in
    let iter t p =
      if not (cl_typ_eq t target) then
        ignore (try_add_new_path (source, t) (ic::p))
    in
    ClTypMap.iter iter dir
  end;
  class_tab := ClTypMap.mapi (fun k k_info ->
      let reachable_k_source = ClTypSet.mem k source_info.cl_reachable_to in
      let reachable_target_k = ClTypSet.mem k target_info.cl_reachable_from in
      { k_info with
        cl_reachable_from =
          if reachable_k_source then
            ClTypSet.union
              k_info.cl_reachable_from target_info.cl_reachable_from
          else
            k_info.cl_reachable_from;
        cl_reachable_to =
          if reachable_target_k then
            ClTypSet.union k_info.cl_reachable_to source_info.cl_reachable_to
          else
            k_info.cl_reachable_to;
        cl_repr =
          if reachable_k_source && reachable_target_k then
            target_info.cl_repr
          else
            k_info.cl_repr
      }) !class_tab;
  match !ambig_paths with [] -> () | _ -> warn_ambiguous_path !ambig_paths

let subst_coercion subst c =
  let env = Global.env () in
  let coe = subst_coe_typ subst c.coe_value in
  let cls = subst_cl_typ env subst c.coe_source in
  let clt = subst_cl_typ env subst c.coe_target in
  let clp = Option.Smart.map (subst_proj_repr subst) c.coe_is_projection in
  if c.coe_value == coe && c.coe_source == cls && c.coe_target == clt &&
     c.coe_is_projection == clp
  then c
  else { c with coe_value = coe; coe_source = cls; coe_target = clt;
                coe_is_projection = clp; }

(* Computation of the class arity *)

let reference_arity_length env sigma ref =
  let t, _ = Typeops.type_of_global_in_context env ref in
  List.length (fst (Reductionops.splay_arity env sigma (EConstr.of_constr t)))

let projection_arity_length env sigma p =
  reference_arity_length env sigma (GlobRef.ConstRef (Projection.Repr.constant p))

let class_params env sigma = function
  | CL_FUN | CL_SORT -> 0
  | CL_CONST sp -> reference_arity_length env sigma (GlobRef.ConstRef sp)
  | CL_PROJ sp -> projection_arity_length env sigma sp
  | CL_SECVAR sp -> reference_arity_length env sigma (GlobRef.VarRef sp)
  | CL_IND sp  -> reference_arity_length env sigma (GlobRef.IndRef sp)

(* add_class : cl_typ -> locality_flag option -> bool -> unit *)

let add_class env sigma cl =
  if not (class_exists cl) then
    let cl_singleton = ClTypSet.singleton cl in
    add_new_class cl {
      cl_param = class_params env sigma cl;
      cl_reachable_from = cl_singleton;
      cl_reachable_to = cl_singleton;
      cl_repr = cl }

let declare_coercion env sigma ?update c =
  let () = add_class env sigma c.coe_source in
  let () = add_class env sigma c.coe_target in
  let () = add_coercion c.coe_value c in
  add_coercion_in_graph env sigma ?update c

(* For printing purpose *)
let classes () =
  List.rev (ClTypMap.fold (fun x _ acc -> x :: acc) !class_tab [])
let coercions () =
  List.rev (CoeTypMap.fold (fun _ y acc -> y::acc) !coercion_tab [])

let inheritance_graph () =
  ClGraph.bindings !inheritance_graph

let coercion_of_reference r =
  let ref = Nametab.global r in
  if not (coercion_exists ref) then
    user_err
      (Nametab.pr_global_env Id.Set.empty ref ++ str" is not a coercion.");
  ref

module CoercionPrinting =
  struct
    type t = coe_typ
    module Set = GlobRef.Set
    let encode _env = coercion_of_reference
    let subst = subst_coe_typ

    let check_local local = let open GlobRef in function
      | ConstRef _ | ConstructRef _ | IndRef _ -> ()
      | VarRef x -> match local with
        | Libobject.Local -> ()
        | Export | SuperGlobal ->
          let local = if local = Export then "export" else "global" in
          CErrors.user_err
            Pp.(Id.print x ++ str " cannot be added with locality " ++ str local ++ str ".")

    let discharge = let open GlobRef in function
      | ConstRef _ | ConstructRef _ | IndRef _ as x -> x
      | VarRef _ as x -> assert (not (Lib.is_in_section x)); x

    let printer x = Nametab.pr_global_env Id.Set.empty x
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
