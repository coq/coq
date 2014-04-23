(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Names
open Nameops
open Term
open Vars
open Termops
open Environ
open Globnames
open Mod_subst

(** Generic filters *)
module Filter :
sig
  type t
  val equal : t -> t -> bool
  val identity : t
  val filter_list : t -> 'a list -> 'a list
  val filter_array : t -> 'a array -> 'a array
  val extend : int -> t -> t
  val compose : t -> t -> t
  val restrict_upon : t -> int -> (int -> bool) -> t option
  val map_along : (bool -> 'a -> bool) -> t -> 'a list -> t
  val make : bool list -> t
  val repr :  t -> bool list option
end =
struct
  type t = bool list option
  (** We guarantee through the interface that if a filter is [Some _] then it
      contains at least one [false] somewhere. *)

  let identity = None

  let rec equal l1 l2 = match l1, l2 with
  | [], [] -> true
  | h1 :: l1, h2 :: l2 ->
    (if h1 then h2 else not h2) && equal l1 l2
  | _ -> false

  let equal l1 l2 = match l1, l2 with
  | None, None -> true
  | Some _, None | None, Some _ -> false
  | Some l1, Some l2 -> equal l1 l2

  let rec is_identity = function
  | [] -> true
  | true :: l -> is_identity l
  | false :: _ -> false

  let normalize f = if is_identity f then None else Some f

  let filter_list f l = match f with
  | None -> l
  | Some f -> CList.filter_with f l

  let filter_array f v = match f with
  | None -> v
  | Some f -> CArray.filter_with f v

  let rec extend n l =
    if n = 0 then l
    else extend (pred n) (true :: l)

  let extend n = function
  | None -> None
  | Some f -> Some (extend n f)

  let compose f1 f2 = match f1 with
  | None -> f2
  | Some f1 ->
    match f2 with
    | None -> None
    | Some f2 -> normalize (CList.filter_with f1 f2)

  let apply_subfilter filter subfilter =
    let len = Array.length subfilter in
    let fold b (i, ans) =
      if b then
        let () = assert (0 <= i) in
        (pred i, Array.unsafe_get subfilter i :: ans)
      else
        (i, false :: ans)
    in
    snd (List.fold_right fold filter (pred len, []))

  let restrict_upon f len p =
    let newfilter = Array.init len p in
    if Array.for_all (fun id -> id) newfilter then None
    else
      (** In both cases we statically know that the argument will contain at
          least one [false] *)
      let nf = match f with
      | None -> Some (Array.to_list newfilter)
      | Some f -> Some (apply_subfilter f newfilter)
      in
      Some nf

  let map_along f flt l =
    let ans = match flt with
    | None -> List.map (fun x -> f true x) l
    | Some flt -> List.map2 f flt l
    in
    normalize ans

  let make l = normalize l

  let repr f = f

end

(* The kinds of existential variables are now defined in [Evar_kinds] *)

(* The type of mappings for existential variables *)

module Dummy = struct end
module Store = Store.Make(Dummy)

type evar = Term.existential_key

let string_of_existential evk = "?" ^ string_of_int (Evar.repr evk)

type evar_body =
  | Evar_empty
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context_val;
  evar_body : evar_body;
  evar_filter : Filter.t;
  evar_source : Evar_kinds.t Loc.located;
  evar_candidates : constr list option; (* if not None, list of allowed instances *)
  evar_extra : Store.t }

let make_evar hyps ccl = {
  evar_concl = ccl;
  evar_hyps = hyps;
  evar_body = Evar_empty;
  evar_filter = Filter.identity;
  evar_source = (Loc.ghost,Evar_kinds.InternalHole);
  evar_candidates = None;
  evar_extra = Store.empty
}

let instance_mismatch () =
  anomaly (Pp.str "Signature and its instance do not match")

let evar_concl evi = evi.evar_concl

let evar_filter evi = evi.evar_filter

let evar_body evi = evi.evar_body

let evar_context evi = named_context_of_val evi.evar_hyps

let evar_filtered_context evi =
  Filter.filter_list (evar_filter evi) (evar_context evi)

let evar_hyps evi = evi.evar_hyps

let evar_filtered_hyps evi = match Filter.repr (evar_filter evi) with
| None -> evar_hyps evi
| Some filter ->
  let rec make_hyps filter ctxt = match filter, ctxt with
  | [], [] -> empty_named_context_val
  | false :: filter, _ :: ctxt -> make_hyps filter ctxt
  | true :: filter, decl :: ctxt ->
    let hyps = make_hyps filter ctxt in
    push_named_context_val decl hyps
  | _ -> instance_mismatch ()
  in
  make_hyps filter (evar_context evi)

let evar_env evi = Global.env_of_context evi.evar_hyps

let evar_filtered_env evi = match Filter.repr (evar_filter evi) with
| None -> evar_env evi
| Some filter ->
  let rec make_env filter ctxt = match filter, ctxt with
  | [], [] -> reset_context (Global.env ())
  | false :: filter, _ :: ctxt -> make_env filter ctxt
  | true :: filter, decl :: ctxt ->
    let env = make_env filter ctxt in
    push_named decl env
  | _ -> instance_mismatch ()
  in
  make_env filter (evar_context evi)

let eq_evar_body b1 b2 = match b1, b2 with
| Evar_empty, Evar_empty -> true
| Evar_defined t1, Evar_defined t2 -> eq_constr t1 t2
| _ -> false

let eq_evar_info ei1 ei2 =
  ei1 == ei2 ||
    eq_constr ei1.evar_concl ei2.evar_concl &&
    eq_named_context_val (ei1.evar_hyps) (ei2.evar_hyps) &&
    eq_evar_body ei1.evar_body ei2.evar_body
    (** ppedrot: [eq_constr] may be a bit too permissive here *)

(* spiwack: Revised hierarchy :
   - Evar.Map ( Maps of existential_keys )
   - EvarInfoMap ( .t = evar_info Evar.Map.t * evar_info Evar.Map )
   - EvarMap ( .t = EvarInfoMap.t * sort_constraints )
   - evar_map (exported)
*)

(* This exception is raised by *.existential_value *)
exception NotInstantiatedEvar

(* Note: let-in contributes to the instance *)

let make_evar_instance_array info args =
  let len = Array.length args in
  let rec instrec filter ctxt i = match filter, ctxt with
  | [], [] ->
    if Int.equal i len then []
    else instance_mismatch ()
  | false :: filter, _ :: ctxt ->
    instrec filter ctxt i
  | true :: filter, (id, _, _) :: ctxt ->
    if i < len then
      let c = Array.unsafe_get args i in
      (id, c) :: instrec filter ctxt (succ i)
    else instance_mismatch ()
  | _ -> instance_mismatch ()
  in
  match Filter.repr (evar_filter info) with
  | None ->
    let map i (id, _, _) =
      if (i < len) then (id, Array.unsafe_get args i)
      else instance_mismatch ()
    in
    List.map_i map 0 (evar_context info)
  | Some filter ->
    instrec filter (evar_context info) 0

let instantiate_evar_array info c args =
  let inst = make_evar_instance_array info args in
  match inst with
  | [] -> c
  | _ -> replace_vars inst c

(*******************************************************************)
(* Metamaps *)

(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Int.Set.t }

(* Collects all metavars appearing in a constr *)
let metavars_of c =
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> Int.Set.add mv acc
      | _         -> fold_constr collrec acc c
  in
  collrec Int.Set.empty c

let mk_freelisted c =
  { rebus = c; freemetas = metavars_of c }

let map_fl f cfl = { cfl with rebus=f cfl.rebus }

(* Status of an instance found by unification wrt to the meta it solves:
  - a supertype of the meta (e.g. the solution to ?X <= T is a supertype of ?X)
  - a subtype of the meta (e.g. the solution to T <= ?X is a supertype of ?X)
  - a term that can be eta-expanded n times while still being a solution
    (e.g. the solution [P] to [?X u v = P u v] can be eta-expanded twice)
*)

type instance_constraint = IsSuperType | IsSubType | Conv

let eq_instance_constraint c1 c2 = c1 == c2

(* Status of the unification of the type of an instance against the type of
     the meta it instantiates:
   - CoerceToType means that the unification of types has not been done
     and that a coercion can still be inserted: the meta should not be
     substituted freely (this happens for instance given via the
     "with" binding clause).
   - TypeProcessed means that the information obtainable from the
     unification of types has been extracted.
   - TypeNotProcessed means that the unification of types has not been
     done but it is known that no coercion may be inserted: the meta
     can be substituted freely.
*)

type instance_typing_status =
    CoerceToType | TypeNotProcessed | TypeProcessed

(* Status of an instance together with the status of its type unification *)

type instance_status = instance_constraint * instance_typing_status

(* Clausal environments *)

type clbinding =
  | Cltyp of Name.t * constr freelisted
  | Clval of Name.t * (constr freelisted * instance_status) * constr freelisted

let map_clb f = function
  | Cltyp (na,cfl) -> Cltyp (na,map_fl f cfl)
  | Clval (na,(cfl1,pb),cfl2) -> Clval (na,(map_fl f cfl1,pb),map_fl f cfl2)

(* name of defined is erased (but it is pretty-printed) *)
let clb_name = function
    Cltyp(na,_) -> (na,false)
  | Clval (na,_,_) -> (na,true)

(***********************)

module Metaset = Int.Set

module Metamap = Int.Map

let metamap_to_list m =
  Metamap.fold (fun n v l -> (n,v)::l) m []

(*************************)
(* Unification state *)

type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * Environ.env * constr * constr

module EvMap = Evar.Map

type evar_map = {
  defn_evars : evar_info EvMap.t;
  undf_evars : evar_info EvMap.t;
  universes  : Univ.UniverseLSet.t;
  univ_cstrs : Univ.universes;
  conv_pbs   : evar_constraint list;
  last_mods  : Evar.Set.t;
  metas      : clbinding Metamap.t;
  effects    : Declareops.side_effects;
}

(*** Lifting primitive from EvarMap. ***)

(* HH: The progress tactical now uses this function. *)
let progress_evar_map d1 d2 =
  let is_new k v =
    assert (v.evar_body == Evar_empty);
    EvMap.mem k d2.defn_evars
  in
  not (d1 == d2) && EvMap.exists is_new d1.undf_evars

let add d e i = match i.evar_body with
| Evar_empty ->
  { d with undf_evars = EvMap.add e i d.undf_evars; }
| Evar_defined _ ->
  { d with defn_evars = EvMap.add e i d.defn_evars; }

let remove d e =
  let undf_evars = EvMap.remove e d.undf_evars in
  let defn_evars = EvMap.remove e d.defn_evars in
  { d with undf_evars; defn_evars; }

let find d e =
  try EvMap.find e d.undf_evars
  with Not_found -> EvMap.find e d.defn_evars

let find_undefined d e = EvMap.find e d.undf_evars

let mem d e = EvMap.mem e d.undf_evars || EvMap.mem e d.defn_evars

(* spiwack: this function loses information from the original evar_map
   it might be an idea not to export it. *)
let to_list d =
  (* Workaround for change in Map.fold behavior in ocaml 3.08.4 *)
  let l = ref [] in
  EvMap.iter (fun evk x -> l := (evk,x)::!l) d.defn_evars;
  EvMap.iter (fun evk x -> l := (evk,x)::!l) d.undf_evars;
  !l

let undefined_map d = d.undf_evars

(* spiwack: not clear what folding over an evar_map, for now we shall
    simply fold over the inner evar_map. *)
let fold f d a =
  EvMap.fold f d.defn_evars (EvMap.fold f d.undf_evars a)

let fold_undefined f d a = EvMap.fold f d.undf_evars a

let raw_map f d =
  let f evk info =
    let ans = f evk info in
    let () = match info.evar_body, ans.evar_body with
    | Evar_defined _, Evar_empty
    | Evar_empty, Evar_defined _ ->
      anomaly (str "Unrespectful mapping function.")
    | _ -> ()
    in
    ans
  in
  let defn_evars = EvMap.smartmapi f d.defn_evars in
  let undf_evars = EvMap.smartmapi f d.undf_evars in
  { d with defn_evars; undf_evars; }

let raw_map_undefined f d =
  let f evk info =
    let ans = f evk info in
    let () = match ans.evar_body with
    | Evar_defined _ ->
      anomaly (str "Unrespectful mapping function.")
    | _ -> ()
    in
    ans
  in
  { d with undf_evars = EvMap.smartmapi f d.undf_evars; }

let is_evar = mem

let is_defined d e = EvMap.mem e d.defn_evars

let is_undefined d e = EvMap.mem e d.undf_evars

let existential_value d (n, args) =
  let info = find d n in
  match evar_body info with
  | Evar_defined c ->
    instantiate_evar_array info c args
  | Evar_empty ->
    raise NotInstantiatedEvar

let existential_opt_value d ev =
  try Some (existential_value d ev)
  with NotInstantiatedEvar -> None

let existential_type d (n, args) =
  let info =
    try find d n
    with Not_found ->
      anomaly (str "Evar " ++ str (string_of_existential n) ++ str " was not declared") in
  instantiate_evar_array info info.evar_concl args

let add_constraints d cstrs =
  { d with univ_cstrs = Univ.merge_constraints cstrs d.univ_cstrs }

(*** /Lifting... ***)

(* evar_map are considered empty disregarding histories *)
let is_empty d =
  EvMap.is_empty d.defn_evars &&
  EvMap.is_empty d.undf_evars &&
  List.is_empty d.conv_pbs &&
  Metamap.is_empty d.metas

let subst_named_context_val s = map_named_val (subst_mps s)

let subst_evar_info s evi =
  let subst_evb = function
  | Evar_empty -> Evar_empty
  | Evar_defined c -> Evar_defined (subst_mps s c)
  in
  { evi with
      evar_concl = subst_mps s evi.evar_concl;
      evar_hyps = subst_named_context_val s evi.evar_hyps;
      evar_body = subst_evb evi.evar_body }

let subst_evar_defs_light sub evd =
  assert (Univ.is_initial_universes evd.univ_cstrs);
  assert (match evd.conv_pbs with [] -> true | _ -> false);
  let map_info i = subst_evar_info sub i in
  { evd with
    undf_evars = EvMap.smartmap map_info evd.undf_evars;
    defn_evars = EvMap.smartmap map_info evd.defn_evars;
    metas = Metamap.smartmap (map_clb (subst_mps sub)) evd.metas; }

let subst_evar_map = subst_evar_defs_light

(* spiwack: deprecated *)
let create_evar_defs sigma = { sigma with
  conv_pbs=[]; last_mods=Evar.Set.empty; metas=Metamap.empty }
(* spiwack: tentatively deprecated *)
let create_goal_evar_defs sigma = { sigma with
   (* conv_pbs=[]; last_mods=Evar.Set.empty; metas=Metamap.empty } *)
  metas=Metamap.empty } 

let empty = {
  defn_evars = EvMap.empty;
  undf_evars = EvMap.empty;
  universes  = Univ.UniverseLSet.empty;
  univ_cstrs = Univ.initial_universes;
  conv_pbs   = [];
  last_mods  = Evar.Set.empty;
  metas      = Metamap.empty;
  effects    = Declareops.no_seff;
}

let has_undefined evd = not (EvMap.is_empty evd.undf_evars)

let evars_reset_evd ?(with_conv_pbs=false) evd d =
  let conv_pbs = if with_conv_pbs then evd.conv_pbs else d.conv_pbs in
  let last_mods = if with_conv_pbs then evd.last_mods else d.last_mods in
  { evd with metas = d.metas; last_mods; conv_pbs; }

let add_conv_pb pb d = {d with conv_pbs = pb::d.conv_pbs}

let evar_source evk d = (find d evk).evar_source

let define_aux def undef evk body =
  let oldinfo =
    try EvMap.find evk undef
    with Not_found ->
      if EvMap.mem evk def then
        anomaly ~label:"Evd.define" (Pp.str "cannot define an evar twice")
      else
        anomaly ~label:"Evd.define" (Pp.str "cannot define undeclared evar")
  in
  let () = assert (oldinfo.evar_body == Evar_empty) in
  let newinfo = { oldinfo with evar_body = Evar_defined body } in
  EvMap.add evk newinfo def, EvMap.remove evk undef

(* define the existential of section path sp as the constr body *)
let define evk body evd =
  let (defn_evars, undf_evars) = define_aux evd.defn_evars evd.undf_evars evk body in
  let last_mods = match evd.conv_pbs with
  | [] ->  evd.last_mods
  | _ -> Evar.Set.add evk evd.last_mods
  in
  { evd with defn_evars; undf_evars; last_mods; }

let evar_declare hyps evk ty ?(src=(Loc.ghost,Evar_kinds.InternalHole)) ?(filter = Filter.identity) ?candidates evd =
  let () = match Filter.repr filter with
  | None -> ()
  | Some filter ->
    assert (Int.equal (List.length filter) (List.length (named_context_of_val hyps)))
  in
  let evar_info = {
    evar_hyps = hyps;
    evar_concl = ty;
    evar_body = Evar_empty;
    evar_filter = filter;
    evar_source = src;
    evar_candidates = candidates;
    evar_extra = Store.empty; }
  in
  { evd with undf_evars = EvMap.add evk evar_info evd.undf_evars; }

(* extracts conversion problems that satisfy predicate p *)
(* Note: conv_pbs not satisying p are stored back in reverse order *)
let extract_conv_pbs evd p =
  let (pbs,pbs1) =
    List.fold_left
      (fun (pbs,pbs1) pb ->
    	 if p pb then
	   (pb::pbs,pbs1)
         else
	   (pbs,pb::pbs1))
      ([],[])
      evd.conv_pbs
  in
  {evd with conv_pbs = pbs1; last_mods = Evar.Set.empty},
  pbs

let extract_changed_conv_pbs evd p =
  extract_conv_pbs evd (fun pb -> p evd.last_mods pb)

let extract_all_conv_pbs evd =
  extract_conv_pbs evd (fun _ -> true)

let loc_of_conv_pb evd (pbty,env,t1,t2) =
  match kind_of_term (fst (decompose_app t1)) with
  | Evar (evk1,_) -> fst (evar_source evk1 evd)
  | _ ->
  match kind_of_term (fst (decompose_app t2)) with
  | Evar (evk2,_) -> fst (evar_source evk2 evd)
  | _ -> Loc.ghost

let evar_list evd c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (evk, _ as ev) when mem evd evk -> ev :: acc
    | _ -> fold_constr evrec acc c in
  evrec [] c

let collect_evars c =
  let rec collrec acc c =
    match kind_of_term c with
      | Evar (evk,_) -> Evar.Set.add evk acc
      | _       -> fold_constr collrec acc c
  in
  collrec Evar.Set.empty c

(**********************************************************)
(* Side effects *)

let emit_side_effects eff evd =
  { evd with effects = Declareops.union_side_effects eff evd.effects; }

let drop_side_effects evd =
  { evd with effects = Declareops.no_seff; }

let eval_side_effects evd = evd.effects

(**********************************************************)
(* Sort variables *)

let new_univ_variable evd =
  let u = Termops.new_univ_level () in
  let universes = Univ.UniverseLSet.add u evd.universes in
  ({ evd with universes }, Univ.Universe.make u)

let new_sort_variable d =
  let (d', u) = new_univ_variable d in
  (d', Type u)

let is_sort_variable evd s = match s with Type u -> true | _ -> false 
let whd_sort_variable evd t = t

let univ_of_sort = function
  | Type u -> u
  | Prop Pos -> Univ.type0_univ
  | Prop Null -> Univ.type0m_univ

let is_eq_sort s1 s2 =
  if Sorts.equal s1 s2 then None
  else
    let u1 = univ_of_sort s1
    and u2 = univ_of_sort s2 in
      if Univ.Universe.equal u1 u2 then None
      else Some (u1, u2)

let is_univ_var_or_set u =
  Univ.is_univ_variable u || Univ.is_type0_univ u

let set_leq_sort evd s1 s2 =
  match is_eq_sort s1 s2 with
  | None -> evd
  | Some (u1, u2) ->
    match s1, s2 with
    | Prop Null, Prop Pos -> evd
    | Prop _, Prop _ ->
      raise (Univ.UniverseInconsistency (Univ.Le, u1, u2,[]))
    | Type u, Prop Pos ->
      let cstr = Univ.enforce_leq u Univ.type0_univ Univ.empty_constraint in
      add_constraints evd cstr
    | Type _, Prop _ ->
      raise (Univ.UniverseInconsistency (Univ.Le, u1, u2,[]))
    | _, Type u ->
      if is_univ_var_or_set u then
        let cstr = Univ.enforce_leq u1 u2 Univ.empty_constraint in
        add_constraints evd cstr
      else raise (Univ.UniverseInconsistency (Univ.Le, u1, u2,[]))

let is_univ_level_var us u =
  match Univ.universe_level u with
  | Some u -> Univ.UniverseLSet.mem u us
  | None -> false

let set_eq_sort ({ universes = us; univ_cstrs = sm; } as d) s1 s2 =
  match is_eq_sort s1 s2 with
  | None -> d
  | Some (u1, u2) ->
      match s1, s2 with
      | Prop c, Type u when is_univ_level_var us u ->
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)
      | Type u, Prop c when is_univ_level_var us u ->
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)
      | Type u, Type v when (is_univ_level_var us u) || (is_univ_level_var us v) ->
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)
      | Prop c, Type u when is_univ_var_or_set u &&
	  Univ.lax_check_eq sm u1 u2 -> d
      | Type u, Prop c when is_univ_var_or_set u &&
          Univ.lax_check_eq sm u1 u2 -> d
      | Type u, Type v when is_univ_var_or_set u && is_univ_var_or_set v ->
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)
      | _, _ -> raise (Univ.UniverseInconsistency (Univ.Eq, u1, u2, []))
	    
(**********************************************************)
(* Accessing metas *)

(** We use this function to overcome OCaml compiler limitations and to prevent
    the use of costly in-place modifications. *)
let set_metas evd metas = {
  defn_evars = evd.defn_evars;
  undf_evars = evd.undf_evars;
  universes  = evd.universes;
  univ_cstrs = evd.univ_cstrs;
  conv_pbs = evd.conv_pbs;
  last_mods = evd.last_mods;
  metas;
  effects = evd.effects; }

let meta_list evd = metamap_to_list evd.metas

let undefined_metas evd =
  let filter = function
    | (n,Clval(_,_,typ)) -> None
    | (n,Cltyp (_,typ))  -> Some n
  in
  let m = List.map_filter filter (meta_list evd) in
  List.sort Int.compare m

let map_metas_fvalue f evd =
  let map = function
  | Clval(id,(c,s),typ) -> Clval(id,(mk_freelisted (f c.rebus),s),typ)
  | x -> x
  in
  set_metas evd (Metamap.smartmap map evd.metas)

let meta_opt_fvalue evd mv =
  match Metamap.find mv evd.metas with
    | Clval(_,b,_) -> Some b
    | Cltyp _ -> None

let meta_defined evd mv =
  match Metamap.find mv evd.metas with
    | Clval _ -> true
    | Cltyp _ -> false

let try_meta_fvalue evd mv =
  match Metamap.find mv evd.metas with
    | Clval(_,b,_) -> b
    | Cltyp _ -> raise Not_found

let meta_fvalue evd mv =
  try try_meta_fvalue evd mv
  with Not_found -> anomaly ~label:"meta_fvalue" (Pp.str "meta has no value")

let meta_value evd mv =
  (fst (try_meta_fvalue evd mv)).rebus

let meta_ftype evd mv =
  match Metamap.find mv evd.metas with
    | Cltyp (_,b) -> b
    | Clval(_,_,b) -> b

let meta_type evd mv = (meta_ftype evd mv).rebus

let meta_declare mv v ?(name=Anonymous) evd =
  let metas = Metamap.add mv (Cltyp(name,mk_freelisted v)) evd.metas in
  set_metas evd metas

let meta_assign mv (v, pb) evd =
  let modify _ = function
  | Cltyp (na, ty) -> Clval (na, (mk_freelisted v, pb), ty)
  | _ -> anomaly ~label:"meta_assign" (Pp.str "already defined")
  in
  let metas = Metamap.modify mv modify evd.metas in
  set_metas evd metas

let meta_reassign mv (v, pb) evd =
  let modify _ = function
  | Clval(na, _, ty) -> Clval (na, (mk_freelisted v, pb), ty)
  | _ -> anomaly ~label:"meta_reassign" (Pp.str "not yet defined")
  in
  let metas = Metamap.modify mv modify evd.metas in
  set_metas evd metas

(* If the meta is defined then forget its name *)
let meta_name evd mv =
  try fst (clb_name (Metamap.find mv evd.metas)) with Not_found -> Anonymous

let meta_with_name evd id =
  let na = Name id in
  let (mvl,mvnodef) =
    Metamap.fold
      (fun n clb (l1,l2 as l) ->
        let (na',def) = clb_name clb in
        if Name.equal na na' then if def then (n::l1,l2) else (n::l1,n::l2)
        else l)
      evd.metas ([],[]) in
  match mvnodef, mvl with
    | _,[]  ->
	errorlabstrm "Evd.meta_with_name"
          (str"No such bound variable " ++ pr_id id ++ str".")
    | ([n],_|_,[n]) ->
	n
    | _  ->
	errorlabstrm "Evd.meta_with_name"
          (str "Binder name \"" ++ pr_id id ++
           strbrk "\" occurs more than once in clause.")

let meta_merge evd1 evd2 =
  let metas = Metamap.fold Metamap.add evd1.metas evd2.metas in
  set_metas evd2 metas

type metabinding = metavariable * constr * instance_status

let retract_coercible_metas evd =
  let mc = ref [] in
  let map n v = match v with
  | Clval (na, (b, (Conv, CoerceToType as s)), typ) ->
    let () = mc := (n, b.rebus, s) :: !mc in
    Cltyp (na, typ)
  | v -> v
  in
  let metas = Metamap.smartmapi map evd.metas in
  !mc, set_metas evd metas

let subst_defined_metas bl c =
  let rec substrec c = match kind_of_term c with
    | Meta i ->
      let select (j,_,_) = Int.equal i j in
      substrec (pi2 (List.find select bl))
    | _ -> map_constr substrec c
  in try Some (substrec c) with Not_found -> None

(*******************************************************************)
type open_constr = evar_map * constr

(*******************************************************************)
(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map
}

let sig_it x = x.it
let sig_sig x = x.sigma

(*******************************************************************)
(* The state monad with state an evar map. *)

module MonadR =
  Monad.Make (struct

    type +'a t = evar_map -> evar_map * 'a

    let return a = fun s -> (s,a)

    let (>>=) x f = fun s ->
      let (s',a) = x s in
      f a s'

  end)

module Monad =
  Monad.Make (struct

    type +'a t = evar_map -> 'a * evar_map

    let return a = fun s -> (a,s)

    let (>>=) x f = fun s ->
      let (a,s') = x s in
      f a s'

  end)

(**********************************************************)
(* Failure explanation *)

type unsolvability_explanation = SeveralInstancesFound of int

(**********************************************************)
(* Pretty-printing *)

let pr_instance_status (sc,typ) =
  begin match sc with
  | IsSubType -> str " [or a subtype of it]"
  | IsSuperType -> str " [or a supertype of it]"
  | Conv -> mt ()
  end ++
  begin match typ with
  | CoerceToType -> str " [up to coercion]"
  | TypeNotProcessed -> mt ()
  | TypeProcessed -> str " [type is checked]"
  end

let pr_meta_map mmap =
  let pr_name = function
      Name id -> str"[" ++ pr_id id ++ str"]"
    | _ -> mt() in
  let pr_meta_binding = function
    | (mv,Cltyp (na,b)) ->
      	hov 0
	  (pr_meta mv ++ pr_name na ++ str " : " ++
           print_constr b.rebus ++ fnl ())
    | (mv,Clval(na,(b,s),t)) ->
      	hov 0
	  (pr_meta mv ++ pr_name na ++ str " := " ++
           print_constr b.rebus ++
	   str " : " ++ print_constr t.rebus ++
	   spc () ++ pr_instance_status s ++ fnl ())
  in
  prlist pr_meta_binding (metamap_to_list mmap)

let pr_decl ((id,b,_),ok) =
  match b with
  | None -> if ok then pr_id id else (str "{" ++ pr_id id ++ str "}")
  | Some c -> str (if ok then "(" else "{") ++ pr_id id ++ str ":=" ++
      print_constr c ++ str (if ok then ")" else "}")

let pr_evar_source = function
  | Evar_kinds.QuestionMark _ -> str "underscore"
  | Evar_kinds.CasesType -> str "pattern-matching return predicate"
  | Evar_kinds.BinderType (Name id) -> str "type of " ++ Nameops.pr_id id
  | Evar_kinds.BinderType Anonymous -> str "type of anonymous binder"
  | Evar_kinds.ImplicitArg (c,(n,ido),b) ->
      let id = Option.get ido in
      str "parameter " ++ pr_id id ++ spc () ++ str "of" ++
      spc () ++ print_constr (constr_of_global c)
  | Evar_kinds.InternalHole -> str "internal placeholder"
  | Evar_kinds.TomatchTypeParameter (ind,n) ->
      pr_nth n ++ str " argument of type " ++ print_constr (mkInd ind)
  | Evar_kinds.GoalEvar -> str "goal evar"
  | Evar_kinds.ImpossibleCase -> str "type of impossible pattern-matching clause"
  | Evar_kinds.MatchingVar _ -> str "matching variable"

let pr_evar_info evi =
  let phyps =
    try
      let decls = match Filter.repr (evar_filter evi) with
      | None -> List.map (fun c -> (c, true)) (evar_context evi)
      | Some filter -> List.combine (evar_context evi) filter
      in
      prlist_with_sep spc pr_decl (List.rev decls)
    with Invalid_argument _ -> str "Ill-formed filtered context" in
  let pty = print_constr evi.evar_concl in
  let pb =
    match evi.evar_body with
      | Evar_empty -> mt ()
      | Evar_defined c -> spc() ++ str"=> "  ++ print_constr c
  in
  let candidates =
    match evi.evar_body, evi.evar_candidates with
      | Evar_empty, Some l ->
           spc () ++ str "{" ++
           prlist_with_sep (fun () -> str "|") print_constr l ++ str "}"
      | _ ->
          mt ()
  in
  let src = str "(" ++ pr_evar_source (snd evi.evar_source) ++ str ")" in
  hov 2
    (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pty ++ pb ++ str"]" ++
       candidates ++ spc() ++ src)

let compute_evar_dependency_graph (sigma : evar_map) =
  (* Compute the map binding ev to the evars whose body depends on ev *)
  let fold evk evi acc =
    let fold_ev evk' acc =
      let tab =
        try EvMap.find evk' acc
        with Not_found -> Evar.Set.empty
      in
      EvMap.add evk' (Evar.Set.add evk tab) acc
    in
    match evar_body evi with
    | Evar_empty -> assert false
    | Evar_defined c -> Evar.Set.fold fold_ev (collect_evars c) acc
  in
  EvMap.fold fold sigma.defn_evars EvMap.empty

let evar_dependency_closure n sigma =
  (** Create the DAG of depth [n] representing the recursive dependencies of
      undefined evars. *)
  let graph = compute_evar_dependency_graph sigma in
  let rec aux n curr accu =
    if Int.equal n 0 then Evar.Set.union curr accu
    else
      let fold evk accu =
        try
          let deps = EvMap.find evk graph in
          Evar.Set.union deps accu
        with Not_found -> accu
      in
      (** Consider only the newly added evars *)
      let ncurr = Evar.Set.fold fold curr Evar.Set.empty in
      (** Merge the others *)
      let accu = Evar.Set.union curr accu in
      aux (n - 1) ncurr accu
  in
  let undef = EvMap.domain (undefined_map sigma) in
  aux n undef Evar.Set.empty

let evar_dependency_closure n sigma =
  let deps = evar_dependency_closure n sigma in
  let map = EvMap.bind (fun ev -> find sigma ev) deps in
  EvMap.bindings map

let has_no_evar sigma =
  EvMap.is_empty sigma.defn_evars && EvMap.is_empty sigma.undf_evars

let print_env_short env =
  let pr_body n = function
  | None -> pr_name n
  | Some b -> str "(" ++ pr_name n ++ str " := " ++ print_constr b ++ str ")" in
  let pr_named_decl (n, b, _) = pr_body (Name n) b in
  let pr_rel_decl (n, b, _) = pr_body n b in
  let nc = List.rev (named_context env) in
  let rc = List.rev (rel_context env) in
    str "[" ++ pr_sequence pr_named_decl nc ++ str "]" ++ spc () ++
    str "[" ++ pr_sequence pr_rel_decl rc ++ str "]"

let pr_evar_constraints pbs =
  let pr_evconstr (pbty, env, t1, t2) =
    print_env_short env ++ spc () ++ str "|-" ++ spc () ++
      print_constr t1 ++ spc () ++
      str (match pbty with
            | Reduction.CONV -> "=="
            | Reduction.CUMUL -> "<=") ++
      spc () ++ print_constr t2
  in
  prlist_with_sep fnl pr_evconstr pbs

let pr_evar_map_gen pr_evars sigma =
  let { universes = uvs; univ_cstrs = univs; } = sigma in
  let evs = if has_no_evar sigma then mt () else pr_evars sigma
  and svs =
    if Univ.UniverseLSet.is_empty uvs then mt ()
    else str "UNIVERSE VARIABLES:" ++ brk (0, 1) ++
      h 0 (prlist_with_sep fnl Univ.pr_uni_level
        (Univ.UniverseLSet.elements uvs)) ++ fnl ()
  and cs =
    if Univ.is_initial_universes univs then mt ()
    else str "UNIVERSES:" ++ brk (0, 1) ++
      h 0 (Univ.pr_universes univs) ++ fnl ()
  and cstrs =
    if List.is_empty sigma.conv_pbs then mt ()
    else
    str "CONSTRAINTS:" ++ brk (0, 1) ++
      pr_evar_constraints sigma.conv_pbs ++ fnl ()
  and metas =
    if Metamap.is_empty sigma.metas then mt ()
    else
      str "METAS:" ++ brk (0, 1) ++ pr_meta_map sigma.metas
  in
  evs ++ svs ++ cs ++ cstrs ++ metas

let pr_evar_list l =
  let pr (ev, evi) =
    h 0 (str (string_of_existential ev) ++
      str "==" ++ pr_evar_info evi)
  in
  h 0 (prlist_with_sep fnl pr l)

let pr_evar_by_depth depth sigma = match depth with
| None ->
  (* Print all evars *)
  str"EVARS:"++brk(0,1)++pr_evar_list (to_list sigma)++fnl()
| Some n ->
  (* Print all evars *)
  str"UNDEFINED EVARS:"++
  (if Int.equal n 0 then mt() else str" (+level "++int n++str" closure):")++
  brk(0,1)++
  pr_evar_list (evar_dependency_closure n sigma)++fnl()

let pr_evar_by_filter filter sigma =
  let defined = Evar.Map.filter filter sigma.defn_evars in
  let undefined = Evar.Map.filter filter sigma.undf_evars in
  let prdef =
    if Evar.Map.is_empty defined then mt ()
    else str "DEFINED EVARS:" ++ brk (0, 1) ++
      pr_evar_list (Evar.Map.bindings defined)
  in
  let prundef =
    if Evar.Map.is_empty undefined then mt ()
    else str "UNDEFINED EVARS:" ++ brk (0, 1) ++
      pr_evar_list (Evar.Map.bindings undefined)
  in
  prdef ++ prundef

let pr_evar_map depth sigma =
  pr_evar_map_gen (fun sigma -> pr_evar_by_depth depth sigma) sigma

let pr_evar_map_filter filter sigma =
  pr_evar_map_gen (fun sigma -> pr_evar_by_filter filter sigma) sigma

let pr_metaset metas =
  str "[" ++ pr_sequence pr_meta (Metaset.elements metas) ++ str "]"
