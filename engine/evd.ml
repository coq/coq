(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util
open Names
open Nameops
open Term
open Vars
open Environ

(* module RelDecl = Context.Rel.Declaration *)
module NamedDecl = Context.Named.Declaration

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
  val apply_subfilter : t -> bool list -> t
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

  let apply_subfilter_array filter subfilter =
    (** In both cases we statically know that the argument will contain at
        least one [false] *)
    match filter with
    | None -> Some (Array.to_list subfilter)
    | Some f ->
    let len = Array.length subfilter in
    let fold b (i, ans) =
      if b then
        let () = assert (0 <= i) in
        (pred i, Array.unsafe_get subfilter i :: ans)
      else
        (i, false :: ans)
    in
    Some (snd (List.fold_right fold f (pred len, [])))

  let apply_subfilter filter subfilter =
    apply_subfilter_array filter (Array.of_list subfilter)

  let restrict_upon f len p =
    let newfilter = Array.init len p in
    if Array.for_all (fun id -> id) newfilter then None
    else
      Some (apply_subfilter_array f newfilter)

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

let string_of_existential evk = "?X" ^ string_of_int (Evar.repr evk)

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
  evar_source = Loc.tag @@ Evar_kinds.InternalHole;
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

let map_evar_body f = function
  | Evar_empty -> Evar_empty
  | Evar_defined d -> Evar_defined (f d)

let map_evar_info f evi =
  {evi with
    evar_body = map_evar_body f evi.evar_body;
    evar_hyps = map_named_val f evi.evar_hyps;
    evar_concl = f evi.evar_concl;
    evar_candidates = Option.map (List.map f) evi.evar_candidates }

(* This exception is raised by *.existential_value *)
exception NotInstantiatedEvar

(* Note: let-in contributes to the instance *)

let evar_instance_array test_id info args =
  let len = Array.length args in
  let rec instrec filter ctxt i = match filter, ctxt with
  | [], [] ->
    if Int.equal i len then []
    else instance_mismatch ()
  | false :: filter, _ :: ctxt ->
    instrec filter ctxt i
  | true :: filter, d :: ctxt ->
    if i < len then
      let c = Array.unsafe_get args i in
      if test_id d c then instrec filter ctxt (succ i)
      else (NamedDecl.get_id d, c) :: instrec filter ctxt (succ i)
    else instance_mismatch ()
  | _ -> instance_mismatch ()
  in
  match Filter.repr (evar_filter info) with
  | None ->
     let map i d =
      if (i < len) then
        let c = Array.unsafe_get args i in
        if test_id d c then None else Some (NamedDecl.get_id d, c)
      else instance_mismatch ()
    in
    List.map_filter_i map (evar_context info)
  | Some filter ->
    instrec filter (evar_context info) 0

let make_evar_instance_array info args =
  evar_instance_array (NamedDecl.get_id %> isVarId) info args

let instantiate_evar_array info c args =
  let inst = make_evar_instance_array info args in
  match inst with
  | [] -> c
  | _ -> replace_vars inst c

type evar_universe_context = UState.t

type 'a in_evar_universe_context = 'a * evar_universe_context

let empty_evar_universe_context = UState.empty
let union_evar_universe_context = UState.union
let evar_universe_context_set = UState.context_set
let evar_universe_context_constraints = UState.constraints
let evar_context_universe_context = UState.context
let evar_universe_context_of = UState.of_context_set
let evar_universe_context_subst = UState.subst
let add_constraints_context = UState.add_constraints
let add_universe_constraints_context = UState.add_universe_constraints
let constrain_variables = UState.constrain_variables 
let evar_universe_context_of_binders = UState.of_binders

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
      | _         -> Term.fold_constr collrec acc c
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

module EvNames :
sig

type t

val empty : t
val add_name_undefined : Id.t option -> Evar.t -> evar_info -> t -> t
val remove_name_defined : Evar.t -> t -> t
val rename : Evar.t -> Id.t -> t -> t
val reassign_name_defined : Evar.t -> Evar.t -> t -> t
val ident : Evar.t -> t -> Id.t option
val key : Id.t -> t -> Evar.t

end =
struct

type t = Id.t EvMap.t * existential_key Idmap.t

let empty = (EvMap.empty, Idmap.empty)

let add_name_newly_undefined id evk evi (evtoid, idtoev as names) =
  match id with
  | None -> names
  | Some id ->
    if Idmap.mem id idtoev then
      user_err  (str "Already an existential evar of name " ++ pr_id id);
    (EvMap.add evk id evtoid, Idmap.add id evk idtoev)

let add_name_undefined naming evk evi (evtoid,idtoev as evar_names) =
  if EvMap.mem evk evtoid then
    evar_names
  else
    add_name_newly_undefined naming evk evi evar_names

let remove_name_defined evk (evtoid, idtoev as names) =
  let id = try Some (EvMap.find evk evtoid) with Not_found -> None in
  match id with
  | None -> names
  | Some id -> (EvMap.remove evk evtoid, Idmap.remove id idtoev)

let rename evk id (evtoid, idtoev) =
  let id' = try Some (EvMap.find evk evtoid) with Not_found -> None in
  match id' with
  | None -> (EvMap.add evk id evtoid, Idmap.add id evk idtoev)
  | Some id' ->
    if Idmap.mem id idtoev then anomaly (str "Evar name already in use");
    (EvMap.update evk id evtoid (* overwrite old name *), Idmap.add id evk (Idmap.remove id' idtoev))

let reassign_name_defined evk evk' (evtoid, idtoev as names) =
  let id = try Some (EvMap.find evk evtoid) with Not_found -> None in
  match id with
  | None -> names (** evk' must not be defined *)
  | Some id ->
    (EvMap.add evk' id (EvMap.remove evk evtoid),
    Idmap.add id evk' (Idmap.remove id idtoev))

let ident evk (evtoid, _) =
  try Some (EvMap.find evk evtoid) with Not_found -> None

let key id (_, idtoev) =
  Idmap.find id idtoev

end

type evar_map = {
  (** Existential variables *)
  defn_evars : evar_info EvMap.t;
  undf_evars : evar_info EvMap.t;
  evar_names : EvNames.t;
  (** Universes *)
  universes  : evar_universe_context;
  (** Conversion problems *)
  conv_pbs   : evar_constraint list;
  last_mods  : Evar.Set.t;
  (** Metas *)
  metas      : clbinding Metamap.t;
  (** Interactive proofs *)
  effects    : Safe_typing.private_constants;
  future_goals : Evar.t list; (** list of newly created evars, to be
                                  eventually turned into goals if not solved.*)
  principal_future_goal : Evar.t option; (** if [Some e], [e] must be
                                             contained
                                             [future_goals]. The evar
                                             [e] will inherit
                                             properties (now: the
                                             name) of the evar which
                                             will be instantiated with
                                             a term containing [e]. *)
  extras : Store.t;
}

(*** Lifting primitive from Evar.Map. ***)

let rename evk id evd =
  { evd with evar_names = EvNames.rename evk id evd.evar_names }

let add_with_name ?name d e i = match i.evar_body with
| Evar_empty ->
  let evar_names = EvNames.add_name_undefined name e i d.evar_names in
  { d with undf_evars = EvMap.add e i d.undf_evars; evar_names }
| Evar_defined _ ->
  let evar_names = EvNames.remove_name_defined e d.evar_names in
  { d with defn_evars = EvMap.add e i d.defn_evars; evar_names }

let add d e i = add_with_name d e i

(** New evars *)

let evar_counter_summary_name = "evar counter"

(* Generator of existential names *)
let new_untyped_evar =
  let evar_ctr = Summary.ref 0 ~name:evar_counter_summary_name in
  fun () -> incr evar_ctr; Evar.unsafe_of_int !evar_ctr

let new_evar evd ?name evi =
  let evk = new_untyped_evar () in
  let evd = add_with_name evd ?name evk evi in
  (evd, evk)

let remove d e =
  let undf_evars = EvMap.remove e d.undf_evars in
  let defn_evars = EvMap.remove e d.defn_evars in
  let principal_future_goal = match d.principal_future_goal with
  | None -> None
  | Some e' -> if Evar.equal e e' then None else d.principal_future_goal
  in
  let future_goals = List.filter (fun e' -> not (Evar.equal e e')) d.future_goals in
  { d with undf_evars; defn_evars; principal_future_goal; future_goals }

let find d e =
  try EvMap.find e d.undf_evars
  with Not_found -> EvMap.find e d.defn_evars

let find_undefined d e = EvMap.find e d.undf_evars

let mem d e = EvMap.mem e d.undf_evars || EvMap.mem e d.defn_evars

let undefined_map d = d.undf_evars

let drop_all_defined d = { d with defn_evars = EvMap.empty }

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

let add_constraints d c =
  { d with universes = add_constraints_context d.universes c }

let add_universe_constraints d c = 
  { d with universes = add_universe_constraints_context d.universes c }

(*** /Lifting... ***)

(* evar_map are considered empty disregarding histories *)
let is_empty d =
  EvMap.is_empty d.defn_evars &&
  EvMap.is_empty d.undf_evars &&
  List.is_empty d.conv_pbs &&
  Metamap.is_empty d.metas

let cmap f evd = 
  { evd with
      metas = Metamap.map (map_clb f) evd.metas;
      defn_evars = EvMap.map (map_evar_info f) evd.defn_evars;
      undf_evars = EvMap.map (map_evar_info f) evd.undf_evars
  }

(* spiwack: deprecated *)
let create_evar_defs sigma = { sigma with
  conv_pbs=[]; last_mods=Evar.Set.empty; metas=Metamap.empty }

let empty = {
  defn_evars = EvMap.empty;
  undf_evars = EvMap.empty;
  universes  = empty_evar_universe_context;
  conv_pbs   = [];
  last_mods  = Evar.Set.empty;
  metas      = Metamap.empty;
  effects    = Safe_typing.empty_private_constants;
  evar_names = EvNames.empty; (* id<->key for undefined evars *)
  future_goals = [];
  principal_future_goal = None;
  extras = Store.empty;
}

let from_env e = 
  { empty with universes = UState.make (Environ.universes e) }

let from_ctx ctx = { empty with universes = ctx }

let has_undefined evd = not (EvMap.is_empty evd.undf_evars)

let evars_reset_evd ?(with_conv_pbs=false) ?(with_univs=true) evd d =
  let conv_pbs = if with_conv_pbs then evd.conv_pbs else d.conv_pbs in
  let last_mods = if with_conv_pbs then evd.last_mods else d.last_mods in
  let universes = 
    if not with_univs then evd.universes
    else union_evar_universe_context evd.universes d.universes
  in
  { evd with
    metas = d.metas;
    last_mods; conv_pbs; universes }

let merge_universe_context evd uctx' =
  { evd with universes = union_evar_universe_context evd.universes uctx' }

let set_universe_context evd uctx' =
  { evd with universes = uctx' }

let add_conv_pb ?(tail=false) pb d =
  (** MS: we have duplicates here, why? *)
  if tail then {d with conv_pbs = d.conv_pbs @ [pb]}
  else {d with conv_pbs = pb::d.conv_pbs}

let evar_source evk d = (find d evk).evar_source

let evar_ident evk evd = EvNames.ident evk evd.evar_names
let evar_key id evd = EvNames.key id evd.evar_names

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
  let evar_names = EvNames.remove_name_defined evk evd.evar_names in
  { evd with defn_evars; undf_evars; last_mods; evar_names }

let restrict evk filter ?candidates evd =
  let evk' = new_untyped_evar () in
  let evar_info = EvMap.find evk evd.undf_evars in
  let evar_info' =
    { evar_info with evar_filter = filter;
      evar_candidates = candidates;
      evar_extra = Store.empty } in
  let last_mods = match evd.conv_pbs with
  | [] ->  evd.last_mods
  | _ -> Evar.Set.add evk evd.last_mods in
  let evar_names = EvNames.reassign_name_defined evk evk' evd.evar_names in
  let ctxt = Filter.filter_list filter (evar_context evar_info) in
  let id_inst = Array.map_of_list (NamedDecl.get_id %> mkVar) ctxt in
  let body = mkEvar(evk',id_inst) in
  let (defn_evars, undf_evars) = define_aux evd.defn_evars evd.undf_evars evk body in
  { evd with undf_evars = EvMap.add evk' evar_info' undf_evars;
    defn_evars; last_mods; evar_names }, evk'

let downcast evk ccl evd =
  let evar_info = EvMap.find evk evd.undf_evars in
  let evar_info' = { evar_info with evar_concl = ccl } in
  { evd with undf_evars = EvMap.add evk evar_info' evd.undf_evars }

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
  | _             -> None

(** The following functions return the set of evars immediately
    contained in the object *)

(* excluding defined evars *)

let evars_of_term c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, l) -> Evar.Set.add n (Array.fold_left evrec acc l)
    | _ -> Term.fold_constr evrec acc c
  in
  evrec Evar.Set.empty c

let evars_of_named_context nc =
  Context.Named.fold_outside
    (NamedDecl.fold_constr (fun constr s -> Evar.Set.union s (evars_of_term constr)))
    nc
    ~init:Evar.Set.empty

let evars_of_filtered_evar_info evi =
  Evar.Set.union (evars_of_term evi.evar_concl)
    (Evar.Set.union
	(match evi.evar_body with
	| Evar_empty -> Evar.Set.empty
	| Evar_defined b -> evars_of_term b)
	(evars_of_named_context (evar_filtered_context evi)))

(**********************************************************)
(* Sort variables *)

type rigid = UState.rigid =
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let evar_universe_context d = d.universes

let universe_context_set d = UState.context_set d.universes

let universe_context ?names evd = UState.universe_context ?names evd.universes

let restrict_universe_context evd vars =
  { evd with universes = UState.restrict evd.universes vars }

let universe_subst evd =
  UState.subst evd.universes

let merge_context_set ?loc ?(sideff=false) rigid evd ctx' =
  {evd with universes = UState.merge ?loc sideff rigid evd.universes ctx'}

let merge_universe_subst evd subst = 
  {evd with universes = UState.merge_subst evd.universes subst }

let with_context_set ?loc rigid d (a, ctx) =
  (merge_context_set ?loc rigid d ctx, a)

let new_univ_level_variable ?loc ?name rigid evd =
  let uctx', u = UState.new_univ_variable ?loc rigid name evd.universes in
    ({evd with universes = uctx'}, u)

let new_univ_variable ?loc ?name rigid evd =
  let uctx', u = UState.new_univ_variable ?loc rigid name evd.universes in
    ({evd with universes = uctx'}, Univ.Universe.make u)

let new_sort_variable ?loc ?name rigid d =
  let (d', u) = new_univ_variable ?loc rigid ?name d in
    (d', Type u)

let add_global_univ d u =
  { d with universes = UState.add_global_univ d.universes u }

let make_flexible_variable evd b u =
  { evd with universes = UState.make_flexible_variable evd.universes b u }

let make_evar_universe_context e l =
  let uctx = UState.make (Environ.universes e) in
  match l with
  | None -> uctx
  | Some us ->
      List.fold_left
        (fun uctx (loc,id) ->
        fst (UState.new_univ_variable ?loc univ_rigid (Some (Id.to_string id)) uctx))
        uctx us

(****************************************)
(* Operations on constants              *)
(****************************************)

let fresh_sort_in_family ?loc ?(rigid=univ_flexible) env evd s = 
  with_context_set ?loc rigid evd (Universes.fresh_sort_in_family env s)

let fresh_constant_instance ?loc env evd c =
  with_context_set ?loc univ_flexible evd (Universes.fresh_constant_instance env c)

let fresh_inductive_instance ?loc env evd i =
  with_context_set ?loc univ_flexible evd (Universes.fresh_inductive_instance env i)

let fresh_constructor_instance ?loc env evd c =
  with_context_set ?loc univ_flexible evd (Universes.fresh_constructor_instance env c)

let fresh_global ?loc ?(rigid=univ_flexible) ?names env evd gr =
  with_context_set ?loc rigid evd (Universes.fresh_global_instance ?names env gr)

let whd_sort_variable evd t = t

let is_sort_variable evd s = UState.is_sort_variable evd.universes s

let is_flexible_level evd l = 
  let uctx = evd.universes in
    Univ.LMap.mem l (UState.subst uctx)

let is_eq_sort s1 s2 =
  if Sorts.equal s1 s2 then None
  else
    let u1 = univ_of_sort s1
    and u2 = univ_of_sort s2 in
      if Univ.Universe.equal u1 u2 then None
      else Some (u1, u2)

(* Precondition: l is not defined in the substitution *)
let universe_rigidity evd l =
  let uctx = evd.universes in
  if Univ.LSet.mem l (Univ.ContextSet.levels (UState.context_set uctx)) then
    UnivFlexible (Univ.LSet.mem l (UState.algebraics uctx))
  else UnivRigid

let normalize_universe evd =
  let vars = ref (UState.subst evd.universes) in
  let normalize = Universes.normalize_universe_opt_subst vars in
    normalize

let normalize_universe_instance evd l =
  let vars = ref (UState.subst evd.universes) in
  let normalize = Univ.level_subst_of (Universes.normalize_univ_variable_opt_subst vars) in
    Univ.Instance.subst_fn normalize l

let normalize_sort evars s =
  match s with
  | Prop _ -> s
  | Type u -> 
    let u' = normalize_universe evars u in
    if u' == u then s else Type u'

(* FIXME inefficient *)
let set_eq_sort env d s1 s2 =
  let s1 = normalize_sort d s1 and s2 = normalize_sort d s2 in
  match is_eq_sort s1 s2 with
  | None -> d
  | Some (u1, u2) ->
    if not (type_in_type env) then
      add_universe_constraints d
        (Universes.Constraints.singleton (u1,Universes.UEq,u2))
    else
      d

let has_lub evd u1 u2 =
  if Univ.Universe.equal u1 u2 then evd
  else add_universe_constraints evd
    (Universes.Constraints.singleton (u1,Universes.ULub,u2))

let set_eq_level d u1 u2 =
  add_constraints d (Univ.enforce_eq_level u1 u2 Univ.Constraint.empty)

let set_leq_level d u1 u2 =
  add_constraints d (Univ.enforce_leq_level u1 u2 Univ.Constraint.empty)

let set_eq_instances ?(flex=false) d u1 u2 =
  add_universe_constraints d
    (Universes.enforce_eq_instances_univs flex u1 u2 Universes.Constraints.empty)

let set_leq_sort env evd s1 s2 =
  let s1 = normalize_sort evd s1 
  and s2 = normalize_sort evd s2 in
  match is_eq_sort s1 s2 with
  | None -> evd
  | Some (u1, u2) ->
     if not (type_in_type env) then
       add_universe_constraints evd (Universes.Constraints.singleton (u1,Universes.ULe,u2))
     else evd
	    
let check_eq evd s s' =
  UGraph.check_eq (UState.ugraph evd.universes) s s'

let check_leq evd s s' =
  UGraph.check_leq (UState.ugraph evd.universes) s s'

let normalize_evar_universe_context_variables = UState.normalize_variables

let abstract_undefined_variables = UState.abstract_undefined_variables

let fix_undefined_variables evd =
  { evd with universes = UState.fix_undefined_variables evd.universes }

let refresh_undefined_universes evd =
  let uctx', subst = UState.refresh_undefined_univ_variables evd.universes in
  let evd' = cmap (subst_univs_level_constr subst) {evd with universes = uctx'} in
    evd', subst

let normalize_evar_universe_context = UState.normalize

let nf_univ_variables evd = 
  let subst, uctx' = normalize_evar_universe_context_variables evd.universes in
  let evd' = {evd with universes = uctx'} in
    evd', subst

let nf_constraints evd =
  let subst, uctx' = normalize_evar_universe_context_variables evd.universes in
  let uctx' = normalize_evar_universe_context uctx' in
    {evd with universes = uctx'}

let universe_of_name evd s = UState.universe_of_name evd.universes s

let add_universe_name evd s l =
  { evd with universes = UState.add_universe_name evd.universes s l }

let universes evd = UState.ugraph evd.universes

let update_sigma_env evd env =
  { evd with universes = UState.update_sigma_env evd.universes env }

exception UniversesDiffer = UState.UniversesDiffer

(**********************************************************)
(* Side effects *)

let emit_side_effects eff evd =
  { evd with effects = Safe_typing.concat_private eff evd.effects;
	     universes = UState.emit_side_effects eff evd.universes }

let drop_side_effects evd =
  { evd with effects = Safe_typing.empty_private_constants; }

let eval_side_effects evd = evd.effects

(* Future goals *)
let declare_future_goal evk evd =
  { evd with future_goals = evk::evd.future_goals }

let declare_principal_goal evk evd =
  match evd.principal_future_goal with
  | None -> { evd with
    future_goals = evk::evd.future_goals;
    principal_future_goal=Some evk; }
  | Some _ -> CErrors.error "Only one main subgoal per instantiation."

let future_goals evd = evd.future_goals

let principal_future_goal evd = evd.principal_future_goal

let reset_future_goals evd =
  { evd with future_goals = [] ; principal_future_goal=None }

let restore_future_goals evd gls pgl =
  { evd with future_goals = gls ; principal_future_goal = pgl }

(**********************************************************)
(* Accessing metas *)

(** We use this function to overcome OCaml compiler limitations and to prevent
    the use of costly in-place modifications. *)
let set_metas evd metas = {
  defn_evars = evd.defn_evars;
  undf_evars = evd.undf_evars;
  universes  = evd.universes;
  conv_pbs = evd.conv_pbs;
  last_mods = evd.last_mods;
  metas;
  effects = evd.effects;
  evar_names = evd.evar_names;
  future_goals = evd.future_goals;
  principal_future_goal = evd.principal_future_goal;
  extras = evd.extras;
}

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

let map_metas f evd =
  let map cl = map_clb f cl in
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

let clear_metas evd = {evd with metas = Metamap.empty}

let meta_merge ?(with_univs = true) evd1 evd2 =
  let metas = Metamap.fold Metamap.add evd1.metas evd2.metas in
  let universes =
    if with_univs then union_evar_universe_context evd2.universes evd1.universes
    else evd2.universes
  in
  {evd2 with universes; metas; }

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

let evar_source_of_meta mv evd =
  match meta_name evd mv with
  | Anonymous -> Loc.tag Evar_kinds.GoalEvar
  | Name id   -> Loc.tag @@ Evar_kinds.VarInstance id

let dependent_evar_ident ev evd =
  let evi = find evd ev in
  match evi.evar_source with
  | (_,Evar_kinds.VarInstance id) -> id
  | _ -> anomaly (str "Not an evar resulting of a dependent binding")

(**********************************************************)
(* Extra data *)

let get_extra_data evd = evd.extras
let set_extra_data extras evd = { evd with extras }

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
let on_sig s f = 
  let sigma', v = f s.sigma in
    { s with sigma = sigma' }, v

(*******************************************************************)
(* The state monad with state an evar map. *)

module MonadR =
  Monad.Make (struct

    type +'a t = evar_map -> evar_map * 'a

    let return a = fun s -> (s,a)

    let (>>=) x f = fun s ->
      let (s',a) = x s in
      f a s'

    let (>>) x y = fun s ->
      let (s',()) = x s in
      y s'

    let map f x = fun s ->
      on_snd f (x s)

  end)

module Monad =
  Monad.Make (struct

    type +'a t = evar_map -> 'a * evar_map

    let return a = fun s -> (a,s)

    let (>>=) x f = fun s ->
      let (a,s') = x s in
      f a s'

    let (>>) x y = fun s ->
      let ((),s') = x s in
      y s'

    let map f x = fun s ->
      on_fst f (x s)

  end)

(**********************************************************)
(* Failure explanation *)

type unsolvability_explanation = SeveralInstancesFound of int
