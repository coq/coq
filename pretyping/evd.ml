(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

let map_evar_body f = function
  | Evar_empty -> Evar_empty
  | Evar_defined d -> Evar_defined (f d)

let map_evar_info f evi =
  {evi with
    evar_body = map_evar_body f evi.evar_body;
    evar_hyps = map_named_val f evi.evar_hyps;
    evar_concl = f evi.evar_concl;
    evar_candidates = Option.map (List.map f) evi.evar_candidates }

let evar_ident_info evi =
  match evi.evar_source with
  | _,Evar_kinds.ImplicitArg (c,(n,Some id),b) -> id
  | _,Evar_kinds.VarInstance id -> id
  | _,Evar_kinds.GoalEvar -> Id.of_string "Goal"
  | _ ->
      let env = reset_with_named_context evi.evar_hyps (Global.env()) in
      Namegen.id_of_name_using_hdchar env evi.evar_concl Anonymous

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
  | true :: filter, (id, _, _) :: ctxt ->
    if i < len then
      let c = Array.unsafe_get args i in
      if test_id id c then instrec filter ctxt (succ i)
      else (id, c) :: instrec filter ctxt (succ i)
    else instance_mismatch ()
  | _ -> instance_mismatch ()
  in
  match Filter.repr (evar_filter info) with
  | None ->
    let map i (id, _, _) =
      if (i < len) then
        let c = Array.unsafe_get args i in
        if test_id id c then None else Some (id,c)
      else instance_mismatch ()
    in
    List.map_filter_i map (evar_context info)
  | Some filter ->
    instrec filter (evar_context info) 0

let make_evar_instance_array info args =
  evar_instance_array isVarId info args

let instantiate_evar_array info c args =
  let inst = make_evar_instance_array info args in
  match inst with
  | [] -> c
  | _ -> replace_vars inst c

module StringOrd = struct type t = string let compare = String.compare end
module UNameMap = struct
    
  include Map.Make(StringOrd)
    
  let union s t = 
    if s == t then s
    else
      merge (fun k l r -> 
	match l, r with
	| Some _, _ -> l
	| _, _ -> r) s t
end

(* 2nd part used to check consistency on the fly. *)
type evar_universe_context = 
 { uctx_names : Univ.Level.t UNameMap.t * string Univ.LMap.t;
   uctx_local : Univ.universe_context_set; (** The local context of variables *)
    uctx_univ_variables : Universes.universe_opt_subst;
      (** The local universes that are unification variables *)
    uctx_univ_algebraic : Univ.universe_set; 
    (** The subset of unification variables that
	can be instantiated with algebraic universes as they appear in types 
	and universe instances only. *)
    uctx_universes : Univ.universes; (** The current graph extended with the local constraints *)
    uctx_initial_universes : Univ.universes; (** The graph at the creation of the evar_map *)
  }
  
let empty_evar_universe_context = 
  { uctx_names = UNameMap.empty, Univ.LMap.empty;
    uctx_local = Univ.ContextSet.empty;
    uctx_univ_variables = Univ.LMap.empty;
    uctx_univ_algebraic = Univ.LSet.empty;
    uctx_universes = Univ.initial_universes;
    uctx_initial_universes = Univ.initial_universes }

let evar_universe_context_from e = 
  let u = universes e in
    {empty_evar_universe_context with 
      uctx_universes = u; uctx_initial_universes = u}

let is_empty_evar_universe_context ctx =
  Univ.ContextSet.is_empty ctx.uctx_local && 
    Univ.LMap.is_empty ctx.uctx_univ_variables

let union_evar_universe_context ctx ctx' =
  if ctx == ctx' then ctx
  else if is_empty_evar_universe_context ctx' then ctx
  else
    let local = Univ.ContextSet.union ctx.uctx_local ctx'.uctx_local in
    let names = UNameMap.union (fst ctx.uctx_names) (fst ctx'.uctx_names) in
    let names_rev = Univ.LMap.union (snd ctx.uctx_names) (snd ctx'.uctx_names) in
      { uctx_names = (names, names_rev);
	uctx_local = local;
	uctx_univ_variables = 
	  Univ.LMap.subst_union ctx.uctx_univ_variables ctx'.uctx_univ_variables;
	uctx_univ_algebraic = 
	  Univ.LSet.union ctx.uctx_univ_algebraic ctx'.uctx_univ_algebraic;
	uctx_initial_universes = ctx.uctx_initial_universes;
	uctx_universes = 
	  if local == ctx.uctx_local then ctx.uctx_universes
	  else
	    let cstrsr = Univ.ContextSet.constraints ctx'.uctx_local in
	      Univ.merge_constraints cstrsr ctx.uctx_universes }

(* let union_evar_universe_context_key = Profile.declare_profile "union_evar_universe_context";; *)
(* let union_evar_universe_context =  *)
(*   Profile.profile2 union_evar_universe_context_key union_evar_universe_context;; *)

type 'a in_evar_universe_context = 'a * evar_universe_context

let evar_universe_context_set ctx = ctx.uctx_local
let evar_universe_context_constraints ctx = snd ctx.uctx_local
let evar_context_universe_context ctx = Univ.ContextSet.to_context ctx.uctx_local
let evar_universe_context_of ctx = { empty_evar_universe_context with uctx_local = ctx }
let evar_universe_context_subst ctx = ctx.uctx_univ_variables

let instantiate_variable l b v =
  (* let b = Univ.subst_large_constraint (Univ.Universe.make l) Univ.type0m_univ b in *)
  (* if Univ.univ_depends (Univ.Universe.make l) b then  *)
  (*   error ("Occur-check in universe variable instantiation") *)
  (* else *) v := Univ.LMap.add l (Some b) !v

exception UniversesDiffer

let process_universe_constraints univs vars alg cstrs =
  let vars = ref vars in
  let normalize = Universes.normalize_universe_opt_subst vars in
  let rec unify_universes fo l d r local =
    let l = normalize l and r = normalize r in
      if Univ.Universe.equal l r then local
      else 
	let varinfo x = 
	  match Univ.Universe.level x with
	  | None -> Inl x
	  | Some l -> Inr (l, Univ.LMap.mem l !vars, Univ.LSet.mem l alg)
	in
	  if d == Universes.ULe then
	    if Univ.check_leq univs l r then
	      (** Keep Prop/Set <= var around if var might be instantiated by prop or set
		  later. *)
	      if Univ.Universe.is_level l then 
		match Univ.Universe.level r with
		| Some r ->
		  Univ.Constraint.add (Option.get (Univ.Universe.level l),Univ.Le,r) local
		| _ -> local
	      else local
	    else
	      match Univ.Universe.level r with
	      | None -> error ("Algebraic universe on the right")
	      | Some rl ->
		if Univ.Level.is_small rl then
		  let levels = Univ.Universe.levels l in
		    Univ.LSet.fold (fun l local ->
		      if Univ.Level.is_small l || Univ.LMap.mem l !vars then
			Univ.enforce_eq (Univ.Universe.make l) r local
		      else raise (Univ.UniverseInconsistency (Univ.Le, Univ.Universe.make l, r, None)))
		      levels local
		else
		  Univ.enforce_leq l r local
	  else if d == Universes.ULub then
	    match varinfo l, varinfo r with
	    | (Inr (l, true, _), Inr (r, _, _)) 
	    | (Inr (r, _, _), Inr (l, true, _)) -> 
	      instantiate_variable l (Univ.Universe.make r) vars; 
	      Univ.enforce_eq_level l r local
	    | Inr (_, _, _), Inr (_, _, _) ->
	      unify_universes true l Universes.UEq r local
	    | _, _ -> assert false
	  else (* d = Universes.UEq *)
	    match varinfo l, varinfo r with
	    | Inr (l', lloc, _), Inr (r', rloc, _) ->
	      let () = 
		if lloc then
		  instantiate_variable l' r vars
		else if rloc then 
		  instantiate_variable r' l vars
		else if not (Univ.check_eq univs l r) then
		  (* Two rigid/global levels, none of them being local,
		     one of them being Prop/Set, disallow *)
		  if Univ.Level.is_small l' || Univ.Level.is_small r' then
		    raise (Univ.UniverseInconsistency (Univ.Eq, l, r, None))
		  else
		    if fo then 
		      raise UniversesDiffer
	      in
	        Univ.enforce_eq_level l' r' local
           | _, _ (* One of the two is algebraic or global *) -> 
	     if Univ.check_eq univs l r then local
	     else raise (Univ.UniverseInconsistency (Univ.Eq, l, r, None))
  in
  let local = 
    Universes.Constraints.fold (fun (l,d,r) local -> unify_universes false l d r local)
      cstrs Univ.Constraint.empty
  in
    !vars, local

let add_constraints_context ctx cstrs =
  let univs, local = ctx.uctx_local in
  let cstrs' = Univ.Constraint.fold (fun (l,d,r) acc -> 
    let l = Univ.Universe.make l and r = Univ.Universe.make r in
    let cstr' = 
      if d == Univ.Lt then (Univ.Universe.super l, Universes.ULe, r)
      else (l, (if d == Univ.Le then Universes.ULe else Universes.UEq), r)
    in Universes.Constraints.add cstr' acc)
    cstrs Universes.Constraints.empty
  in
  let vars, local' =
    process_universe_constraints ctx.uctx_universes
      ctx.uctx_univ_variables ctx.uctx_univ_algebraic
      cstrs'
  in
    { ctx with uctx_local = (univs, Univ.Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = Univ.merge_constraints cstrs ctx.uctx_universes }

(* let addconstrkey = Profile.declare_profile "add_constraints_context";; *)
(* let add_constraints_context = Profile.profile2 addconstrkey add_constraints_context;; *)

let add_universe_constraints_context ctx cstrs =
  let univs, local = ctx.uctx_local in
  let vars, local' = 
    process_universe_constraints ctx.uctx_universes 
      ctx.uctx_univ_variables ctx.uctx_univ_algebraic 
      cstrs 
  in
    { ctx with uctx_local = (univs, Univ.Constraint.union local local');
      uctx_univ_variables = vars;
      uctx_universes = Univ.merge_constraints local' ctx.uctx_universes }

(* let addunivconstrkey = Profile.declare_profile "add_universe_constraints_context";; *)
(* let add_universe_constraints_context =  *)
(*   Profile.profile2 addunivconstrkey add_universe_constraints_context;; *)
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
  (** Existential variables *)
  defn_evars : evar_info EvMap.t;
  undf_evars : evar_info EvMap.t;
  evar_names : Id.t EvMap.t * existential_key Idmap.t;
  (** Universes *)
  universes  : evar_universe_context;
  (** Conversion problems *)
  conv_pbs   : evar_constraint list;
  last_mods  : Evar.Set.t;
  (** Metas *)
  metas      : clbinding Metamap.t;
  (** Interactive proofs *)
  effects    : Declareops.side_effects;
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
}

(*** Lifting primitive from Evar.Map. ***)

(* HH: The progress tactical now uses this function. *)
let progress_evar_map d1 d2 =
  let is_new k v =
    assert (v.evar_body == Evar_empty);
    EvMap.mem k d2.defn_evars
  in
  not (d1 == d2) && EvMap.exists is_new d1.undf_evars

let add_name_newly_undefined naming evk evi (evtoid,idtoev) =
  let id = match naming with
  | Misctypes.IntroAnonymous ->
      let id = evar_ident_info evi in
      Namegen.next_ident_away_from id (fun id -> Idmap.mem id idtoev)
  | Misctypes.IntroIdentifier id ->
      let id' =
        Namegen.next_ident_away_from id (fun id -> Idmap.mem id idtoev) in
      if not (Names.Id.equal id id') then
        user_err_loc
          (Loc.ghost,"",str "Already an existential evar of name " ++ pr_id id);
      id'
  | Misctypes.IntroFresh id ->
      Namegen.next_ident_away_from id (fun id -> Idmap.mem id idtoev) in
  (EvMap.add evk id evtoid, Idmap.add id evk idtoev)

let add_name_undefined naming evk evi (evtoid,idtoev as evar_names) =
  if EvMap.mem evk evtoid then
    evar_names
  else
    add_name_newly_undefined naming evk evi evar_names

let remove_name_defined evk (evtoid,idtoev) =
  let id = EvMap.find evk evtoid in
  (EvMap.remove evk evtoid, Idmap.remove id idtoev)

let remove_name_possibly_already_defined evk evar_names =
  try remove_name_defined evk evar_names
  with Not_found -> evar_names

let rename evk id evd =
  let (evtoid,idtoev) = evd.evar_names in
  let id' = EvMap.find evk evtoid in
  if Idmap.mem id idtoev then anomaly (str "Evar name already in use");
  { evd with evar_names =
      (EvMap.add evk id evtoid (* overwrite old name *),
       Idmap.add id evk (Idmap.remove id' idtoev)) }

let reassign_name_defined evk evk' (evtoid,idtoev) =
  let id = EvMap.find evk evtoid in
  (EvMap.add evk' id (EvMap.remove evk evtoid),
   Idmap.add id evk' (Idmap.remove id idtoev))

let add d e i = match i.evar_body with
| Evar_empty ->
  let evar_names = add_name_undefined Misctypes.IntroAnonymous e i d.evar_names in
  { d with undf_evars = EvMap.add e i d.undf_evars; evar_names }
| Evar_defined _ ->
  let evar_names = remove_name_possibly_already_defined e d.evar_names in
  { d with defn_evars = EvMap.add e i d.defn_evars; evar_names }

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
      undf_evars = EvMap.map (map_evar_info f) evd.defn_evars
  }

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
  universes  = empty_evar_universe_context;
  conv_pbs   = [];
  last_mods  = Evar.Set.empty;
  metas      = Metamap.empty;
  effects    = Declareops.no_seff;
  evar_names = (EvMap.empty,Idmap.empty); (* id<->key for undefined evars *)
  future_goals = [];
  principal_future_goal = None;
}

let from_env ?ctx e = 
  match ctx with
  | None -> { empty with universes = evar_universe_context_from e }
  | Some ctx -> { empty with universes = ctx }

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

let add_conv_pb pb d = {d with conv_pbs = pb::d.conv_pbs}

let evar_source evk d = (find d evk).evar_source

let evar_ident evk evd =
  try EvMap.find evk (fst evd.evar_names)
  with Not_found ->
    (* Unnamed (non-dependent) evar *)
    add_suffix (Id.of_string "X") (string_of_int (Evar.repr evk))

let evar_key id evd =
  Idmap.find id (snd evd.evar_names)

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
  let evar_names = remove_name_defined evk evd.evar_names in
  { evd with defn_evars; undf_evars; last_mods; evar_names }

let evar_declare hyps evk ty ?(src=(Loc.ghost,Evar_kinds.InternalHole)) 
    ?(filter=Filter.identity) ?candidates ?(store=Store.empty)
    ?(naming=Misctypes.IntroAnonymous) evd =
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
    evar_extra = store; }
  in
  let evar_names = add_name_newly_undefined naming evk evar_info evd.evar_names in
  { evd with undf_evars = EvMap.add evk evar_info evd.undf_evars; evar_names }

let restrict evk evk' filter ?candidates evd =
  let evar_info = EvMap.find evk evd.undf_evars in
  let evar_info' =
    { evar_info with evar_filter = filter;
      evar_candidates = candidates;
      evar_extra = Store.empty } in
  let evar_names = reassign_name_defined evk evk' evd.evar_names in
  let ctxt = Filter.filter_list filter (evar_context evar_info) in
  let id_inst = Array.map_of_list (fun (id,_,_) -> mkVar id) ctxt in
  let body = mkEvar(evk',id_inst) in
  let (defn_evars, undf_evars) = define_aux evd.defn_evars evd.undf_evars evk body in
  { evd with undf_evars = EvMap.add evk' evar_info' undf_evars;
    defn_evars; evar_names }

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
  | _ -> Loc.ghost

(** The following functions return the set of evars immediately
    contained in the object *)

(* excluding defined evars *)

let evar_list c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (evk, _ as ev) -> ev :: acc
    | _ -> fold_constr evrec acc c in
  evrec [] c

let evars_of_term c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (n, l) -> Evar.Set.add n (Array.fold_left evrec acc l)
    | _ -> fold_constr evrec acc c
  in
  evrec Evar.Set.empty c

let evars_of_named_context nc =
  List.fold_right (fun (_, b, t) s ->
    Option.fold_left (fun s t ->
      Evar.Set.union s (evars_of_term t))
      (Evar.Set.union s (evars_of_term t)) b)
    nc Evar.Set.empty

let evars_of_filtered_evar_info evi =
  Evar.Set.union (evars_of_term evi.evar_concl)
    (Evar.Set.union
	(match evi.evar_body with
	| Evar_empty -> Evar.Set.empty
	| Evar_defined b -> evars_of_term b)
	(evars_of_named_context (evar_filtered_context evi)))

(**********************************************************)
(* Side effects *)

let emit_side_effects eff evd =
  { evd with effects = Declareops.union_side_effects eff evd.effects; }

let drop_side_effects evd =
  { evd with effects = Declareops.no_seff; }

let eval_side_effects evd = evd.effects

(* Future goals *)
let declare_future_goal evk evd =
  { evd with future_goals = evk::evd.future_goals }

let declare_principal_goal evk evd =
  match evd.principal_future_goal with
  | None -> { evd with
    future_goals = evk::evd.future_goals;
    principal_future_goal=Some evk; }
  | Some _ -> Errors.error "Only one main subgoal per instantiation."

let future_goals evd = evd.future_goals

let principal_future_goal evd = evd.principal_future_goal

let reset_future_goals evd =
  { evd with future_goals = [] ; principal_future_goal=None }

let restore_future_goals evd gls pgl =
  { evd with future_goals = gls ; principal_future_goal = pgl }

(**********************************************************)
(* Sort variables *)

type rigid = 
  | UnivRigid
  | UnivFlexible of bool (** Is substitution by an algebraic ok? *)

let univ_rigid = UnivRigid
let univ_flexible = UnivFlexible false
let univ_flexible_alg = UnivFlexible true

let evar_universe_context d = d.universes

let universe_context_set d = d.universes.uctx_local

let universe_context evd =
  Univ.ContextSet.to_context evd.universes.uctx_local

let universe_subst evd =
  evd.universes.uctx_univ_variables

let merge_uctx rigid uctx ctx' =
  let open Univ in
  let uctx = 
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b ->
      let levels = ContextSet.levels ctx' in
      let fold u accu =
        if LMap.mem u accu then accu
        else LMap.add u None accu
      in
      let uvars' = LSet.fold fold levels uctx.uctx_univ_variables in
	if b then
	  { uctx with uctx_univ_variables = uvars';
	  uctx_univ_algebraic = LSet.union uctx.uctx_univ_algebraic levels }
	else { uctx with uctx_univ_variables = uvars' }
  in
  let uctx_local = ContextSet.append ctx' uctx.uctx_local in
  let uctx_universes = merge_constraints (ContextSet.constraints ctx') uctx.uctx_universes in
  { uctx with uctx_local; uctx_universes }

let merge_context_set rigid evd ctx' = 
  {evd with universes = merge_uctx rigid evd.universes ctx'}

let merge_uctx_subst uctx s =
  { uctx with uctx_univ_variables = Univ.LMap.subst_union uctx.uctx_univ_variables s }
      
let merge_universe_subst evd subst = 
  {evd with universes = merge_uctx_subst evd.universes subst }

let with_context_set rigid d (a, ctx) = 
  (merge_context_set rigid d ctx, a)

let add_uctx_names s l (names, names_rev) =
    (UNameMap.add s l names, Univ.LMap.add l s names_rev)

let uctx_new_univ_variable rigid name
  ({ uctx_local = ctx; uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as uctx) =
  let u = Universes.new_univ_level (Global.current_dirpath ()) in
  let ctx' = Univ.ContextSet.add_universe u ctx in
  let uctx' = 
    match rigid with
    | UnivRigid -> uctx
    | UnivFlexible b -> 
      let uvars' = Univ.LMap.add u None uvars in
	if b then {uctx with uctx_univ_variables = uvars';
	  uctx_univ_algebraic = Univ.LSet.add u avars}
	else {uctx with uctx_univ_variables = Univ.LMap.add u None uvars} in
  let names = 
    match name with
    | Some n -> add_uctx_names n u uctx.uctx_names
    | None -> uctx.uctx_names
  in
    {uctx' with uctx_names = names; uctx_local = ctx';
      uctx_universes = Univ.add_universe u uctx.uctx_universes}, u

let new_univ_level_variable ?name rigid evd =
  let uctx', u = uctx_new_univ_variable rigid name evd.universes in
    ({evd with universes = uctx'}, u)

let new_univ_variable ?name rigid evd =
  let uctx', u = uctx_new_univ_variable rigid name evd.universes in
    ({evd with universes = uctx'}, Univ.Universe.make u)

let new_sort_variable ?name rigid d =
  let (d', u) = new_univ_variable rigid ?name d in
    (d', Type u)

let make_flexible_variable evd b u =
  let {uctx_univ_variables = uvars; uctx_univ_algebraic = avars} as ctx = evd.universes in
  let uvars' = Univ.LMap.add u None uvars in
  let avars' = 
    if b then
      let uu = Univ.Universe.make u in
      let substu_not_alg u' v =
	Option.cata (fun vu -> Univ.Universe.equal uu vu && not (Univ.LSet.mem u' avars)) false v
      in
	if not (Univ.LMap.exists substu_not_alg uvars)
	then Univ.LSet.add u avars else avars 
    else avars 
  in
    {evd with universes = {ctx with uctx_univ_variables = uvars'; 
      uctx_univ_algebraic = avars'}}

(****************************************)
(* Operations on constants              *)
(****************************************)

let fresh_sort_in_family ?(rigid=univ_flexible) env evd s = 
  with_context_set rigid evd (Universes.fresh_sort_in_family env s)

let fresh_constant_instance env evd c =
  with_context_set univ_flexible evd (Universes.fresh_constant_instance env c)

let fresh_inductive_instance env evd i =
  with_context_set univ_flexible evd (Universes.fresh_inductive_instance env i)

let fresh_constructor_instance env evd c =
  with_context_set univ_flexible evd (Universes.fresh_constructor_instance env c)

let fresh_global ?(rigid=univ_flexible) ?names env evd gr =
  with_context_set rigid evd (Universes.fresh_global_instance ?names env gr)

let whd_sort_variable evd t = t

let is_sort_variable evd s = 
  match s with 
  | Type u -> 
    (match Univ.universe_level u with
    | Some l as x -> 
      let uctx = evd.universes in
	if Univ.LSet.mem l (Univ.ContextSet.levels uctx.uctx_local) then x
	else None
    | None -> None)
  | _ -> None

let is_flexible_level evd l = 
  let uctx = evd.universes in
    Univ.LMap.mem l uctx.uctx_univ_variables

let is_eq_sort s1 s2 =
  if Sorts.equal s1 s2 then None
  else
    let u1 = univ_of_sort s1
    and u2 = univ_of_sort s2 in
      if Univ.Universe.equal u1 u2 then None
      else Some (u1, u2)

let normalize_universe evd =
  let vars = ref evd.universes.uctx_univ_variables in
  let normalize = Universes.normalize_universe_opt_subst vars in
    normalize

let normalize_universe_instance evd l =
  let vars = ref evd.universes.uctx_univ_variables in
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
  (* let normalize = Universes.normalize_universe_opt_subst (ref univs.uctx_univ_variables) in *)
  (* (\* let dref, norm = memo_normalize_universe d in *\) *)
  (* let u1 = normalize u1 and u2 = normalize u2 in *)
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
    (* if Univ.is_type0_univ u2 then *)
    (*   if Univ.is_small_univ u1 then evd *)
    (*   else raise (Univ.UniverseInconsistency (Univ.Le, u1, u2, [])) *)
    (* else if Univ.is_type0m_univ u2 then  *)
    (*   raise (Univ.UniverseInconsistency (Univ.Le, u1, u2, [])) *)
    (* else  *)
      if not (type_in_type env) then
      add_universe_constraints evd (Universes.Constraints.singleton (u1,Universes.ULe,u2))
      else evd
	    
let check_eq evd s s' =
  Univ.check_eq evd.universes.uctx_universes s s'

let check_leq evd s s' =
  Univ.check_leq evd.universes.uctx_universes s s'

let subst_univs_context_with_def def usubst (ctx, cst) =
  (Univ.LSet.diff ctx def, Univ.subst_univs_constraints usubst cst)

let normalize_evar_universe_context_variables uctx =
  let normalized_variables, undef, def, subst = 
    Universes.normalize_univ_variables uctx.uctx_univ_variables 
  in
  let ctx_local = subst_univs_context_with_def def (Univ.make_subst subst) uctx.uctx_local in
  let ctx_local', univs = Universes.refresh_constraints uctx.uctx_initial_universes ctx_local in
    subst, { uctx with uctx_local = ctx_local';
      uctx_univ_variables = normalized_variables;
      uctx_universes = univs }

(* let normvarsconstrkey = Profile.declare_profile "normalize_evar_universe_context_variables";; *)
(* let normalize_evar_universe_context_variables = *)
(*   Profile.profile1 normvarsconstrkey normalize_evar_universe_context_variables;; *)
    
let abstract_undefined_variables uctx =
  let vars' = 
    Univ.LMap.fold (fun u v acc ->
      if v == None then Univ.LSet.remove u acc
      else acc)
    uctx.uctx_univ_variables uctx.uctx_univ_algebraic
  in { uctx with uctx_local = Univ.ContextSet.empty;
      uctx_univ_algebraic = vars' }


let refresh_undefined_univ_variables uctx =
  let subst, ctx' = Universes.fresh_universe_context_set_instance uctx.uctx_local in
  let alg = Univ.LSet.fold (fun u acc -> Univ.LSet.add (Univ.subst_univs_level_level subst u) acc) 
    uctx.uctx_univ_algebraic Univ.LSet.empty 
  in
  let vars = 
    Univ.LMap.fold
      (fun u v acc ->
	Univ.LMap.add (Univ.subst_univs_level_level subst u) 
          (Option.map (Univ.subst_univs_level_universe subst) v) acc)
      uctx.uctx_univ_variables Univ.LMap.empty
  in 
  let uctx' = {uctx_names = uctx.uctx_names;
	       uctx_local = ctx'; 
	       uctx_univ_variables = vars; uctx_univ_algebraic = alg;
	       uctx_universes = Univ.initial_universes;
	       uctx_initial_universes = uctx.uctx_initial_universes } in
    uctx', subst

let refresh_undefined_universes evd =
  let uctx', subst = refresh_undefined_univ_variables evd.universes in
  let evd' = cmap (subst_univs_level_constr subst) {evd with universes = uctx'} in
    evd', subst

let normalize_evar_universe_context uctx = 
  let rec fixpoint uctx = 
    let ((vars',algs'), us') = 
      Universes.normalize_context_set uctx.uctx_local uctx.uctx_univ_variables
        uctx.uctx_univ_algebraic
    in
      if Univ.LSet.equal (fst us') (fst uctx.uctx_local) then 
        uctx
      else
	let us', universes = Universes.refresh_constraints uctx.uctx_initial_universes us' in
	let uctx' = 
	  { uctx_names = uctx.uctx_names;
	    uctx_local = us'; 
	    uctx_univ_variables = vars'; 
	    uctx_univ_algebraic = algs';
	    uctx_universes = universes;
	    uctx_initial_universes = uctx.uctx_initial_universes }
	in fixpoint uctx'
  in fixpoint uctx

let nf_univ_variables evd = 
  let subst, uctx' = normalize_evar_universe_context_variables evd.universes in
  let evd' = {evd with universes = uctx'} in
    evd', subst

let nf_constraints evd =
  let subst, uctx' = normalize_evar_universe_context_variables evd.universes in
  let uctx' = normalize_evar_universe_context uctx' in
    {evd with universes = uctx'}

let nf_constraints = 
  if Flags.profile then
    let nfconstrkey = Profile.declare_profile "nf_constraints" in
      Profile.profile1 nfconstrkey nf_constraints
  else nf_constraints

let universe_of_name evd s = 
  UNameMap.find s (fst evd.universes.uctx_names)

let add_universe_name evd s l =
  let names' = add_uctx_names s l evd.universes.uctx_names in
    {evd with universes = {evd.universes with uctx_names = names'}}

let universes evd = evd.universes.uctx_universes

(* Conversion w.r.t. an evar map and its local universes. *)

let conversion_gen env evd pb t u =
  match pb with 
  | Reduction.CONV -> 
    Reduction.trans_conv_universes 
      full_transparent_state ~evars:(existential_opt_value evd) env 
      evd.universes.uctx_universes t u
  | Reduction.CUMUL -> Reduction.trans_conv_leq_universes
     full_transparent_state ~evars:(existential_opt_value evd) env 
    evd.universes.uctx_universes t u

(* let conversion_gen_key = Profile.declare_profile "conversion_gen" *)
(* let conversion_gen = Profile.profile5 conversion_gen_key conversion_gen *)

let conversion env d pb t u =
  conversion_gen env d pb t u; d

let test_conversion env d pb t u =
  try conversion_gen env d pb t u; true
  with _ -> false

let eq_constr_univs evd t u =
  let b, c = Universes.eq_constr_univs_infer evd.universes.uctx_universes t u in
    if b then 
      try let evd' = add_universe_constraints evd c in evd', b
      with Univ.UniverseInconsistency _ | UniversesDiffer -> evd, false
    else evd, b

let e_eq_constr_univs evdref t u =
  let evd, b = eq_constr_univs !evdref t u in
    evdref := evd; b

let eq_constr_univs_test evd t u =
  snd (eq_constr_univs evd t u)

let eq_named_context_val d ctx1 ctx2 = 
  ctx1 == ctx2 ||
    let c1 = named_context_of_val ctx1 and c2 = named_context_of_val ctx2 in
    let eq_named_declaration (i1, c1, t1) (i2, c2, t2) =
      Id.equal i1 i2 && Option.equal (eq_constr_univs_test d) c1 c2 
      && (eq_constr_univs_test d) t1 t2
    in List.equal eq_named_declaration c1 c2

let eq_evar_body d b1 b2 = match b1, b2 with
| Evar_empty, Evar_empty -> true
| Evar_defined t1, Evar_defined t2 -> eq_constr_univs_test d t1 t2
| _ -> false

let eq_evar_info d ei1 ei2 =
  ei1 == ei2 ||
    eq_constr_univs_test d ei1.evar_concl ei2.evar_concl &&
    eq_named_context_val d (ei1.evar_hyps) (ei2.evar_hyps) &&
    eq_evar_body d ei1.evar_body ei2.evar_body
    (** ppedrot: [eq_constr] may be a bit too permissive here *)


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

let explain_no_such_bound_variable evd id =
  let mvl =
    List.rev (Metamap.fold (fun n clb l ->
      let na = fst (clb_name clb) in
      if na != Anonymous then out_name na :: l else l)
    evd.metas []) in
  errorlabstrm "Evd.meta_with_name"
    (str"No such bound variable " ++ pr_id id ++
     (if mvl == [] then str " (no bound variables at all in the expression)."
      else
        (str" (possible name" ++
         str (if List.length mvl == 1 then " is: " else "s are: ") ++
         pr_enum pr_id mvl ++ str").")))

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
      explain_no_such_bound_variable evd id
    | ([n],_|_,[n]) ->
	n
    | _  ->
	errorlabstrm "Evd.meta_with_name"
          (str "Binder name \"" ++ pr_id id ++
           strbrk "\" occurs more than once in clause.")

let clear_metas evd = {evd with metas = Metamap.empty}

let meta_merge evd1 evd2 =
  let metas = Metamap.fold Metamap.add evd1.metas evd2.metas in
  let universes = union_evar_universe_context evd2.universes evd1.universes in
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

let subst_defined_metas_evars (bl,el) c =
  let rec substrec c = match kind_of_term c with
    | Meta i ->
      let select (j,_,_) = Int.equal i j in
      substrec (pi2 (List.find select bl))
    | Evar (evk,args) ->
      let select (_,(evk',args'),_) = Evar.equal evk evk' && Array.equal Constr.equal args args' in
      (try substrec (pi3 (List.find select el))
       with Not_found -> map_constr substrec c)
    | _ -> map_constr substrec c
  in try Some (substrec c) with Not_found -> None

let evar_source_of_meta mv evd =
  match meta_name evd mv with
  | Anonymous -> (Loc.ghost,Evar_kinds.GoalEvar)
  | Name id -> (Loc.ghost,Evar_kinds.VarInstance id)

let dependent_evar_ident ev evd =
  let evi = find evd ev in
  match evi.evar_source with
  | (_,Evar_kinds.VarInstance id) -> id
  | _ -> anomaly (str "Not an evar resulting of a dependent binding")

(*******************************************************************)

type pending = (* before: *) evar_map * (* after: *) evar_map

type pending_constr = pending * constr

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

(**********************************************************)
(* Pretty-printing *)

let pr_existential_key sigma evk = str "?" ++ pr_id (evar_ident evk sigma)

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

let rec pr_evar_source = function
  | Evar_kinds.QuestionMark _ -> str "underscore"
  | Evar_kinds.CasesType false -> str "pattern-matching return predicate"
  | Evar_kinds.CasesType true ->
      str "subterm of pattern-matching return predicate"
  | Evar_kinds.BinderType (Name id) -> str "type of " ++ Nameops.pr_id id
  | Evar_kinds.BinderType Anonymous -> str "type of anonymous binder"
  | Evar_kinds.ImplicitArg (c,(n,ido),b) ->
      let id = Option.get ido in
      str "parameter " ++ pr_id id ++ spc () ++ str "of" ++
      spc () ++ print_constr (printable_constr_of_global c)
  | Evar_kinds.InternalHole -> str "internal placeholder"
  | Evar_kinds.TomatchTypeParameter (ind,n) ->
      pr_nth n ++ str " argument of type " ++ print_constr (mkInd ind)
  | Evar_kinds.GoalEvar -> str "goal evar"
  | Evar_kinds.ImpossibleCase -> str "type of impossible pattern-matching clause"
  | Evar_kinds.MatchingVar _ -> str "matching variable"
  | Evar_kinds.VarInstance id -> str "instance of " ++ pr_id id
  | Evar_kinds.SubEvar evk ->
      str "subterm of " ++ str (string_of_existential evk)

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
    | Evar_defined c -> Evar.Set.fold fold_ev (evars_of_term c) acc
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

let pr_uctx_level uctx = 
  let map, map_rev = uctx.uctx_names in 
    fun l ->
      try str(Univ.LMap.find l map_rev)
      with Not_found -> 
	Universes.pr_with_global_universes l

let pr_evd_level evd = pr_uctx_level evd.universes

let pr_evar_universe_context ctx =
  let prl = pr_uctx_level ctx in
  if is_empty_evar_universe_context ctx then mt ()
  else
    (str"UNIVERSES:"++brk(0,1)++ 
       h 0 (Univ.pr_universe_context_set prl ctx.uctx_local) ++ fnl () ++
     str"ALGEBRAIC UNIVERSES:"++brk(0,1)++
     h 0 (Univ.LSet.pr prl ctx.uctx_univ_algebraic) ++ fnl() ++
     str"UNDEFINED UNIVERSES:"++brk(0,1)++
       h 0 (Universes.pr_universe_opt_subst ctx.uctx_univ_variables) ++ fnl())

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
      print_constr_env env t1 ++ spc () ++
      str (match pbty with
            | Reduction.CONV -> "=="
            | Reduction.CUMUL -> "<=") ++
      spc () ++ print_constr_env env t2
  in
  prlist_with_sep fnl pr_evconstr pbs

let pr_evar_map_gen with_univs pr_evars sigma =
  let { universes = uvs } = sigma in
  let evs = if has_no_evar sigma then mt () else pr_evars sigma ++ fnl ()
  and svs = if with_univs then pr_evar_universe_context uvs else mt ()
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
  evs ++ svs ++ cstrs ++ metas

let pr_evar_list sigma l =
  let pr (ev, evi) =
    h 0 (str (string_of_existential ev) ++
      str "==" ++ pr_evar_info evi ++
      (if evi.evar_body == Evar_empty
       then str " {" ++ pr_id (evar_ident ev sigma) ++ str "}"
       else mt ()))
  in
  h 0 (prlist_with_sep fnl pr l)

let pr_evar_by_depth depth sigma = match depth with
| None ->
  (* Print all evars *)
  str"EVARS:"++brk(0,1)++pr_evar_list sigma (to_list sigma)++fnl()
| Some n ->
  (* Print all evars *)
  str"UNDEFINED EVARS:"++
  (if Int.equal n 0 then mt() else str" (+level "++int n++str" closure):")++
  brk(0,1)++
  pr_evar_list sigma (evar_dependency_closure n sigma)++fnl()

let pr_evar_by_filter filter sigma =
  let defined = Evar.Map.filter filter sigma.defn_evars in
  let undefined = Evar.Map.filter filter sigma.undf_evars in
  let prdef =
    if Evar.Map.is_empty defined then mt ()
    else str "DEFINED EVARS:" ++ brk (0, 1) ++
      pr_evar_list sigma (Evar.Map.bindings defined)
  in
  let prundef =
    if Evar.Map.is_empty undefined then mt ()
    else str "UNDEFINED EVARS:" ++ brk (0, 1) ++
      pr_evar_list sigma (Evar.Map.bindings undefined)
  in
  prdef ++ prundef

let pr_evar_map ?(with_univs=true) depth sigma =
  pr_evar_map_gen with_univs (fun sigma -> pr_evar_by_depth depth sigma) sigma

let pr_evar_map_filter ?(with_univs=true) filter sigma =
  pr_evar_map_gen with_univs (fun sigma -> pr_evar_by_filter filter sigma) sigma

let pr_metaset metas =
  str "[" ++ pr_sequence pr_meta (Metaset.elements metas) ++ str "]"
