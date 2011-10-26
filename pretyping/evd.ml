(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Names
open Nameops
open Term
open Termops
open Sign
open Environ
open Libnames
open Mod_subst

(* The kinds of existential variable *)

type obligation_definition_status = Define of bool | Expand

type hole_kind =
  | ImplicitArg of global_reference * (int * identifier option) * bool
  | BinderType of name
  | QuestionMark of obligation_definition_status
  | CasesType
  | InternalHole
  | TomatchTypeParameter of inductive * int
  | GoalEvar
  | ImpossibleCase
  | MatchingVar of bool * identifier

(* The type of mappings for existential variables *)

type evar = existential_key

let string_of_existential evk = "?" ^ string_of_int evk
let existential_of_int evk = evk

type evar_body =
  | Evar_empty
  | Evar_defined of constr

type evar_info = {
  evar_concl : constr;
  evar_hyps : named_context_val;
  evar_body : evar_body;
  evar_filter : bool list;
  evar_source : hole_kind located;
  evar_extra : Store.t }

let make_evar hyps ccl = {
  evar_concl = ccl;
  evar_hyps = hyps;
  evar_body = Evar_empty;
  evar_filter = List.map (fun _ -> true) (named_context_of_val hyps);
  evar_source = (dummy_loc,InternalHole);
  evar_extra = Store.empty
}

let evar_concl evi = evi.evar_concl
let evar_hyps evi = evi.evar_hyps
let evar_context evi = named_context_of_val evi.evar_hyps
let evar_body evi = evi.evar_body
let evar_filter evi = evi.evar_filter
let evar_unfiltered_env evi = Global.env_of_context evi.evar_hyps
let evar_filtered_context evi =
  snd (list_filter2 (fun b c -> b) (evar_filter evi,evar_context evi))
let evar_env evi =
  List.fold_right push_named (evar_filtered_context evi)
    (reset_context (Global.env()))

let eq_evar_info ei1 ei2 =
  ei1 == ei2 ||
    eq_constr ei1.evar_concl ei2.evar_concl &&
    eq_named_context_val (ei1.evar_hyps) (ei2.evar_hyps) &&
    ei1.evar_body = ei2.evar_body

(* spiwack: Revised hierarchy :
   - ExistentialMap ( Maps of existential_keys )
   - EvarInfoMap ( .t = evar_info ExistentialMap.t * evar_info ExistentialMap )
   - EvarMap ( .t = EvarInfoMap.t * sort_constraints )
   - evar_map (exported)
*)

module ExistentialMap = Intmap
module ExistentialSet = Intset

(* This exception is raised by *.existential_value *)
exception NotInstantiatedEvar

(* Note: let-in contributes to the instance *)
let make_evar_instance sign args =
  let rec instrec = function
    | (id,_,_) :: sign, c::args when isVarId id c -> instrec (sign,args)
    | (id,_,_) :: sign, c::args -> (id,c) :: instrec (sign,args)
    | [],[] -> []
    | [],_ | _,[] -> anomaly "Signature and its instance do not match"
  in
    instrec (sign,args)

let instantiate_evar sign c args =
  let inst = make_evar_instance sign args in
  if inst = [] then c else replace_vars inst c

module EvarInfoMap = struct
  type t = evar_info ExistentialMap.t * evar_info ExistentialMap.t

  let empty = ExistentialMap.empty, ExistentialMap.empty

  let is_empty (d,u) = ExistentialMap.is_empty d && ExistentialMap.is_empty u

  let has_undefined (_,u) = not (ExistentialMap.is_empty u)

  let to_list (def,undef) =
    (* Workaround for change in Map.fold behavior in ocaml 3.08.4 *)
    let l = ref [] in
    ExistentialMap.iter (fun evk x -> l := (evk,x)::!l) def;
    ExistentialMap.iter (fun evk x -> l := (evk,x)::!l) undef;
    !l

  let undefined_list (def,undef) =
    (* Order is important: needs ocaml >= 3.08.4 from which "fold" is a
       "fold_left" *)
    ExistentialMap.fold (fun evk evi l -> (evk,evi)::l) undef []

  let undefined_evars (def,undef) = (ExistentialMap.empty,undef)
  let defined_evars (def,undef) = (def,ExistentialMap.empty)

  let find (def,undef) k =
    try ExistentialMap.find k def
    with Not_found -> ExistentialMap.find k undef
  let find_undefined (def,undef) k = ExistentialMap.find k undef
  let remove (def,undef) k =
    (ExistentialMap.remove k def,ExistentialMap.remove k undef)
  let mem (def,undef) k =
    ExistentialMap.mem k def || ExistentialMap.mem k undef
  let fold (def,undef) f a =
    ExistentialMap.fold f def (ExistentialMap.fold f undef a)
  let fold_undefined (def,undef) f a =
    ExistentialMap.fold f undef a
  let exists_undefined (def,undef) f =
    ExistentialMap.fold (fun k v b -> b || f k v) undef false

  let add (def,undef) evk newinfo =
    if newinfo.evar_body = Evar_empty then
      (def,ExistentialMap.add evk newinfo undef)
    else
      (ExistentialMap.add evk newinfo def,undef)

  let add_undefined (def,undef) evk newinfo =
    assert (newinfo.evar_body = Evar_empty);
    (def,ExistentialMap.add evk newinfo undef)

  let map f (def,undef) = (ExistentialMap.map f def, ExistentialMap.map f undef)

  let define (def,undef) evk body =
    let oldinfo =
      try ExistentialMap.find evk undef
      with Not_found -> 
	try ExistentialMap.find evk def
	with Not_found -> 
	  anomaly "Evd.define: cannot define undeclared evar" in
    let newinfo =
      { oldinfo with
	  evar_body = Evar_defined body } in
      match oldinfo.evar_body with
	| Evar_empty ->
	    (ExistentialMap.add evk newinfo def,ExistentialMap.remove evk undef)
	| _ ->
	    anomaly "Evd.define: cannot define an evar twice"

  let is_evar = mem

  let is_defined (def,undef) evk = ExistentialMap.mem evk def
  let is_undefined (def,undef) evk = ExistentialMap.mem evk undef

  (*******************************************************************)
  (* Formerly Instantiate module *)

  (* Existentials. *)

  let existential_type sigma (n,args) =
    let info =
      try find sigma n
      with Not_found ->
	anomaly ("Evar "^(string_of_existential n)^" was not declared") in
    let hyps = evar_filtered_context info in
      instantiate_evar hyps info.evar_concl (Array.to_list args)

  let existential_value sigma (n,args) =
    let info = find sigma n in
    let hyps = evar_filtered_context info in
      match evar_body info with
	| Evar_defined c ->
	    instantiate_evar hyps c (Array.to_list args)
	| Evar_empty ->
	    raise NotInstantiatedEvar

  let existential_opt_value sigma ev =
    try Some (existential_value sigma ev)
    with NotInstantiatedEvar -> None

end

module EvarMap = struct
  type t = EvarInfoMap.t * (Univ.UniverseLSet.t * Univ.universes)
  let empty = EvarInfoMap.empty, (Univ.UniverseLSet.empty, Univ.initial_universes)
  let is_empty (sigma,_) = EvarInfoMap.is_empty sigma
  let has_undefined (sigma,_) = EvarInfoMap.has_undefined sigma
  let add (sigma,sm) k v = (EvarInfoMap.add sigma k v, sm)
  let add_undefined (sigma,sm) k v = (EvarInfoMap.add_undefined sigma k v, sm)
  let find (sigma,_) = EvarInfoMap.find sigma
  let find_undefined (sigma,_) = EvarInfoMap.find_undefined sigma
  let remove (sigma,sm) k = (EvarInfoMap.remove sigma k, sm)
  let mem (sigma,_) = EvarInfoMap.mem sigma
  let to_list (sigma,_) = EvarInfoMap.to_list sigma
  let undefined_list (sigma,_) = EvarInfoMap.undefined_list sigma
  let undefined_evars (sigma,sm) = (EvarInfoMap.undefined_evars sigma, sm)
  let defined_evars (sigma,sm) = (EvarInfoMap.defined_evars sigma, sm)
  let fold (sigma,_) = EvarInfoMap.fold sigma
  let fold_undefined (sigma,_) = EvarInfoMap.fold_undefined sigma
  let define (sigma,sm) k v = (EvarInfoMap.define sigma k v, sm)
  let is_evar (sigma,_) = EvarInfoMap.is_evar sigma
  let is_defined (sigma,_) = EvarInfoMap.is_defined sigma
  let is_undefined (sigma,_) = EvarInfoMap.is_undefined sigma
  let existential_value (sigma,_) = EvarInfoMap.existential_value sigma
  let existential_type (sigma,_) = EvarInfoMap.existential_type sigma
  let existential_opt_value (sigma,_) = EvarInfoMap.existential_opt_value sigma
  let progress_evar_map (sigma1,sm1 as x) (sigma2,sm2 as y) = not (x == y) &&
    (EvarInfoMap.exists_undefined sigma1
      (fun k v -> assert (v.evar_body = Evar_empty);
        EvarInfoMap.is_defined sigma2 k))

  let merge e e' = fold e' (fun n v sigma -> add sigma n v) e
  let add_constraints (sigma, (us, sm)) cstrs =
    (sigma, (us, Univ.merge_constraints cstrs sm))
end

(*******************************************************************)
(* Metamaps *)

(*******************************************************************)
(*            Constraints for existential variables                *)
(*******************************************************************)

type 'a freelisted = {
  rebus : 'a;
  freemetas : Intset.t }

(* Collects all metavars appearing in a constr *)
let metavars_of c =
  let rec collrec acc c =
    match kind_of_term c with
      | Meta mv -> Intset.add mv acc
      | _         -> fold_constr collrec acc c
  in
  collrec Intset.empty c

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
  | Cltyp of name * constr freelisted
  | Clval of name * (constr freelisted * instance_status) * constr freelisted

let map_clb f = function
  | Cltyp (na,cfl) -> Cltyp (na,map_fl f cfl)
  | Clval (na,(cfl1,pb),cfl2) -> Clval (na,(map_fl f cfl1,pb),map_fl f cfl2)

(* name of defined is erased (but it is pretty-printed) *)
let clb_name = function
    Cltyp(na,_) -> (na,false)
  | Clval (na,_,_) -> (na,true)

(***********************)

module Metaset = Intset

let meta_exists p s = Metaset.fold (fun x b -> b || (p x)) s false

module Metamap = Intmap

let metamap_to_list m =
  Metamap.fold (fun n v l -> (n,v)::l) m []

(*************************)
(* Unification state *)

type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * Environ.env * constr * constr
type evar_map =
    { evars : EvarMap.t;
      conv_pbs : evar_constraint list;
      last_mods : ExistentialSet.t;
      metas : clbinding Metamap.t }

(*** Lifting primitive from EvarMap. ***)

(* HH: The progress tactical now uses this function. *)
let progress_evar_map d1 d2 =
  EvarMap.progress_evar_map d1.evars d2.evars

(* spiwack: tentative. It might very well not be the semantics we want
     for merging evar_map *)
let merge d1 d2 = {
  evars = EvarMap.merge d1.evars d2.evars ;
  conv_pbs = List.rev_append d1.conv_pbs d2.conv_pbs ;
  last_mods = ExistentialSet.union d1.last_mods d2.last_mods ;
  metas = Metamap.fold (fun k m r -> Metamap.add k m r) d2.metas d1.metas
}
let add d e i = { d with evars=EvarMap.add d.evars e i }
let remove d e = { d with evars=EvarMap.remove d.evars e }
let find d e = EvarMap.find d.evars e
let find_undefined d e = EvarMap.find_undefined d.evars e
let mem d e = EvarMap.mem d.evars e
(* spiwack: this function loses information from the original evar_map
   it might be an idea not to export it. *)
let to_list d = EvarMap.to_list d.evars
let undefined_list d = EvarMap.undefined_list d.evars
let undefined_evars d = { d with evars=EvarMap.undefined_evars d.evars }
let defined_evars d = { d with evars=EvarMap.defined_evars d.evars }
(* spiwack: not clear what folding over an evar_map, for now we shall
    simply fold over the inner evar_map. *)
let fold f d a = EvarMap.fold d.evars f a
let fold_undefined f d a = EvarMap.fold_undefined d.evars f a
let is_evar d e = EvarMap.is_evar d.evars e
let is_defined d e = EvarMap.is_defined d.evars e
let is_undefined d e = EvarMap.is_undefined d.evars e

let existential_value d e = EvarMap.existential_value d.evars e
let existential_type d e = EvarMap.existential_type d.evars e
let existential_opt_value d e = EvarMap.existential_opt_value d.evars e

let add_constraints d e = {d with evars= EvarMap.add_constraints d.evars e}

(*** /Lifting... ***)

(* evar_map are considered empty disregarding histories *)
let is_empty d =
  EvarMap.is_empty d.evars &&
  d.conv_pbs = [] &&
  Metamap.is_empty d.metas

let subst_named_context_val s = map_named_val (subst_mps s)

let subst_evar_info s evi =
  let subst_evb = function Evar_empty -> Evar_empty
    | Evar_defined c -> Evar_defined (subst_mps s c) in
  { evi with
      evar_concl = subst_mps s evi.evar_concl;
      evar_hyps = subst_named_context_val s evi.evar_hyps;
      evar_body = subst_evb evi.evar_body }

let subst_evar_defs_light sub evd =
  assert (Univ.is_initial_universes (snd (snd evd.evars)));
  assert (evd.conv_pbs = []);
  { evd with
      metas = Metamap.map (map_clb (subst_mps sub)) evd.metas;
      evars = EvarInfoMap.map (subst_evar_info sub)  (fst evd.evars), (snd evd.evars)
  }

let subst_evar_map = subst_evar_defs_light

(* spiwack: deprecated *)
let create_evar_defs sigma = { sigma with
  conv_pbs=[]; last_mods=ExistentialSet.empty; metas=Metamap.empty }
(* spiwack: tentatively deprecated *)
let create_goal_evar_defs sigma = { sigma with
   (* conv_pbs=[]; last_mods=ExistentialSet.empty; metas=Metamap.empty } *)
  metas=Metamap.empty } 
let empty =  {
  evars=EvarMap.empty;
  conv_pbs=[];
  last_mods = ExistentialSet.empty;
  metas=Metamap.empty
}

let has_undefined evd =
  EvarMap.has_undefined evd.evars

let evars_reset_evd ?(with_conv_pbs=false) evd d = 
  {d with evars = evd.evars; 
     conv_pbs = if with_conv_pbs then evd.conv_pbs else d.conv_pbs }
let add_conv_pb pb d = {d with conv_pbs = pb::d.conv_pbs}
let evar_source evk d = (EvarMap.find d.evars evk).evar_source

(* define the existential of section path sp as the constr body *)
let define evk body evd =
  { evd with
    evars = EvarMap.define evd.evars evk body;
    last_mods =
        match evd.conv_pbs with
	| [] ->  evd.last_mods
        | _ -> ExistentialSet.add evk evd.last_mods }

let evar_declare hyps evk ty ?(src=(dummy_loc,InternalHole)) ?filter evd =
  let filter =
    if filter = None then
      List.map (fun _ -> true) (named_context_of_val hyps)
    else
      (let filter = Option.get filter in
      assert (List.length filter = List.length (named_context_of_val hyps));
      filter)
  in
  { evd with
    evars = EvarMap.add_undefined evd.evars evk
      {evar_hyps = hyps;
       evar_concl = ty;
       evar_body = Evar_empty;
       evar_filter = filter;
       evar_source = src;
       evar_extra = Store.empty } }

let is_defined_evar evd (evk,_) = EvarMap.is_defined evd.evars evk

(* Does k corresponds to an (un)defined existential ? *)
let is_undefined_evar evd c = match kind_of_term c with
  | Evar ev -> not (is_defined_evar evd ev)
  | _ -> false

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
  {evd with conv_pbs = pbs1; last_mods = ExistentialSet.empty},
  pbs

let extract_changed_conv_pbs evd p =
  extract_conv_pbs evd (p evd.last_mods)

let extract_all_conv_pbs evd =
  extract_conv_pbs evd (fun _ -> true)

(* spiwack: should it be replaced by Evd.merge? *)
let evar_merge evd evars =
  { evd with evars = EvarMap.merge evd.evars evars.evars }

let evar_list evd c =
  let rec evrec acc c =
    match kind_of_term c with
    | Evar (evk, _ as ev) when mem evd evk -> ev :: acc
    | _ -> fold_constr evrec acc c in
  evrec [] c

let collect_evars c =
  let rec collrec acc c =
    match kind_of_term c with
      | Evar (evk,_) -> ExistentialSet.add evk acc
      | _       -> fold_constr collrec acc c
  in
  collrec ExistentialSet.empty c

(**********************************************************)
(* Sort variables *)

let new_univ_variable ({ evars = (sigma,(us,sm)) } as d) =
  let u = Termops.new_univ_level () in
  let us' = Univ.UniverseLSet.add u us in
    ({d with evars = (sigma, (us', sm))}, Univ.make_universe u)
  
let new_sort_variable d =
  let (d', u) = new_univ_variable d in
    (d', Type u)

let is_sort_variable {evars=(_,(us,_))} s = match s with Type u -> true | _ -> false 
let whd_sort_variable {evars=(_,sm)} t = t

let univ_of_sort = function
  | Type u -> u
  | Prop Pos -> Univ.type0_univ
  | Prop Null -> Univ.type0m_univ

let is_eq_sort s1 s2 =
  if s1 = s2 then None
  else 
    let u1 = univ_of_sort s1 and u2 = univ_of_sort s2 in
      if u1 = u2 then None
      else Some (u1, u2)

let is_univ_var_or_set u =   
  Univ.is_univ_variable u || u = Univ.type0_univ

let set_leq_sort ({evars = (sigma, (us, sm))} as d) s1 s2 =
  match is_eq_sort s1 s2 with
  | None -> d
  | Some (u1, u2) ->
      match s1, s2 with
      | Prop c, Prop c' -> 
	  if c = Null && c' = Pos then d
	  else (raise (Univ.UniverseInconsistency (Univ.Le, u1, u2)))
     | Type u, Prop c -> 
	  if c = Pos then 
	    add_constraints d (Univ.enforce_geq Univ.type0_univ u Univ.empty_constraint)
	  else raise (Univ.UniverseInconsistency (Univ.Le, u1, u2))
      | _, Type u ->
	  if is_univ_var_or_set u then
	    add_constraints d (Univ.enforce_geq u2 u1 Univ.empty_constraint)
	  else raise (Univ.UniverseInconsistency (Univ.Le, u1, u2))

let is_univ_level_var us u =
  match Univ.universe_level u with
  | Some u -> Univ.UniverseLSet.mem u us
  | None -> false

let set_eq_sort ({evars = (sigma, (us, sm))} as d) s1 s2 =
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
	  Univ.check_eq sm u1 u2 -> d
      | Type u, Prop c when is_univ_var_or_set u && Univ.check_eq sm u1 u2 -> d
      | Type u, Type v when is_univ_var_or_set u && is_univ_var_or_set v ->
	  add_constraints d (Univ.enforce_eq u1 u2 Univ.empty_constraint)
      | _, _ -> raise (Univ.UniverseInconsistency (Univ.Eq, u1, u2))
	    
(**********************************************************)
(* Accessing metas *)

let meta_list evd = metamap_to_list evd.metas

let find_meta evd mv = Metamap.find mv evd.metas

let undefined_metas evd =
  List.sort Pervasives.compare (map_succeed (function
    | (n,Clval(_,_,typ)) -> failwith ""
    | (n,Cltyp (_,typ))  -> n)
    (meta_list evd))

let metas_of evd =
  List.map (function
    | (n,Clval(_,_,typ)) -> (n,typ.rebus)
    | (n,Cltyp (_,typ))  -> (n,typ.rebus))
    (meta_list evd)

let map_metas_fvalue f evd =
  { evd with metas =
      Metamap.map
        (function
          | Clval(id,(c,s),typ) -> Clval(id,(mk_freelisted (f c.rebus),s),typ)
          | x -> x) evd.metas }

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
  with Not_found -> anomaly "meta_fvalue: meta has no value"

let meta_value evd mv =
  (fst (try_meta_fvalue evd mv)).rebus

let meta_ftype evd mv =
  match Metamap.find mv evd.metas with
    | Cltyp (_,b) -> b
    | Clval(_,_,b) -> b

let meta_type evd mv = (meta_ftype evd mv).rebus

let meta_declare mv v ?(name=Anonymous) evd =
  { evd with metas = Metamap.add mv (Cltyp(name,mk_freelisted v)) evd.metas }

let meta_assign mv (v,pb) evd =
  match Metamap.find mv evd.metas with
  | Cltyp(na,ty) ->
      { evd with
        metas = Metamap.add mv (Clval(na,(mk_freelisted v,pb),ty)) evd.metas }
  | _ -> anomaly "meta_assign: already defined"

let meta_reassign mv (v,pb) evd =
  match Metamap.find mv evd.metas with
  | Clval(na,_,ty) ->
      { evd with
        metas = Metamap.add mv (Clval(na,(mk_freelisted v,pb),ty)) evd.metas }
  | _ -> anomaly "meta_reassign: not yet defined"

(* If the meta is defined then forget its name *)
let meta_name evd mv =
  try fst (clb_name (Metamap.find mv evd.metas)) with Not_found -> Anonymous

let meta_with_name evd id =
  let na = Name id in
  let (mvl,mvnodef) =
    Metamap.fold
      (fun n clb (l1,l2 as l) ->
        let (na',def) = clb_name clb in
        if na = na' then if def then (n::l1,l2) else (n::l1,n::l2)
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
  {evd2 with
    metas = List.fold_left (fun m (n,v) -> Metamap.add n v m)
      evd2.metas (metamap_to_list evd1.metas) }

type metabinding = metavariable * constr * instance_status

let retract_coercible_metas evd =
  let mc,ml =
    Metamap.fold (fun n v (mc,ml) ->
      match v with
	| Clval (na,(b,(Conv,CoerceToType as s)),typ) ->
	    (n,b.rebus,s)::mc, Metamap.add n (Cltyp (na,typ)) ml
	| v ->
	    mc, Metamap.add n v ml)
      evd.metas ([],Metamap.empty) in
  mc, { evd with metas = ml }

let rec list_assoc_in_triple x = function
    [] -> raise Not_found
  | (a,b,_)::l -> if compare a x = 0 then b else list_assoc_in_triple x l

let subst_defined_metas bl c =
  let rec substrec c = match kind_of_term c with
    | Meta i -> substrec (list_assoc_in_triple i bl)
    | _ -> map_constr substrec c
  in try Some (substrec c) with Not_found -> None

(*******************************************************************)
type open_constr = evar_map * constr

(*******************************************************************)
(* The type constructor ['a sigma] adds an evar map to an object of
  type ['a] *)
type 'a sigma = {
  it : 'a ;
  sigma : evar_map}

let sig_it x = x.it
let sig_sig x = x.sigma

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
  | QuestionMark _ -> str "underscore"
  | CasesType -> str "pattern-matching return predicate"
  | BinderType (Name id) -> str "type of " ++ Nameops.pr_id id
  | BinderType Anonymous -> str "type of anonymous binder"
  | ImplicitArg (c,(n,ido),b) ->
      let id = Option.get ido in
      str "parameter " ++ pr_id id ++ spc () ++ str "of" ++
      spc () ++ print_constr (constr_of_global c)
  | InternalHole -> str "internal placeholder"
  | TomatchTypeParameter (ind,n) ->
      nth n ++ str " argument of type " ++ print_constr (mkInd ind)
  | GoalEvar -> str "goal evar"
  | ImpossibleCase -> str "type of impossible pattern-matching clause"
  | MatchingVar _ -> str "matching variable"

let pr_evar_info evi =
  let phyps =
    try
      let decls = List.combine (evar_context evi) (evar_filter evi) in
      prlist_with_sep pr_spc pr_decl (List.rev decls)
    with Invalid_argument _ -> str "Ill-formed filtered context" in
  let pty = print_constr evi.evar_concl in
  let pb =
    match evi.evar_body with
      | Evar_empty -> mt ()
      | Evar_defined c -> spc() ++ str"=> "  ++ print_constr c
  in
  let src = str "(" ++ pr_evar_source (snd evi.evar_source) ++ str ")" in
  hov 2
    (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pty ++ pb ++ str"]" ++
       spc() ++ src)

let compute_evar_dependency_graph (sigma:evar_map) =
  (* Compute the map binding ev to the evars whose body depends on ev *)
  fold (fun evk evi acc ->
    let deps =
      match evar_body evi with
      | Evar_empty -> ExistentialSet.empty
      | Evar_defined c -> collect_evars c in
    ExistentialSet.fold (fun evk' acc ->
      let tab = try ExistentialMap.find evk' acc with Not_found -> [] in
      ExistentialMap.add evk' ((evk,evi)::tab) acc) deps acc)
    sigma ExistentialMap.empty

let evar_dependency_closure n sigma =
  let graph = compute_evar_dependency_graph sigma in
  let order a b = fst a < fst b in
  let rec aux n l =
    if n=0 then l
    else
      let l' =
        list_map_append (fun (evk,_) ->
          try ExistentialMap.find evk graph with Not_found -> []) l in
      aux (n-1) (list_uniquize (Sort.list order (l@l'))) in
  aux n (undefined_list sigma)

let pr_evar_map_t depth sigma =
  let (evars,(uvs,univs)) = sigma.evars in
  let pr_evar_list l =
    h 0 (prlist_with_sep pr_fnl
	   (fun (ev,evi) ->
	     h 0 (str(string_of_existential ev) ++
                    str"==" ++ pr_evar_info evi)) l) in
  let evs =
    if EvarInfoMap.is_empty evars then mt ()
    else
      match depth with
      | None ->
          (* Print all evars *)
          str"EVARS:"++brk(0,1)++pr_evar_list (to_list sigma)++fnl()
      | Some n ->
          (* Print all evars *)
          str"UNDEFINED EVARS"++
          (if n=0 then mt() else str" (+level "++int n++str" closure):")++
          brk(0,1)++
          pr_evar_list (evar_dependency_closure n sigma)++fnl()
  and svs =
    if Univ.UniverseLSet.is_empty uvs then mt ()
    else str"UNIVERSE VARIABLES:"++brk(0,1)++
      h 0 (prlist_with_sep pr_fnl 
	     (fun u -> Univ.pr_uni_level u) (Univ.UniverseLSet.elements uvs))++fnl()
  and cs =
    if Univ.is_initial_universes univs then mt ()
    else str"UNIVERSES:"++brk(0,1)++
      h 0 (Univ.pr_universes univs)++fnl()
  in evs ++ svs ++ cs

let print_env_short env =
  let pr_body n = function None -> pr_name n | Some b -> str "(" ++ pr_name n ++ str " := " ++ print_constr b ++ str ")" in
  let pr_named_decl (n, b, _) = pr_body (Name n) b in
  let pr_rel_decl (n, b, _) = pr_body n b in
  let nc = List.rev (named_context env) in
  let rc = List.rev (rel_context env) in
    str "[" ++ prlist_with_sep pr_spc pr_named_decl nc ++ str "]" ++ spc () ++
    str "[" ++ prlist_with_sep pr_spc pr_rel_decl rc ++ str "]"

let pr_constraints pbs =
  h 0
    (prlist_with_sep pr_fnl 
       (fun (pbty,env,t1,t2) ->
	  print_env_short env ++ spc () ++ str "|-" ++ spc () ++
	    print_constr t1 ++ spc() ++
	    str (match pbty with
		 | Reduction.CONV -> "=="
		 | Reduction.CUMUL -> "<=") ++
	    spc() ++ print_constr t2) pbs)

let pr_evar_map_constraints evd =
  if evd.conv_pbs = [] then mt() 
  else pr_constraints evd.conv_pbs++fnl()

let pr_evar_map allevars evd =
  let pp_evm =
    if EvarMap.is_empty evd.evars then mt() else
      pr_evar_map_t allevars evd++fnl() in
  let cstrs = if evd.conv_pbs = [] then mt() else
    str"CONSTRAINTS:"++brk(0,1)++pr_constraints evd.conv_pbs++fnl() in
  let pp_met =
    if Metamap.is_empty evd.metas then mt() else
      str"METAS:"++brk(0,1)++pr_meta_map evd.metas in
  v 0 (pp_evm ++ cstrs ++ pp_met)

let pr_metaset metas =
  str "[" ++ prlist_with_sep spc pr_meta (Metaset.elements metas) ++ str "]"
