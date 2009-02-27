(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

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
  evar_extra : Dyn.t option}

let make_evar hyps ccl = {
  evar_concl = ccl;
  evar_hyps = hyps;
  evar_body = Evar_empty;
  evar_filter = List.map (fun _ -> true) (named_context_of_val hyps);
  evar_extra = None
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
      - EvarInfoMap ( .t ~ evar_info ExistentialMap.t )
      - EvarMap ( .t = EvarInfoMap.t * sort_constraints )
      - evar_defs (= unification states, exported)
*)

module ExistentialMap = Intmap
module ExistentialSet = Intset

(* This exception is raised by *.existential_value *)	
exception NotInstantiatedEvar

module EvarInfoMap = struct
   (**************************************************************
    * EvarInfoMap represents maps from [evar] to [evar_info] (that is
    * a structure which associates to existential variables their type
    * and possibly their definition (aka body)) plus certain cached
    * information (values of [whd_evar] and [nf_evar] on those 
    * existential variables before substituting anything for their 
    * hypotheses).
    * Caches are represented as mutable cells (in the type 
    * [cached_info] which encapsulates [evar_info]) to keep caching 
    * transparent to the interface. The down side of using mutable 
    * cells in a persistant data-structure is that mutations influence
    * past versions of the structure. To ensure that the structure stays
    * pure we have to  track a "version number" together with the 
    * cache. If the cache is more recent than the structure then it is
    * considered inconsistent and discarded.
    * The price is that we cannot say much about the effect of 
    * caching in the worst case. Also caching makes [nf_evar]
    * and [whd_evar] non-tail recursive (because substitution of
    * the hypotheses is delayed). Which may make them inefficient
    * in some cases.
    *************************************************************)


  (* Invariant: whd and nf are [None] while evar_info.evar_body is [Evar_Empty] *)
  type cached_info = { 
      evar_info : evar_info ;
      (* stores the last computed whd of the existential variale. *)
      mutable whd : (int*constr) option;
      (* stores the last computed nf (=fully instantiated value) of the existential var.*)
      mutable nf : (int*constr) option
  } 
  let empty_cache ei = { evar_info=ei;whd=None;nf=None }

  (* mapping * version number *)
  type t = cached_info ExistentialMap.t*int

  let empty = (ExistentialMap.empty,0)

  let to_list (evc,_) = (* Workaround for change in Map.fold behavior *)
    let l = ref [] in 
    ExistentialMap.iter (fun evk x -> l := (evk,x.evar_info)::!l) evc;
    !l

  let dom (evc,_) = ExistentialMap.fold (fun evk _ acc -> evk::acc) evc []
  let find (evc,_) k = (ExistentialMap.find k evc).evar_info
  let mem (evc,_) k = ExistentialMap.mem k evc

  let add (evd,v) evk newinfo =  
    (ExistentialMap.add evk (empty_cache newinfo) evd,v+1)

  (* spiwack: this should be considered deprecated *)
  let unsafe_remove (evc,v) k = (ExistentialMap.remove k evc,v+1)

  let map f (evc,v)= 
    (ExistentialMap.map (fun ci -> empty_cache (f ci.evar_info)) evc,0)
  let fold f (evc,_)= ExistentialMap.fold (fun evk ci acc -> f evk ci.evar_info acc) evc

  let equal f (evc1,_) (evc2,_) = 
    ExistentialMap.equal (fun ci1 ci2 -> f ci1.evar_info ci2.evar_info) evc1 evc2

  let define evd evk body = 
    let oldinfo =
      try find evd evk
      with Not_found -> error "Evd.define: cannot define undeclared evar" in
    let newinfo =
      { oldinfo with
	  evar_body = Evar_defined body } in
      match oldinfo.evar_body with
	| Evar_empty -> add evd evk newinfo
	| _ -> anomaly "Evd.define: cannot define an evar twice"

  let is_evar sigma evk = mem sigma evk

  let is_defined sigma evk =
    let info = find sigma evk in 
      not (info.evar_body = Evar_empty)


  (*******************************************************************)
  (* Formerly Instantiate module *)

  let is_id_inst inst =
    let is_id (id,c) = match kind_of_term c with
      | Var id' -> id = id'
      | _ -> false
    in
      List.for_all is_id inst

  (* Vérifier que les instances des let-in sont compatibles ?? *)
  let instantiate_sign_including_let sign args =
    let rec instrec = function
      | ((id,b,_) :: sign, c::args) -> (id,c) :: (instrec (sign,args))
      | ([],[])                        -> []
      | ([],_) | (_,[]) ->
	  anomaly "Signature and its instance do not match"
    in 
      instrec (sign,args)

  let instantiate_evar sign c args =
    let inst = instantiate_sign_including_let sign args in
      if is_id_inst inst then
	c
      else
	replace_vars inst c

  (* Existentials. *)

  let existential_type sigma (n,args) =
    let info =
      try find sigma n
      with Not_found ->
	anomaly ("Evar "^(string_of_existential n)^" was not declared") in
    let hyps = evar_filtered_context info in
      instantiate_evar hyps info.evar_concl (Array.to_list args)

  let get_evar_body evi =
    match evar_body evi with
      | Evar_defined c -> c 
      | Evar_empty -> raise NotInstantiatedEvar
    
  let existential_value sigma (n,args) =
    let info = find sigma n in
    let hyps = evar_filtered_context info in
    let c = get_evar_body info in
    instantiate_evar hyps c (Array.to_list args)

  let existential_opt_value sigma ev =
    try Some (existential_value sigma ev)
    with NotInstantiatedEvar -> None

  (*** Computing instantiated forms of existential variables. ***)

  let get_whd_cache ci = ci.whd
  let set_whd_cache ci v c = ci.whd <- Some (v,c)
  let get_nf_cache ci = ci.nf
  let set_nf_cache ci v c = ci.nf <- Some (v,c)

  (* [inst_gen] is the prototype for [whd_evar] and [nf_evar]. It takes
      as additional parameters a pair of arguments [set]/[get] which 
      are meant to respectively cache a ([constr]) value (together with
      a version number) and return the value previously cached by [set].
      It also takes an argument [r] which specifies what to do on non-[Evar]
      terms. That is "just return it" for [whd_evar], and "operate recursively
      on subterms" for [nf_evar]. *)
  let rec inst_gen set get r sigma c =
    match kind_of_term c with
      | Evar (e,args) -> 
	  begin try 
	    let (c',hyps) = inst_gen_of_evar set get r sigma e in
	    instantiate_evar hyps c' (Array.to_list args)
	  with Not_found | NotInstantiatedEvar -> c end
      | _ -> r c
  and inst_gen_of_evar set get r ((sigma,v) as evc) e =
    let oci =  ExistentialMap.find e sigma in
    let info = oci.evar_info in
    let hyps = evar_filtered_context info in
    match get oci with
      | None ->
	  (* The cache is empty. 
	      We call [inst_gen] recursively to construct the cache. *)
	  let c = get_evar_body info in
	  let c' = inst_gen set get r evc c in
	  set oci v c';
	  (c', hyps)
      | Some (v',_) when v' > v ->
	  (* This is a copy of previous case. It'd be better to factorise it somehow,
	      but "when" clauses cannot operate on operands of or-patterns. *)
	  (* The cache is inconsistent (comes from a future version
	      of the map). 
	      We call [inst_gen] recursively to construct the cache. *)
	  let c = get_evar_body info in
	  let c' = inst_gen set get r evc c in
	  set oci v c';
	  (c', hyps)
      | Some (v',c) when v' < v -> 
	  (* The cache is consistent but not necessarily complete. 
	      It comes from a past version of the map.
	      We call [inst_gen] recursively on the cached value, 
	      and update the cache. *)
	  let c' = inst_gen set get r evc c in
	  set oci v c';
	  (c', hyps)
      | Some (_,c') (*when v'=v *) ->
	  (* The cache is fully consistent, as it has been made on
	      this version of the map. We can simply return it. *)
	  (c', hyps)

  let  whd_evar = inst_gen set_whd_cache get_whd_cache Util.identity
  let rec nf_evar sigma c = 
    inst_gen set_nf_cache get_nf_cache (map_constr  (nf_evar sigma)) sigma c

end

(*******************************************************************)
(*                Constraints for sort variables                   *)
(*******************************************************************)

type sort_var = Univ.universe

type sort_constraint =
  | DefinedSort of sorts (* instantiated sort var *)
  | SortVar of sort_var list * sort_var list (* (leq,geq) *)
  | EqSort of sort_var

module UniverseOrdered = struct
  type t = Univ.universe
  let compare = Pervasives.compare
end
module UniverseMap = Map.Make(UniverseOrdered)

type sort_constraints = sort_constraint UniverseMap.t

let rec canonical_find u scstr =
  match UniverseMap.find u scstr with
      EqSort u' -> canonical_find u' scstr
    | c -> (u,c)

let whd_sort_var scstr t =
  match kind_of_term t with
      Sort(Type u) ->
        (try
          match canonical_find u scstr with
              _, DefinedSort s -> mkSort s
            | _ -> t
        with Not_found -> t)
    | _ -> t

let rec set_impredicative u s scstr =
  match UniverseMap.find u scstr with
    | DefinedSort s' ->
        if family_of_sort s = family_of_sort s' then scstr
        else failwith "sort constraint inconsistency"
    | EqSort u' ->
        UniverseMap.add u (DefinedSort s) (set_impredicative u' s scstr)
    | SortVar(_,ul) ->
        (* also set sorts lower than u as impredicative *)
        UniverseMap.add u (DefinedSort s)
          (List.fold_left (fun g u' -> set_impredicative u' s g) scstr ul)

let rec set_predicative u s scstr =
  match UniverseMap.find u scstr with
    | DefinedSort s' ->
        if family_of_sort s = family_of_sort s' then scstr
        else failwith "sort constraint inconsistency"
    | EqSort u' ->
        UniverseMap.add u (DefinedSort s) (set_predicative u' s scstr)
    | SortVar(ul,_) ->
        UniverseMap.add u (DefinedSort s)
          (List.fold_left (fun g u' -> set_impredicative u' s g) scstr ul)

let var_of_sort = function
    Type u -> u
  | _ -> assert false

let is_sort_var s scstr =
  match s with
      Type u ->
        (try
          match canonical_find u scstr with
              _, DefinedSort _ -> false
            | _ -> true
        with Not_found -> false)
    | _ -> false

let rec nf_sort_var scstr t =
  match kind_of_term t with
    | Sort s when is_sort_var s scstr -> whd_sort_var scstr t
    | _ -> map_constr (nf_sort_var scstr) t

let new_sort_var cstr =
  let u = Termops.new_univ() in
  (u, UniverseMap.add u (SortVar([],[])) cstr)


let set_leq_sort (u1,(leq1,geq1)) (u2,(leq2,geq2)) scstr =
  let rec search_rec (is_b, betw, not_betw) u1 =
    if List.mem u1 betw then (true, betw, not_betw)
    else if List.mem u1 not_betw then (is_b, betw, not_betw)
    else if u1 = u2 then (true, u1::betw,not_betw) else
      match UniverseMap.find u1 scstr with
          EqSort u1' -> search_rec (is_b,betw,not_betw) u1'
        | SortVar(leq,_) ->
            let (is_b',betw',not_betw') = 
              List.fold_left search_rec (false,betw,not_betw) leq in
            if is_b' then (true, u1::betw', not_betw')
            else (false, betw', not_betw')
        | DefinedSort _ -> (false,betw,u1::not_betw) in
  let (is_betw,betw,_) = search_rec (false, [], []) u1 in
  if is_betw then
    UniverseMap.add u1 (SortVar(leq1@leq2,geq1@geq2))
      (List.fold_left
        (fun g u -> UniverseMap.add u (EqSort u1) g) scstr betw)
  else
    UniverseMap.add u1 (SortVar(u2::leq1,geq1))
      (UniverseMap.add u2 (SortVar(leq2, u1::geq2)) scstr)

let set_leq s1 s2 scstr =
  let u1 = var_of_sort s1 in
  let u2 = var_of_sort s2 in
  let (cu1,c1) = canonical_find u1 scstr in
  let (cu2,c2) = canonical_find u2 scstr in
  if cu1=cu2 then scstr
  else
    match c1,c2 with
        (EqSort _, _ | _, EqSort _) -> assert false
      | SortVar(leq1,geq1), SortVar(leq2,geq2) ->
          set_leq_sort (cu1,(leq1,geq1)) (cu2,(leq2,geq2)) scstr
      | _, DefinedSort(Prop _ as s) -> set_impredicative u1 s scstr
      | _, DefinedSort(Type _) -> scstr
      | DefinedSort(Type _ as s), _ -> set_predicative u2 s scstr
      | DefinedSort(Prop _), _ -> scstr

let set_sort_variable s1 s2 scstr =
  let u = var_of_sort s1 in
  match s2 with
      Prop _ -> set_impredicative u s2 scstr
    | Type _ -> set_predicative u s2 scstr

let pr_sort_cstrs g =
  let l = UniverseMap.fold (fun u c l -> (u,c)::l) g [] in
  str "SORT CONSTRAINTS:" ++ fnl() ++
  prlist_with_sep fnl (fun (u,c) ->
    match c with
        EqSort u' -> Univ.pr_uni u ++ str" == " ++ Univ.pr_uni u'
      | DefinedSort s -> Univ.pr_uni u ++ str " := " ++ print_sort s
      | SortVar(leq,geq) ->
          str"[" ++ hov 0 (prlist_with_sep spc Univ.pr_uni geq) ++
          str"] <= "++ Univ.pr_uni u ++ brk(0,0) ++ str"<= [" ++
          hov 0 (prlist_with_sep spc Univ.pr_uni leq) ++ str"]")
    l

module EvarMap = struct
  type t = EvarInfoMap.t * sort_constraints
  let empty = EvarInfoMap.empty, UniverseMap.empty
  let add (sigma,sm) k v = (EvarInfoMap.add sigma k v, sm)
  let dom (sigma,_) = EvarInfoMap.dom sigma
  let find (sigma,_) = EvarInfoMap.find sigma
  (* spiwack: unsafe_remove should be considered deprecated *)
  let unsafe_remove (sigma,sm) k = (EvarInfoMap.unsafe_remove sigma k, sm)
  let mem (sigma,_) = EvarInfoMap.mem sigma
  let to_list (sigma,_) = EvarInfoMap.to_list sigma
  let fold f (sigma,_) = EvarInfoMap.fold f sigma
  let define (sigma,sm) k v = (EvarInfoMap.define sigma k v, sm)
  let is_evar (sigma,_) = EvarInfoMap.is_evar sigma
  let is_defined (sigma,_) = EvarInfoMap.is_defined sigma
  let existential_value (sigma,_) = EvarInfoMap.existential_value sigma
  let existential_type (sigma,_) = EvarInfoMap.existential_type sigma
  let existential_opt_value (sigma,_) = EvarInfoMap.existential_opt_value sigma
  let eq_evar_map x y = x == y ||
    (EvarInfoMap.equal eq_evar_info (fst x) (fst y) &&
      UniverseMap.equal (=) (snd x) (snd y))

  let merge e e' = fold (fun n v sigma -> add sigma n v) e' e
  
  let whd_evar (sigma,sm) c =
    let c = EvarInfoMap.whd_evar sigma c in
    match kind_of_term c with
      | Sort s when is_sort_var s sm -> whd_sort_var sm c
      | _ -> c


  let nf_evar (sigma,sm) c =
    let c = EvarInfoMap.nf_evar sigma c in
    nf_sort_var sm c

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

type instance_constraint =
    IsSuperType | IsSubType | ConvUpToEta of int | UserGiven

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

type obligation_definition_status = Define of bool | Expand

type hole_kind =
  | ImplicitArg of global_reference * (int * identifier option)
  | BinderType of name
  | QuestionMark of obligation_definition_status
  | CasesType
  | InternalHole
  | TomatchTypeParameter of inductive * int
  | GoalEvar
  | ImpossibleCase

type conv_pb = Reduction.conv_pb
type evar_constraint = conv_pb * Environ.env * constr * constr
type evar_defs =
    { evars : EvarMap.t;
      conv_pbs : evar_constraint list;
      last_mods : ExistentialSet.t;
      history : (existential_key * (loc * hole_kind)) list;
      metas : clbinding Metamap.t }

(*** Lifting primitive from EvarMap. ***)
type evar_map = evar_defs
(* spiwack: this function seems to be used only for the definition of the progress
    tactical. I would recommand not using it in other places. *)
let eq_evar_map d1 d2 =
  EvarMap.eq_evar_map d1.evars d2.evars 

(* spiwack: tentative. It might very well not be the semantics we want
     for merging evar_defs *)
let merge d1 d2 = {
(* d1 with evars = EvarMap.merge d1.evars d2.evars*)
  evars = EvarMap.merge d1.evars d2.evars ;
  conv_pbs = List.rev_append d1.conv_pbs d2.conv_pbs ;
  last_mods = ExistentialSet.union d1.last_mods d2.last_mods ;
  history = List.rev_append d1.history d2.history ;
  metas = Metamap.fold (fun k m r -> Metamap.add k m r) d2.metas d1.metas
}
let add d e i = { d with evars=EvarMap.add d.evars e i }
(* spiwack: unsafe_remove should be considered deprecated *)
let unsafe_remove d e = { d with evars=EvarMap.unsafe_remove d.evars e }
let dom d = EvarMap.dom d.evars
let find d e = EvarMap.find d.evars e
let mem d e = EvarMap.mem d.evars e
(* spiwack: this function loses information from the original evar_defs
   it might be an idea not to export it. *)
let to_list d = EvarMap.to_list d.evars
(* spiwack: not clear what folding over an evar_defs, for now we shall 
    simply fold over the inner evar_map. *)
let fold f d a = EvarMap.fold f d.evars a
let is_evar d e = EvarMap.is_evar d.evars e
let is_defined d e = EvarMap.is_defined d.evars e

let existential_value d e = EvarMap.existential_value d.evars e
let existential_type d e = EvarMap.existential_type d.evars e
let existential_opt_value d e = EvarMap.existential_opt_value d.evars e

(*** /Lifting... ***)

(* evar_defs are considered empty disregarding histories *)
let is_empty d = 
  d.evars = EvarMap.empty &&
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
  assert (UniverseMap.is_empty (snd evd.evars));
  assert (evd.conv_pbs = []);
  { evd with
      metas = Metamap.map (map_clb (subst_mps sub)) evd.metas;
      evars = EvarInfoMap.map (subst_evar_info sub)  (fst evd.evars), snd evd.evars
  }

let subst_evar_map = subst_evar_defs_light

(* spiwack: deprecated *)
let create_evar_defs sigma = { sigma with
  conv_pbs=[]; last_mods=ExistentialSet.empty; history=[]; metas=Metamap.empty }
(* spiwack: tentatively deprecated *)
let create_goal_evar_defs sigma = { sigma with
   conv_pbs=[]; last_mods=ExistentialSet.empty; metas=Metamap.empty }
let empty =  { 
  evars=EvarMap.empty; 
  conv_pbs=[]; 
  last_mods = ExistentialSet.empty; 
  history=[]; 
  metas=Metamap.empty 
}

let evars_reset_evd evd d = {d with evars = evd.evars}
let add_conv_pb pb d = {d with conv_pbs = pb::d.conv_pbs}
let evar_source evk d =
  try List.assoc evk d.history
  with Not_found -> (dummy_loc, InternalHole)

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
    evars = EvarMap.add evd.evars evk
      {evar_hyps = hyps;
       evar_concl = ty;
       evar_body = Evar_empty;
       evar_filter = filter;
       evar_extra = None};
    history = (evk,src)::evd.history }

let is_defined_evar evd (evk,_) = EvarMap.is_defined evd.evars evk

(* Does k corresponds to an (un)defined existential ? *)
let is_undefined_evar evd c = match kind_of_term c with
  | Evar ev -> not (is_defined_evar evd ev)
  | _ -> false

let undefined_evars evd = 
  let evars = 
    EvarMap.fold (fun evk evi sigma -> if evi.evar_body = Evar_empty then 
	    EvarMap.add sigma evk evi else sigma) 
      evd.evars EvarMap.empty
  in 
    { evd with evars = evars }

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



(**********************************************************)
(* Sort variables *)

let new_sort_variable ({ evars = (sigma,sm) } as d)=
  let (u,scstr) = new_sort_var sm in
  (Type u,{ d with evars = (sigma,scstr) } )
let is_sort_variable {evars=(_,sm)} s =
  is_sort_var s sm
let whd_sort_variable {evars=(_,sm)} t = whd_sort_var sm t
let set_leq_sort_variable ({evars=(sigma,sm)}as d) u1 u2 =
  { d with evars = (sigma, set_leq u1 u2 sm) }
let define_sort_variable ({evars=(sigma,sm)}as d) u s =
  { d with evars = (sigma, set_sort_variable u s sm) }
let pr_sort_constraints {evars=(_,sm)} = pr_sort_cstrs sm

(**********************************************************)
(* Substitution of existential variables  *)

let whd_evar { evars=em } t = EvarMap.whd_evar em t
let nf_evar { evars=em } t = EvarMap.nf_evar em t

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

let meta_fvalue evd mv =
  match Metamap.find mv evd.metas with
    | Clval(_,b,_) -> b
    | Cltyp _ -> anomaly "meta_fvalue: meta has no value"
           
let meta_ftype evd mv =
  match Metamap.find mv evd.metas with
    | Cltyp (_,b) -> b
    | Clval(_,_,b) -> b
 
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
  try
    let (na,def) = clb_name (Metamap.find mv evd.metas) in
    if def then Anonymous else na
  with Not_found -> Anonymous

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


(* spiwack: we should try and replace this List.fold_left by a Metamap.fold.  *)
let meta_merge evd1 evd2 =
  {evd2 with
    metas = List.fold_left (fun m (n,v) -> Metamap.add n v m) 
      evd2.metas (metamap_to_list evd1.metas) }

type metabinding = metavariable * constr * instance_status

let retract_coercible_metas evd =
  let mc,ml = 
    Metamap.fold (fun n v (mc,ml) -> 
      match v with
	| Clval (na,(b,(UserGiven,CoerceToType as s)),typ) ->
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
  | ConvUpToEta 0 -> mt ()
  | UserGiven -> mt ()
  | ConvUpToEta n -> str" [or an eta-expansion up to " ++ int n ++ str" of it]"
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
    | (mv,Clval(na,(b,s),_)) ->
      	hov 0 
	  (pr_meta mv ++ pr_name na ++ str " := " ++
           print_constr b.rebus ++ spc () ++ pr_instance_status s ++ fnl ())
  in
  prlist pr_meta_binding (metamap_to_list mmap)

let pr_decl ((id,b,_),ok) =
  match b with
  | None -> if ok then pr_id id else (str "{" ++ pr_id id ++ str "}")
  | Some c -> str (if ok then "(" else "{") ++ pr_id id ++ str ":=" ++ 
      print_constr c ++ str (if ok then ")" else "}")

let pr_evar_info evi =
  let decls = List.combine (evar_context evi) (evar_filter evi) in
  let phyps = prlist_with_sep pr_spc pr_decl (List.rev decls) in
  let pty = print_constr evi.evar_concl in
  let pb =
    match evi.evar_body with
      | Evar_empty -> mt ()
      | Evar_defined c -> spc() ++ str"=> "  ++ print_constr c
  in
  hov 2 (str"["  ++ phyps ++ spc () ++ str"|- "  ++ pty ++ pb ++ str"]")

let pr_evar_defs_t sigma =
  h 0 
    (prlist_with_sep pr_fnl
      (fun (ev,evi) ->
        h 0 (str(string_of_existential ev)++str"=="++ pr_evar_info evi))
      (EvarMap.to_list sigma))

let pr_constraints pbs =
  h 0
    (prlist_with_sep pr_fnl (fun (pbty,_,t1,t2) ->
      print_constr t1 ++ spc() ++
      str (match pbty with
	| Reduction.CONV -> "=="
	| Reduction.CUMUL -> "<=") ++ 
      spc() ++ print_constr t2) pbs)

let pr_evar_defs evd =
  let pp_evm =
    if evd.evars = EvarMap.empty then mt() else
      str"EVARS:"++brk(0,1)++pr_evar_defs_t evd.evars++fnl() in
  let cstrs =
    if evd.conv_pbs = [] then mt() else
    str"CONSTRAINTS:"++brk(0,1)++pr_constraints evd.conv_pbs++fnl() in
  let pp_met =
    if evd.metas = Metamap.empty then mt() else
      str"METAS:"++brk(0,1)++pr_meta_map evd.metas in
  v 0 (pp_evm ++ cstrs ++ pp_met)

let pr_metaset metas = 
  str "[" ++ prlist_with_sep spc pr_meta (Metaset.elements metas) ++ str "]"
