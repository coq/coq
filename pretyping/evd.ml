(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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


module EvarInfoMap = struct
  type t = evar_info ExistentialMap.t * evar_info ExistentialMap.t

  let empty = ExistentialMap.empty, ExistentialMap.empty
  let is_empty (def,undef) =
    (ExistentialMap.is_empty def, ExistentialMap.is_empty undef)

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
      with Not_found -> anomaly "Evd.define: cannot define undeclared evar" in
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

(*******************************************************************)
(*                Constraints for sort variables                   *)
(*******************************************************************)

type sort_var = Univ.universe

type sort_constraint =
  | DefinedSort of sorts (* instantiated sort var *)
  | SortVar of sort_var list * sort_var list (* (leq,geq) *)
  | EqSort of sort_var

module UniverseMap =
  Map.Make (struct type t = Univ.universe let compare = compare end)

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
  let add_undefined (sigma,sm) k v = (EvarInfoMap.add_undefined sigma k v, sm)
  let find (sigma,_) = EvarInfoMap.find sigma
  let find_undefined (sigma,_) = EvarInfoMap.find_undefined sigma
  let remove (sigma,sm) k = (EvarInfoMap.remove sigma k, sm)
  let mem (sigma,_) = EvarInfoMap.mem sigma
  let to_list (sigma,_) = EvarInfoMap.to_list sigma
  let undefined_list (sigma,_) = EvarInfoMap.undefined_list sigma
  let undefined_evars (sigma,sm) = (EvarInfoMap.undefined_evars sigma, sm)
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
        EvarInfoMap.is_defined sigma2 k)
    || not (UniverseMap.equal (=) sm1 sm2))

  let merge e e' = fold e' (fun n v sigma -> add sigma n v) e

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

(*** /Lifting... ***)

(* evar_map are considered empty disregarding histories *)
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

let evars_reset_evd evd d = {d with evars = evd.evars}
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

let pr_evar_map_t (evars,cstrs as sigma) =
  let evs =
    if evars = EvarInfoMap.empty then mt ()
    else
      str"EVARS:"++brk(0,1)++
	h 0 (prlist_with_sep pr_fnl
		(fun (ev,evi) ->
		  h 0 (str(string_of_existential ev)++str"=="++ pr_evar_info evi))
		(EvarMap.to_list sigma))++fnl()
  and cs =
    if cstrs = UniverseMap.empty then mt ()
    else pr_sort_cstrs cstrs++fnl()
  in evs ++ cs

let pr_constraints pbs =
  h 0
    (prlist_with_sep pr_fnl (fun (pbty,_,t1,t2) ->
      print_constr t1 ++ spc() ++
      str (match pbty with
	| Reduction.CONV -> "=="
	| Reduction.CUMUL -> "<=") ++
      spc() ++ print_constr t2) pbs)

let pr_evar_map evd =
  let pp_evm =
    if evd.evars = EvarMap.empty then mt() else
      pr_evar_map_t evd.evars++fnl() in
  let cstrs =
    if evd.conv_pbs = [] then mt() else
    str"CONSTRAINTS:"++brk(0,1)++pr_constraints evd.conv_pbs++fnl() in
  let pp_met =
    if evd.metas = Metamap.empty then mt() else
      str"METAS:"++brk(0,1)++pr_meta_map evd.metas in
  v 0 (pp_evm ++ cstrs ++ pp_met)

let pr_metaset metas =
  str "[" ++ prlist_with_sep spc pr_meta (Metaset.elements metas) ++ str "]"
