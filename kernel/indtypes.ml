
(* $Id$ *)

open Util
open Names
open Term
open Declarations
open Inductive
open Sign
open Environ
open Instantiate
open Reduction
open Typeops

(* In the following, each time an [evar_map] is required, then [Evd.empty]
   is given, since inductive types are typed in an environment without 
   existentials. *)

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

(***********************************************************************)
(* Various well-formedness check for inductive declarations            *)

type inductive_error =
  (* These are errors related to inductive constructions in this module *)
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier * identifier
  | NotAnArity of identifier
  | BadEntry
  (* These are errors related to recursors building in Indrec *)
  | NotAllowedCaseAnalysis of bool * sorts * inductive
  | BadInduction of bool * identifier * sorts
  | NotMutualInScheme

exception InductiveError of inductive_error

let check_constructors_names id =
  let rec check idset = function
    | [] -> idset
    | c::cl -> 
	if Idset.mem c idset then 
	  raise (InductiveError (SameNamesConstructors (id,c)))
	else
	  check (Idset.add c idset) cl
  in
  check

(* [mind_check_names mie] checks the names of an inductive types declaration,
   and raises the corresponding exceptions when two types or two constructors
   have the same name. *)

let mind_check_names mie =
  let rec check indset cstset = function
    | [] -> ()
    | ind::inds -> 
	let id = ind.mind_entry_typename in
	let cl = ind.mind_entry_consnames in
	if Idset.mem id indset then
	  raise (InductiveError (SameNamesTypes id))
	else
	  let cstset' = check_constructors_names id cstset cl in
	  check (Idset.add id indset) cstset' inds
  in
  check Idset.empty Idset.empty mie.mind_entry_inds

(* [mind_extract_params mie] extracts the params from an inductive types
   declaration, and checks that they are all present (and all the same)
   for all the given types. *)

let mind_extract_params n c =
  let (l,c') = decompose_prod_n_assum n c in (l,c')

let mind_check_arities env mie =
  let check_arity id c =
    if not (is_arity env Evd.empty c) then 
      raise (InductiveError (NotAnArity id))
  in
  List.iter
    (fun {mind_entry_typename=id; mind_entry_arity=ar} -> check_arity id ar)
    mie.mind_entry_inds

let mind_check_wellformed env mie =
  if mie.mind_entry_inds = [] then anomaly "empty inductive types declaration";
  mind_check_names mie;
  mind_check_arities env mie

(***********************************************************************)

let allowed_sorts issmall isunit = function
  | Type _ -> 
      [prop;spec;types]
  | Prop Pos -> 
      if issmall then [prop;spec;types] else [prop;spec]
  | Prop Null -> 
      if isunit then [prop;spec] else [prop]

type ill_formed_ind =
  | LocalNonPos of int
  | LocalNotEnoughArgs of int
  | LocalNotConstructor
  | LocalNonPar of int * int

exception IllFormedInd of ill_formed_ind

let explain_ind_err ntyp env0 nbpar c err = 
  let (lpar,c') = mind_extract_params nbpar c in
  let env = push_rels lpar env0 in
  match err with
    | LocalNonPos kt -> 
	raise (InductiveError (NonPos (env,c',mkRel (kt+nbpar))))
    | LocalNotEnoughArgs kt -> 
	raise (InductiveError 
		 (NotEnoughArgs (env,c',mkRel (kt+nbpar))))
    | LocalNotConstructor ->
	raise (InductiveError 
		 (NotConstructor (env,c',mkRel (ntyp+nbpar))))
    | LocalNonPar (n,l) ->
	raise (InductiveError 
		 (NonPar (env,c',n,mkRel (nbpar-n+1), mkRel (l+nbpar))))

let failwith_non_pos_vect n ntypes v =
  for i = 0 to Array.length v - 1 do
    for k = n to n + ntypes - 1 do
      if not (noccurn k v.(i)) then raise (IllFormedInd (LocalNonPos (k-n+1)))
    done
  done;
  anomaly "failwith_non_pos_vect: some k in [n;n+ntypes-1] should occur in v"

let check_correct_par env nparams ntypes n l largs =
  let largs = Array.of_list largs in
  if Array.length largs < nparams then 
    raise (IllFormedInd (LocalNotEnoughArgs l));
  let (lpar,largs') = array_chop nparams largs in
  for k = 0 to nparams - 1 do
    match kind_of_term (whd_betadeltaiotaeta env Evd.empty lpar.(k)) with
      | IsRel w when (n-k-1 = w) -> ()
      | _ -> raise (IllFormedInd (LocalNonPar (k+1,l)))
  done;
  if not (array_for_all (noccur_between n ntypes) largs') then 
    failwith_non_pos_vect n ntypes largs'

(* This removes global parameters of the inductive types in lc *)
let abstract_mind_lc env ntyps npars lc = 
  if npars = 0 then 
    lc
  else 
    let make_abs = 
      list_tabulate
	(function i -> lambda_implicit_lift npars (mkRel (i+1))) ntyps 
    in 
    Array.map (compose (nf_beta env Evd.empty) (substl make_abs)) lc

let listrec_mconstr env ntypes nparams i indlc =
  (* check the inductive types occur positively in [c] *)
  let rec check_pos env n c = 
    let x,largs = whd_betadeltaiota_stack env Evd.empty c in
    match kind_of_term x with
      | IsProd (na,b,d) ->
	  assert (largs = []);
          if not (noccur_between n ntypes b) then
	    raise (IllFormedInd (LocalNonPos n));
	  check_pos (push_rel_assum (na, b) env) (n+1) d
      | IsRel k ->
          if k >= n && k<n+ntypes then begin
	    check_correct_par env nparams ntypes n (k-n+1) largs;
	    Mrec(n+ntypes-k-1)
          end else if List.for_all (noccur_between n ntypes) largs then 
	    if (n-nparams) <= k & k <= (n-1) 
	    then Param(n-1-k)
            else Norec
	  else
	    raise (IllFormedInd (LocalNonPos n))
      | IsMutInd (ind_sp,a) -> 
          if array_for_all (noccur_between n ntypes) a
            && List.for_all (noccur_between n ntypes) largs 
	  then Norec
          else Imbr(ind_sp,imbr_positive env n (ind_sp,a) largs)
      | err -> 
	  if noccur_between n ntypes x && List.for_all (noccur_between n ntypes) largs 
	  then Norec
	  else raise (IllFormedInd (LocalNonPos n))

  and imbr_positive env n mi largs =
    let mispeci = lookup_mind_specif mi env in
    let auxnpar = mis_nparams mispeci in
    let (lpar,auxlargs) = list_chop auxnpar largs in 
    if not (List.for_all (noccur_between n ntypes) auxlargs) then
      raise (IllFormedInd (LocalNonPos n));
    let auxlc = mis_nf_lc mispeci 
    and auxntyp = mis_ntypes mispeci in 
    if auxntyp <> 1 then raise (IllFormedInd (LocalNonPos n));
    let lrecargs = List.map (check_weak_pos env n) lpar in
    (* The abstract imbricated inductive type with parameters substituted *)
    let auxlcvect = abstract_mind_lc env auxntyp auxnpar auxlc in
    let newidx = n + auxntyp in
(* Extends the environment with a variable corresponding to the inductive def *)
    let env' = push_rel_assum (Anonymous,mis_user_arity mispeci) env in
    let _ = 
      (* fails if the inductive type occurs non positively *)
      (* when substituted *) 
      Array.map 
	(function c -> 
	   let c' = hnf_prod_applist env Evd.empty c 
		      (List.map (lift auxntyp) lpar) in 
	   check_construct env' false newidx c') 
	auxlcvect
    in 
    lrecargs

  (* The function check_weak_pos is exactly the same as check_pos, but
     with an extra case for traversing abstractions, like in Marseille's
     contribution about bisimulations:
     
     CoInductive strong_eq:process->process->Prop:=
       str_eq:(p,q:process)((a:action)(p':process)(transition p a p')->
          (Ex [q':process] (transition q a q')/\(strong_eq p' q')))->
             ((a:action)(q':process)(transition q a q')->
          (Ex [p':process] (transition p a p')/\(strong_eq p' q')))->
          (strong_eq p q).

     Abstractions may occur in imbricated recursive ocurrences, but I am
     not sure if they make sense in a form of constructor. This is why I
     chose to duplicated the code.  Eduardo 13/7/99. *)
  (* Since Lambda can no longer occur after a product or a MutInd,
     I have branched the remaining cases on check_pos. HH 28/1/00 *)

  and check_weak_pos env n c =
    let x = whd_betadeltaiota env Evd.empty c in
    match kind_of_term x with 
      (* The extra case *)
      | IsLambda (na,b,d) -> 
          if noccur_between n ntypes b
          then check_weak_pos (push_rel_assum (na,b) env) (n+1) d
          else raise (IllFormedInd (LocalNonPos n))
      (******************)
      | _ -> check_pos env n x
  
  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *) 

  and check_construct env check_head = 
    let rec check_constr_rec env lrec n c = 
      let x,largs = whd_betadeltaiota_stack env Evd.empty c in
      match kind_of_term x with

        | IsProd (na,b,d) -> 
	    assert (largs = []);
            let recarg = check_pos env n b in 
	    check_constr_rec (push_rel_assum (na, b) env)
	      (recarg::lrec) (n+1) d

        (* LetIn's must be free of occurrence of the inductive types and
	   they do not contribute to recargs *)
        | IsLetIn (na,b,t,d) -> 
	    assert (largs = []);
            if not (noccur_between n ntypes b & noccur_between n ntypes t) then
	      check_constr_rec (push_rel_def (na,b, b) env)
		lrec n (subst1 b d)
	    else
              let recarg = check_pos env n b in 
	      check_constr_rec (push_rel_def (na,b, b) env)
		lrec (n+1) d 
	| hd ->
	    if check_head then
	      if hd = IsRel (n+ntypes-i) then
		check_correct_par env nparams ntypes n (ntypes-i+1) largs
	      else
		raise (IllFormedInd LocalNotConstructor)
	    else
	      if not (List.for_all (noccur_between n ntypes) largs)
              then raise (IllFormedInd (LocalNonPos n));
	    List.rev lrec
    in check_constr_rec env []
  in
  Array.map
    (fun c ->
       let c = body_of_type c in
       let sign, rawc = mind_extract_params nparams c in
       let env' = push_rels sign env in
       try
	 check_construct env' true (1+nparams) rawc
       with IllFormedInd err -> 
	 explain_ind_err (ntypes-i+1) env nparams c err)
    indlc
    
let is_recursive listind =
  let rec one_is_rec rvec = 
    List.exists (function Mrec(i) -> List.mem i listind 
                   | Imbr(_,lvec) -> one_is_rec lvec
                   | Norec -> false
                   | Param _ -> false) rvec
  in 
  array_exists one_is_rec

let cci_inductive env env_ar kind finite inds cst =
  let ntypes = List.length inds in
  let one_packet i (nparams,id,ar,cnames,issmall,isunit,lc) =
    let recargs = listrec_mconstr env_ar ntypes nparams i lc in
    let isunit = isunit && ntypes = 1 && (not (is_recursive [0] recargs)) in
    let (ar_sign,ar_sort) = splay_arity env Evd.empty (body_of_type ar) in
    
    let nf_ar,user_ar =
      if isArity (body_of_type ar) then ar,None
      else (prod_it (mkSort ar_sort) ar_sign, Some ar) in
    let kelim = allowed_sorts issmall isunit ar_sort in
    let lc_bodies = Array.map body_of_type lc in

    let splayed_lc = Array.map (splay_prod_assum env_ar Evd.empty) lc_bodies in
    let nf_lc =
      array_map2 (fun (d,b) c -> it_mkProd_or_LetIn b d) splayed_lc lc in
    let nf_lc,user_lc = if nf_lc = lc then lc,None else nf_lc, Some lc in
    { mind_consnames = Array.of_list cnames;
      mind_typename = id;
      mind_user_lc = user_lc;
      mind_nf_lc = nf_lc;
      mind_user_arity  = user_ar;
      mind_nf_arity = nf_ar;
      mind_nrealargs = List.length ar_sign - nparams;
      mind_sort = ar_sort;
      mind_kelim = kelim;
      mind_listrec = recargs;
      mind_finite = finite;
      mind_nparams = nparams }
  in
  let ids = 
    List.fold_left 
      (fun acc (_,_,ar,_,_,_,lc) -> 
	 Idset.union (global_vars_set (body_of_type ar))
	   (Array.fold_left
	      (fun acc c -> Idset.union (global_vars_set (body_of_type c)) acc)
	      acc
	      lc))
      Idset.empty inds
  in
  let packets = Array.of_list (list_map_i one_packet 1 inds) in
  { mind_kind = kind;
    mind_ntypes = ntypes;
    mind_hyps = keep_hyps ids (named_context env);
    mind_packets = packets;
    mind_constraints = cst;
    mind_singl = None }
