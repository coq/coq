
(* $Id$ *)

open Util
open Names
open Generic
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
  | NonPos of name list * constr * constr
  | NotEnoughArgs of name list * constr * constr
  | NotConstructor of name list * constr * constr
  | NonPar of name list * constr * int * constr * constr
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
    | (id,_,cl,_)::inds -> 
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
  let (l,c') = decompose_prod_n n c in (List.rev l,c')
  
let extract nparams c =
  try mind_extract_params nparams c 
  with UserError _ -> raise (InductiveError BadEntry)

let check_params nparams params c = 
  let eparams = fst (extract nparams c) in
  try
    List.iter2 
      (fun (n1,t1) (n2,t2) ->
	 if n1 <> n2 || strip_all_casts t1 <> strip_all_casts t2 then
	   raise (InductiveError BadEntry))
      eparams params
  with Invalid_argument _ ->
    raise (InductiveError BadEntry)

let mind_extract_and_check_params mie =
  let nparams = mie.mind_entry_nparams in
  match mie.mind_entry_inds with
    | [] -> anomaly "empty inductive types declaration"
    | (_,ar,_,_)::l -> 
	let (params,_) = extract nparams ar in
	List.iter (fun (_,c,_,_) -> check_params nparams params c) l;
	params

let decomp_all_DLAMV_name constr = 
  let rec decomprec lna = function 
    | DLAM(na,lc)  -> decomprec (na::lna) lc
    | DLAMV(na,lc) -> (na::lna,lc)
    | _ -> assert false
  in 
  decomprec [] constr

let mind_check_lc params mie =
  let nparams = List.length params in
  let check_lc (_,_,_,lc) = List.iter (check_params nparams params) lc in
  List.iter check_lc mie.mind_entry_inds

let mind_check_arities env mie =
  let check_arity id c =
    if not (is_arity env Evd.empty c) then 
      raise (InductiveError (NotAnArity id))
  in
  List.iter (fun (id,ar,_,_) -> check_arity id ar) mie.mind_entry_inds

(***********************************************************************)

let allowed_sorts issmall isunit = function
  | Type _ -> 
      [prop;spec;types]
  | Prop Pos -> 
      if issmall then [prop;spec;types] else [prop;spec]
  | Prop Null -> 
      if isunit then [prop;spec] else [prop]

let is_small_type t = is_small t.typ

type ill_formed_ind =
  | LocalNonPos of int
  | LocalNotEnoughArgs of int
  | LocalNotConstructor
  | LocalNonPar of int * int

exception IllFormedInd of ill_formed_ind

let explain_ind_err ntyp lna nbpar c err = 
  let (lpar,c') = mind_extract_params nbpar c in
  let env = (List.map fst lpar)@lna in
  match err with
    | LocalNonPos kt -> 
	raise (InductiveError (NonPos (env,c',Rel (kt+nbpar))))
    | LocalNotEnoughArgs kt -> 
	raise (InductiveError 
		 (NotEnoughArgs (env,c',Rel (kt+nbpar))))
    | LocalNotConstructor ->
	raise (InductiveError 
		 (NotConstructor (env,c',Rel (ntyp+nbpar))))
    | LocalNonPar (n,l) ->
	raise (InductiveError 
		 (NonPar (env,c',n,Rel (nbpar-n+1), Rel (l+nbpar))))

let failwith_non_pos_vect n ntypes v =
  for i = 0 to Array.length v - 1 do
    for k = n to n + ntypes - 1 do
      if not (noccurn k v.(i)) then raise (IllFormedInd (LocalNonPos (k-n+1)))
    done
  done;
  anomaly "failwith_non_pos_vect: some k in [n;n+ntypes-1] should occur in v"

let check_correct_par env nparams ntypes n l largs =
  if Array.length largs < nparams then 
    raise (IllFormedInd (LocalNotEnoughArgs l));
  let (lpar,largs') = array_chop nparams largs in
  for k = 0 to nparams - 1 do
    if not ((Rel (n-k-1))= whd_betadeltaiotaeta env Evd.empty lpar.(k)) then
      raise (IllFormedInd (LocalNonPar (k+1,l)))
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
	(function i -> lambda_implicit_lift npars (Rel (i+1))) ntyps 
    in 
    Array.map (compose (nf_beta env Evd.empty) (substl make_abs)) lc

let decomp_par n c = snd (mind_extract_params n c)
      
let listrec_mconstr env ntypes nparams i indlc =
  (* check the inductive types occur positively in [c] *)
  let rec check_pos n c = 
    match whd_betadeltaiota env Evd.empty c with 
      | DOP2(Prod,b,DLAM(na,d)) -> 
          if not (noccur_between n ntypes b) then raise (IllFormedInd (LocalNonPos n));
	  check_pos (n+1) d
      | x -> 
	  let hd,largs = destApplication (ensure_appl x) in
          match hd with
            | Rel k ->
                if k >= n && k<n+ntypes then begin
		  check_correct_par env nparams ntypes n (k-n+1) largs;
		  Mrec(n+ntypes-k-1)
                end else if noccur_between n ntypes x then 
		  if (n-nparams) <= k & k <= (n-1) 
		  then Param(n-1-k)
                  else Norec
		else
		  raise (IllFormedInd (LocalNonPos n))
            | DOPN(MutInd ind_sp,a) -> 
                if (noccur_between n ntypes x) then Norec
                else Imbr(ind_sp,imbr_positive n (ind_sp,a) largs)
            | err -> 
		if noccur_between n ntypes x then Norec
		else raise (IllFormedInd (LocalNonPos n))

  and imbr_positive n mi largs =
    let mispeci = lookup_mind_specif mi env in
    let auxnpar = mis_nparams mispeci in
    let (lpar,auxlargs) = array_chop auxnpar largs in 
    if not (array_for_all (noccur_between n ntypes) auxlargs) then
      raise (IllFormedInd (LocalNonPos n));
    let auxlc = mis_lc mispeci 
    and auxntyp = mis_ntypes mispeci in 
    if auxntyp <> 1 then raise (IllFormedInd (LocalNonPos n));
    let lrecargs = array_map_to_list (check_weak_pos n) lpar in
    (* The abstract imbricated inductive type with parameters substituted *)
    let auxlcvect = abstract_mind_lc env auxntyp auxnpar auxlc in
    let newidx = n + auxntyp in
    let _ = 
      (* fails if the inductive type occurs non positively *)
      (* when substituted *) 
      Array.map 
	(function c -> 
	   let c' = hnf_prod_appvect env Evd.empty c 
		      (Array.map (lift auxntyp) lpar) in 
	   check_construct false newidx c') 
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

  and check_weak_pos n c = 
    match whd_betadeltaiota env Evd.empty c with 
      (* The extra case *)
      | DOP2(Lambda,b,DLAM(na,d)) -> 
          if noccur_between n ntypes b
          then check_weak_pos (n+1) d
          else raise (IllFormedInd (LocalNonPos n))
      (******************)
      | x -> check_pos n x
  
  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *) 

  and check_construct check_head = 
    let rec check_constr_rec lrec n c = 
      match whd_betadeltaiota env Evd.empty c with
        | DOP2(Prod,b,DLAM(na,d)) -> 
            let recarg = check_pos n b in 
	    check_constr_rec (recarg::lrec) (n+1) d 
	| x -> 
            let hd,largs = destApplication (ensure_appl x) in
	    if check_head then
              match hd with
		| Rel k when k = n+ntypes-i ->
		    check_correct_par env nparams ntypes n (k-n+1) largs
                | _ -> raise (IllFormedInd LocalNotConstructor)
	    else
	      if not (array_for_all (noccur_between n ntypes) largs)
              then raise (IllFormedInd (LocalNonPos n));
	    List.rev lrec
    in check_constr_rec []
  in
  let lna = it_dbenv (fun l na t -> na::l) [] (context env) in
  Array.map
    (fun c ->
       let c = body_of_type c in
       try
	 check_construct true (1+nparams) (decomp_par nparams c)
       with IllFormedInd err -> 
	 explain_ind_err (ntypes-i+1) lna nparams c err)
    indlc
    
let is_recursive listind =
  let rec one_is_rec rvec = 
    List.exists (function Mrec(i) -> List.mem i listind 
                   | Imbr(_,lvec) -> one_is_rec lvec
                   | Norec -> false
                   | Param _ -> false) rvec
  in 
  array_exists one_is_rec

let cci_inductive env env_ar kind nparams finite inds cst =
  let ntypes = List.length inds in
  let one_packet i (id,ar,cnames,issmall,isunit,lc) =
    let recargs = listrec_mconstr env_ar ntypes nparams i lc in
    let isunit = isunit && ntypes = 1 && (not (is_recursive [0] recargs)) in
    let (ar_sign,ar_sort) = splay_arity env Evd.empty (body_of_type ar) in
    let nf_ar,user_ar =
      if isArity (body_of_type ar) then ar,None
      else 
	(make_typed_lazy (prod_it (mkSort ar_sort) ar_sign)
	   (fun _ -> level_of_type ar)),
	Some (body_of_type ar) in
    let kelim = allowed_sorts issmall isunit ar_sort in
    let lc_bodies = Array.map body_of_type lc in
    let splayed_lc = Array.map (splay_prod env Evd.empty) lc_bodies in
    let nf_lc = Array.map (fun (d,b) -> prod_it b d) splayed_lc in
    let nf_typed_lc,user_lc =
      if nf_lc = lc_bodies then lc,None
      else
	(array_map2
	   (fun nfc c -> make_typed_lazy nfc (fun _ -> level_of_type c))
	   nf_lc lc),
        Some lc_bodies in
    { mind_consnames = Array.of_list cnames;
      mind_typename = id;
      mind_user_lc = user_lc;
      mind_nf_lc = nf_typed_lc;
      mind_user_arity  = user_ar;
      mind_nf_arity = nf_ar;
      mind_nrealargs = List.length ar_sign - nparams;
      mind_sort = ar_sort;
      mind_kelim = kelim;
      mind_listrec = recargs;
      mind_finite = finite }
  in
  let ids = 
    List.fold_left 
      (fun acc (_,ar,_,_,_,lc) -> 
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
    mind_hyps = keep_hyps (var_context env) ids;
    mind_packets = packets;
    mind_constraints = cst;
    mind_singl = None;
    mind_nparams = nparams }
