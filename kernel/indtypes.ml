
(* $Id$ *)

open Util
open Names
open Generic
open Term
open Inductive
open Sign
open Environ
open Instantiate
open Reduction
open Typeops

(* In the following, each time an [evar_map] is required, then [Evd.empty]
   is given, since inductive types are typed in an environment without 
   existentials. *)

let mind_check_arities env mie =
  let check_arity id c =
    if not (is_arity env Evd.empty c) then 
      raise (InductiveError (NotAnArity id))
  in
  List.iter (fun (id,ar,_,_) -> check_arity id ar) mie.mind_entry_inds

let allowed_sorts issmall isunit = function
  | Type _ -> 
      [prop;spec;types]
  | Prop Pos -> 
      if issmall then [prop;spec;types] else [prop;spec]
  | Prop Null -> 
      if isunit then [prop;spec] else [prop]

let is_small_type t = is_small t.typ

type ill_formed_ind =
  | NonPos of int
  | NotEnoughArgs of int
  | NotConstructor
  | NonPar of int * int

exception IllFormedInd of ill_formed_ind

let explain_ind_err ntyp lna nbpar c err = 
  let (lpar,c') = mind_extract_params nbpar c in
  let env = (List.map fst lpar)@lna in
  match err with
    | NonPos kt -> 
	raise (InductiveError (Inductive.NonPos (env,c',Rel (kt+nbpar))))
    | NotEnoughArgs kt -> 
	raise (InductiveError 
		 (Inductive.NotEnoughArgs (env,c',Rel (kt+nbpar))))
    | NotConstructor ->
	raise (InductiveError 
		 (Inductive.NotConstructor (env,c',Rel (ntyp+nbpar))))
    | NonPar (n,l) ->
	raise (InductiveError 
		 (Inductive.NonPar (env,c',n,Rel (nbpar-n+1), Rel (l+nbpar))))

let failwith_non_pos_vect n ntypes v =
  for i = 0 to Array.length v - 1 do
    for k = n to n + ntypes - 1 do
      if not (noccurn k v.(i)) then raise (IllFormedInd (NonPos (k-n+1)))
    done
  done;
  anomaly "failwith_non_pos_vect: some k in [n;n+ntypes-1] should occur in v"

let check_correct_par env nparams ntypes n l largs =
  if Array.length largs < nparams then 
    raise (IllFormedInd (NotEnoughArgs l));
  let (lpar,largs') = array_chop nparams largs in
  for k = 0 to nparams - 1 do
    if not ((Rel (n-k-1))= whd_betadeltaiotaeta env Evd.empty lpar.(k)) then
      raise (IllFormedInd (NonPar (k+1,l)))
  done;
  if not (array_for_all (noccur_bet n ntypes) largs') then 
    failwith_non_pos_vect n ntypes largs'

(* This removes global parameters of the inductive types in lc *)
let abstract_mind_lc env ntyps npars lc = 
  let lC = decomp_DLAMV ntyps lc in
  if npars = 0 then 
    lC 
  else 
    let make_abs = 
      list_tabulate
	(function i -> lambda_implicit_lift npars (Rel (i+1))) ntyps 
    in 
    Array.map (compose (nf_beta env Evd.empty) (substl make_abs)) lC

let decomp_par n c = snd (mind_extract_params n c)
      
let listrec_mconstr env ntypes nparams i indlc =
  (* check the inductive types occur positively in [c] *)
  let rec check_pos n c = 
    match whd_betadeltaiota env Evd.empty c with 
      | DOP2(Prod,b,DLAM(na,d)) -> 
          if not (noccur_bet n ntypes b) then raise (IllFormedInd (NonPos n));
	  check_pos (n+1) d
      | x -> 
	  let hd,largs = destApplication (ensure_appl x) in
          match hd with
            | Rel k ->
                if k >= n && k<n+ntypes then begin
		  check_correct_par env nparams ntypes n (k-n+1) largs;
		  Mrec(n+ntypes-k-1)
                end else if noccur_bet n ntypes x then 
		  if (n-nparams) <= k & k <= (n-1) 
		  then Param(n-1-k)
                  else Norec
		else
		  raise (IllFormedInd (NonPos n))
            | DOPN(MutInd ind_sp,a) -> 
                if (noccur_bet n ntypes x) then Norec
                else Imbr(ind_sp,imbr_positive n (ind_sp,a) largs)
            | err -> 
		if noccur_bet n ntypes x then Norec
		else raise (IllFormedInd (NonPos n))

  and imbr_positive n mi largs =
    let mispeci = lookup_mind_specif mi env in
    let auxnpar = mis_nparams mispeci in
    let (lpar,auxlargs) = array_chop auxnpar largs in 
    if not (array_for_all (noccur_bet n ntypes) auxlargs) then
      raise (IllFormedInd (NonPos n));
    let auxlc = mis_lc mispeci 
    and auxntyp = mis_ntypes mispeci in 
    if auxntyp <> 1 then raise (IllFormedInd (NonPos n));
    let lrecargs = array_map_to_list (check_weak_pos n) lpar in
    (* The abstract imbricated inductive type with parameters substituted *)
    let auxlcvect = abstract_mind_lc env auxntyp auxnpar auxlc in
    let newidx = n + auxntyp in
    let _ = 
      (* fails if the inductive type occurs non positively *)
      (* when substituted *) 
      Array.map 
	(function c -> 
	   let c' = hnf_prod_appvect env Evd.empty "is_imbr_pos" c 
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
          if noccur_bet n ntypes b
          then check_weak_pos (n+1) d
          else raise (IllFormedInd (NonPos n))
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
                | _ -> raise (IllFormedInd NotConstructor)
	    else
	      if not (array_for_all (noccur_bet n ntypes) largs)
              then raise (IllFormedInd (NonPos n));
	    List.rev lrec
    in check_constr_rec []
  in
  let (lna,lC) = decomp_DLAMV_name ntypes indlc in
  Array.map
    (fun c ->
       try
	 check_construct true (1+nparams) (decomp_par nparams c)
       with IllFormedInd err -> 
	 explain_ind_err (ntypes-i+1) lna nparams c err)
    lC
    
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
    let (ar_sign,ar_sort) = splay_arity env Evd.empty ar.body in
    let kelim = allowed_sorts issmall isunit ar_sort in
    { mind_consnames = Array.of_list cnames;
      mind_typename = id;
      mind_lc = lc;
      mind_nrealargs = List.length ar_sign - nparams;
      mind_arity  = ar;
      mind_kelim = kelim;
      mind_listrec = recargs;
      mind_finite = finite }
  in
  let ids = 
    List.fold_left 
      (fun acc (_,ar,_,_,_,lc) -> 
	 Idset.union (global_vars_set ar.body) 
	   (Idset.union (global_vars_set lc) acc))
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
