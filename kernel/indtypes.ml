
(* $Id$ *)

open Util
open Generic
open Term
open Inductive
open Sign
open Environ
open Instantiate
open Reduction

(* In the following, each time an [evar_map] is required, then [Evd.empty]
   is given, since inductive types are typed in an environment without 
   existentials. *)

let mind_check_arities env mie =
  let check_arity id c =
    if not (is_arity env Evd.empty c) then 
      raise (InductiveError (NotAnArity id))
  in
  List.iter (fun (id,ar,_,_) -> check_arity id ar) mie.mind_entry_inds

let sort_of_arity env c =
  let rec sort_of ar =
    match whd_betadeltaiota env Evd.empty ar with
      | DOP0 (Sort s) -> s
      | DOP2 (Prod, _, DLAM (_, c)) -> sort_of c
      | _ -> error "not an arity"
  in
  sort_of c

let allowed_sorts issmall isunit = function
  | Type _ -> 
      [prop;spec;types]
  | Prop Pos -> 
      if issmall then [prop;spec;types] else [prop;spec]
  | Prop Null -> 
      if isunit then [prop;spec] else [prop]

let is_small_type t = is_small t.typ

let failwith_non_pos_vect n ntypes v =
  for i = 0 to Array.length v - 1 do
    for k = n to n + ntypes - 1 do
      if not (noccurn k v.(i)) then raise (InductiveError (NonPos (k-n+1)))
    done
  done;
  anomaly "failwith_non_pos_vect: some k in [n;n+ntypes-1] should occur in v"

let check_correct_par env nparams ntypes n l largs =
  if Array.length largs < nparams then raise (InductiveError (NotEnoughArgs l));
  let (lpar,largs') = array_chop nparams largs in
  for k = 0 to nparams - 1 do
    if not ((Rel (n-k-1))= whd_betadeltaiotaeta env Evd.empty lpar.(k)) then
      raise (InductiveError (NonPar (k+1,l)))
  done;
  if not (array_for_all (noccur_bet n ntypes) largs') then 
    failwith_non_pos_vect n ntypes largs'

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

let decomp_par n c = snd (decompose_prod_n n c)
      
let listrec_mconstr env ntypes nparams i indlc =
  (* check the inductive types occur positively in C *)
  let rec check_pos n c = 
    match whd_betadeltaiota env Evd.empty c with 
      | DOP2(Prod,b,DLAM(na,d)) -> 
          if not (noccur_bet n ntypes b) then raise (InductiveError (NonPos n));
	  check_pos (n+1) d
      | x -> 
	  (match ensure_appl x with 
             | DOPN(AppL,cl) -> 
                 let hd = array_hd cl 
		 and largs = array_tl cl in
                 (match hd with 
                    | Rel k -> 
			check_correct_par env nparams ntypes n (k-n+1) largs;
                        if k >= n && k<n+ntypes then 
			  Mrec(n+ntypes-k-1) 
                        else if noccur_bet n ntypes x then 
			  if (n-nparams) <= k & k <= (n-1) 
			  then Param(n-1-k)
                          else Norec
			else 
			  raise (InductiveError (NonPos n))
                    | (DOPN(MutInd(sp,i),_) as mi) -> 
                        if (noccur_bet n ntypes x) then
                          Norec
                        else 
			  Imbr(sp,i,imbr_positive n mi largs)
                    | err -> 
			if noccur_bet n ntypes x then Norec
			else raise (InductiveError (NonPos n)))
             | _ -> anomaly "check_pos")
	  
  and imbr_positive n mi largs = 
    let mispeci = lookup_mind_specif mi env in
    let auxnpar = mis_nparams mispeci in
    let (lpar,auxlargs) = array_chop auxnpar largs in 
    if not (array_for_all (noccur_bet n ntypes) auxlargs) then
      raise (InductiveError (NonPos n));
    let auxlc = mis_lc mispeci 
    and auxntyp = mis_ntypes mispeci in 
    if auxntyp <> 1 then raise (InductiveError (NonPos n));
    let lrecargs = array_map_to_list (check_param_pos n) lpar in
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

  (* The function check_param_pos is exactly the same as check_pos, but
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
  and check_param_pos n c = 
    match whd_betadeltaiota env Evd.empty c with 
      (* The extra case *)
      | DOP2(Lambda,b,DLAM(na,d)) -> 
          if noccur_bet n ntypes b
          then check_param_pos (n+1) d
          else raise (InductiveError (NonPos n))
      (******************)
      | DOP2(Prod,b,DLAM(na,d)) -> 
          if (noccur_bet n ntypes b) 
          then check_param_pos (n+1) d
          else raise (InductiveError (NonPos n))
      | x -> 
	  (match ensure_appl x with 
             | DOPN(AppL,cl) -> 
                 let hd = array_hd cl 
		 and largs = array_tl cl in 
		 (match hd with 
                    | Rel k -> 
                        check_correct_par env nparams ntypes n (k-n+1) largs;
			if k >= n & k<n+ntypes then 
			  Mrec(n+ntypes-k-1) 
                        else if noccur_bet n ntypes x then 
			  if (n-nparams) <= k & k <= (n-1)
                          then Param(n-1-k)
                          else Norec
			else raise (InductiveError (NonPos n))
                    | (DOPN(MutInd(sp,i),_) as mi) -> 
                        if (noccur_bet n ntypes x) 
                        then Norec
                        else Imbr(sp,i,imbr_positive n mi largs)
                    | err -> if noccur_bet n ntypes x then Norec
		      else raise (InductiveError (NonPos n)))
             | _ -> anomaly "check_param_pos")
  
  (* check the inductive types occur positively in the products of C, if
     checkhd=true, also check the head corresponds to a constructor of
     the ith type *) 

  and check_construct check = 
    let rec check_constr_rec lrec n c = 
      match whd_betadeltaiota env Evd.empty c with
        | DOP2(Prod,b,DLAM(na,d)) -> 
            let recarg = (check_pos n b) in 
	    check_constr_rec (recarg::lrec) (n+1) d 
	| x -> 
	    (match ensure_appl x with 
               | DOPN(AppL,cl) ->
                   let hd = array_hd cl 
                   and largs = array_tl cl in 
                   if check then 
                     (match hd with 
			| Rel k -> 
			    check_correct_par env nparams ntypes n (k-n+1) largs;
                            if k = n+ntypes-i then 
			      List.rev lrec 
                            else 
			      raise (InductiveError (NonPos n))
                        | _ -> raise (InductiveError (NonPos n)))
                   else 
                     if array_for_all (noccur_bet n ntypes) largs 
                     then List.rev lrec 
                     else raise (InductiveError (NonPos n)) 
	       | _ -> anomaly "ensure_appl should return an AppL") 
    in check_constr_rec []
  in
  let (lna,lC) = decomp_DLAMV_name ntypes indlc in
  Array.map
    (fun c ->
       (* try *)
       check_construct true (1+nparams) (decomp_par nparams c)
       (* with InductiveError err -> 
	    explain_ind_err (ntypes-i+1) lna nparams c err *))
    lC
    
let is_recursive listind =
  let rec one_is_rec rvec = 
    List.exists (function Mrec(i) -> List.mem i listind 
                   | Imbr(_,_,lvec) -> one_is_rec lvec
                   | Norec -> false
                   | Param _ -> false) rvec
  in 
  array_exists one_is_rec

let cci_inductive env env_ar kind nparams finite inds cst =
  let ntypes = List.length inds in
  let one_packet i (id,ar,cnames,issmall,isunit,lc) =
    let recargs = listrec_mconstr env_ar ntypes nparams i lc in
    let isunit = isunit && ntypes = 1 && (not (is_recursive [0] recargs)) in
    let kelim = allowed_sorts issmall isunit (sort_of_arity env ar.body) in
    { mind_consnames = Array.of_list cnames;
      mind_typename = id;
      mind_lc = lc;
      mind_arity  = ar;
      mind_kelim = kelim;
      mind_listrec = recargs;
      mind_finite = finite }
  in
  let packets = Array.of_list (list_map_i one_packet 1 inds) in
  { mind_kind = kind;
    mind_ntypes = ntypes;
    mind_hyps = var_context env;
    mind_packets = packets;
    mind_constraints = cst;
    mind_singl = None;
    mind_nparams = nparams }
