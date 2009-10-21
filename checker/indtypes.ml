(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: indtypes.ml 10296 2007-11-07 11:02:42Z barras $ *)

open Util
open Names
open Univ
open Term
open Inductive
open Reduction
open Typeops
open Pp
open Declarations
open Environ

let rec debug_string_of_mp = function
  | MPfile sl -> string_of_dirpath sl
  | MPbound uid -> "bound("^string_of_mbid uid^")"
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

let rec string_of_mp = function
  | MPfile sl -> string_of_dirpath sl
  | MPbound uid -> string_of_mbid uid
  | MPdot (mp,l) -> string_of_mp mp ^ "." ^ string_of_label l

let string_of_mp mp =
  if !Flags.debug then debug_string_of_mp mp else string_of_mp mp

let prkn kn =
  let (mp,_,l) = repr_kn kn in
  str(string_of_mp mp ^ "." ^ string_of_label l)
let prcon c =
  let (mp,_,l) = repr_con c in
  str(string_of_mp mp ^ "." ^ string_of_label l)

(* Same as noccur_between but may perform reductions.
   Could be refined more...  *)
let weaker_noccur_between env x nvars t =
  if noccur_between x nvars t then Some t
  else
   let t' = whd_betadeltaiota env t in
   if noccur_between x nvars t' then Some t'
   else None

let is_constructor_head t =
  match fst(decompose_app t) with
  | Rel _ -> true
  | _ -> false

let conv_ctxt_prefix env (ctx1:rel_context) ctx2 =
  let rec chk env rctx1 rctx2 =
    match rctx1, rctx2 with
        (_,None,ty1 as d1)::rctx1', (_,None,ty2)::rctx2' ->
          conv env ty1 ty2;
          chk (push_rel d1 env) rctx1' rctx2'
      | (_,Some bd1,ty1 as d1)::rctx1', (_,Some bd2,ty2)::rctx2' ->
          conv env ty1 ty2;
          conv env bd1 bd2;
          chk (push_rel d1 env) rctx1' rctx2'
      | [],_ -> ()
      | _ -> failwith "non convertible contexts" in
  chk env (List.rev ctx1) (List.rev ctx2)

(************************************************************************)
(* Various well-formedness check for inductive declarations            *)

(* Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * constr * constr
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of identifier
  | SameNamesConstructors of identifier
  | SameNamesOverlap of identifier list
  | NotAnArity of identifier
  | BadEntry

exception InductiveError of inductive_error

(************************************************************************)
(************************************************************************)

(* Typing the arities and constructor types *)

let rec sorts_of_constr_args env t =
  let t = whd_betadeltaiota_nolet env t in
  match t with
    | Prod (name,c1,c2) ->
        let varj = infer_type env c1 in
	let env1 = push_rel (name,None,c1) env in
	varj :: sorts_of_constr_args env1 c2
    | LetIn (name,def,ty,c) ->
        let env1 = push_rel (name,Some def,ty) env in
	sorts_of_constr_args env1 c
    | _ when is_constructor_head t -> []
    | _ -> anomaly "infos_and_sort: not a positive constructor"


(* Prop and Set are small *)
let is_small_sort = function
  | Prop _ -> true
  | _ -> false

let is_logic_sort s = (s = Prop Null)

(* [infos] is a sequence of pair [islogic,issmall] for each type in
   the product of a constructor or arity *)

let is_small_constr infos = List.for_all (fun s -> is_small_sort s) infos
let is_logic_constr infos = List.for_all (fun s -> is_logic_sort s) infos

(* An inductive definition is a "unit" if it has only one constructor
   and that all arguments expected by this constructor are
   logical, this is the case for equality, conjunction of logical properties
*)
let is_unit constrsinfos =
  match constrsinfos with  (* One info = One constructor *)
   | [|constrinfos|] -> is_logic_constr constrinfos
   | [||] -> (* type without constructors *) true
   | _ -> false

let small_unit constrsinfos =
  let issmall = array_for_all is_small_constr constrsinfos
  and isunit = is_unit constrsinfos in
  issmall, isunit

(* check information related to inductive arity *)
let typecheck_arity env params inds =
  let nparamargs = rel_context_nhyps params in
  let nparamdecls = rel_context_length params in
  let check_arity arctxt = function
      Monomorphic mar ->
        let ar = mar.mind_user_arity in
        let _ = infer_type env ar in
        conv env (it_mkProd_or_LetIn (Sort mar.mind_sort) arctxt) ar;
        ar
    | Polymorphic par ->
        check_polymorphic_arity env params par;
        it_mkProd_or_LetIn (Sort(Type par.poly_level)) arctxt in
  let env_arities =
    Array.fold_left
      (fun env_ar ind ->
        let ar_ctxt = ind.mind_arity_ctxt in
        let _ = check_ctxt env ar_ctxt in
        conv_ctxt_prefix env params ar_ctxt;
        (* Arities (with params) are typed-checked here *)
        let arity = check_arity ar_ctxt ind.mind_arity in
        (* mind_nrealargs *)
	let nrealargs = rel_context_nhyps ar_ctxt - nparamargs in
        if ind.mind_nrealargs <> nrealargs then
             failwith "bad number of real inductive arguments";
	let nrealargs_ctxt = rel_context_length ar_ctxt - nparamdecls in
        if ind.mind_nrealargs_ctxt <> nrealargs_ctxt then
             failwith "bad length of real inductive arguments signature";
	(* We do not need to generate the universe of full_arity; if
	   later, after the validation of the inductive definition,
	   full_arity is used as argument or subject to cast, an
	   upper universe will be generated *)
	let id = ind.mind_typename in
	let env_ar' = push_rel (Name id, None, arity) env_ar in
        env_ar')
      env
      inds in
  env_arities

(* Allowed eliminations *)

let check_predicativity env s small level =
  match s, engagement env with
      Type u, _ ->
        let u' = fresh_local_univ () in
        let cst =
          merge_constraints (enforce_geq u' u Constraint.empty)
            (universes env) in
        if not (check_geq cst u' level) then
          failwith "impredicative Type inductive type"
    | Prop Pos, Some ImpredicativeSet -> ()
    | Prop Pos, _ ->
        if not small then failwith "impredicative Set inductive type"
    | Prop Null,_ -> ()


let sort_of_ind = function
    Monomorphic mar -> mar.mind_sort
  | Polymorphic par -> Type par.poly_level

let all_sorts = [InProp;InSet;InType]
let small_sorts = [InProp;InSet]
let logical_sorts = [InProp]

let allowed_sorts issmall isunit s =
  match family_of_sort s with
  (* Type: all elimination allowed *)
  | InType -> all_sorts

  (* Small Set is predicative: all elimination allowed *)
  | InSet when issmall -> all_sorts

  (* Large Set is necessarily impredicative: forbids large elimination *)
  | InSet -> small_sorts

  (* Unitary/empty Prop: elimination to all sorts are realizable *)
  (* unless the type is large. If it is large, forbids large elimination *)
  (* which otherwise allows to simulate the inconsistent system Type:Type *)
  | InProp when isunit -> if issmall then all_sorts else small_sorts

  (* Other propositions: elimination only to Prop *)
  | InProp -> logical_sorts



let compute_elim_sorts env_ar params mib arity lc =
  let inst = extended_rel_list 0 params in
  let env_params = push_rel_context params env_ar in
  let lc = Array.map
    (fun c ->
      hnf_prod_applist env_params (lift (rel_context_length params) c) inst)
    lc in
  let s = sort_of_ind arity in
  let infos = Array.map (sorts_of_constr_args env_params) lc in
  let (small,unit) = small_unit infos in
  (* We accept recursive unit types... *)
  let unit = unit && mib.mind_ntypes = 1 in
  (* compute the max of the sorts of the products of the constructor type *)
  let level = max_inductive_sort
    (Array.concat (Array.to_list (Array.map Array.of_list infos))) in
  check_predicativity env_ar s small level;
  allowed_sorts small unit s


let typecheck_one_inductive env params mib mip =
  (* mind_typename and mind_consnames not checked *)
  (* mind_reloc_tbl, mind_nb_constant, mind_nb_args not checked (VM) *)
  (* mind_arity_ctxt, mind_arity, mind_nrealargs DONE (typecheck_arity) *)
  (* mind_user_lc *)
  let _ = Array.map (infer_type env) mip.mind_user_lc in
  (* mind_nf_lc *)
  let _ = Array.map (infer_type env) mip.mind_nf_lc in
  array_iter2 (conv env) mip.mind_nf_lc mip.mind_user_lc;
  (* mind_consnrealdecls *)
  let check_cons_args c n =
    let ctx,_ = decompose_prod_assum c in
    if n <> rel_context_length ctx - rel_context_length params then
      failwith "bad number of real constructor arguments" in
  array_iter2 check_cons_args mip.mind_nf_lc mip.mind_consnrealdecls;
  (* mind_kelim: checked by positivity criterion ? *)
  let sorts =
    compute_elim_sorts env params mib mip.mind_arity mip.mind_nf_lc in
  if List.exists (fun s -> not (List.mem s sorts)) mip.mind_kelim then
    failwith "elimination not allowed";
  (* mind_recargs: checked by positivity criterion *)
  ()

(************************************************************************)
(************************************************************************)
(* Positivity *)

type ill_formed_ind =
  | LocalNonPos of int
  | LocalNotEnoughArgs of int
  | LocalNotConstructor
  | LocalNonPar of int * int

exception IllFormedInd of ill_formed_ind

(* [mind_extract_params mie] extracts the params from an inductive types
   declaration, and checks that they are all present (and all the same)
   for all the given types. *)

let mind_extract_params = decompose_prod_n_assum

let explain_ind_err ntyp env0 nbpar c err =
  let (lpar,c') = mind_extract_params nbpar c in
  let env = push_rel_context lpar env0 in
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

let failwith_non_pos n ntypes c =
  for k = n to n + ntypes - 1 do
    if not (noccurn k c) then raise (IllFormedInd (LocalNonPos (k-n+1)))
  done

let failwith_non_pos_vect n ntypes v =
  Array.iter (failwith_non_pos n ntypes) v;
  anomaly "failwith_non_pos_vect: some k in [n;n+ntypes-1] should occur"

let failwith_non_pos_list n ntypes l =
  List.iter (failwith_non_pos n ntypes) l;
  anomaly "failwith_non_pos_list: some k in [n;n+ntypes-1] should occur"

(* Conclusion of constructors: check the inductive type is called with
   the expected parameters *)
let check_correct_par (env,n,ntypes,_) hyps l largs =
  let nparams = rel_context_nhyps hyps in
  let largs = Array.of_list largs in
  if Array.length largs < nparams then
    raise (IllFormedInd (LocalNotEnoughArgs l));
  let (lpar,largs') = array_chop nparams largs in
  let nhyps = List.length hyps in
  let rec check k index = function
    | [] -> ()
    | (_,Some _,_)::hyps -> check k (index+1) hyps
    | _::hyps ->
        match whd_betadeltaiota env lpar.(k) with
	  | Rel w when w = index -> check (k-1) (index+1) hyps
	  | _ -> raise (IllFormedInd (LocalNonPar (k+1,l)))
  in check (nparams-1) (n-nhyps) hyps;
  if not (array_for_all (noccur_between n ntypes) largs') then
    failwith_non_pos_vect n ntypes largs'

(* Arguments of constructor: check the number of recursive parameters nrecp.
    the first parameters which are constant in recursive arguments
    n is the current depth, nmr is the maximum number of possible
    recursive parameters *)

let check_rec_par (env,n,_,_) hyps nrecp largs =
  let (lpar,_) = list_chop nrecp largs in
  let rec find index =
    function
      | ([],_) -> ()
      | (_,[]) ->
          failwith "number of recursive parameters cannot be greater than the number of parameters."
      | (lp,(_,Some _,_)::hyps) -> find (index-1) (lp,hyps)
      | (p::lp,_::hyps) ->
          (match whd_betadeltaiota env p with
	    | Rel w when w = index -> find (index-1) (lp,hyps)
            | _ -> failwith "bad number of recursive parameters")
  in find (n-1) (lpar,List.rev hyps)

let lambda_implicit_lift n a =
  let lambda_implicit a = Lambda(Anonymous,Evar(0,[||]),a) in
  iterate lambda_implicit n (lift n a)

(* This removes global parameters of the inductive types in lc (for
   nested inductive types only ) *)
let abstract_mind_lc env ntyps npars lc =
  if npars = 0 then
    lc
  else
    let make_abs =
      list_tabulate
	(function i -> lambda_implicit_lift npars (Rel (i+1))) ntyps
    in
    Array.map (substl make_abs) lc

(* [env] is the typing environment
   [n] is the dB of the last inductive type
   [ntypes] is the number of inductive types in the definition
     (i.e. range of inductives is [n; n+ntypes-1])
   [lra] is the list of recursive tree of each variable
 *)
let ienv_push_var (env, n, ntypes, lra) (x,a,ra) =
 (push_rel (x,None,a) env, n+1, ntypes, (Norec,ra)::lra)

let ienv_push_inductive (env, n, ntypes, ra_env) (mi,lpar) =
  let auxntyp = 1 in
  let specif = lookup_mind_specif env mi in
  let env' =
    push_rel (Anonymous,None,
              hnf_prod_applist env (type_of_inductive env specif) lpar) env in
  let ra_env' =
    (Imbr mi,(Rtree.mk_rec_calls 1).(0)) ::
    List.map (fun (r,t) -> (r,Rtree.lift 1 t)) ra_env in
  (* New index of the inductive types *)
  let newidx = n + auxntyp in
  (env', newidx, ntypes, ra_env')

(* The recursive function that checks positivity and builds the list
   of recursive arguments *)
let check_positivity_one (env, _,ntypes,_ as ienv) hyps nrecp i indlc =
  let lparams = rel_context_length hyps in
  (* check the inductive types occur positively in [c] *)
  let rec check_pos (env, n, ntypes, ra_env as ienv) c =
    let x,largs = decompose_app (whd_betadeltaiota env c) in
      match x with
	| Prod (na,b,d) ->
	    assert (largs = []);
            (match weaker_noccur_between env n ntypes b with
		None -> failwith_non_pos_list n ntypes [b]
              | Some b ->
	          check_pos (ienv_push_var ienv (na, b, mk_norec)) d)
	| Rel k ->
            (try
              let (ra,rarg) = List.nth ra_env (k-1) in
	      (match ra with
                  Mrec _ -> check_rec_par ienv hyps nrecp largs
		|  _ -> ());
	      if not (List.for_all (noccur_between n ntypes) largs)
	      then failwith_non_pos_list n ntypes largs
	      else rarg
            with Failure _ | Invalid_argument _ -> mk_norec)
	| Ind ind_kn ->
            (* If the inductive type being defined appears in a
               parameter, then we have an imbricated type *)
            if List.for_all (noccur_between n ntypes) largs then mk_norec
            else check_positive_imbr ienv (ind_kn, largs)
	| err ->
	    if noccur_between n ntypes x &&
              List.for_all (noccur_between n ntypes) largs
	    then mk_norec
	    else failwith_non_pos_list n ntypes (x::largs)

  (* accesses to the environment are not factorised, but is it worth it? *)
  and check_positive_imbr (env,n,ntypes,ra_env as ienv) (mi, largs) =
    let (mib,mip) = lookup_mind_specif env mi in
    let auxnpar = mib.mind_nparams_rec in
    let (lpar,auxlargs) =
      try list_chop auxnpar largs
      with Failure _ -> raise (IllFormedInd (LocalNonPos n)) in
      (* If the inductive appears in the args (non params) then the
	 definition is not positive. *)
      if not (List.for_all (noccur_between n ntypes) auxlargs) then
	raise (IllFormedInd (LocalNonPos n));
      (* We do not deal with imbricated mutual inductive types *)
      let auxntyp = mib.mind_ntypes in
	if auxntyp <> 1 then raise (IllFormedInd (LocalNonPos n));
	(* The nested inductive type with parameters removed *)
	let auxlcvect = abstract_mind_lc env auxntyp auxnpar mip.mind_nf_lc in
	  (* Extends the environment with a variable corresponding to
	     the inductive def *)
	let (env',_,_,_ as ienv') = ienv_push_inductive ienv (mi,lpar) in
	  (* Parameters expressed in env' *)
	let lpar' = List.map (lift auxntyp) lpar in
	let irecargs =
	  (* fails if the inductive type occurs non positively *)
	  (* when substituted *)
	  Array.map
	    (function c ->
	      let c' = hnf_prod_applist env' c lpar' in
		check_constructors ienv' false c')
	    auxlcvect in
	(Rtree.mk_rec [|mk_paths (Imbr mi) irecargs|]).(0)

  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *)

  and check_constructors ienv check_head c =
    let rec check_constr_rec (env,n,ntypes,ra_env as ienv) lrec c =
      let x,largs = decompose_app (whd_betadeltaiota env c) in
	match x with
          | Prod (na,b,d) ->
	      assert (largs = []);
              let recarg = check_pos ienv b in
              let ienv' = ienv_push_var ienv (na,b,mk_norec) in
		check_constr_rec ienv' (recarg::lrec) d

	  | hd ->
	      if check_head then
		if hd = Rel (n+ntypes-i-1) then
		  check_correct_par ienv hyps (ntypes-i) largs
		else
		  raise (IllFormedInd LocalNotConstructor)
	      else
		if not (List.for_all (noccur_between n ntypes) largs)
              then raise (IllFormedInd (LocalNonPos n));
	      List.rev lrec
    in check_constr_rec ienv [] c
  in
  let irecargs =
    Array.map
      (fun c ->
        let _,rawc = mind_extract_params lparams c in
          try
	    check_constructors ienv true rawc
          with IllFormedInd err ->
            explain_ind_err (ntypes-i) env lparams c err)
      indlc
  in mk_paths (Mrec i) irecargs

let check_subtree (t1:'a) (t2:'a) =
  if not (Rtree.compare_rtree (fun t1 t2 ->
    let l1 = fst(Rtree.dest_node t1) in
    let l2 = fst(Rtree.dest_node t2) in
    if l1 = Norec || l1 = l2 then 0 else -1)
    t1 t2) then
    failwith "bad recursive trees"
(* if t1=t2 then () else msg_warning (str"TODO: check recursive positions")*)

let check_positivity env_ar params nrecp inds =
  let ntypes = Array.length inds in
  let rc = Array.mapi (fun j t -> (Mrec j,t)) (Rtree.mk_rec_calls ntypes) in
  let lra_ind = List.rev (Array.to_list rc) in
  let lparams = rel_context_length params in
  let check_one i mip =
    let ra_env =
      list_tabulate (fun _ -> (Norec,mk_norec)) lparams @ lra_ind in
    let ienv = (env_ar, 1+lparams, ntypes, ra_env) in
      check_positivity_one ienv params nrecp i mip.mind_nf_lc
  in
  let irecargs = Array.mapi check_one inds in
  let wfp = Rtree.mk_rec irecargs in
  array_iter2 (fun ind wfpi -> check_subtree ind.mind_recargs wfpi) inds wfp

(************************************************************************)
(************************************************************************)

let check_inductive env kn mib =
  Flags.if_verbose msgnl (str "  checking ind: " ++ pr_mind kn);
  (* check mind_constraints: should be consistent with env *)
  let env = add_constraints mib.mind_constraints env in
  (* check mind_record : TODO ? check #constructor = 1 ? *)
  (* check mind_finite : always OK *)
  (* check mind_ntypes *)
  if Array.length mib.mind_packets <> mib.mind_ntypes then
    error "not the right number of packets";
  (* check mind_hyps: should be empty *)
  if mib.mind_hyps <> empty_named_context then
    error "section context not empty";
  (* check mind_params_ctxt *)
  let params = mib.mind_params_ctxt in
  let _ = check_ctxt env params in
  (* check mind_nparams *)
  if rel_context_nhyps params <> mib.mind_nparams then
    error "number the right number of parameters";
  (* mind_packets *)
  (*  - check arities *)
  let env_ar = typecheck_arity env params mib.mind_packets in
  (*  - check constructor types *)
  Array.iter (typecheck_one_inductive env_ar params mib) mib.mind_packets;
  (* check mind_nparams_rec: positivity condition *)
  check_positivity env_ar params mib.mind_nparams_rec mib.mind_packets;
  (* check mind_equiv... *)
  (* Now we can add the inductive *)
  add_mind kn mib env

