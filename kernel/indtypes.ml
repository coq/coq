(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util
open Names
open Univ
open Term
open Vars
open Context
open Declarations
open Declareops
open Inductive
open Environ
open Reduction
open Typeops
open Entries
open Pp

(* Tell if indices (aka real arguments) contribute to size of inductive type *)
(* If yes, this is compatible with the univalent model *)

let indices_matter = ref false

let enforce_indices_matter () = indices_matter := true
let is_indices_matter () = !indices_matter

(* Same as noccur_between but may perform reductions.
   Could be refined more...  *)
let weaker_noccur_between env x nvars t =
  if noccur_between x nvars t then Some t
  else
   let t' = whd_betadeltaiota env t in
   if noccur_between x nvars t' then Some t'
   else None

let is_constructor_head t =
  isRel(fst(decompose_app t))

(************************************************************************)
(* Various well-formedness check for inductive declarations            *)

(* Errors related to inductive constructions *)
type inductive_error =
  | NonPos of env * constr * constr
  | NotEnoughArgs of env * constr * constr
  | NotConstructor of env * Id.t * constr * constr * int * int
  | NonPar of env * constr * int * constr * constr
  | SameNamesTypes of Id.t
  | SameNamesConstructors of Id.t
  | SameNamesOverlap of Id.t list
  | NotAnArity of env * constr
  | BadEntry
  | LargeNonPropInductiveNotInType

exception InductiveError of inductive_error

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

let check_constructors_names =
  let rec check idset = function
    | [] -> idset
    | c::cl ->
	if Id.Set.mem c idset then
	  raise (InductiveError (SameNamesConstructors c))
	else
	  check (Id.Set.add c idset) cl
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
	if Id.Set.mem id indset then
	  raise (InductiveError (SameNamesTypes id))
	else
	  let cstset' = check_constructors_names cstset cl in
	  check (Id.Set.add id indset) cstset' inds
  in
  check Id.Set.empty Id.Set.empty mie.mind_entry_inds
(* The above verification is not necessary from the kernel point of
  vue since inductive and constructors are not referred to by their
  name, but only by the name of the inductive packet and an index. *)

(************************************************************************)
(************************************************************************)

(* Typing the arities and constructor types *)

(* An inductive definition is a "unit" if it has only one constructor
   and that all arguments expected by this constructor are
   logical, this is the case for equality, conjunction of logical properties
*)
let is_unit constrsinfos =
  match constrsinfos with  (* One info = One constructor *)
   | [level] -> is_type0m_univ level
   | [] -> (* type without constructors *) true
   | _ -> false

let infos_and_sort env ctx t =
  let rec aux env ctx t max =
    let t = whd_betadeltaiota env t in
      match kind_of_term t with
      | Prod (name,c1,c2) ->
        let varj = infer_type env c1 in
	let env1 = Environ.push_rel (name,None,varj.utj_val) env in
	let max = Universe.sup max (univ_of_sort varj.utj_type) in
	  aux env1 ctx c2 max
    | _ when is_constructor_head t -> max
    | _ -> (* don't fail if not positive, it is tested later *) max
  in aux env ctx t Universe.type0m

(* Computing the levels of polymorphic inductive types

   For each inductive type of a block that is of level u_i, we have
   the constraints that u_i >= v_i where v_i is the type level of the
   types of the constructors of this inductive type. Each v_i depends
   of some of the u_i and of an extra (maybe non variable) universe,
   say w_i that summarize all the other constraints. Typically, for
   three inductive types, we could have

   u1,u2,u3,w1 <= u1
   u1       w2 <= u2
      u2,u3,w3 <= u3

   From this system of inequations, we shall deduce

   w1,w2,w3 <= u1
   w1,w2 <= u2
   w1,w2,w3 <= u3
*)

(* This (re)computes informations relevant to extraction and the sort of an
   arity or type constructor; we do not to recompute universes constraints *)

let infer_constructor_packet env_ar_par ctx params lc =
  (* type-check the constructors *)
  let jlc = List.map (infer_type env_ar_par) lc in
  let jlc = Array.of_list jlc in
  (* generalize the constructor over the parameters *)
  let lc'' = Array.map (fun j -> it_mkProd_or_LetIn j.utj_val params) jlc in
  (* compute the max of the sorts of the products of the constructors types *)
  let levels = List.map (infos_and_sort env_ar_par ctx) lc in
  let isunit = is_unit levels in
  let min = if Array.length jlc > 1 then Universe.type0 else Universe.type0m in
  let level = List.fold_left (fun max l -> Universe.sup max l) min levels in
  (lc'', (isunit, level))

(* If indices matter *)
let cumulate_arity_large_levels env sign =
  fst (List.fold_right
    (fun (_,_,t as d) (lev,env) ->
      let tj = infer_type env t in
      let u = univ_of_sort tj.utj_type in
	(Universe.sup u lev, push_rel d env))
    sign (Universe.type0m,env))

let is_impredicative env u =
  is_type0m_univ u || (is_type0_univ u && engagement env = Some ImpredicativeSet)

let param_ccls params =
  let has_some_univ u = function
    | Some v when Univ.Level.equal u v -> true
    | _ -> false
  in
  let remove_some_univ u = function
    | Some v when Univ.Level.equal u v -> None
    | x -> x
  in
  let fold l (_, b, p) = match b with
  | None ->
    (* Parameter contributes to polymorphism only if explicit Type *)
    let c = strip_prod_assum p in
    (* Add Type levels to the ordered list of parameters contributing to *)
    (* polymorphism unless there is aliasing (i.e. non distinct levels) *)
    begin match kind_of_term c with
    | Sort (Type u) ->
      (match Univ.Universe.level u with
      | Some u ->
	if List.exists (has_some_univ u) l then
          None :: List.map (remove_some_univ u) l
	else
          Some u :: l
      | None -> None :: l)
    | _ ->
      None :: l
    end
  | _ -> l
  in
    List.fold_left fold [] params

(* Type-check an inductive definition. Does not check positivity
   conditions. *)
(* TODO check that we don't overgeneralize construcors/inductive arities with
   universes that are absent from them. Is it possible? 
*)
let typecheck_inductive env mie =
  let () = match mie.mind_entry_inds with
  | [] -> anomaly (Pp.str "empty inductive types declaration")
  | _ -> ()
  in
  (* Check unicity of names *)
  mind_check_names mie;
  (* Params are typed-checked here *)
  let env' = push_context mie.mind_entry_universes env in
  let (env_params, params) = infer_local_decls env' mie.mind_entry_params in
  (* We first type arity of each inductive definition *)
  (* This allows building the environment of arities and to share *)
  (* the set of constraints *)
  let env_arities, rev_arity_list =
    List.fold_left
      (fun (env_ar,l) ind ->
         (* Arities (without params) are typed-checked here *)
	 let expltype = ind.mind_entry_template in
         let arity =
	   if isArity ind.mind_entry_arity then
	     let (ctx,s) = dest_arity env_params ind.mind_entry_arity in
	       match s with
	       | Type u when Univ.universe_level u = None ->
	         (** We have an algebraic universe as the conclusion of the arity,
		     typecheck the dummy Π ctx, Prop and do a special case for the conclusion.
		 *)
	         let proparity = infer_type env_params (mkArity (ctx, prop_sort)) in
		 let (cctx, _) = destArity proparity.utj_val in
		   (* Any universe is well-formed, we don't need to check [s] here *)
		   mkArity (cctx, s)
	       | _ -> 
		 let arity = infer_type env_params ind.mind_entry_arity in
		   arity.utj_val
	   else let arity = infer_type env_params ind.mind_entry_arity in
		  arity.utj_val
	 in
	 let (sign, deflev) = dest_arity env_params arity in
	 let inflev = 
	   (* The level of the inductive includes levels of indices if 
	      in indices_matter mode *)
	     if !indices_matter 
	     then Some (cumulate_arity_large_levels env_params sign)
	     else None
	 in
	 (* We do not need to generate the universe of full_arity; if
	    later, after the validation of the inductive definition,
	    full_arity is used as argument or subject to cast, an
	    upper universe will be generated *)
	 let full_arity = it_mkProd_or_LetIn arity params in
	 let id = ind.mind_entry_typename in
	 let env_ar' =
           push_rel (Name id, None, full_arity) env_ar in
             (* (add_constraints cst2 env_ar) in *)
	   (env_ar', (id,full_arity,sign @ params,expltype,deflev,inflev)::l))
      (env',[])
      mie.mind_entry_inds in

  let arity_list = List.rev rev_arity_list in

  (* builds the typing context "Gamma, I1:A1, ... In:An, params" *)
  let env_ar_par = push_rel_context params env_arities in

  (* Now, we type the constructors (without params) *)
  let inds =
    List.fold_right2
      (fun ind arity_data inds ->
	 let (lc',cstrs_univ) =
	   infer_constructor_packet env_ar_par ContextSet.empty
	     params ind.mind_entry_lc in
	 let consnames = ind.mind_entry_consnames in
	 let ind' = (arity_data,consnames,lc',cstrs_univ) in
	   ind'::inds)
      mie.mind_entry_inds
      arity_list
    ([]) in

  let inds = Array.of_list inds in

  (* Compute/check the sorts of the inductive types *)

  let inds =
    Array.map (fun ((id,full_arity,sign,expltype,def_level,inf_level),cn,lc,(is_unit,clev))  ->
      let infu = 
	(** Inferred level, with parameters and constructors. *)
	match inf_level with
	| Some alev -> Universe.sup clev alev
	| None -> clev
      in
      let full_polymorphic () = 
	let defu = Term.univ_of_sort def_level in
	let is_natural =
	  type_in_type env || (check_leq (universes env') infu defu &&
	    not (is_type0m_univ defu && not is_unit))
	in
	let _ =
	  (** Impredicative sort, always allow *)
	  if is_impredicative env defu then ()
	  else (** Predicative case: the inferred level must be lower or equal to the
		   declared level. *)
	    if not is_natural then
	      anomaly ~label:"check_inductive" 
		(Pp.str"Incorrect universe " ++
		   Universe.pr defu ++ Pp.str " declared for inductive type, inferred level is "
		 ++ Universe.pr infu)
	in
	  RegularArity (not is_natural,full_arity,defu)
      in
      let template_polymorphic () =
	let sign, s =
          try dest_arity env full_arity
          with NotArity -> raise (InductiveError (NotAnArity (env, full_arity)))
	in
	  match s with
	  | Type u when expltype (* Explicitly polymorphic *) ->
	    (* The polymorphic level is a function of the level of the *)
	    (* conclusions of the parameters *)
            (* We enforce [u >= lev] in case [lev] has a strict upper *)
            (* constraints over [u] *)
	    let b = type_in_type env || check_leq (universes env') infu u in
	      if not b then
		anomaly ~label:"check_inductive" 
		  (Pp.str"Incorrect universe " ++
		     Universe.pr u ++ Pp.str " declared for inductive type, inferred level is "
		   ++ Universe.pr clev)
	      else
		TemplateArity (param_ccls params, infu)
	  | _ (* Not an explicit occurrence of Type *) ->
	    full_polymorphic ()
      in
      let arity = 
	if mie.mind_entry_polymorphic then full_polymorphic ()
	else template_polymorphic ()
      in
	(id,cn,lc,(sign,arity)))
    inds
  in (env_arities, params, inds)

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

let explain_ind_err id ntyp env0 nbpar c nargs err =
  let (lpar,c') = mind_extract_params nbpar c in
  let env = push_rel_context lpar env0 in
  match err with
    | LocalNonPos kt ->
	raise (InductiveError (NonPos (env,c',mkRel (kt+nbpar))))
    | LocalNotEnoughArgs kt ->
	raise (InductiveError
		 (NotEnoughArgs (env,c',mkRel (kt+nbpar))))
    | LocalNotConstructor ->
	raise (InductiveError
		 (NotConstructor (env,id,c',mkRel (ntyp+nbpar),nbpar,nargs)))
    | LocalNonPar (n,l) ->
	raise (InductiveError
		 (NonPar (env,c',n,mkRel (nbpar-n+1), mkRel (l+nbpar))))

let failwith_non_pos n ntypes c =
  for k = n to n + ntypes - 1 do
    if not (noccurn k c) then raise (IllFormedInd (LocalNonPos (k-n+1)))
  done

let failwith_non_pos_vect n ntypes v =
  Array.iter (failwith_non_pos n ntypes) v;
  anomaly ~label:"failwith_non_pos_vect" (Pp.str "some k in [n;n+ntypes-1] should occur")

let failwith_non_pos_list n ntypes l =
  List.iter (failwith_non_pos n ntypes) l;
  anomaly ~label:"failwith_non_pos_list" (Pp.str "some k in [n;n+ntypes-1] should occur")

(* Check the inductive type is called with the expected parameters *)
let check_correct_par (env,n,ntypes,_) hyps l largs =
  let nparams = rel_context_nhyps hyps in
  let largs = Array.of_list largs in
  if Array.length largs < nparams then
    raise (IllFormedInd (LocalNotEnoughArgs l));
  let (lpar,largs') = Array.chop nparams largs in
  let nhyps = List.length hyps in
  let rec check k index = function
    | [] -> ()
    | (_,Some _,_)::hyps -> check k (index+1) hyps
    | _::hyps ->
        match kind_of_term (whd_betadeltaiota env lpar.(k)) with
	  | Rel w when Int.equal w index -> check (k-1) (index+1) hyps
	  | _ -> raise (IllFormedInd (LocalNonPar (k+1,l)))
  in check (nparams-1) (n-nhyps) hyps;
  if not (Array.for_all (noccur_between n ntypes) largs') then
    failwith_non_pos_vect n ntypes largs'

(* Computes the maximum number of recursive parameters :
    the first parameters which are constant in recursive arguments
    n is the current depth, nmr is the maximum number of possible
    recursive parameters *)

let compute_rec_par (env,n,_,_) hyps nmr largs =
if Int.equal nmr 0 then 0 else
(* start from 0, hyps will be in reverse order *)
  let (lpar,_) = List.chop nmr largs in
  let rec find k index =
      function
	  ([],_) -> nmr
	| (_,[]) -> assert false (* |hyps|>=nmr *)
	| (lp,(_,Some _,_)::hyps) -> find k (index-1) (lp,hyps)
	| (p::lp,_::hyps) ->
       ( match kind_of_term (whd_betadeltaiota env p) with
	  | Rel w when Int.equal w index -> find (k+1) (index-1) (lp,hyps)
          | _ -> k)
  in find 0 (n-1) (lpar,List.rev hyps)

(* [env] is the typing environment
   [n] is the dB of the last inductive type
   [ntypes] is the number of inductive types in the definition
     (i.e. range of inductives is [n; n+ntypes-1])
   [lra] is the list of recursive tree of each variable
 *)
let ienv_push_var (env, n, ntypes, lra) (x,a,ra) =
 (push_rel (x,None,a) env, n+1, ntypes, (Norec,ra)::lra)

let ienv_push_inductive (env, n, ntypes, ra_env) ((mi,u),lpar) =
  let auxntyp = 1 in
  let specif = (lookup_mind_specif env mi, u) in
  let ty = type_of_inductive env specif in
  let env' =
    push_rel (Anonymous,None,
              hnf_prod_applist env ty lpar) env in
  let ra_env' =
    (Imbr mi,(Rtree.mk_rec_calls 1).(0)) ::
    List.map (fun (r,t) -> (r,Rtree.lift 1 t)) ra_env in
  (* New index of the inductive types *)
  let newidx = n + auxntyp in
  (env', newidx, ntypes, ra_env')

let rec ienv_decompose_prod (env,_,_,_ as ienv) n c =
  if Int.equal n 0 then (ienv,c) else
    let c' = whd_betadeltaiota env c in
    match kind_of_term c' with
	Prod(na,a,b) ->
	  let ienv' = ienv_push_var ienv (na,a,mk_norec) in
	  ienv_decompose_prod ienv' (n-1) b
      | _ -> assert false

let array_min nmr a = if Int.equal nmr 0 then 0 else
  Array.fold_left (fun k (nmri,_) -> min k nmri) nmr a

(* The recursive function that checks positivity and builds the list
   of recursive arguments *)
let check_positivity_one (env,_,ntypes,_ as ienv) hyps (_,i as ind) nargs lcnames indlc =
  let lparams = rel_context_length hyps in
  let nmr = rel_context_nhyps hyps in
  (* Checking the (strict) positivity of a constructor argument type [c] *)
  let rec check_pos (env, n, ntypes, ra_env as ienv) nmr c =
    let x,largs = decompose_app (whd_betadeltaiota env c) in
      match kind_of_term x with
	| Prod (na,b,d) ->
	    let () = assert (List.is_empty largs) in
            (match weaker_noccur_between env n ntypes b with
		None -> failwith_non_pos_list n ntypes [b]
              | Some b ->
	          check_pos (ienv_push_var ienv (na, b, mk_norec)) nmr d)
	| Rel k ->
            (try let (ra,rarg) = List.nth ra_env (k-1) in
	    let nmr1 =
	      (match ra with
                  Mrec _ -> compute_rec_par ienv hyps nmr largs
		|  _ -> nmr)
	    in
	      if not (List.for_all (noccur_between n ntypes) largs)
	      then failwith_non_pos_list n ntypes largs
	      else (nmr1,rarg)
              with Failure _ | Invalid_argument _ -> (nmr,mk_norec))
	| Ind ind_kn ->
            (* If the inductive type being defined appears in a
               parameter, then we have a nested indtype *)
            if List.for_all (noccur_between n ntypes) largs then (nmr,mk_norec)
            else check_positive_nested ienv nmr (ind_kn, largs)
	| err ->
	    if noccur_between n ntypes x &&
              List.for_all (noccur_between n ntypes) largs
	    then (nmr,mk_norec)
	    else failwith_non_pos_list n ntypes (x::largs)

  (* accesses to the environment are not factorised, but is it worth? *)
  and check_positive_nested (env,n,ntypes,ra_env as ienv) nmr ((mi,u), largs) =
    let (mib,mip) = lookup_mind_specif env mi in
    let auxnpar = mib.mind_nparams_rec in
    let nonrecpar = mib.mind_nparams - auxnpar in
    let (lpar,auxlargs) =
      try List.chop auxnpar largs
      with Failure _ -> raise (IllFormedInd (LocalNonPos n)) in
      (* If the inductive appears in the args (non params) then the
	 definition is not positive. *)

      if not (List.for_all (noccur_between n ntypes) auxlargs) then
	failwith_non_pos_list n ntypes auxlargs;
      (* We do not deal with imbricated mutual inductive types *)
      let auxntyp = mib.mind_ntypes in
	if not (Int.equal auxntyp 1) then raise (IllFormedInd (LocalNonPos n));
	(* The nested inductive type with parameters removed *)
	let auxlcvect = abstract_mind_lc auxntyp auxnpar mip.mind_nf_lc in
	  (* Extends the environment with a variable corresponding to
	     the inductive def *)
	let (env',_,_,_ as ienv') = ienv_push_inductive ienv ((mi,u),lpar) in
	  (* Parameters expressed in env' *)
	let lpar' = List.map (lift auxntyp) lpar in
	let irecargs_nmr =
	  (* fails if the inductive type occurs non positively *)
	  (* with recursive parameters substituted *)
	  Array.map
	    (function c ->
	      let c' = hnf_prod_applist env' c lpar' in
	      (* skip non-recursive parameters *)
	      let (ienv',c') = ienv_decompose_prod ienv' nonrecpar c' in
		check_constructors ienv' false nmr c')
	    auxlcvect
	in
	let irecargs = Array.map snd irecargs_nmr
	and nmr' = array_min nmr irecargs_nmr
	in
	  (nmr',(Rtree.mk_rec [|mk_paths (Imbr mi) irecargs|]).(0))

  (* check the inductive types occur positively in the products of C, if
     check_head=true, also check the head corresponds to a constructor of
     the ith type *)

  and check_constructors ienv check_head nmr c =
    let rec check_constr_rec (env,n,ntypes,ra_env as ienv) nmr lrec c =
      let x,largs = decompose_app (whd_betadeltaiota env c) in
	match kind_of_term x with

          | Prod (na,b,d) ->
	      let () = assert (List.is_empty largs) in
              let nmr',recarg = check_pos ienv nmr b in
              let ienv' = ienv_push_var ienv (na,b,mk_norec) in
                check_constr_rec ienv' nmr' (recarg::lrec) d
          | hd ->
            let () =
              if check_head then
                begin match hd with
                | Rel j when Int.equal j (n + ntypes - i - 1) ->
                  check_correct_par ienv hyps (ntypes - i) largs
                | _ -> raise (IllFormedInd LocalNotConstructor)
                end
              else
                if not (List.for_all (noccur_between n ntypes) largs)
                then failwith_non_pos_list n ntypes largs
            in
            (nmr, List.rev lrec)
    in check_constr_rec ienv nmr [] c
  in
  let irecargs_nmr =
    Array.map2
      (fun id c ->
        let _,rawc = mind_extract_params lparams c in
          try
	    check_constructors ienv true nmr rawc
          with IllFormedInd err ->
	    explain_ind_err id (ntypes-i) env lparams c nargs err)
      (Array.of_list lcnames) indlc
  in
  let irecargs = Array.map snd irecargs_nmr
  and nmr' = array_min nmr irecargs_nmr
  in (nmr', mk_paths (Mrec ind) irecargs)

let check_positivity kn env_ar params inds =
  let ntypes = Array.length inds in
  let rc = Array.mapi (fun j t -> (Mrec (kn,j),t)) (Rtree.mk_rec_calls ntypes) in
  let lra_ind = Array.rev_to_list rc in
  let lparams = rel_context_length params in
  let nmr = rel_context_nhyps params in
  let check_one i (_,lcnames,lc,(sign,_)) =
    let ra_env =
      List.init lparams (fun _ -> (Norec,mk_norec)) @ lra_ind in
    let ienv = (env_ar, 1+lparams, ntypes, ra_env) in
    let nargs = rel_context_nhyps sign - nmr in
    check_positivity_one ienv params (kn,i) nargs lcnames lc
  in
  let irecargs_nmr = Array.mapi check_one inds in
  let irecargs = Array.map snd irecargs_nmr
  and nmr' = array_min nmr irecargs_nmr
  in (nmr',Rtree.mk_rec irecargs)


(************************************************************************)
(************************************************************************)
(* Build the inductive packet *)

(* Allowed eliminations *)

let all_sorts = [InProp;InSet;InType]
let small_sorts = [InProp;InSet]
let logical_sorts = [InProp]

let allowed_sorts is_smashed s =
  if not is_smashed 
  then (** Naturally in the defined sort.
	   If [s] is Prop, it must be small and unitary.
	   Unsmashed, predicative Type and Set: all elimination allowed
	   as well. *)
      all_sorts
  else 
    match family_of_sort s with
    (* Type: all elimination allowed: above and below *)
    | InType -> all_sorts
    (* Smashed Set is necessarily impredicative: forbids large elimination *)
    | InSet -> small_sorts
    (* Smashed to Prop, no informative eliminations allowed *)
    | InProp -> logical_sorts
    
(* Previous comment: *)
(* Unitary/empty Prop: elimination to all sorts are realizable *)
(* unless the type is large. If it is large, forbids large elimination *)
(* which otherwise allows simulating the inconsistent system Type:Type. *)
(* -> this is now handled by is_smashed: *)
(* - all_sorts in case of small, unitary Prop (not smashed) *)
(* - logical_sorts in case of large, unitary Prop (smashed) *)

let arity_conclusion = function
  | RegularArity (_, c, _) -> c
  | TemplateArity (_, s) -> mkType s

let fold_inductive_blocks f =
  Array.fold_left (fun acc (_,_,lc,(arsign,ar)) ->
    f (Array.fold_left f acc lc) (it_mkProd_or_LetIn (arity_conclusion ar) arsign))

let used_section_variables env inds =
  let ids = fold_inductive_blocks
    (fun l c -> Id.Set.union (Environ.global_vars_set env c) l)
      Id.Set.empty inds in
  keep_hyps env ids

let rel_vect n m = Array.init m (fun i -> mkRel(n+m-i))
let rel_appvect n m = rel_vect n (List.length m)

exception UndefinableExpansion

(** From a rel context describing the constructor arguments,
    build an expansion function.
    The term built is expecting to be substituted first by 
    a substitution of the form [params, x : ind params] *)
let compute_projections ((kn, _ as ind), u as indsp) n x nparamargs params
    mind_consnrealdecls mind_consnrealargs ctx =
  let mp, dp, l = repr_mind kn in
  let rp = mkApp (mkIndU indsp, rel_vect 0 nparamargs) in
  let ci = 
    let print_info =
      { ind_tags = []; cstr_tags = [|rel_context_tags ctx|]; style = LetStyle } in
      { ci_ind     = ind;
	ci_npar    = nparamargs;
	ci_cstr_ndecls = mind_consnrealdecls;
	ci_cstr_nargs = mind_consnrealargs;
	ci_pp_info = print_info }
  in
  let len = List.length ctx in
  let x = Name x in
  let compat_body ccl i = 
    (* [ccl] is defined in context [params;x:rp] *)
    (* [ccl'] is defined in context [params;x:rp;x:rp] *)
    let ccl' = liftn 1 2 ccl in
    let p = mkLambda (x, lift 1 rp, ccl') in
    let branch = it_mkLambda_or_LetIn (mkRel (len - i)) ctx in
    let body = mkCase (ci, p, mkRel 1, [|lift 1 branch|]) in
      it_mkLambda_or_LetIn (mkLambda (x,rp,body)) params
  in
  let projections (na, b, t) (i, j, kns, pbs, subst) =
    match b with
    | Some c -> (i, j+1, kns, pbs, substl subst c :: subst)
    | None ->
      match na with
      | Name id ->
	let kn = Constant.make1 (KerName.make mp dp (Label.of_id id)) in
	let ty = substl subst (liftn 1 j t) in
	let term = mkProj (Projection.make kn true, mkRel 1) in
	let fterm = mkProj (Projection.make kn false, mkRel 1) in
	let compat = compat_body ty (j - 1) in
	let etab = it_mkLambda_or_LetIn (mkLambda (x, rp, term)) params in
	let etat = it_mkProd_or_LetIn (mkProd (x, rp, ty)) params in
	let body = { proj_ind = fst ind; proj_npars = nparamargs;
		     proj_arg = i; proj_type = ty; proj_eta = etab, etat; 
		     proj_body = compat } in
	  (i + 1, j + 1, kn :: kns, body :: pbs, fterm :: subst)
      | Anonymous -> raise UndefinableExpansion
  in
  let (_, _, kns, pbs, subst) = List.fold_right projections ctx (0, 1, [], [], []) in
    Array.of_list (List.rev kns),
    Array.of_list (List.rev pbs)

let build_inductive env p prv ctx env_ar params kn isrecord isfinite inds nmr recargs =
  let ntypes = Array.length inds in
  (* Compute the set of used section variables *)
  let hyps = used_section_variables env inds in
  let nparamargs = rel_context_nhyps params in
  let nparamdecls = rel_context_length params in
  let subst, ctx = Univ.abstract_universes p ctx in
  let params = Vars.subst_univs_level_context subst params in
  let env_ar = 
    let ctx = Environ.rel_context env_ar in 
    let ctx' = Vars.subst_univs_level_context subst ctx in
      Environ.push_rel_context ctx' env
  in
  (* Check one inductive *)
  let build_one_packet (id,cnames,lc,(ar_sign,ar_kind)) recarg =
    (* Type of constructors in normal form *)
    let lc = Array.map (Vars.subst_univs_level_constr subst) lc in
    let splayed_lc = Array.map (dest_prod_assum env_ar) lc in
    let nf_lc = Array.map (fun (d,b) -> it_mkProd_or_LetIn b d) splayed_lc in
    let consnrealdecls =
      Array.map (fun (d,_) -> rel_context_length d - rel_context_length params)
	splayed_lc in
    let consnrealargs =
      Array.map (fun (d,_) -> rel_context_nhyps d - rel_context_nhyps params)
	splayed_lc in
    (* Elimination sorts *)
    let arkind,kelim = 
      match ar_kind with
      | TemplateArity (paramlevs, lev) -> 
	let ar = {template_param_levels = paramlevs; template_level = lev} in
	  TemplateArity ar, all_sorts
      | RegularArity (info,ar,defs) ->
	let s = sort_of_univ defs in
	let kelim = allowed_sorts info s in
	let ar = RegularArity 
	  { mind_user_arity = Vars.subst_univs_level_constr subst ar; 
	    mind_sort = sort_of_univ (Univ.subst_univs_level_universe subst defs); } in
	  ar, kelim in
    (* Assigning VM tags to constructors *)
    let nconst, nblock = ref 0, ref 0 in
    let transf num =
      let arity = List.length (dest_subterms recarg).(num) in
	if Int.equal arity 0 then
	  let p  = (!nconst, 0) in
	    incr nconst; p
	else
	  let p = (!nblock + 1, arity) in
	    incr nblock; p
	      (* les tag des constructeur constant commence a 0,
		 les tag des constructeur non constant a 1 (0 => accumulator) *)
    in
    let rtbl = Array.init (List.length cnames) transf in
      (* Build the inductive packet *)
      { mind_typename = id;
	mind_arity = arkind;
	mind_arity_ctxt = Vars.subst_univs_level_context subst ar_sign;
	mind_nrealargs = rel_context_nhyps ar_sign - nparamargs;
	mind_nrealdecls = rel_context_length ar_sign - nparamdecls;
	mind_kelim = kelim;
	mind_consnames = Array.of_list cnames;
	mind_consnrealdecls = consnrealdecls;
	mind_consnrealargs = consnrealargs;
	mind_user_lc = lc;
	mind_nf_lc = nf_lc;
	mind_recargs = recarg;
	mind_nb_constant = !nconst;
	mind_nb_args = !nblock;
	mind_reloc_tbl = rtbl;
      } in
  let packets = Array.map2 build_one_packet inds recargs in
  let pkt = packets.(0) in	  
  let isrecord = 
    match isrecord with
    | Some (Some rid) when pkt.mind_kelim == all_sorts && Array.length pkt.mind_consnames == 1
			   && pkt.mind_consnrealargs.(0) > 0 ->
      (** The elimination criterion ensures that all projections can be defined. *)
      let u = 
	if p then 
	  subst_univs_level_instance subst (Univ.UContext.instance ctx)
	else Univ.Instance.empty 
      in
      let indsp = ((kn, 0), u) in
      let rctx, _ = decompose_prod_assum (subst1 (mkIndU indsp) pkt.mind_nf_lc.(0)) in
	(try 
	   let fields = List.firstn pkt.mind_consnrealdecls.(0) rctx in
	   let kns, projs = 
	     compute_projections indsp pkt.mind_typename rid nparamargs params
	       pkt.mind_consnrealdecls pkt.mind_consnrealargs fields
	   in Some (Some (rid, kns, projs))
	 with UndefinableExpansion -> Some None)
    | Some _ -> Some None
    | None -> None
  in
    (* Build the mutual inductive *)
    { mind_record = isrecord;
      mind_ntypes = ntypes;
      mind_finite = isfinite;
      mind_hyps = hyps;
      mind_nparams = nparamargs;
      mind_nparams_rec = nmr;
      mind_params_ctxt = params;
      mind_packets = packets;
      mind_polymorphic = p;
      mind_universes = ctx;
      mind_private = prv;
    }

(************************************************************************)
(************************************************************************)

let check_inductive env kn mie =
  (* First type-check the inductive definition *)
  let (env_ar, params, inds) = typecheck_inductive env mie in
  (* Then check positivity conditions *)
  let (nmr,recargs) = check_positivity kn env_ar params inds in
  (* Build the inductive packets *)
    build_inductive env mie.mind_entry_polymorphic mie.mind_entry_private
      mie.mind_entry_universes
      env_ar params kn mie.mind_entry_record mie.mind_entry_finite
      inds nmr recargs
