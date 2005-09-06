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
open Univ
open Names
open Term
open Declarations
open Inductive
open Inductiveops
open Environ
open Sign
open Rawterm
open Nameops
open Termops
open Libnames
open Nametab

(****************************************************************************)
(* Tools for printing of Cases                                              *)

let encode_inductive qid =
  let indsp = global_inductive qid in
  let constr_lengths = mis_constr_nargs indsp in
  (indsp,constr_lengths)

(* Parameterization of the translation from constr to ast      *)

(* Tables for Cases printing under a "if" form, a "let" form,  *)

let has_two_constructors lc =
  Array.length lc = 2 (* & lc.(0) = 0 & lc.(1) = 0 *)

let isomorphic_to_tuple lc = (Array.length lc = 1)

let encode_bool r =
  let (_,lc as x) = encode_inductive r in
  if not (has_two_constructors lc) then
    user_err_loc (loc_of_reference r,"encode_if",
      str "This type has not exactly two constructors");
  x

let encode_tuple r =
  let (_,lc as x) = encode_inductive r in
  if not (isomorphic_to_tuple lc) then
    user_err_loc (loc_of_reference r,"encode_tuple",
      str "This type cannot be seen as a tuple type");
  x

module PrintingCasesMake =
  functor (Test : sig 
     val encode : reference -> inductive * int array
     val member_message : std_ppcmds -> bool -> std_ppcmds
     val field : string
     val title : string
  end) ->
  struct
    type t = inductive * int array
    let encode = Test.encode
    let subst subst ((kn,i), ints as obj) =
      let kn' = subst_kn subst kn in
	if kn' == kn then obj else
	  (kn',i), ints
    let printer (ind,_) = pr_global_env Idset.empty (IndRef ind)
    let key = Goptions.SecondaryTable ("Printing",Test.field)
    let title = Test.title
    let member_message x = Test.member_message (printer x)
    let synchronous = true
  end

module PrintingCasesIf =
  PrintingCasesMake (struct 
    let encode = encode_bool
    let field = "If"
    let title = "Types leading to pretty-printing of Cases using a `if' form: "
    let member_message s b =
      str "Cases on elements of " ++ s ++ 
      str
	(if b then " are printed using a `if' form"
         else " are not printed using a `if' form")
  end)

module PrintingCasesLet =
  PrintingCasesMake (struct 
    let encode = encode_tuple
    let field = "Let"
    let title = 
      "Types leading to a pretty-printing of Cases using a `let' form:"
    let member_message s b =
      str "Cases on elements of " ++ s ++
      str
	(if b then " are printed using a `let' form"
         else " are not printed using a `let' form")
  end)

module PrintingIf  = Goptions.MakeRefTable(PrintingCasesIf)
module PrintingLet = Goptions.MakeRefTable(PrintingCasesLet)

let force_let ci =
  let indsp = ci.ci_ind in
  let lc = mis_constr_nargs indsp in PrintingLet.active (indsp,lc)
let force_if ci =
  let indsp = ci.ci_ind in
  let lc = mis_constr_nargs indsp in PrintingIf.active (indsp,lc)

(* Options for printing or not wildcard and synthetisable types *)

open Goptions

let wildcard_value = ref true
let force_wildcard () = !wildcard_value

let _ = declare_bool_option 
	  { optsync  = true;
	    optname  = "forced wildcard";
	    optkey   = SecondaryTable ("Printing","Wildcard");
	    optread  = force_wildcard;
	    optwrite = (:=) wildcard_value }

let synth_type_value = ref true
let synthetize_type () = !synth_type_value

let _ = declare_bool_option 
	  { optsync  = true;
	    optname  = "synthesizability";
	    optkey   = SecondaryTable ("Printing","Synth");
	    optread  = synthetize_type;
	    optwrite = (:=) synth_type_value }

(* Auxiliary function for MutCase printing *)
(* [computable] tries to tell if the predicate typing the result is inferable*)

let computable p k =
    (* We first remove as many lambda as the arity, then we look
       if it remains a lambda for a dependent elimination. This function
       works for normal eta-expanded term. For non eta-expanded or
       non-normal terms, it may affirm the pred is synthetisable
       because of an undetected ultimate dependent variable in the second
       clause, or else, it may affirms the pred non synthetisable
       because of a non normal term in the fourth clause.
       A solution could be to store, in the MutCase, the eta-expanded
       normal form of pred to decide if it depends on its variables

       Lorsque le prédicat est dépendant de manière certaine, on
       ne déclare pas le prédicat synthétisable (même si la
       variable dépendante ne l'est pas effectivement) parce que
       sinon on perd la réciprocité de la synthèse (qui, lui,
       engendrera un prédicat non dépendant) *)

  (nb_lam p = k+1)
  &&
  let _,ccl = decompose_lam p in 
  noccur_between 1 (k+1) ccl


let lookup_name_as_renamed env t s =
  let rec lookup avoid env_names n c = match kind_of_term c with
    | Prod (name,_,c') ->
	(match concrete_name true avoid env_names name c' with
           | (Name id,avoid') -> 
	       if id=s then (Some n) 
	       else lookup avoid' (add_name (Name id) env_names) (n+1) c'
	   | (Anonymous,avoid')    -> lookup avoid' env_names (n+1) (pop c'))
    | LetIn (name,_,_,c') ->
	(match concrete_name true avoid env_names name c' with
           | (Name id,avoid') -> 
	       if id=s then (Some n) 
	       else lookup avoid' (add_name (Name id) env_names) (n+1) c'
	   | (Anonymous,avoid')    -> lookup avoid' env_names (n+1) (pop c'))
    | Cast (c,_) -> lookup avoid env_names n c
    | _ -> None
  in lookup (ids_of_named_context (named_context env)) empty_names_context 1 t

let lookup_index_as_renamed env t n =
  let rec lookup n d c = match kind_of_term c with
    | Prod (name,_,c') ->
	  (match concrete_name true [] empty_names_context name c' with
               (Name _,_) -> lookup n (d+1) c'
             | (Anonymous,_) -> if n=1 then Some d else lookup (n-1) (d+1) c')
    | LetIn (name,_,_,c') ->
	  (match concrete_name true [] empty_names_context name c' with
             | (Name _,_) -> lookup n (d+1) c'
             | (Anonymous,_) -> if n=1 then Some d else lookup (n-1) (d+1) c')
    | Cast (c,_) -> lookup n d c
    | _ -> None
  in lookup n 1 t

let is_nondep_branch c n =
  try
    let _,ccl = decompose_lam_n_assum n c in
    noccur_between 1 n ccl
  with _ -> (* Not eta-expanded or not reduced *)
    false

let extract_nondep_branches test c b n =
  let rec strip n r = if n=0 then r else
    match r with
      | RLambda (_,_,_,t) -> strip (n-1) t
      | RLetIn (_,_,_,t) -> strip (n-1) t
      | _ -> assert false in
  if test c n then Some (strip n b) else None

let detype_case computable detype detype_eqn testdep
    tenv avoid indsp st p k c bl =
  let synth_type = synthetize_type () in
  let tomatch = detype c in

  (* Find constructors arity *)
  let (mib,mip) = Inductive.lookup_mind_specif tenv indsp in
  let get_consnarg j = 
    let typi = mis_nf_constructor_type (indsp,mib,mip) (j+1) in
    let _,t = decompose_prod_n_assum (List.length mip.mind_params_ctxt) typi in
    List.rev (fst (decompose_prod_assum t)) in
  let consnargs = Array.init (Array.length mip.mind_consnames) get_consnarg in
  let consnargsl = Array.map List.length consnargs in
  let alias, aliastyp, newpred, pred = 
    if (not !Options.raw_print) & synth_type & computable & bl <> [||] then
      Anonymous, None, None, None
    else
      let p = option_app detype p in
      match p with
        | None -> Anonymous, None, None, None
        | Some p ->
            let decompose_lam k c =
              let rec lamdec_rec l avoid k c =
                if k = 0 then List.rev l,c else match c with
                  | RLambda (_,x,t,c) -> 
                      lamdec_rec (x::l) (name_cons x avoid) (k-1) c
                  | c -> 
                      let x = next_ident_away (id_of_string "x") avoid in
                      lamdec_rec ((Name x)::l) (x::avoid) (k-1)
                        (let a = RVar (dummy_loc,x) in
                          match c with
                          | RApp (loc,p,l) -> RApp (loc,p,l@[a])
                          | _ -> (RApp (dummy_loc,c,[a])))
              in 
              lamdec_rec [] [] k c in
            let nl,typ = decompose_lam k p in
	    let n,typ = match typ with 
              | RLambda (_,x,t,c) -> x, c
	      | _ -> Anonymous, typ in
	    let aliastyp =
	      if List.for_all ((=) Anonymous) nl then None
	      else 
		let pars = list_tabulate (fun _ -> Anonymous) mip.mind_nparams
		in Some (dummy_loc,indsp,pars@nl) in
            n, aliastyp, Some typ, Some p
  in
  let constructs = Array.init (Array.length bl) (fun i -> (indsp,i+1)) in
  let eqnv = array_map3 detype_eqn constructs consnargsl bl in
  let eqnl = Array.to_list eqnv in
  let tag =
    try 
      if !Options.raw_print then
        RegularStyle
      else if PrintingLet.active (indsp,consnargsl) then
	LetStyle
      else if PrintingIf.active (indsp,consnargsl) then 
	IfStyle
      else 
	st
    with Not_found -> st
  in 
  if tag = RegularStyle then
    RCases (dummy_loc,(pred,ref newpred),[tomatch,ref (alias,aliastyp)],eqnl)
  else
    let bl' = Array.map detype bl in
    if not !Options.v7 && tag = LetStyle && aliastyp = None then
      let rec decomp_lam_force n avoid l p =
	if n = 0 then (List.rev l,p) else
          match p with
            | RLambda (_,na,_,c) -> 
		decomp_lam_force (n-1) (name_cons na avoid) (na::l) c
            | RLetIn (_,na,_,c) -> 
		decomp_lam_force (n-1) (name_cons na avoid) (na::l) c
            | _ ->
		let x = Nameops.next_ident_away (id_of_string "x") avoid in
		decomp_lam_force (n-1) (x::avoid) (Name x :: l) 
                  (* eta-expansion *)
                  (let a = RVar (dummy_loc,x) in
                  match p with
                    | RApp (loc,p,l) -> RApp (loc,p,l@[a])
                    | _ -> (RApp (dummy_loc,p,[a]))) in
      let (nal,d) = decomp_lam_force consnargsl.(0) avoid [] bl'.(0) in
      RLetTuple (dummy_loc,nal,(alias,newpred),tomatch,d)
    else
    let nondepbrs =
      array_map3 (extract_nondep_branches testdep) bl bl' consnargsl in
    if not !Options.v7 && tag = IfStyle && aliastyp = None
      && array_for_all ((<>) None) nondepbrs then
      RIf (dummy_loc,tomatch,(alias,newpred),
           out_some nondepbrs.(0),out_some nondepbrs.(1))
    else if !Options.v7 then
      let rec remove_type avoid args c =
	match c,args with
          | RLambda (loc,na,t,c), _::args ->
              let h = RHole (dummy_loc,BinderType na) in
              RLambda (loc,na,h,remove_type avoid args c)
          | RLetIn (loc,na,b,c), _::args ->
              RLetIn (loc,na,b,remove_type avoid args c)
          | c, (na,None,t)::args ->
              let id = next_name_away_with_default "x" na avoid in
              let h = RHole (dummy_loc,BinderType na) in
              let c = remove_type (id::avoid) args
		(RApp (dummy_loc,c,[RVar (dummy_loc,id)])) in
              RLambda (dummy_loc,Name id,h,c)
          | c, (na,Some b,t)::args ->
              let h = RHole (dummy_loc,BinderType na) in
              let avoid = name_fold (fun x l -> x::l) na avoid in
              RLetIn (dummy_loc,na,h,remove_type avoid args c)
          | c, [] -> c in
      let bl' = array_map2 (remove_type avoid) consnargs bl' in
      ROrderedCase (dummy_loc,tag,pred,tomatch,bl',ref None)
    else
      RCases(dummy_loc,(pred,ref newpred),[tomatch,ref (alias,aliastyp)],eqnl)


let rec detype tenv avoid env t =
  match kind_of_term (collapse_appl t) with
    | Rel n ->
      (try match lookup_name_of_rel n env with
	 | Name id   -> RVar (dummy_loc, id)
	 | Anonymous -> anomaly "detype: index to an anonymous variable"
       with Not_found ->
	 let s = "_UNBOUND_REL_"^(string_of_int n)
	 in RVar (dummy_loc, id_of_string s))
    | Meta n ->
	(* Meta in constr are not user-parsable and are mapped to Evar *)
	REvar (dummy_loc, n, None)
    | Var id ->
	(try
	  let _ = Global.lookup_named id in RRef (dummy_loc, VarRef id)
	 with _ ->
	  RVar (dummy_loc, id))
    | Sort (Prop c) -> RSort (dummy_loc,RProp c)
    | Sort (Type u) -> RSort (dummy_loc,RType (Some u))
    | Cast (c1,c2) ->
	RCast(dummy_loc,detype tenv avoid env c1,
              detype tenv avoid env c2)
    | Prod (na,ty,c) -> detype_binder tenv BProd avoid env na ty c
    | Lambda (na,ty,c) -> detype_binder tenv BLambda avoid env na ty c
    | LetIn (na,b,_,c) -> detype_binder tenv BLetIn avoid env na b c
    | App (f,args) ->
	RApp (dummy_loc,detype tenv avoid env f,
              array_map_to_list (detype tenv avoid env) args)
    | Const sp -> RRef (dummy_loc, ConstRef sp)
    | Evar (ev,cl) ->
        REvar (dummy_loc, ev, 
               Some (List.map (detype tenv avoid env) (Array.to_list cl)))
    | Ind ind_sp ->
	RRef (dummy_loc, IndRef ind_sp)
    | Construct cstr_sp ->
	RRef (dummy_loc, ConstructRef cstr_sp)
    | Case (annot,p,c,bl) ->
	let comp = computable p (annot.ci_pp_info.ind_nargs) in
	let ind = annot.ci_ind in
	let st = annot.ci_pp_info.style in
	detype_case comp (detype tenv avoid env) (detype_eqn tenv avoid env)
	  is_nondep_branch
	  (snd tenv) avoid ind st (Some p) annot.ci_pp_info.ind_nargs c bl
    | Fix (nvn,recdef) -> detype_fix tenv avoid env nvn recdef
    | CoFix (n,recdef) -> detype_cofix tenv avoid env n recdef

and detype_fix tenv avoid env (vn,_ as nvn) (names,tys,bodies) =
  let def_avoid, def_env, lfi =
    Array.fold_left
      (fun (avoid, env, l) na ->
	 let id = next_name_away na avoid in 
	 (id::avoid, add_name (Name id) env, id::l))
      (avoid, env, []) names in
  let n = Array.length tys in
  let v = array_map3
    (fun c t i -> share_names tenv (i+1) [] def_avoid def_env c (lift n t))
    bodies tys vn in
  RRec(dummy_loc,RFix nvn,Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)

and detype_cofix tenv avoid env n (names,tys,bodies) =
  let def_avoid, def_env, lfi =
    Array.fold_left
      (fun (avoid, env, l) na ->
	 let id = next_name_away na avoid in 
	 (id::avoid, add_name (Name id) env, id::l))
      (avoid, env, []) names in
  let ntys = Array.length tys in
  let v = array_map2
    (fun c t -> share_names tenv 0 [] def_avoid def_env c (lift ntys t))
    bodies tys in
  RRec(dummy_loc,RCoFix n,Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)

and share_names tenv n l avoid env c t =
  if !Options.v7 && n=0 then
    let c = detype tenv avoid env c in
    let t = detype tenv avoid env t in
    (List.rev l,c,t)
  else
  match kind_of_term c, kind_of_term t with
    (* factorize even when not necessary to have better presentation *)
    | Lambda (na,t,c), Prod (na',t',c') ->
        let na = match (na,na') with
            Name _, _ -> na
          | _, Name _ -> na'
          | _ -> na in 
        let t = detype tenv avoid env t in
	let id = next_name_away na avoid in 
        let avoid = id::avoid and env = add_name (Name id) env in
        share_names tenv (n-1) ((Name id,None,t)::l) avoid env c c'
    (* May occur for fix built interactively *)
    | LetIn (na,b,t',c), _ when n > 0 ->
        let t' = detype tenv avoid env t' in
        let b = detype tenv avoid env b in
	let id = next_name_away na avoid in 
        let avoid = id::avoid and env = add_name (Name id) env in
        share_names tenv n ((Name id,Some b,t')::l) avoid env c t
    (* Only if built with the f/n notation or w/o let-expansion in types *)
    | _, LetIn (_,b,_,t) when n > 0 ->
	share_names tenv n l avoid env c (subst1 b t)
    (* If it is an open proof: we cheat and eta-expand *)
    | _, Prod (na',t',c') when n > 0 ->
        let t' = detype tenv avoid env t' in
	let id = next_name_away na' avoid in 
        let avoid = id::avoid and env = add_name (Name id) env in
        let appc = mkApp (lift 1 c,[|mkRel 1|]) in
        share_names tenv (n-1) ((Name id,None,t')::l) avoid env appc c'
    (* If built with the f/n notation: we renounce to share names *)
    | _ ->
        if n>0 then warning "Detyping.detype: cannot factorize fix enough";
        let c = detype tenv avoid env c in
        let t = detype tenv avoid env t in
        (List.rev l,c,t)

and detype_eqn tenv avoid env constr construct_nargs branch =
  let make_pat x avoid env b ids =
    if force_wildcard () & noccurn 1 b then
      PatVar (dummy_loc,Anonymous),avoid,(add_name Anonymous env),ids
    else
      let id = next_name_away_with_default "x" x avoid in
      PatVar (dummy_loc,Name id),id::avoid,(add_name (Name id) env),id::ids
  in
  let rec buildrec ids patlist avoid env n b =
    if n=0 then
      (dummy_loc, ids, 
       [PatCstr(dummy_loc, constr, List.rev patlist,Anonymous)],
       detype tenv avoid env b)
    else
      match kind_of_term b with
	| Lambda (x,_,b) -> 
	    let pat,new_avoid,new_env,new_ids = make_pat x avoid env b ids in
            buildrec new_ids (pat::patlist) new_avoid new_env (n-1) b

	| LetIn (x,_,_,b) -> 
	    let pat,new_avoid,new_env,new_ids = make_pat x avoid env b ids in
            buildrec new_ids (pat::patlist) new_avoid new_env (n-1) b

	| Cast (c,_) ->    (* Oui, il y a parfois des cast *)
	    buildrec ids patlist avoid env n c

	| _ -> (* eta-expansion : n'arrivera plus lorsque tous les
                  termes seront construits à partir de la syntaxe Cases *)
            (* nommage de la nouvelle variable *)
	    let new_b = applist (lift 1 b, [mkRel 1]) in
            let pat,new_avoid,new_env,new_ids =
	      make_pat Anonymous avoid env new_b ids in
	    buildrec new_ids (pat::patlist) new_avoid new_env (n-1) new_b
	  
  in 
  buildrec [] [] avoid env construct_nargs branch

and detype_binder tenv bk avoid env na ty c =
  let na',avoid' =
    if bk = BLetIn then
      concrete_let_name (fst tenv) avoid env na c
    else
      concrete_name (fst tenv) avoid env na c in
  let r =  detype tenv avoid' (add_name na' env) c in
  match bk with
    | BProd -> RProd (dummy_loc, na',detype tenv avoid env ty, r)
    | BLambda -> RLambda (dummy_loc, na',detype tenv avoid env ty, r)
    | BLetIn -> RLetIn (dummy_loc, na',detype tenv avoid env ty, r)
