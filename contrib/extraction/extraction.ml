(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Declarations
open Environ
open Reduction
open Inductive
open Instantiate
open Miniml
open Mlimport
open Closure

(*s Extraction results. *)

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* The flag [type_var] gives us information about an identifier
   coming from a Lambda or a Product:
   \begin{itemize}
   \item [Varity] denotes identifiers of type an arity of sort [Set]
     or [Type], that is $(x_1:X_1)\ldots(x_n:X_n)s$ with [s = Set] or [Type] 
   \item [Vprop] denotes identifiers of type an arity of sort [Prop], 
     or of type of type [Prop] 
   \item [Vdefault] represents the other cases. It may be inexact after 
   instanciation. For example [(X:Type)X] is [Vdefault] and may give [Set]
   after instanciation, which is rather [Varity]
   \end{itemize} *)

type type_var = Varity | Vprop | Vdefault

type signature = (type_var * identifier) list

(* When dealing with CIC contexts, we maintain corresponding contexts 
   made of [type_var] *)

type extraction_context = type_var list

(* The [type_extraction_result] is the result of the [extract_type] function
   that extracts a CIC object into an ML type. It is either: 
   \begin{itemize}
   \item a real ML type, followed by its signature and its list of dummy fresh 
     type variables (called flexible variables)
   \item a CIC arity, without counterpart in ML
   \item a non-informative type, which will receive special treatment
   \end{itemize} *)

type type_extraction_result =
  | Tmltype of ml_type * signature * identifier list
  | Tarity
  | Tprop

(* The [term_extraction_result] is the result of the [extract_term]
   function that extracts a CIC object into an ML term *)

type term_extraction_result = 
  | Rmlterm of ml_ast
  | Rprop

(* The [extraction_result] is the result of the [extract_constr]
   function that extracts any CIC object. It is either a ML type, a ML
   object or something non-informative. *)

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast
  | Eprop

(*s Utility functions. *)

let whd_betaiotalet = clos_norm_flags (UNIFORM, red_add betaiota_red ZETA)

(* Translation between [Type_extraction_result] and [type_var]. *)

let v_of_t = function
  | Tprop -> Vprop
  | Tarity -> Varity
  | Tmltype _ -> Vdefault

type lamprod = Lam | Prod

(* FIXME: to be moved somewhere else *)
let array_foldi f a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i a.(i) v) in
  fold 0

let flexible_name = id_of_string "flex"

let id_of_name = function
  | Anonymous -> id_of_string "_"
  | Name id   -> id

(* This function [params_of_sign] extracts the type parameters ('a in Caml)
   from a signature. *)

let params_of_sign = 
  List.fold_left (fun l v -> match v with Varity,id -> id :: l | _ -> l) []

(* [get_arity c] returns [Some s] if [c] is an arity of sort [s], 
   and [None] otherwise. *)

let rec get_arity env c =
  match kind_of_term (whd_betadeltaiota env Evd.empty c) with
    | IsProd (x,t,c0) -> get_arity (push_rel_assum (x,t) env) c0
    | IsCast (t,_) -> get_arity env t
    | IsSort s -> Some s
    | _ -> None

(* idem, but goes through [Lambda] as well. Cf. [find_conclusion]. *)

let rec get_lam_arity env c =
  match kind_of_term (whd_betadeltaiota env Evd.empty c) with
    | IsLambda (x,t,c0) -> get_lam_arity (push_rel_assum (x,t) env) c0
    | IsProd (x,t,c0) -> get_lam_arity (push_rel_assum (x,t) env) c0
    | IsCast (t,_) -> get_lam_arity env t
    | IsSort s -> Some s
    | _ -> None

(* Detection of non-informative parts. *)

let is_non_info_sort env s = is_Prop (whd_betadeltaiota env Evd.empty s)

let is_non_info_type env t = 
  let s = Typing.type_of env Evd.empty t in
  (is_non_info_sort env s) || ((get_arity env t) = (Some (Prop Null)))

let is_non_info_term env c = 
  let t = Typing.type_of env Evd.empty c in
  let s = Typing.type_of env Evd.empty t in
  (is_non_info_sort env s) ||
  match get_arity env t with 
    | Some (Prop Null) -> true
    | Some (Type _) -> (get_lam_arity env c = Some (Prop Null))
    | _ -> false


(* The next function transforms a type [t] into a [type_var] flag. *)

let v_of_arity env t = match get_arity env t with
  | Some (Prop Null) -> Vprop
  | Some _ -> Varity 
  | _ -> if (is_non_info_type env t) then Vprop else Vdefault
      

(* The next function transforms an arity into a signature. It is used 
   for example with the types of inductive definitions, which are known
   to be already in arity form. *)

let rec signature_of_arity env c = match kind_of_term c with
  | IsProd (n, t, c') ->
      let env' = push_rel (n,None,t) env in
      let id = id_of_name n in
      (v_of_arity env t, id) :: (signature_of_arity env' c')
  | IsSort _ -> 
      []
  | _ ->
      assert false

(* [list_of_ml_arrows] applied to the ML type [a->b->]\dots[z->t]
   returns the list [[a;b;...;z]]. It is used when making the ML types
   of inductive definitions. *)

let rec list_of_ml_arrows = function
  | Tarr (a, b) -> a :: list_of_ml_arrows b
  | t -> []

(* [renum_db] gives the new de Bruijn indices for variables in an ML
   term.  This translation is made according to a context: only
   variables corresponding to a real ML type are keeped *)
	
let renum_db ctx n = 
  let rec renum = function
    | (1, Vdefault :: _) -> 1
    | (n, Vdefault :: s) -> succ (renum (pred n, s))
    | (n,        _ :: s) -> renum (pred n, s)
    | _ -> assert false
  in
  renum (n, ctx)

(*s Environment for the bodies of some mutual fixpoints. *)

let push_many_rels env binders =  
    List.fold_left (fun e (f,t) -> push_rel (f,None,t) e) env binders

let rec push_many_rels_ctx env ctx = function
  | (fi,ti) :: l -> 
      push_many_rels_ctx 
	(push_rel (fi,None,ti) env) ((v_of_arity env ti)::ctx) l
  | [] ->
      (env, ctx)

let fix_environment env ctx fl tl =
  push_many_rels_ctx env ctx (List.combine fl (Array.to_list tl))

(* Decomposition of a type beginning with at least n products when reduced *)

let decompose_prod_reduce n env c = 
  let c = 
    if nb_prod c >= n then 
      c 
    else 
      whd_betadeltaiota env Evd.empty c 
  in decompose_prod_n n c

(* Decomposition of a function expecting n arguments at least. We eta-expanse
   if needed *)

let decompose_lam_eta n env c = 
  let dif = n - (nb_lam c) in 
  if (dif <= 0) then 
    decompose_lam_n n c
  else 
    let tyc = Typing.type_of env Evd.empty c in
    let (type_binders,_) = decompose_prod_reduce n env tyc in
    let (binders, e) = decompose_lam c in 
    let binders = (list_firstn dif type_binders) @ binders in 
    let e =
      applist (lift dif e, List.rev_map mkRel (interval 1 dif)) in
    (binders, e)


(*s Tables to keep the extraction of inductive types and constructors. *)

type inductive_extraction_result = signature * identifier list

let inductive_extraction_table = 
  ref (Gmap.empty : (inductive_path, inductive_extraction_result) Gmap.t)

let add_inductive_extraction i e = 
  inductive_extraction_table := Gmap.add i e !inductive_extraction_table

let lookup_inductive_extraction i = Gmap.find i !inductive_extraction_table

type constructor_extraction_result = ml_type list * signature

let constructor_extraction_table = 
  ref (Gmap.empty : (constructor_path, constructor_extraction_result) Gmap.t)

let add_constructor_extraction c e = 
  constructor_extraction_table := Gmap.add c e !constructor_extraction_table

let lookup_constructor_extraction i = Gmap.find i !constructor_extraction_table

(*s Extraction of a type. *)

(* When calling [extract_type] we suppose that the type of [c] is an
   arity.  This is for example checked in [extract_constr]. 

   Relation with [v_of_arity]: it is less precise, since we do not 
   delta-reduce in [extract_type] in general.
   \begin{itemize}
   \item If [v_of_arity env t = Vdefault], 
   then [extract_type env t] is a [Tmltype].
   \item If [extract_type env t = Tprop], then [v_of_arity env t = Vprop]
   \item If [extract_type env t = Tarity], then [v_of_arity env t = Varity]
   \end{itemize} *)

let rec extract_type env c =
  let rec extract_rec env fl c args = 
    (* We accumulate the two contexts, the generated flexible 
       variables, and the arguments of [c]. *) 
    let ty = Typing.type_of env Evd.empty (applist (c, args)) in
    (* Since [ty] is an arity, there is two non-informative case: 
       [ty] is an arity of sort [Prop], or 
       [c] has a non-informative head symbol *)
    match get_arity env ty with 
      | None -> 
	  assert false (* Cf. precondition. *)
      | Some (Prop Null) ->
	  Tprop 
      | Some _ -> 
	  (match (kind_of_term (whd_betaiotalet env Evd.empty c)) with
	    | IsSort (Prop Null) ->
		assert (args = []); (* A sort can't be applied. *)
		Tprop 
	    | IsSort _ ->
		assert (args = []); (* A sort can't be applied. *)
		Tarity 
	    | IsProd (n,t,d) ->
		assert (args = []); (* A product can't be applied. *)
		extract_prod_lam env fl (n,t,d) Prod
	    | IsLambda (n,t,d) ->
		assert (args = []); (* [c] is now in head normal form. *)
		extract_prod_lam env fl (n,t,d) Lam
	    | IsApp (d, args') ->
		(* We just accumulate the arguments. *)
		extract_rec env fl d (Array.to_list args' @ args)
	    | IsRel n -> 
		(match lookup_rel_value n env with
		   | Some t -> 
		       extract_rec env fl t args  
		   | None ->
		       let id = id_of_name (fst (lookup_rel_type n env)) in 
		       Tmltype (Tvar id, [], fl))
	    | IsConst (sp,a) ->
		let cty = constant_type env Evd.empty (sp,a) in 
		if is_arity env Evd.empty cty then
		  (match extract_constant sp with
		     | Emltype (_, sc, flc) -> 
			 extract_type_app env fl (ConstRef sp,sc,flc) args
		     | Eprop -> 
			 Tprop
		     | Emlterm _ -> 
			 assert false 
			 (* [cty] is of type an arity. *))
		else 
		  (* We can't keep as ML type abbreviation a CIC constant 
		     which type is not an arity: we reduce this constant. *)
		  let cvalue = constant_value env (sp,a) in
		  extract_rec env fl (applist (cvalue, args)) []
	    | IsMutInd (spi,_) ->
		let (si,fli) = extract_inductive spi in
		extract_type_app env fl (IndRef spi,si,fli) args
	    | IsMutCase _ 
	    | IsFix _ ->
		let id = next_ident_away flexible_name fl in
		Tmltype (Tvar id, [], id :: fl)
		(* CIC type without counterpart in ML: we generate a 
		   new flexible type variable. *) 
	    | IsCast (c, _) ->
		extract_rec env fl c args
	    | _ -> 
		assert false)

  (* Auxiliary function used to factor code in lambda and product cases *)

  and extract_prod_lam env fl (n,t,d) flag = 
    let id = id_of_name n in (* FIXME: capture problem *)
    let env' = push_rel (n,None,t) env in
    let tag = v_of_arity env t in
    if tag = Vdefault && flag = Prod then
      (match extract_rec env fl t [] with
	 | Tprop | Tarity -> assert false 
	       (* Cf. relation between [extract_type] and [v_of_arity] *)
	 | Tmltype (mlt,_,fl') -> 
	     (match extract_rec env' fl' d [] with 
		| Tmltype (mld, sign, fl'') -> 
		    Tmltype (Tarr(mlt,mld), (tag,id)::sign, fl'')
		| et -> et))
    else
      (match extract_rec env' fl d [] with 
	 | Tmltype (mld, sign, fl'') ->
	     Tmltype (mld, (tag,id)::sign, fl'')
	 | et -> et)

 (* Auxiliary function dealing with type application. 
    Precondition: [r] is of type an arity. *)
		  
  and extract_type_app env fl (r,sc,flc) args =
    let nargs = List.length args in
    assert (List.length sc >= nargs); 
    (* [r] is of type an arity, so it can't be applied to more than n args, 
       where n is the number of products in this arity type. *)
    let (sign_args,sign_rest) = list_chop nargs sc in
    let (mlargs,fl') = 
      List.fold_right 
	(fun (v,a) ((args,fl) as acc) -> match v with
	   | (Vdefault | Vprop), _ -> acc
	   | Varity,_ -> match extract_rec env fl a [] with
	       | Tarity -> (Miniml.Tarity :: args, fl) 
  	         (* we pass a dummy type [arity] as argument *)
	       | Tprop -> (Miniml.Tprop :: args, fl)
	       | Tmltype (mla,_,fl') -> (mla :: args, fl'))
	(List.combine sign_args args) 
	([],fl)
    in
    let flc = List.map (fun i -> Tvar i) flc in
    Tmltype (Tapp ((Tglob r) :: mlargs @ flc), sign_rest, fl')
      
  in
  extract_rec env [] c []
    
    
(*s Extraction of a term. 
    Precondition: [c] has a type which is not an arity. 
    This is normaly checked in [extract_constr]. *)

and extract_term env ctx c = 
  let t = Typing.type_of env Evd.empty c in
  extract_term_with_type env ctx c t

and extract_term_with_type env ctx c t =
  let s = Typing.type_of env Evd.empty t in
  (* The only non-informative case: [s] is [Prop] *)
  if is_Prop (whd_betadeltaiota env Evd.empty s) then
    Rprop
  else match kind_of_term c with
    | IsLambda (n, t, d) ->
	let id = id_of_name n in
	let v = v_of_arity env t in 
	let env' = push_rel (n,None,t) env in
	let ctx' = v :: ctx in
	let d' = extract_term env' ctx' d in 
	(* If [d] was of type an arity, [c] too would be so *)
	(match v with
	   | Varity | Vprop -> d'
	   | Vdefault -> match d' with
	       | Rmlterm a -> Rmlterm (MLlam (id, a))
	       | Rprop -> assert false (* Cf. rem. above *))
    | IsRel n ->
	(* TODO : magic or not *) 
	(match List.nth ctx (pred n) with
	   | Varity -> assert false (* Cf. precondition *)
	   | Vprop -> assert false
	   | Vdefault -> Rmlterm (MLrel (renum_db ctx n))) 
    | IsApp (f,a) ->
	let tyf = Typing.type_of env Evd.empty f in
	let tyf = 
	  if nb_prod tyf >= Array.length a then 
	    tyf 
	  else 
	    whd_betadeltaiota env Evd.empty tyf 
	in
	(match extract_type env tyf with
	   | Tmltype (_,s,_) -> 
	       extract_app env ctx (f,tyf,s) (Array.to_list a) 
	   | Tarity -> assert false (* Cf. precondition *)
	   | Tprop -> assert false)
    | IsConst (sp,_) ->
	Rmlterm (MLglob (ConstRef sp))
    | IsMutConstruct (cp,_) ->
	Rmlterm (MLglob (ConstructRef cp)) (* TODO eta-expansion *)
    | IsMutCase ((ni,(ip,cnames,_,_,_)),p,c,br) ->
	let extract_branch j b =
	  let (_,s) = extract_constructor (ip,succ j) in
	  assert (List.length s = ni.(j));
	  (* number of arguments, without parameters *)
	  let (binders,e) = decompose_lam_eta ni.(j) env b in
	  let binders = List.rev binders in
	  let (env',ctx') = push_many_rels_ctx env ctx binders in
	  (* Some patological cases need an extract_constr here 
	     rather than an extract_term. See exemples in test_extraction.v *)
	  let e' = match extract_constr env' ctx' e with
	    | Eprop -> MLprop
	    | Emltype _ -> MLarity
	    | Emlterm a -> a
	  in
	  let ids = 
	    List.fold_right 
	      (fun ((v,_),(n,_)) acc ->
		 if v = Vdefault then (id_of_name n :: acc) else acc)
	      (List.combine s binders) []
	  in
	  (cnames.(j), ids, e')
	in
	(* c has an  inductive type, not an arity type *)
	(match extract_term env ctx c with
	   | Rmlterm a -> Rmlterm (MLcase (a, Array.mapi extract_branch br))
	   | Rprop -> (* Singlaton elimination *)
	       assert (Array.length br = 1);
	       let (c,ids,e) = extract_branch 0 br.(0) in 	  
	       Rmlterm e)
    | IsFix ((_,i),(ti,fi,ci)) ->
	let (env', ctx') = fix_environment env ctx fi ti in
	let extract_fix_body c = 
	  match extract_constr env' ctx' c with
	    | Eprop -> MLprop (* TODO: probably wrong *)
	    | Emltype _ -> assert false
	    | Emlterm a -> a
	in
	let ei = array_map_to_list extract_fix_body ci in
	Rmlterm (MLfix (i, true, List.map id_of_name fi, ei))
    | IsLetIn (n, c1, t1, c2) ->
	let id = id_of_name n in
	let env' = push_rel (n,Some c1,t1) env in
	(match get_arity env t1 with
	   | Some (Prop Null) -> 
	       extract_term env' (Vprop::ctx) c2
	   | Some _ ->
	       extract_term env' (Varity::ctx) c2
	   | None -> 
	       let c1' = extract_term_with_type env ctx c1 t1 in
	       let c2' = extract_term env' (Vdefault::ctx) c2 in
	       (* If [c2] was of type an arity, [c] too would be so *)
	       (match (c1',c2') with
		  | (Rmlterm a1,Rmlterm a2) -> Rmlterm (MLletin (id,a1,a2))
		  | _ -> assert false (* Cf. rem. above *)))
    | IsCast (c, _) ->
	extract_term_with_type env ctx c t
    | IsMutInd _ | IsProd _ | IsSort _ | IsVar _ 
    | IsMeta _ | IsEvar _ | IsCoFix _ ->
	assert false 
	  
and extract_app env ctx (f,tyf,sf) args =
  let nargs = List.length args in
  assert (List.length sf >= nargs);
  (* We have reduced type of [f] if needed to ensure this property *)
  let mlargs = 
    List.fold_right 
      (fun (v,a) args -> match v with
	 | (Varity | Vprop), _ -> args
	 | Vdefault,_ ->  
	     (* We can't trust the tag [Vdefault], we use [extract_constr] *)
	     match extract_constr env ctx a with 
	       | Emltype _ -> MLarity :: args
	       | Eprop -> MLprop :: args
	       | Emlterm mla -> mla :: args)
      (List.combine (list_firstn nargs sf) args)
      []
  in
  (* [f : arity] implies [(f args):arity], that can't be *)
  match extract_term_with_type env ctx f tyf with
    | Rmlterm f' -> Rmlterm (MLapp (f', mlargs))
    | Rprop -> assert false
	  

(*s Extraction of a constr. *)

and extract_constr_with_type env ctx c t =
    match get_arity env t with
      | Some (Prop Null) -> 
	  Eprop
      | Some _ -> 
	  (match extract_type env c with
	     | Tprop -> Eprop
	     | Tarity -> Emltype (Miniml.Tarity, [], []) (* any other arity *)
	     | Tmltype (t, sign, fl) -> Emltype (t, sign, fl))
      | None -> 
	  (match extract_term env ctx c with 
	     | Rmlterm a -> Emlterm a
	     | Rprop -> Eprop)
 	    
and extract_constr env ctx c = 
  extract_constr_with_type env ctx c (Typing.type_of env Evd.empty c)

(*s Extraction of a constant. *)
		
and extract_constant sp =
  (* TODO: Axioms *)
  let cb = Global.lookup_constant sp in
  let typ = cb.const_type in
  let body = match cb.const_body with Some c -> c | None -> assert false in
  extract_constr_with_type (Global.env()) [] body typ
    
(*s Extraction of an inductive. *)
    
and extract_inductive ((sp,_) as i) =
  extract_mib sp;
  lookup_inductive_extraction i
			     
and extract_constructor (((sp,_),_) as c) =
  extract_mib sp;
  lookup_constructor_extraction c

and extract_mib sp =
  if not (Gmap.mem (sp,0) !inductive_extraction_table) then begin
    let mib = Global.lookup_mind sp in
    let genv = Global.env () in
    (* first pass: we store inductive signatures together with empty flex. *)
    Array.iteri
      (fun i ib -> add_inductive_extraction (sp,i) 
	   (signature_of_arity genv ib.mind_nf_arity, []))
      mib.mind_packets;
    (* second pass: we extract constructors arities and we accumulate
       flexible variables. *)
    let fl = 
      array_foldi
	(fun i ib fl ->
	   let mis = build_mis ((sp,i),[||]) mib in
	   array_foldi
	     (fun j _ fl -> 
		let t = mis_constructor_type (succ j) mis in
		let nparams = mis_nparams mis in 
		let (binders, t) = decompose_prod_n nparams t in
		let env = push_many_rels genv (List.rev binders) in
		match extract_type env t with
		  | Tarity | Tprop -> assert false
		  | Tmltype (mlt, s, f) -> 
		      let l = list_of_ml_arrows mlt in
		      add_constructor_extraction ((sp,i),succ j) (l,s);
		      f @ fl)
	     ib.mind_nf_lc fl)
	mib.mind_packets []
    in
    (* third pass: we update the inductive flexible variables. *)
    for i = 0 to mib.mind_ntypes - 1 do
      let (s,_) = lookup_inductive_extraction (sp,i) in
      add_inductive_extraction (sp,i) (s,fl)
    done
  end
    
(*s Extraction of a global reference i.e. a constant or an inductive. *)
    
and extract_inductive_declaration sp =
  extract_mib sp;
  let mib = Global.lookup_mind sp in
  let one_constructor ind j id = 
    let (t,_) = lookup_constructor_extraction (ind,succ j) in (id, t)
  in
  let one_inductive i ip =
    let (s,fl) = lookup_inductive_extraction (sp,i) in
    (params_of_sign s @ fl, ip.mind_typename, 
     Array.to_list (Array.mapi (one_constructor (sp,i)) ip.mind_consnames))
  in
  Dtype (Array.to_list (Array.mapi one_inductive mib.mind_packets))

(*s ML declaration from a reference. *)

let extract_declaration = function
  | ConstRef sp -> 
      let id = basename sp in (* FIXME *)
      (match extract_constant sp with
	 | Emltype (mlt, s, fl) -> Dabbrev (id, params_of_sign s @ fl, mlt)
	 | Emlterm t -> Dglob (id, t)
	 | Eprop -> Dglob (id, MLprop))
  | IndRef (sp,_) -> extract_inductive_declaration sp
  | ConstructRef ((sp,_),_) -> extract_inductive_declaration sp
  | VarRef _ -> assert false

(*s Registration of vernac commands for extraction. *)

module Pp = Ocaml.Make(struct let pp_global = Printer.pr_global end)

open Vernacinterp

let _ = 
  vinterp_add "Extraction"
    (function 
       | [VARG_CONSTR ast] ->
	   (fun () -> 
	      let c = Astterm.interp_constr Evd.empty (Global.env()) ast in
	      match kind_of_term c with
		(* If it is a global reference, then output the declaration *)
		| IsConst (sp,_) -> 
		    mSGNL (Pp.pp_decl (extract_declaration (ConstRef sp)))
		| IsMutInd (ind,_) ->
		    mSGNL (Pp.pp_decl (extract_declaration (IndRef ind)))
		| IsMutConstruct (cs,_) ->
		    mSGNL (Pp.pp_decl (extract_declaration (ConstructRef cs)))
		(* Otherwise, output the ML type or expression *)
		| _ ->
		    match extract_constr (Global.env()) [] c with
		      | Emltype (t,_,_) -> mSGNL (Pp.pp_type t)
		      | Emlterm a -> mSGNL (Pp.pp_ast a)
		      | Eprop -> message "prop")
       | _ -> assert false)

