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
open Mlutil
open Closure

(*s Extraction results. *)

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* The flag [type_var] gives us information about an identifier
   coming from a Lambda or a Product:
   \begin{itemize}
   \item [Arity] denotes identifiers of type an arity of some sort [Set],
     [Prop] or [Type], that is $(x_1:X_1)\ldots(x_n:X_n)s$ with [s = Set],
     [Prop] or [Type] 
   \item [NotArity] denotes the other cases. It may be inexact after 
   instanciation. For example [(X:Type)X] is [NotArity] and may give [Set]
   after instanciation, which is rather [Arity]
   \item [Logic] denotes identifiers of type an arity of sort [Prop], 
     or of type of type [Prop]
   \item [Info] is the opposite. The same example [(X:Type)X] shows 
     that an [Info] term might in fact be [Logic] later on. 
   \end{itemize} *)

type info = Logic | Info

type arity = Arity | NotArity

type type_var = info * arity

let logic_arity = (Logic, Arity)
let info_arity = (Info, Arity)
let logic = (Logic, NotArity)
let default = (Info, NotArity)

type signature = (type_var * identifier) list

(* When dealing with CIC contexts, we maintain corresponding contexts 
   telling whether a variable will be kept or will disappear *)

type extraction_context = bool list

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

(*s Utility functions. *)

let whd_betaiotalet = clos_norm_flags (UNIFORM, red_add betaiota_red ZETA)

type lamprod = Lam | Prod

(* FIXME: to be moved somewhere else *)
let array_foldi f a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i a.(i) v) in
  fold 0

let flexible_name = id_of_string "flex"

let id_of_name = function
  | Anonymous -> id_of_string "x"
  | Name id   -> id

(* This function [params_of_sign] extracts the type parameters (['a] in Caml)
   from a signature. *)

let params_of_sign = 
  List.fold_left 
    (fun l v -> match v with (Info,Arity),id -> id :: l | _ -> l) []

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

(*s Detection of non-informative parts. *)

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
  | Some (Prop Null) -> logic_arity
  | Some _ -> info_arity
  | _ -> if is_non_info_type env t then logic else default
      
let rec nb_params_to_keep env = function
  | [] -> 0
  | (n,t) :: l ->
      let v = v_of_arity env t in
      let env' = push_rel (n,None,t) env in
      (nb_params_to_keep env' l) + (if snd v = NotArity then 1 else 0)

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
   of inductive definitions. We also suppress [Prop] parts. *)

let rec list_of_ml_arrows = function
  | Tarr (Miniml.Tprop, b) -> list_of_ml_arrows b
  | Tarr (a, b) -> a :: list_of_ml_arrows b
  | t -> []

(* [renum_db] gives the new de Bruijn indices for variables in an ML
   term.  This translation is made according to an [extraction_context]. *)
	
let renum_db ctx n = 
  let rec renum = function
    | (1, true  :: _) -> 1
    | (n, true  :: s) -> succ (renum (pred n, s))
    | (n, false :: s) -> renum (pred n, s)
    | _ -> assert false
  in
  renum (n, ctx)

(*s Environment for the bodies of some mutual fixpoints. *)

let push_many_rels env binders =  
    List.fold_left (fun e (f,t) -> push_rel (f,None,t) e) env binders

let rec push_many_rels_ctx keep_prop env ctx = function
  | (fi,ti) :: l -> 
      let v = v_of_arity env ti in
      let keep = (v = default) || (keep_prop && v = logic) in
      push_many_rels_ctx keep_prop (push_rel (fi,None,ti) env) (keep :: ctx) l
  | [] ->
      (env, ctx)

let fix_environment env ctx fl tl =
  let tl' = Array.mapi lift tl in
  push_many_rels_ctx true env ctx (List.combine fl (Array.to_list tl'))

(* Decomposition of a type beginning with at least n products when reduced *)

let decompose_prod_reduce n env c = 
  let c = 
    if nb_prod c >= n then 
      c 
    else 
      whd_betadeltaiota env Evd.empty c 
  in 
  decompose_prod_n n c

(* Decomposition of a function expecting n arguments at least. We eta-expanse
   if needed *)

let decompose_lam_eta n env c = 
  let dif = n - (nb_lam c) in 
  if dif <= 0 then 
    decompose_lam_n n c
  else 
    let tyc = Typing.type_of env Evd.empty c in
    let (type_binders,_) = decompose_prod_reduce n env tyc in
    let (binders, e) = decompose_lam c in 
    let binders = (list_firstn dif type_binders) @ binders in 
    let e = applist (lift dif e, List.rev_map mkRel (interval 1 dif)) in
    (binders, e)

let rec abstract_n n a = 
  if n = 0 then a else MLlam (anonymous, ml_lift 1 (abstract_n (n-1) a))

(*s Error message when extraction ends on an axiom. *)

let axiom_message sp =
  errorlabstrm "axiom_message"
    [< 'sTR "You must specify an extraction for axiom"; 'sPC; 
       pr_sp sp; 'sPC; 'sTR "first" >]


(*s Tables to keep the extraction of inductive types and constructors. *)

type inductive_extraction_result = 
  | Iml of signature * identifier list
  | Iprop
   
let inductive_extraction_table = 
  ref (Gmap.empty : (inductive_path, inductive_extraction_result) Gmap.t)

let add_inductive_extraction i e = 
  inductive_extraction_table := Gmap.add i e !inductive_extraction_table

let lookup_inductive_extraction i = Gmap.find i !inductive_extraction_table

type constructor_extraction_result = 
  | Cml of ml_type list * signature * int
  | Cprop

let constructor_extraction_table = 
  ref (Gmap.empty : (constructor_path, constructor_extraction_result) Gmap.t)

let add_constructor_extraction c e = 
  constructor_extraction_table := Gmap.add c e !constructor_extraction_table

let lookup_constructor_extraction i = Gmap.find i !constructor_extraction_table

let constant_table = 
  ref (Gmap.empty : (section_path, extraction_result) Gmap.t)


(*s Extraction of a type. *)

(* When calling [extract_type] we suppose that the type of [c] is an
   arity.  This is for example checked in [extract_constr]. 

   Relation with [v_of_arity]: it is less precise, since we do not 
   delta-reduce in [extract_type] in general.
   \begin{itemize}
   \item If [v_of_arity env t = NotArity,_], 
   then [extract_type env t] is a [Tmltype].
   \item If [extract_type env t = Tarity], then [v_of_arity env t = Arity,_]
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
		     | Emltype (mlt, sc, flc) ->
			 assert (mlt<>Miniml.Tprop);
			 extract_type_app env fl (ConstRef sp,sc,flc) args
		     | Emlterm _ -> 
			 assert false 
			 (* [cty] is of type an arity. *))
		else 
		  (* We can't keep as ML type abbreviation a CIC constant 
		     which type is not an arity: we reduce this constant. *)
		  let cvalue = constant_value env (sp,a) in
		  extract_rec env fl (applist (cvalue, args)) []
	    | IsMutInd (spi,_) ->
		(match extract_inductive spi with 
		   |Iml (si,fli) -> 
		       extract_type_app env fl (IndRef spi,si,fli) args
		   |Iprop -> assert false
			 (* Cf. initial tests *))
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
    match tag,flag with
      | (_, Arity), _ | _, Lam ->
	  (match extract_rec env' fl d [] with 
	     | Tmltype (mld, sign, fl'') -> Tmltype (mld, (tag,id)::sign, fl'')
	     | et -> et)
      | (Logic, NotArity), Prod ->
	  (match extract_rec env' fl d [] with 
	     | Tmltype (mld, sign, fl'') ->
		 Tmltype (Tarr (Miniml.Tprop, mld), (tag,id)::sign, fl'')
	     | et -> et)
      | (Info, NotArity), Prod ->
	  (match extract_rec env fl t [] with
	     | Tprop | Tarity -> 
		assert false 
		(* Cf. relation between [extract_type] and [v_of_arity] *)
	     | Tmltype (mlt,_,fl') -> 
		 (match extract_rec env' fl' d [] with 
		    | Tmltype (mld, sign, fl'') -> 
			Tmltype (Tarr(mlt,mld), (tag,id)::sign, fl'')
		    | et -> et))

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
	   | (_, NotArity), _ -> acc
	   | (_, Arity), _ -> match extract_rec env fl a [] with
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
  else 
    Rmlterm (extract_term_info_with_type env ctx c t)

(* Variants with a stronger precondition: [c] is informative. 
   We directly return a [mlast], not a [term_extraction_result] *)

and extract_term_info env ctx c = 
  let t = Typing.type_of env Evd.empty c in
  extract_term_info_with_type env ctx c t

and extract_term_info_with_type env ctx c t = 
    match kind_of_term c with
      | IsLambda (n, t, d) ->
	  let v = v_of_arity env t in 
	  let env' = push_rel (n,None,t) env in
	  let ctx' = (snd v = NotArity) :: ctx in
	  let d' = extract_term_info env' ctx' d in
	  (* If [d] was of type an arity, [c] too would be so *)
	  (match v with
	     | _,Arity -> d'
	     | l,NotArity -> 
		 let id = if l = Logic then prop_name else id_of_name n in
		 MLlam (id, d'))
      | IsRel n ->
	  (* TODO : magic or not *) 
	  MLrel (renum_db ctx n)
      | IsApp (f,a) ->
  	  let tyf = Typing.type_of env Evd.empty f in
          let s = signature_of_application env f tyf a in  
      	  extract_app env ctx (f,tyf,s) (Array.to_list a) 
      | IsConst (sp,_) ->
	  MLglob (ConstRef sp)
      | IsMutConstruct (cp,_) ->
	  let (s,n) = signature_of_constructor cp in
	  let ns = List.length s + 1 in
	  let rec abstract rels i = function
	    | [] -> 
		MLcons (ConstructRef cp, List.length rels, List.rev rels)
	    | ((Info,NotArity),id) :: l -> 
		MLlam (id, abstract (MLrel (ns - i) :: rels) (succ i) l)
	    | (_,id) :: l ->
		MLlam (id, abstract rels (succ i) l)
	  in
	  abstract_n n (abstract [] 1 s)
      | IsMutCase ((ni,(ip,cnames,_,_,_)),p,c,br) ->
	  let extract_branch_aux j b = 	  
	    let (binders,e) = decompose_lam_eta ni.(j) env b in
	    let binders = List.rev binders in
	    let (env',ctx') = push_many_rels_ctx false env ctx binders in
	    (* Some patological cases need an [extract_constr] here 
	       rather than an [extract_term]. See exemples in 
	       [test_extraction.v] *)
	    let e' = match extract_constr env' ctx' e with
	      | Emltype _ -> MLarity
	      | Emlterm a -> a
	    in (binders,e')
	  in
	  let extract_branch j b =
	    let cp = (ip,succ j) in
	    let (s,_) = signature_of_constructor cp in
	    assert (List.length s = ni.(j));
	    (* number of arguments, without parameters *)
	    let (binders, e') = extract_branch_aux j b in
	    let ids = 
	      List.fold_right 
		(fun ((v,_),(n,_)) acc ->
		   if v = default then (id_of_name n :: acc) else acc)
		(List.combine s binders) []
	    in
	    (ConstructRef cp, ids, e')
	  in
	  (* [c] has an inductive type, not an arity type *)
	  (match extract_term env ctx c with
	     | Rmlterm a -> MLcase (a, Array.mapi extract_branch br)
	     | Rprop -> (* Singleton elimination *)
		 assert (Array.length br = 1);
		 snd (extract_branch_aux 0 br.(0)))
      | IsFix ((_,i),(ti,fi,ci)) ->
	  let n = Array.length ti in
	  let (env', ctx') = fix_environment env ctx fi ti in
	  let extract_fix_body c t =
	    match extract_constr_with_type env' ctx' c (lift n t) with
	      | Emltype _ -> MLarity
	      | Emlterm a -> a
	  in
	  let ei = Array.to_list (array_map2 extract_fix_body ci ti) in
	  MLfix (i, List.map id_of_name fi, ei)
      | IsLetIn (n, c1, t1, c2) ->
	  let id = id_of_name n in
	  let env' = push_rel (n,Some c1,t1) env in
	  let tag = v_of_arity env t1 in
	  (match tag with
	     | (Info, NotArity) -> 
		 let c1' = extract_term_info_with_type env ctx c1 t1 in
		 let c2' = extract_term_info env' (true :: ctx) c2 in
		 (* If [c2] was of type an arity, [c] too would be so *)
		 MLletin (id,c1',c2')
	     | _ ->
		 extract_term_info env' (false :: ctx) c2)
      | IsCast (c, _) ->
	  extract_term_info_with_type env ctx c t
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
	 | (_,Arity), _ -> args
	 | (Logic,NotArity), _ -> MLprop :: args
	 | (Info,NotArity), _ ->  
	     (* We can't trust the tag [Vdefault], we use [extract_constr] *)
	     match extract_constr env ctx a with 
	       | Emltype _ -> MLarity :: args
	       | Emlterm mla -> mla :: args)
      (List.combine (list_firstn nargs sf) args)
      []
  in
  (* [f : arity] implies [(f args):arity], that can't be *)
  let f' = extract_term_info_with_type env ctx f tyf in 
  MLapp (f', mlargs)


and signature_of_application env f t a = 
  let nargs = Array.length a in	 	
  let t = 
    if nb_prod t >= nargs then 
      t 
    else 
      whd_betadeltaiota env Evd.empty t 
  in
  let nbp = nb_prod t in
  let s = match extract_type env t with
    | Tmltype (_,s,_) -> s	
    | Tarity -> assert false (* Cf. precondition *)
    | Tprop -> assert false
  in 
  if nbp >= nargs then 
    s
  else 
    let f' = mkApp (f, Array.sub a 0 nbp) in 
    let a' = Array.sub a nbp (nargs-nbp) in 
    let t' = Typing.type_of env Evd.empty f' in
    s @ signature_of_application env f' t' a'
	  

(*s Extraction of a constr. *)

and extract_constr_with_type env ctx c t =
    match v_of_arity env t with
      | (Logic, Arity) -> Emltype (Miniml.Tarity, [], [])
      | (Logic, NotArity) -> Emlterm MLprop
      | (Info, Arity) -> 
	  (match extract_type env c with
	     | Tprop -> Emltype (Miniml.Tprop, [], [])
	     | Tarity -> Emltype (Miniml.Tarity, [], [])
	     | Tmltype (t, sign, fl) -> Emltype (t, sign, fl))
      | (Info, NotArity) -> 
	  Emlterm (extract_term_info_with_type env ctx c t)
 	    
and extract_constr env ctx c = 
  extract_constr_with_type env ctx c (Typing.type_of env Evd.empty c)

(*s Extraction of a constant. *)
		
and extract_constant sp =
  try
    Gmap.find sp !constant_table
  with Not_found ->
    let cb = Global.lookup_constant sp in
    let typ = cb.const_type in
    let body = match cb.const_body with 
      | Some c -> c 
      | None -> axiom_message sp
    in
    let e = extract_constr_with_type (Global.env()) [] body typ in
    constant_table := Gmap.add sp e !constant_table;
    e
    
(*s Extraction of an inductive. *)
    
and extract_inductive ((sp,_) as i) =
  extract_mib sp;
  lookup_inductive_extraction i
			     
and extract_constructor (((sp,_),_) as c) =
  extract_mib sp;
  lookup_constructor_extraction c

and signature_of_constructor cp = match extract_constructor cp with
  | Cprop -> assert false
  | Cml (_,s,n) -> (s,n)

and extract_mib sp =
  if not (Gmap.mem (sp,0) !inductive_extraction_table) then begin
    let mib = Global.lookup_mind sp in
    let genv = Global.env () in
    (* first pass: we store inductive signatures together with empty flex. *)
    Array.iteri
      (fun i ib -> 
	 let mis = build_mis ((sp,i),[||]) mib in 
	 if (mis_sort mis) = (Prop Null) then 
	   add_inductive_extraction (sp,i) Iprop
	 else
	   add_inductive_extraction (sp,i) 
	     (Iml (signature_of_arity genv ib.mind_nf_arity, [])))
      mib.mind_packets;
    (* second pass: we extract constructors arities and we accumulate
       flexible variables. *)
    let fl = 
      array_foldi
	(fun i ib fl ->
	   let ip = (sp,i) in
	   let mis = build_mis (ip,[||]) mib in
	   if mis_sort mis = Prop Null then
	     (for j = 0 to mis_nconstr mis do
		add_constructor_extraction (ip,succ j) Cprop
	      done;
	      fl)
	   else
	     array_foldi
	       (fun j _ fl -> 
		  let t = mis_constructor_type (succ j) mis in
		  let nparams = mis_nparams mis in 
		  let (binders, t) = decompose_prod_n nparams t in
		  let binders = List.rev binders in
		  let nparams' = nb_params_to_keep genv binders in
		  let env = push_many_rels genv binders in
		  match extract_type env t with
		    | Tarity | Tprop -> assert false
		    | Tmltype (mlt, s, f) -> 
			let l = list_of_ml_arrows mlt in
			let cp = (ip,succ j) in
			add_constructor_extraction cp (Cml (l,s,nparams'));
			f @ fl)
	       ib.mind_nf_lc fl)
	mib.mind_packets []
    in
    (* third pass: we update the inductive flexible variables. *)
    for i = 0 to mib.mind_ntypes - 1 do
      match lookup_inductive_extraction (sp,i) with 
	| Iprop -> ()
	| Iml (s,_) -> add_inductive_extraction (sp,i) (Iml (s,fl))
    done
  end
    
and extract_inductive_declaration sp =
  extract_mib sp;
  let mib = Global.lookup_mind sp in
  let one_constructor ind j _ = 
    let cp = (ind,succ j) in
    match lookup_constructor_extraction cp with 
      | Cprop -> assert false
      | Cml (t,_,_) -> (ConstructRef cp, t)
  in
  let l = 
    array_foldi
      (fun i packet acc -> 
	 let ip = (sp,i) in
	 match lookup_inductive_extraction ip with
	   | Iprop -> acc
	   | Iml (s,fl) -> 
	       (params_of_sign s @ fl, 
		IndRef ip, 
		Array.to_list 
		  (Array.mapi (one_constructor ip) packet.mind_consnames))
	       :: acc )
	 mib.mind_packets [] 
  in
  Dtype l

(*s Extraction of a global reference i.e. a constant or an inductive. *)

let extract_declaration r = match r with
  | ConstRef sp -> 
      (match extract_constant sp with
	 | Emltype (mlt, s, fl) -> Dabbrev (r, params_of_sign s @ fl, mlt)
	 | Emlterm t -> Dglob (r, t))
  | IndRef (sp,_) -> extract_inductive_declaration sp
  | ConstructRef ((sp,_),_) -> extract_inductive_declaration sp
  | VarRef _ -> assert false
