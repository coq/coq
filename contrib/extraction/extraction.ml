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
open Summary

(*s Extraction results. *)

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

(* The [signature] type is used to know how many arguments a CIC
   object expects, and what these arguments will become in the ML
   object. *)
   
(* Convention: outmost lambda/product gives the head of the list *)

type signature = type_var list

(* When dealing with CIC contexts, we maintain corresponding contexts 
   telling whether a variable will be kept or will disappear.
   Cf. [renum_db]. *)

(* Convention: innermost ([Rel 1]) is at the head of the list *)

type extraction_context = bool list

(* The [type_extraction_result] is the result of the [extract_type] function
   that extracts a CIC object into an ML type. It is either: 
   \begin{itemize}
   \item a real ML type, followed by its signature and its list of type 
   variables (['a],\ldots)
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

let none = Evd.empty

let type_of env c = Typing.type_of env Evd.empty c

let whd_betaiotalet = clos_norm_flags (UNIFORM, red_add betaiota_red ZETA)

let is_axiom sp = (Global.lookup_constant sp).const_body = None

type lamprod = Lam | Prod

let flexible_name = id_of_string "flex"

let id_of_name = function
  | Anonymous -> id_of_string "x"
  | Name id   -> id

(* [list_of_ml_arrows] applied to the ML type [a->b->]\dots[z->t]
   returns the list [[a;b;...;z]]. It is used when making the ML types
   of inductive definitions. We also suppress [Prop] parts. *)

let rec list_of_ml_arrows = function
  | Tarr (Miniml.Tarity, b) -> assert false
  | Tarr (Miniml.Tprop, b) -> list_of_ml_arrows b
  | Tarr (a, b) -> a :: list_of_ml_arrows b
  | t -> []

(*s [get_arity c] returns [Some s] if [c] is an arity of sort [s], 
   and [None] otherwise. *)

let rec get_arity env c =
  match kind_of_term (whd_betadeltaiota env none c) with
    | IsProd (x,t,c0) -> get_arity (push_rel_assum (x,t) env) c0
    | IsCast (t,_) -> get_arity env t
    | IsSort s -> Some s
    | _ -> None

(* idem, but goes through [Lambda] as well. Cf. [find_conclusion]. *)

let rec get_lam_arity env c =
  match kind_of_term (whd_betadeltaiota env none c) with
    | IsLambda (x,t,c0) -> get_lam_arity (push_rel_assum (x,t) env) c0
    | IsProd (x,t,c0) -> get_lam_arity (push_rel_assum (x,t) env) c0
    | IsCast (t,_) -> get_lam_arity env t
    | IsSort s -> Some s
    | _ -> None

(*s Detection of non-informative parts. *)

let is_non_info_sort env s = is_Prop (whd_betadeltaiota env none s)

let is_non_info_type env t = 
  (is_non_info_sort env (type_of env t)) || (get_arity env t) = Some (Prop Null)

(*i This one is not used, left only to precise what we call a non-informative 
   term.

let is_non_info_term env c = 
  let t = type_of env c in
  let s = type_of env t in
  (is_non_info_sort env s) ||
  match get_arity env t with 
    | Some (Prop Null) -> true
    | Some (Type _) -> (get_lam_arity env c = Some (Prop Null))
    | _ -> false
i*)

(* [v_of_t] transforms a type [t] into a [type_var] flag. *)

let v_of_t env t = match get_arity env t with
  | Some (Prop Null) -> logic_arity
  | Some _ -> info_arity
  | _ -> if is_non_info_type env t then logic else default

(*s Operations on binders *)

type binders = (name * constr) list

(* Convention: right binders give [Rel 1] at the head, like those answered by 
   [decompose_prod]. Left binders are the converse. *)

let rec lbinders_fold f acc env = function 
  | [] -> acc
  | (n,t) :: l -> 
      f n t (v_of_t env t) (lbinders_fold f acc (push_rel_assum (n,t) env) l)

(* [sign_of_arity] transforms an arity into a signature. It is used 
   for example with the types of inductive definitions, which are known
   to be already in arity form. *)

let sign_of_lbinders = lbinders_fold (fun _ _ v a -> v::a) [] 

let sign_of_arity env c = sign_of_lbinders env (List.rev (fst (decompose_prod c)))

(* [vl_of_arity] returns the list of the lambda variables tagged [info_arity]
   in an arity. Renaming is done. *)

let vl_of_lbinders = 
  lbinders_fold 
    (fun n _ v a -> 
       if v = info_arity then (next_ident_away (id_of_name n) a)::a else a) []
  
let vl_of_arity env c = vl_of_lbinders env (List.rev (fst (decompose_prod c)))
	 
(*s [renum_db] gives the new de Bruijn indices for variables in an ML
   term.  This translation is made according to an [extraction_context]. *)
	
let renum_db ctx n = 
  let rec renum = function
    | (1, true  :: _) -> 1
    | (n, true  :: s) -> succ (renum (pred n, s))
    | (n, false :: s) -> renum (pred n, s)
    | _ -> assert false
  in
  renum (n, ctx)

(*s Decomposition of a function expecting n arguments at least. We eta-expanse
   if needed *)

let force_n_prod n env c = 
  if nb_prod c < n then whd_betadeltaiota env none c else c

let decompose_lam_eta n env c = 
  let dif = n - (nb_lam c) in 
  if dif <= 0 then 
    decompose_lam_n n c
  else
    let t = type_of env c in
    let (trb,_) = decompose_prod_n n (force_n_prod n env t) in
    let (rb, e) = decompose_lam c in 
    let rb = (list_firstn dif trb) @ rb in 
    let e = applist (lift dif e, List.rev_map mkRel (interval 1 dif)) in
    (rb, e)

let rec abstract_n n a = 
  if n = 0 then a else MLlam (anonymous, ml_lift 1 (abstract_n (n-1) a))

(*s Eta-expansion to bypass ML type inference limitations (due to possible
    polymorphic references, the ML type system does not generalize all
    type variables that could be generalized). *)

let eta_expanse ec = function 
  | Tmltype (Tarr _, _, _) ->
      (match ec with
	 | Emlterm (MLlam _) -> ec
	 | Emlterm a -> Emlterm (MLlam (anonymous, MLapp (a, [MLrel 1])))
	 | _ -> ec)
  | _ -> ec

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

(* Tables synchronization. *)

let freeze () =
  !inductive_extraction_table, !constructor_extraction_table, !constant_table

let unfreeze (it,cst,ct) =
  inductive_extraction_table := it;
  constructor_extraction_table := cst;
  constant_table := ct

let _ = declare_summary "Extraction tables"
	  { freeze_function = freeze;
	    unfreeze_function = unfreeze;
	    init_function = (fun () -> ());
	    survive_section = true }

(*s Extraction of a type. *)

(* When calling [extract_type] we suppose that the type of [c] is an
   arity. This is for example checked in [extract_constr]. *)

(* Relation with [v_of_t]: it is less precise, since we do not 
   delta-reduce in [extract_type] in general.
   \begin{itemize}
   \item If [v_of_t env t = NotArity,_], 
   then [extract_type env t] is a [Tmltype].
   \item If [extract_type env t = Tarity], then [v_of_t env t = Arity,_]
   \end{itemize} *)

(* Generation of type variable list (['a] in caml).
   In Coq [(a:Set)(a:Set)a] is legal, but in ML we have only a flat list 
   of type variable, so we must take care of renaming now, in order to get 
   something like [type ('a,'a0) foo = 'a0].  The list [vl] is used to 
   accumulate those type variables and to do renaming on the fly. 
   Convention: the last elements of this list correspond to external products.
   This is used when dealing with applications *)


let rec extract_type env c =
  extract_type_rec env c [] [] 

and extract_type_rec env c vl args = 
  (* We accumulate the context, the arguments and the generated variable list *)
  let t = type_of env (applist (c, args)) in
  (* Since [ty] is an arity, there is two non-informative case: 
     [ty] is an arity of sort [Prop], or 
     [c] has a non-informative head symbol *)
  match get_arity env t with 
    | None -> 
	assert false (* Cf. precondition. *)
    | Some (Prop Null) ->
	Tprop 
    | Some _ -> extract_type_rec_info env c vl args
 
and extract_type_rec_info env c vl args = 
  match (kind_of_term (whd_betaiotalet env none c)) with
    | IsSort _ ->
	assert (args = []); (* A sort can't be applied. *)
	Tarity 
    | IsProd (n,t,d) ->
	assert (args = []); (* A product can't be applied. *)
	extract_prod_lam env (n,t,d) vl Prod
    | IsLambda (n,t,d) ->
	assert (args = []); (* [c] is now in head normal form. *)
	extract_prod_lam env (n,t,d) vl Lam
    | IsApp (d, args') ->
	(* We just accumulate the arguments. *)
	extract_type_rec_info env d vl (Array.to_list args' @ args)
    | IsRel n -> 
	(match lookup_rel_value n env with
	   | Some t -> 
	       extract_type_rec_info env (lift n t) vl args  
	   | None ->
	       let id = id_of_name (fst (lookup_rel_type n env)) in 
	       Tmltype (Tvar id, [], vl))
    | IsConst (sp,a) when is_axiom sp -> 
	let id = next_ident_away (basename sp) vl in 
	Tmltype (Tvar id, [], id :: vl)
    | IsConst (sp,a) ->
	let t = constant_type env none (sp,a) in 
	if is_arity env none t then
	  (match extract_constant sp with 
	     | Emltype (Miniml.Tarity,_,_) -> Tarity
	     | Emltype (Miniml.Tprop,_,_) -> Tprop
	     | Emltype (_, sc, vlc) ->  
		 extract_type_app env (ConstRef sp,sc,vlc) vl args 
	     | Emlterm _ -> assert false) 
	else 
	  (* We can't keep as ML type abbreviation a CIC constant *)
	  (*   which type is not an arity: we reduce this constant. *)
	  let cvalue = constant_value env (sp,a) in
	  extract_type_rec_info env (applist (cvalue, args)) vl []
    | IsMutInd (spi,_) ->
	(match extract_inductive spi with 
	   |Iml (si,vli) -> 
	       extract_type_app env (IndRef spi,si,vli) vl args 
	   |Iprop -> assert false (* Cf. initial tests *))
    | IsMutCase _ | IsFix _ | IsCoFix _ ->
	let id = next_ident_away flexible_name vl in
	Tmltype (Tvar id, [], id :: vl)
	  (* Type without counterpart in ML: we generate a 
	     new flexible type variable. *) 
    | IsCast (c, _) ->
	extract_type_rec_info env c vl args
    | _ -> 
	assert false

(* Auxiliary function used to factor code in lambda and product cases *)

and extract_prod_lam env (n,t,d) vl flag = 
  let tag = v_of_t env t in
  let env' = push_rel_assum (n,t) env in
  match tag,flag with
    | (Info, Arity), _ -> 
	  (* We rename before the [push_rel], to be sure that the corresponding *)
	  (* [lookup_rel] will be correct. *)
	  let id' = next_ident_away (id_of_name n) vl in 
	  let env' = push_rel_assum (Name id', t) env in
	  (match extract_type_rec_info env' d (id'::vl) [] with 
	     | Tmltype (mld, sign, vl') -> Tmltype (mld, tag::sign, vl')
	     | et -> et)
    | (Logic, Arity), _ | _, Lam ->
	(match extract_type_rec_info  env' d vl [] with 
	   | Tmltype (mld, sign, vl') -> Tmltype (mld, tag::sign, vl')
	   | et -> et)
    | (Logic, NotArity), Prod ->
	  (match extract_type_rec_info env' d vl [] with 
	     | Tmltype (mld, sign, vl') ->
		 Tmltype (Tarr (Miniml.Tprop, mld), tag::sign, vl')
	     | et -> et)
    | (Info, NotArity), Prod ->
	(* It is important to treat [d] first and [t] in second. *)
	(* This ensures that the end of [vl] correspond to external binders. *)
	(match extract_type_rec_info env' d vl [] with 
	   | Tmltype (mld, sign, vl') -> 
	       (match extract_type_rec_info env t vl' [] with
		  | Tprop | Tarity -> 
		      assert false 
			(* Cf. relation between [extract_type] and [v_of_t] *)
		  | Tmltype (mlt,_,vl'') -> 
		      Tmltype (Tarr(mlt,mld), tag::sign, vl''))
	   | et -> et)
	
 (* Auxiliary function dealing with type application. 
    Precondition: [r] is of type an arity. *)
		  
and extract_type_app env (r,sc,vlc) vl args =
  let nargs = List.length args in
  assert (List.length sc >= nargs);
  (* [r] is of type an arity, so it can't be applied to more than n args, 
     where n is the number of products in this arity type. *)
  let (sign_args,sign_rem) = list_chop nargs sc in
  let (mlargs,vl') = 
    List.fold_right 
      (fun (v,a) ((args,vl) as acc) -> match v with
	 | _, NotArity -> acc
	 | Logic, Arity -> acc (* TO JUSTIFY *)
	 | Info, Arity -> match extract_type_rec_info env a vl [] with
	     | Tarity -> (Miniml.Tarity :: args, vl) 
  	           (* we pass a dummy type [arity] as argument *)
	     | Tprop -> (Miniml.Tprop :: args, vl)
	     | Tmltype (mla,_,vl') -> (mla :: args, vl'))
      (List.combine sign_args args) 
      ([],vl)
  in
  (* The type variable list is [vl'] plus those variables of [c] not 
     corresponding to arguments. There is [nvlargs] such variables of [c] *)
  let nvlargs = List.length vlc - List.length mlargs in 
  assert (nvlargs >= 0);
  let vl'' = 
    List.fold_right 
      (fun id l -> (next_ident_away id l) :: l) 
      (list_firstn nvlargs vlc) vl'
  in
  (* We complete the list of arguments of [c] by variables *)
  let vlargs = 
    List.rev_map (fun i -> Tvar i) (list_firstn nvlargs vl'') in
  Tmltype (Tapp ((Tglob r) :: mlargs @ vlargs), sign_rem, vl'')
    

(*s Extraction of a term. 
    Precondition: [c] has a type which is not an arity. 
    This is normaly checked in [extract_constr]. *)

and extract_term env ctx c = 
  extract_term_with_type env ctx c (type_of env c)

and extract_term_with_type env ctx c t =
  let s = Typing.type_of env none t in
  (* The only non-informative case: [s] is [Prop] *)
  if is_Prop (whd_betadeltaiota env none s) then
    Rprop
  else 
    Rmlterm (extract_term_info_with_type env ctx c t)

(* Variants with a stronger precondition: [c] is informative. 
   We directly return a [ml_ast], not a [term_extraction_result] *)

and extract_term_info env ctx c = 
  extract_term_info_with_type env ctx c (type_of env c)

and extract_term_info_with_type env ctx c t = 
   match kind_of_term c with
     | IsLambda (n, t, d) ->
	 let v = v_of_t env t in 
	  let env' = push_rel_assum (n,t) env in
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
  	  let tf = type_of env f in
          let s = signature_of_application env f tf a in  
      	  extract_app env ctx (f,tf,s) (Array.to_list a) 
      | IsConst (sp,_) ->
	  MLglob (ConstRef sp)
      | IsMutConstruct (cp,_) ->
	  let (s,n) = signature_of_constructor cp in
	  let rec abstract rels i = function
	    | [] -> 
		let rels = List.rev_map (fun x -> MLrel (i-x)) rels in
		if (is_singleton_constructor cp) then 
		  match rels with 
		    | [var]->var
		    | _ -> assert false
		else
		  MLcons (ConstructRef cp, rels)
	    | (Info,NotArity) :: l -> 
		MLlam (id_of_name Anonymous, abstract (i :: rels) (succ i) l)
	    | (Logic,NotArity) :: l ->
		MLlam (id_of_name Anonymous, abstract rels (succ i) l)
	    | (_,Arity) :: l -> 
		abstract rels i l
	  in
	  abstract_n n (abstract [] 1 s)
      | IsMutCase ((ni,(ip,cnames,_,_,_)),p,c,br) ->
	  extract_case env ctx ni ip cnames p c br
      | IsFix ((_,i),recd) -> 
	  extract_fix env ctx i recd
      | IsCoFix (i,recd) -> 
	  extract_fix env ctx i recd  
      | IsLetIn (n, c1, t1, c2) ->
	  let id = id_of_name n in
	  let env' = push_rel_def (n,c1,t1) env in
	  let tag = v_of_t env t1 in
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
      | IsMutInd _ | IsProd _ | IsSort _ | IsVar _ | IsMeta _ | IsEvar _ ->
	  assert false 
	    
and extract_case env ctx ni ip cnames p c br = 
  let extract_branch_aux j b = 	  
    let (rb,e) = decompose_lam_eta ni.(j) env b in
    let lb = List.rev rb in
    let env' = push_rels_assum rb env in
    let ctx' = 
      lbinders_fold (fun _ _ v a -> (v = default) :: a) ctx env lb in
    (* Some pathological cases need an [extract_constr] here rather *)
    (* than an [extract_term]. See exemples in [test_extraction.v] *)
    let e' = match extract_constr env' ctx' e with
      | Emltype _ -> MLarity
      | Emlterm a -> a
    in (lb,e')
  in
  let extract_branch j b =
    let cp = (ip,succ j) in
    let (s,_) = signature_of_constructor cp in
    assert (List.length s = ni.(j));
    (* number of arguments, without parameters *)
    let (lb, e') = extract_branch_aux j b in
    let ids = 
      List.fold_right 
	(fun (v,(n,_)) acc -> 
	   if v = default then (id_of_name n :: acc) else acc)
	(List.combine s lb) []
    in
    (ConstructRef cp, ids, e')
  in
  (* [c] has an inductive type, not an arity type *)
  (match extract_term env ctx c with
     | Rmlterm a -> 
	 if (is_singleton_inductive ip) then 
	   begin
	     (* informative singleton case *)
	     assert (Array.length br = 1);
	     let (_,ids,e') = extract_branch 0 br.(0) in
	     assert (List.length ids = 1);
	     MLletin (List.hd ids,a,e')
	   end
	 else
	   MLcase (a, Array.mapi extract_branch br)
     | Rprop -> (* Logical singleton elimination *)
	 assert (Array.length br = 1);
	 snd (extract_branch_aux 0 br.(0)))
  
and extract_fix env ctx i (fi,ti,ci as recd) = 
  let n = Array.length ti in
  let env' = push_rec_types recd env in
  let ti' = Array.mapi lift ti in 
  let lb =
    Array.to_list
      (array_map2_i (fun i na t -> (na, type_app (lift i) t)) fi ti) in
  let ctx' = 
    lbinders_fold (fun _ _ v a -> (snd v = NotArity) :: a) ctx env lb in
  let extract_fix_body c t =
    match extract_constr_with_type env' ctx' c (lift n t) with
      | Emltype _ -> MLarity
      | Emlterm a -> a
  in
  let ei = array_map2 extract_fix_body ci ti in
  MLfix (i, Array.map id_of_name fi, ei)

and extract_app env ctx (f,tyf,sf) args =
  let nargs = List.length args in
  assert (List.length sf >= nargs);
  (* We have reduced type of [f] if needed to ensure this property *)
  let mlargs = 
    List.fold_right 
      (fun (v,a) args -> match v with
	 | (_,Arity) -> args
	 | (Logic,NotArity) -> MLprop :: args
	 | (Info,NotArity) ->  
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
  let t = force_n_prod nargs env t  in
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
    let t' = type_of env f' in
    s @ signature_of_application env f' t' a'
	  

(*s Extraction of a constr. *)

and extract_constr_with_type env ctx c t =
    match v_of_t env t with
      | (Logic, Arity) -> Emltype (Miniml.Tarity, [], [])
      | (Logic, NotArity) -> Emlterm MLprop
      | (Info, Arity) -> 
	  (match extract_type env c with
	     | Tprop -> Emltype (Miniml.Tprop, [], [])
	     | Tarity -> Emltype (Miniml.Tarity, [], [])
	     | Tmltype (t, sign, vl) -> Emltype (t, sign, vl))
      | (Info, NotArity) -> 
	  Emlterm (extract_term_info_with_type env ctx c t)
 	    
and extract_constr env ctx c = 
  extract_constr_with_type env ctx c (type_of env c)

(*s Extraction of a constant. *)
		
and extract_constant sp =
  try
    Gmap.find sp !constant_table
  with Not_found ->
    let env = Global.env() in    
    let cb = Global.lookup_constant sp in
    let typ = cb.const_type in
    match cb.const_body with
      | None ->
          (match v_of_t env typ with
             | (Info,_) -> axiom_message sp
             | (Logic,Arity) -> Emltype (Miniml.Tarity,[],[])
             | (Logic,NotArity) -> Emlterm MLprop)
      | Some body ->
          let e = extract_constr_with_type env [] body typ in
          let e = eta_expanse e (extract_type env typ) in
          constant_table := Gmap.add sp e !constant_table;
          e

(*s Extraction of an inductive. *)
    
and extract_inductive ((sp,_) as i) =
  extract_mib sp;
  lookup_inductive_extraction i
			     
and extract_constructor (((sp,_),_) as c) =
  extract_mib sp;
  lookup_constructor_extraction c

and is_singleton_inductive (sp,_) = 
  let mib = Global.lookup_mind sp in 
  (mib.mind_ntypes = 1) &&
  let mis = build_mis ((sp,0),[||]) mib in
  (mis_nconstr mis = 1) && 
  match extract_constructor ((sp,0),1) with 
    | Cml ([_],_,_)-> true
    | _ -> false
	  
and is_singleton_constructor ((sp,i),_) = 
  is_singleton_inductive (sp,i) 

and signature_of_constructor cp = match extract_constructor cp with
  | Cprop -> assert false
  | Cml (_,s,n) -> (s,n)

and extract_mib sp =
  if not (Gmap.mem (sp,0) !inductive_extraction_table) then begin
    let mib = Global.lookup_mind sp in
    let genv = Global.env () in 
    (* Everything concerning parameters: *)
    let mis = build_mis ((sp,0),[||]) mib in
    let nb = mis_nparams mis in
    let rb = mis_params_ctxt mis in 
    let env = push_rels rb genv in
    let lb = List.rev_map (fun (n,s,t)->(n,t)) rb in 
    let nbtokeep = 
      lbinders_fold 
	(fun _ _ v a -> if snd v = NotArity then a+1 else a) 0 genv lb in
    let vl = vl_of_lbinders genv lb in
    (* First pass: we store inductive signatures together with 
       an initial type var list. *)
    Array.iteri
      (fun i ib -> 
	 let mis = build_mis ((sp,i),[||]) mib in 
	 if (mis_sort mis) = (Prop Null) then 
	   add_inductive_extraction (sp,i) Iprop
	 else
	   add_inductive_extraction (sp,i) 
	     (Iml (sign_of_arity genv ib.mind_nf_arity, 
		   vl_of_arity genv ib.mind_nf_arity)))
      mib.mind_packets;
    (* Second pass: we extract constructors arities and we accumulate
       type variables. *)
    let vl = 
      array_fold_left_i 
	(fun i vl packet -> 
	   let ip = (sp,i) in
	   let mis = build_mis (ip,[||]) mib in
	   if mis_sort mis = Prop Null then begin
	     for j = 0 to mis_nconstr mis do
		 add_constructor_extraction (ip,succ j) Cprop
	     done;
	     vl
	   end else begin
	     array_fold_left_i
	       (fun j vl _ -> 
		  let t = mis_constructor_type (succ j) mis in
		  let t = snd (decompose_prod_n nb t) in
		  match extract_type_rec_info env t vl [] with
		    | Tarity | Tprop -> assert false
		    | Tmltype (mlt, s, v) -> 
			let l = list_of_ml_arrows mlt in
			let cp = (ip,succ j) in
			  add_constructor_extraction cp (Cml (l,s,nbtokeep));
			v)
	       vl packet.mind_nf_lc
	   end) 
	vl mib.mind_packets
    in
    (* Third pass: we update the type variables list in every tables *)
    for i = 0 to mib.mind_ntypes-1 do 
      match lookup_inductive_extraction (sp,i) with 
	| Iprop -> ()
	| Iml (s,_) -> begin 
	    add_inductive_extraction (sp,i) (Iml (s,vl));
	    let ip = (sp,i) in 
	    let mis = build_mis (ip,[||]) mib in 
	    for j = 1 to mis_nconstr mis do
	      let cp = (ip,j) in 
	      match lookup_constructor_extraction cp  with 
		| Cprop -> assert false
		| Cml (t,s,n) -> 
		    let vl = List.rev_map (fun i -> Tvar i) vl in
		    let t' = List.map (update_args sp vl) t in 
		    add_constructor_extraction cp (Cml (t',s, n))
	    done
	  end
    done
  end	      

and extract_inductive_declaration sp =
  extract_mib sp;
  let ip = (sp,0) in 
  if (is_singleton_inductive ip) then
    let t = match lookup_constructor_extraction (ip,1) with 
	  | Cml ([t],_,_)-> t
	  | _ -> assert false
    in
    let vl = match lookup_inductive_extraction ip with 
      | Iml (_,vl) -> vl
      | _ -> assert false
    in 
    Dabbrev (IndRef ip,vl,t)
  else
    let mib = Global.lookup_mind sp in
    let one_constructor ind j _ = 
      let cp = (ind,succ j) in
      match lookup_constructor_extraction cp with 
	| Cprop -> assert false
	| Cml (t,_,_) -> (ConstructRef cp, t)
    in
    let l = 
      array_fold_left_i
	(fun i acc packet -> 
	   let ip = (sp,i) in
	   match lookup_inductive_extraction ip with
	     | Iprop -> acc
	     | Iml (s,vl) -> 
		 (List.rev vl, 
		  IndRef ip, 
		  Array.to_list 
		    (Array.mapi (one_constructor ip) packet.mind_consnames))
		 :: acc )
	[] mib.mind_packets 
    in
    Dtype (List.rev l, not (mind_type_finite mib 0))

(*s Extraction of a global reference i.e. a constant or an inductive. *)

let false_rec_sp = path_of_string "Coq.Init.Specif.False_rec"
let false_rec_e = MLlam (prop_name, MLexn (id_of_string "False_rec"))

let extract_declaration r = match r with
  | ConstRef sp when sp = false_rec_sp -> Dglob (r, false_rec_e)
  | ConstRef sp -> 
      (match extract_constant sp with
	 | Emltype (mlt, s, vl) -> Dabbrev (r, List.rev vl, mlt)
	 | Emlterm t -> Dglob (r, t))
  | IndRef (sp,_) -> extract_inductive_declaration sp
  | ConstructRef ((sp,_),_) -> extract_inductive_declaration sp
  | VarRef _ -> assert false
