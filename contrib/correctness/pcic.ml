(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Libnames
open Term
open Termops
open Nametab
open Declarations
open Indtypes
open Sign
open Rawterm
open Typeops
open Entries

open Pmisc
open Past


(* Here we translate intermediates terms (cc_term) into CCI terms (constr) *)

let make_hole c = mkCast (isevar, c)

(* Tuples are defined in file Tuples.v 
 * and their constructors are called Build_tuple_n or exists_n,
 * wether they are dependant (last element only) or not. 
 * If necessary, tuples are generated ``on the fly''. *)

let tuple_exists id = 
  try let _ = Nametab.locate (make_short_qualid id) in true
  with Not_found -> false

let ast_set = Ast.ope ("SET", [])

let tuple_n n =
  let name = "tuple_" ^ string_of_int n in
  let id = id_of_string name in
  let l1n = Util.interval 1 n in
  let params = 
    List.map 
      (fun i -> let id = id_of_string ("T" ^ string_of_int i) in (id, ast_set))
      l1n
  in
  let fields = 
    List.map
      (fun i -> 
	 let id = id_of_string 
		    ("proj_" ^ string_of_int n ^ "_" ^ string_of_int i) in
	 (false, Vernacexpr.AssumExpr (id, Ast.nvar (id_of_string ("T" ^ string_of_int i)))))
      l1n 
  in
  let cons = id_of_string ("Build_tuple_" ^ string_of_int n) in
  Record.definition_structure ((false, id), params, fields, cons, mk_Set)

(*s [(sig_n n)] generates the inductive
    \begin{verbatim}
    Inductive sig_n [T1,...,Tn:Set; P:T1->...->Tn->Prop] : Set :=
      exist_n : (x1:T1)...(xn:Tn)(P x1 ... xn) -> (sig_n T1 ... Tn P).
    \end{verbatim} *)

let sig_n n =
  let name = "sig_" ^ string_of_int n in
  let id = id_of_string name in
  let l1n = Util.interval 1 n in
  let lT = List.map (fun i -> id_of_string ("T" ^ string_of_int i)) l1n in
  let lx = List.map (fun i -> id_of_string ("x" ^ string_of_int i)) l1n in
  let idp = id_of_string "P" in
  let params =
    let typ = List.fold_right (fun _ c -> mkArrow (mkRel n) c) lT mkProp in
    (idp, LocalAssum typ) :: 
    (List.rev_map (fun id -> (id, LocalAssum mkSet)) lT)
  in
  let lc = 
    let app_sig = mkApp(mkRel (2*n+3),
                        Array.init (n+1) (fun i -> mkRel (2*n+2-i))) in
    let app_p = mkApp(mkRel (n+1),
                      Array.init n (fun i -> mkRel (n-i))) in
    let c = mkArrow app_p app_sig in
    List.fold_right (fun id c -> mkProd (Name id, mkRel (n+1), c)) lx c
  in
  let cname = id_of_string ("exist_" ^ string_of_int n) in
  Declare.declare_mind 
    { mind_entry_finite = true;
      mind_entry_inds = 
	[ { mind_entry_params = params;
	    mind_entry_typename = id;
	    mind_entry_arity = mkSet;
	    mind_entry_consnames = [ cname ];
	    mind_entry_lc = [ lc ] } ] }

(*s On the fly generation of needed (possibly dependent) tuples. *)

let check_product_n n =
  if n > 2 then
    let s = Printf.sprintf "tuple_%d" n in
    if not (tuple_exists (id_of_string s)) then tuple_n n

let check_dep_product_n n =
  if n > 1 then
    let s = Printf.sprintf "sig_%d" n in
    if not (tuple_exists (id_of_string s)) then ignore (sig_n n)

(*s Constructors for the tuples. *)
	
let pair = ConstructRef ((coq_constant ["Init"; "Datatypes"] "prod",0),1)
let exist = ConstructRef ((coq_constant ["Init"; "Specif"] "sig",0),1)

let tuple_ref dep n =
  if n = 2 & not dep then
    pair
  else
    let n = n - (if dep then 1 else 0) in
    if dep then
      if n = 1 then 
	exist
      else begin
	let name = Printf.sprintf "exist_%d" n in
	let id = id_of_string name in
	if not (tuple_exists id) then ignore (sig_n n);
	Nametab.locate (make_short_qualid id)
      end
    else begin
      let name = Printf.sprintf "Build_tuple_%d" n in
      let id = id_of_string name in
      if not (tuple_exists id) then tuple_n n;
      Nametab.locate (make_short_qualid id)
    end

(* Binders. *)

let trad_binder avoid nenv id = function
  | CC_untyped_binder -> RHole (dummy_loc,AbstractionType (Name id))
  | CC_typed_binder ty -> Detyping.detype (Global.env()) avoid nenv ty

let rec push_vars avoid nenv = function
  | [] -> ([],avoid,nenv)
  | (id,b) :: bl -> 
      let b' = trad_binder avoid nenv id b in
      let bl',avoid',nenv' = 
	push_vars (id :: avoid) (add_name (Name id) nenv) bl 
      in
      ((id,b') :: bl', avoid', nenv')

let rec raw_lambda bl v = match bl with
  | [] -> 
      v
  | (id,ty) :: bl' -> 
      RLambda (dummy_loc, Name id, ty, raw_lambda bl' v)

(* The translation itself is quite easy.
   letin are translated into Cases constructions *)

let rawconstr_of_prog p =
  let rec trad avoid nenv = function
    | CC_var id -> 
	RVar (dummy_loc, id)

    (*i optimisation : let x = <constr> in e2  =>  e2[x<-constr] 
    | CC_letin (_,_,[id,_],CC_expr c,e2) ->
	real_subst_in_constr [id,c] (trad e2)
    | CC_letin (_,_,([_] as b),CC_expr e1,e2) ->
	let (b',avoid',nenv') = push_vars avoid nenv b in
      	let c1 = Detyping.detype avoid nenv e1 
	and c2 = trad avoid' nenv' e2 in
	let id = Name (fst (List.hd b')) in
	RLetIn (dummy_loc, id, c1, c2)
    i*)

    | CC_letin (_,_,([_] as b),e1,e2) ->
	let (b',avoid',nenv') = push_vars avoid nenv b in
      	let c1 = trad avoid nenv e1 
	and c2 = trad avoid' nenv' e2 in
	RApp (dummy_loc, raw_lambda b' c2, [c1])

    | CC_letin (dep,ty,bl,e1,e2) ->
	let (bl',avoid',nenv') = push_vars avoid nenv bl in
	let c1 = trad avoid nenv e1
	and c2 = trad avoid' nenv' e2 in
	ROldCase (dummy_loc, false, None, c1, [| raw_lambda bl' c2 |])

    | CC_lam (bl,e) ->
	let bl',avoid',nenv' = push_vars avoid nenv bl in
	let c = trad avoid' nenv' e in 
	raw_lambda bl' c

    | CC_app (f,args) ->
	let c = trad avoid nenv f
	and cargs = List.map (trad avoid nenv) args in
	RApp (dummy_loc, c, cargs)

    | CC_tuple (_,_,[e]) -> 
	trad avoid nenv e
	
    | CC_tuple (false,_,[e1;e2]) ->
	let c1 = trad avoid nenv e1 
	and c2 = trad avoid nenv e2 in
	RApp (dummy_loc, RRef (dummy_loc,pair),
	      [RHole (dummy_loc,ImplicitArg (pair,1));
	       RHole (dummy_loc,ImplicitArg (pair,2));c1;c2])

    | CC_tuple (dep,tyl,l) ->
      	let n = List.length l in
      	let cl = List.map (trad avoid nenv) l in
      	let tuple = tuple_ref dep n in
	let tyl = List.map (Detyping.detype (Global.env()) avoid nenv) tyl in
      	let args = tyl @ cl in
	RApp (dummy_loc, RRef (dummy_loc, tuple), args)

    | CC_case (ty,b,el) ->
	let c = trad avoid nenv b in
	let cl = List.map (trad avoid nenv) el in
	let ty = Detyping.detype (Global.env()) avoid nenv ty in
	ROldCase (dummy_loc, false, Some ty, c, Array.of_list cl)

    | CC_expr c -> 
	Detyping.detype (Global.env()) avoid nenv c

    | CC_hole c -> 
	RCast (dummy_loc, RHole (dummy_loc, QuestionMark),
               Detyping.detype (Global.env()) avoid nenv c)

  in
  trad [] empty_names_context p
