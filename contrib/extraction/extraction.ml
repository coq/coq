
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

(*s Extraction results. *)

type type_var = Varity | Vprop | Vdefault

type signature = (type_var * identifier) list

type type_extraction_result =
  | Tmltype of ml_type * signature * identifier list
  | Tarity
  | Tprop

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast
  | Eprop

(*s Utility functions. *)

let v_of_t = function
  | Tprop -> Vprop
  | Tarity -> Varity
  | Tmltype _ -> Vdefault

let array_foldi f a =
  let n = Array.length a in
  let rec fold i v = if i = n then v else fold (succ i) (f i a.(i) v) in
  fold 0

let flexible_name = id_of_string "flex"

let id_of_name = function
  | Anonymous -> id_of_string "_"
  | Name id   -> id

let params_of_sign = 
  List.fold_left (fun l v -> match v with Varity,id -> id :: l | _ -> l) []

let rec get_arity env c =
  match kind_of_term (whd_betadeltaiota env Evd.empty c) with
    | IsProd (x,t,c0) -> get_arity (push_rel_assum (x,t) env) c0
    | IsCast (t,_) -> get_arity env t
    | IsSort s -> Some s
    | _ -> None

let signature_of_arity = 
  let rec sign_of acc env c = match kind_of_term c with
    | IsProd (n, t, c') ->
	let env' = push_rel (n,None,t) env in
	let id = id_of_name n in
	sign_of 
	  (((match get_arity env t with
	       | Some (Prop Null) -> Vprop
	       | Some _ -> Varity 
	       | _ -> Vdefault), id) :: acc)
	  env' c'
    | IsSort _ -> 
	acc
    | _ ->
	assert false
  in
  sign_of []

(* [list_of_ml_arrows] applied to the ML type [a->b->]\dots[z->t]
   returns the list [[a;b;...;z]]. *)
let rec list_of_ml_arrows = function
  | Tarr (a, b) -> a :: list_of_ml_arrows b
  | t -> []

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

(*i FIXME
let inductive_declaration_table =
  ref (Gmap.empty : (section_path, ml_ind list) Gmap.t)

let add_inductive_declaration sp d = 
  inductive_declaration_table := Gmap.add
i*)

(*s Extraction of a type. *)

let rec extract_type env c =
  let genv = Global.env() in
  let rec extract_rec env sign fl c args = 
    let ty = Typing.type_of env Evd.empty c in
    if is_Prop (whd_betadeltaiota env Evd.empty ty) then
      Tprop
    else
      match kind_of_term (whd_betaiota c) with
	| IsProd (n, t, d) ->
	    assert (args = []);
	    let id = id_of_name n in (* FIXME: capture problem *)
	    let env' = push_rel (n,None,t) env in
	    (match extract_rec env sign fl t [] with
	       | Tarity | Tprop as et ->
		   extract_rec env' ((v_of_t et,id) :: sign) fl d []
	       | Tmltype (t', _, fl') ->
		   (match extract_rec env' ((Vdefault,id)::sign) fl' d [] with
		      | Tmltype (d', sign', fl'') -> 
			  Tmltype (Tarr (t', d'), sign', fl'')
		      | et -> et))
	| IsLambda (n, t, d) ->
	    assert (args = []);
	    let id = id_of_name n in (* FIXME: capture problem *)
	    let env' = push_rel (n,None,t) env in
	    (match extract_rec env sign fl t [] with
	       | Tarity | Tprop as et ->
		   extract_rec env' ((v_of_t et,id) :: sign) fl d []
	       | Tmltype (t', _, fl') ->
		   extract_rec env' ((Vdefault,id) :: sign) fl' d [])
	| IsSort (Prop Null) ->
	    assert (args = []);
	    Tprop
	| IsSort _ ->
	    assert (args = []);
	    Tarity
	| IsApp (d, args') ->
	    extract_rec env sign fl d (Array.to_list args' @ args)
	| IsRel n ->
	    (match List.nth sign (pred n) with
	       | Vprop, _ -> assert false
	       | Vdefault, id -> Tmltype (Tvar id, sign, id :: fl)
	       | Varity, id -> Tmltype (Tvar id, sign, fl))
	| IsConst (sp,a) ->
	    let cty = constant_type genv Evd.empty (sp,a) in
	    if is_arity env Evd.empty cty then
	      (match extract_constant sp with
		 | Emltype (_, sc, flc) -> 
		     extract_type_app env sign fl (ConstRef sp,sc,flc) args
		 | Eprop -> Tprop
		 | Emlterm _ -> assert false)
	    else
	      let cvalue = constant_value env (sp,a) in
	      extract_rec env sign fl (mkApp (cvalue, Array.of_list args)) []
	| IsMutInd (spi,_) ->
	    let (si,fli) = extract_inductive spi in
	    extract_type_app env sign fl (IndRef spi,si,fli) args
	| IsMutCase _ 
	| IsFix _ ->
	    let id = next_ident_away flexible_name fl in
	    Tmltype (Tvar id, sign, id :: fl)
	| IsCast (c, _) ->
	    extract_rec env sign fl c args
	| _ -> 
	    assert false
  and extract_type_app env sign fl (r,sc,flc) args =
    let nargs = List.length args in
    assert (List.length sc >= nargs);
    let (mlargs,fl') = 
      List.fold_right 
	(fun (v,a) ((args,fl) as acc) -> match v with
	   | (Vdefault | Vprop), _ -> acc
	   | Varity,_ -> match extract_rec env sign fl a [] with
	       | Tarity -> assert false
	       | Tprop -> (Miniml.Tprop :: args, fl)
	       | Tmltype (mla,_,fl') -> (mla :: args, fl'))
	(List.combine (list_firstn nargs (List.rev sc)) args)
	([],fl)
    in
    let flc = List.map (fun i -> Tvar i) flc in
    Tmltype (Tapp ((Tglob r) :: mlargs @ flc), sign, fl')
  in
  extract_rec env [] [] c []


(*s Extraction of a term. *)

and extract_term c =
    (*i
      let rec extract_rec env c = match kind_of_term (whd_beta c) with
      | _ -> 
      failwith "todo"
      | IsSort _ | IsXtra _ | IsVar _ | IsMeta _ ->
      assert false 
      in
      extract_rec (Global.env()) c
      i*)
  failwith "todo"

(*s Extraction of a constr. *)

and extract_constr_with_type c t =
  let genv = Global.env () in
  match get_arity genv t with
    | Some (Prop Null) -> 
	Eprop
    | Some _ -> 
	(match extract_type genv c with
	   | Tprop -> Eprop
	   | Tarity -> error "not an ML type"
	   | Tmltype (t, sign, fl) -> Emltype (t, sign, fl))
    | None -> 
	let t = extract_term c in Emlterm t

and extract_constr c = 
  extract_constr_with_type c (Typing.type_of (Global.env()) Evd.empty c)

(*s Extraction of a constant. *)

and extract_constant sp =
  let cb = Global.lookup_constant sp in
  let typ = cb.const_type in
  let body = match cb.const_body with Some c -> c | None -> assert false in
  extract_constr_with_type body typ
    
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
       all flexible variables. *)
    let fl = 
      array_foldi
	(fun i ib fl ->
	   let mis = build_mis ((sp,i),[||]) mib in
	   array_foldi
	     (fun j _ fl -> 
		let t = mis_constructor_type (succ j) mis in
		match extract_type genv t with
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
		    match extract_constr c with
		      | Emltype (t,_,_) -> mSGNL (Pp.pp_type t)
		      | Emlterm a -> mSGNL (Pp.pp_ast a)
		      | Eprop -> message "prop")
       | _ -> assert false)

