
(*i $Id$ i*)

open Pp
open Util
open Names
open Term
open Declarations
open Environ
open Reduction
open Instantiate
open Miniml
open Mlimport

(*s Extraction results. *)

type type_var = Varity | Vskip

type signature = (type_var * identifier) list

type type_extraction_result =
  | Tmltype of ml_type * signature * identifier list
  | Tarity

type extraction_result =
  | Emltype of ml_type * signature * identifier list
  | Emlterm of ml_ast

let flexible_name = id_of_string "flex"

let id_of_name = function
  | Anonymous -> id_of_string "_"
  | Name id   -> id

(*s Extraction of a type. *)

let rec extract_type c =
  let genv = Global.env() in
  let rec extract_rec env sign fl c args = match kind_of_term (whd_beta c) with
    | IsProd (n, t, d) ->
	assert (args = []);
	let id = id_of_name n in (* FIXME: capture problem *)
	let env' = push_rel (n,None,t) env in
	(match extract_rec env sign fl t [] with
	   | Tarity ->
	       extract_rec env' ((Varity,id) :: sign) fl d []
	   | Tmltype (t', _, fl') ->
	       (match extract_rec env' ((Vskip,id) :: sign) fl' d [] with
		  | Tarity -> Tarity
		  | Tmltype (d', sign', fl'') -> 
		      Tmltype (Tarr (t', d'), sign', fl'')))
    | IsSort (Prop Null) ->
	assert (args = []);
	Tmltype (Tprop, [], [])
    | IsSort _ ->
	assert (args = []);
	Tarity
    | IsApp (d, args') ->
	extract_rec env sign fl d (Array.to_list args' @ args)
    | IsRel n ->
	(match List.nth sign (pred n) with
	   | Vskip, id -> Tmltype (Tvar id, sign, id :: fl)
	   | Varity, id -> Tmltype (Tvar id, sign, fl))
    | IsConst (sp,a) ->
	let cty = constant_type genv Evd.empty (sp,a) in
	if is_arity genv Evd.empty cty then
	  (match extract_constant sp with
	     | Emltype (_, sc, flc) ->
		 assert (List.length sc = List.length args);
		 let (mlargs,fl') = 
		   List.fold_left 
		     (fun ((args,fl) as acc) (v,a) -> match v with
			| Vskip,_ -> acc
			| Varity,_ -> match extract_rec env sign fl a [] with
			    | Tarity -> assert false
			    | Tmltype (mla,_,fl') -> (mla :: args, fl')
		     )
		     ([],fl) (List.combine sc args)
		 in
		 let flc = List.map (fun i -> Tvar i) flc in
		 Tmltype (Tapp ((Tglob (ConstRef sp)) :: mlargs @ flc), 
			  sign, fl')
	     | Emlterm _ -> 
		 assert false)
	else
	  failwith "todo: expanse c, reduce and apply recursively"
    | IsMutInd _ ->
	failwith "todo"
    | IsMutCase _ 
    | IsFix _ ->
	let id = next_ident_away flexible_name fl in
	Tmltype (Tvar id, sign, id :: fl)
    | IsCast (c, _) ->
	extract_rec env sign fl c args
    | _ -> 
	assert false
  in
  extract_rec (Global.env()) [] [] c []

(*s Extraction of a term. *)

and extract_term c =
  failwith "todo"
(*i
  let rec extract_rec env c = match kind_of_term (whd_beta c) with
    | _ -> 
	failwith "todo"
    | IsSort _ | IsXtra _ | IsVar _ | IsMeta _ ->
	assert false 
  in
  extract_rec (Global.env()) c
i*)

(*s Extraction of a constr. *)

and extract_constr_with_type c t =
  let redt = whd_betadeltaiota (Global.env()) Evd.empty t in
  if isSort redt then begin
    if is_Prop redt then
      Emltype (Tprop, [], [])
    else
      match extract_type c with
	| Tarity -> error "not an ML type"
	| Tmltype (t, sign, fl) -> Emltype (t, sign, fl)
  end else 
    let t = extract_term c in
    Emlterm t

and extract_constr c = 
  extract_constr_with_type c (Typing.type_of (Global.env()) Evd.empty c)

(*s Extraction of a constant. *)

and extract_constant sp =
  let cb = Global.lookup_constant sp in
  let typ = cb.const_type in
  let body = match cb.const_body with Some c -> c | None -> assert false in
  extract_constr_with_type body typ
      
(*s Extraction of an inductive. *)

and extract_inductive sp =
  let mib = Global.lookup_mind sp in
  failwith "todo"
  (* Dtype ... *)

(*s Extraction of a global reference i.e. a constant or an inductive. *)

and extract_reference = function
  | ConstRef sp -> extract_constant sp
  | IndRef (sp,_) -> extract_inductive sp
  | VarRef _ | ConstructRef _ -> assert false

(*s ML declaration from a reference. *)

let params_of_sign = 
  List.fold_left (fun l v -> match v with Vskip,_ -> l | _,id -> id :: l) []

let extract_declaration r = 
  let id = basename (Global.sp_of_global r) in (* FIXME *)
  match extract_reference r with
    | Emltype (mlt, s, fl) -> Dabbrev (id, params_of_sign s @ fl, mlt)
    | Emlterm t -> Dglob (id, t)
