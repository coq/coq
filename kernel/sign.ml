(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Util
open Term

(* Signatures *)

let add d sign = d::sign
let map f = List.map (fun (na,c,t) -> (na,option_app f c,type_app f t))

let add_decl (n,t) sign = (n,None,t)::sign
let add_def (n,c,t) sign = (n,Some c,t)::sign

type named_declaration = identifier * constr option * types
type named_context = named_declaration list

let add_named_decl = add
let add_named_assum = add_decl
let add_named_def = add_def
let rec lookup_named id = function
  | (id',_,_ as decl) :: _ when id=id' -> decl
  | _ :: sign -> lookup_named id sign
  | [] -> raise Not_found
let empty_named_context = []
let pop_named_decl id = function
  | (id',_,_) :: sign -> assert (id = id'); sign
  | [] -> assert false
let ids_of_named_context = List.map (fun (id,_,_) -> id)
let instance_from_named_context sign =
  let rec inst_rec = function
    | (id,None,_) :: sign -> mkVar id :: inst_rec sign
    | _ :: sign -> inst_rec sign
    | [] -> [] in
  Array.of_list (inst_rec sign)
let map_named_context = map
let rec mem_named_context id = function
  | (id',_,_) :: _ when id=id' -> true
  | _ :: sign -> mem_named_context id sign
  | [] -> false
let fold_named_context = List.fold_right
let fold_named_context_reverse = List.fold_left
let fold_named_context_both_sides = list_fold_right_and_left
let it_named_context_quantifier f = List.fold_left (fun c d -> f d c)

let it_mkNamedProd_or_LetIn   =
  List.fold_left (fun c d -> mkNamedProd_or_LetIn d c)
let it_mkNamedLambda_or_LetIn =
  List.fold_left (fun c d -> mkNamedLambda_or_LetIn d c)

(*s Signatures of ordered section variables *)
type section_context = named_context

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices *)

type rel_declaration = name * constr option * types
type rel_context = rel_declaration list
type rev_rel_context = rel_declaration list

let fold_rel_context = List.fold_right
let fold_rel_context_reverse = List.fold_left

let it_mkProd_or_LetIn   = List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkLambda_or_LetIn = List.fold_left (fun c d -> mkLambda_or_LetIn d c)

let add_rel_decl = add
let add_rel_assum = add_decl
let add_rel_def = add_def
let lookup_rel n sign =
  let rec lookrec = function
    | (1, decl :: _) -> decl
    | (n, _ :: sign) -> lookrec (n-1,sign)
    | (_, [])        -> raise Not_found
  in 
  lookrec (n,sign)
let rec lookup_rel_id id sign = 
  let rec lookrec = function
    | (n, (Anonymous,_,_)::l) -> lookrec (n+1,l)
    | (n, (Name id',_,t)::l)  -> if id' = id then (n,t) else lookrec (n+1,l)
    | (_, [])                 -> raise Not_found
  in 
  lookrec (1,sign)
let empty_rel_context = []
let rel_context_length = List.length
let lift_rel_context n sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,option_app (liftn n k) c,type_app (liftn n k) t)
	::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (rel_context_length sign) sign
let lift_rev_rel_context n sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,option_app (liftn n k) c,type_app (liftn n k) t)
	::(liftrec (k+1) sign)
    | [] -> []
  in
  liftrec 1 sign
let concat_rel_context = (@)
let ids_of_rel_context sign =
  List.fold_right
    (fun (na,_,_) l -> match na with Name id -> id::l | Anonymous -> l)
    sign []
let names_of_rel_context = List.map (fun (na,_,_) -> na)
let map_rel_context = map
let push_named_to_rel_context hyps ctxt =
  let rec push = function
    | (id,b,t) :: l ->
	let s, hyps = push l in
	let d = (Name id, option_app (subst_vars s) b, subst_vars s t) in
	id::s, d::hyps
    | [] -> [],[] in
  let s, hyps = push hyps in
  let rec subst = function
    | (na,b,t) :: l ->
	let n, ctxt = subst l in
	let d = (na, option_app (substn_vars n s) b, substn_vars n s t) in
	(n+1), d::ctxt
    | [] -> 1, hyps in
  snd (subst ctxt)
let reverse_rel_context = List.rev

let instantiate_sign sign args =
  let rec instrec = function
    | ((id,None,_) :: sign, c::args) -> (id,c) :: (instrec (sign,args))
    | ((id,Some c,_) :: sign, args)  -> instrec (sign,args)
    | ([],[])                        -> []
    | ([],_) | (_,[]) ->
    anomaly "Signature and its instance do not match"
  in 
  instrec (sign,Array.to_list args)

(*************************)
(*   Names environments  *)
(*************************)
type names_context = name list
let add_name n nl = n::nl
let lookup_name_of_rel p names =
  try List.nth names (p-1)
  with Invalid_argument _ | Failure _ -> raise Not_found
let rec lookup_rel_of_name id names = 
  let rec lookrec n = function
    | Anonymous :: l  -> lookrec (n+1) l
    | (Name id') :: l -> if id' = id then n else lookrec (n+1) l
    | []            -> raise Not_found
  in 
  lookrec 1 names
let empty_names_context = []

(*********************************)
(*       Term destructors        *)
(*********************************)

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod_assum = 
  let rec prodec_rec l c =
    match kind_of_term c with
    | Prod (x,t,c)  -> prodec_rec (add_rel_assum (x,t) l) c
    | LetIn (x,b,t,c) -> prodec_rec (add_rel_def (x,b,t) l) c
    | Cast (c,_)    -> prodec_rec l c
    | _               -> l,c
  in 
  prodec_rec empty_rel_context

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam_assum = 
  let rec lamdec_rec l c =
    match kind_of_term c with
    | Lambda (x,t,c) -> lamdec_rec (add_rel_assum (x,t) l) c
    | LetIn (x,b,t,c) -> lamdec_rec (add_rel_def (x,b,t) l) c
    | Cast (c,_)     -> lamdec_rec l c
    | _                -> l,c
  in 
  lamdec_rec empty_rel_context

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n_assum n =
  if n < 0 then
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c = 
    if n=0 then l,c 
    else match kind_of_term c with 
    | Prod (x,t,c) -> prodec_rec (add_rel_assum(x,t) l) (n-1) c
    | LetIn (x,b,t,c) ->
	prodec_rec (add_rel_def (x,b,t) l) (n-1) c
    | Cast (c,_)   -> prodec_rec l n c
    | c -> error "decompose_prod_n_assum: not enough assumptions"
  in 
  prodec_rec empty_rel_context n 

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n_assum n =
  if n < 0 then
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c = 
    if n=0 then l,c 
    else match kind_of_term c with 
    | Lambda (x,t,c) -> lamdec_rec (add_rel_assum (x,t) l) (n-1) c
    | LetIn (x,b,t,c) ->
	lamdec_rec (add_rel_def (x,b,t) l) (n-1) c
    | Cast (c,_)     -> lamdec_rec l n c
    | c -> error "decompose_lam_n_assum: not enough abstractions"
  in 
  lamdec_rec empty_rel_context n 
