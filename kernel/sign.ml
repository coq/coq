
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
let rec lookup_id_type id = function
  | (id',c,t) :: _ when id=id' -> t
  | _ :: sign -> lookup_id_type id sign
  | [] -> raise Not_found
let rec lookup_id_value id = function
  | (id',c,t) :: _ when id=id' -> c
  | _ :: sign -> lookup_id_value id sign
  | [] -> raise Not_found
let rec lookup_id id = function
  | (id',c,t) :: _ when id=id' -> (c,t)
  | _ :: sign -> lookup_id id sign
  | [] -> raise Not_found
let empty_named_context = []
let pop_named_decl id = function
  | (id',_,_) :: sign -> assert (id = id'); sign
  | [] -> assert false
let ids_of_named_context = List.map (fun (id,_,_) -> id)
let map_named_context = map
let rec mem_named_context id = function
  | (id',_,_) :: _ when id=id' -> true
  | _ :: sign -> mem_named_context id sign
  | [] -> false
let fold_named_context = List.fold_right
let fold_named_context_reverse = List.fold_left
let fold_named_context_both_sides = list_fold_right_and_left
let it_named_context_quantifier f = List.fold_left (fun c d -> f d c)

type rel_declaration = name * constr option * types
type rel_context = rel_declaration list

let add_rel_decl = add
let add_rel_assum = add_decl
let add_rel_def = add_def
let lookup_rel_type n sign =
  let rec lookrec = function
    | (1, (na,_,t) :: _) -> (na,t)
    | (n, _ :: sign)     -> lookrec (n-1,sign)
    | (_, [])            -> raise Not_found
  in 
  lookrec (n,sign)
let lookup_rel_value n sign =
  let rec lookrec = function
    | (1, (_,c,_) :: _) -> c
    | (n, _ :: sign )   -> lookrec (n-1,sign)
    | (_, [])           -> raise Not_found
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
let concat_rel_context = (@)
let ids_of_rel_context sign =
  List.fold_right
    (fun (na,_,_) l -> match na with Name id -> id::l | Anonymous -> l)
    sign []
let names_of_rel_context = List.map (fun (na,_,_) -> na)
let assums_of_rel_context sign =
  List.fold_right
    (fun (na,c,t) l -> match c with Some _ -> l | None -> (na,body_of_type t)::l)
    sign []
let map_rel_context = map

let instantiate_sign sign args =
  let rec instrec = function
    | ((id,None,_) :: sign, c::args) -> (id,c) :: (instrec (sign,args))
    | ((id,Some c,_) :: sign, args)     -> (id,c) :: (instrec (sign,args))
    | ([],[])                       -> []
    | ([],_) | (_,[]) ->
    anomaly "Signature and its instance do not match"
  in 
  instrec (sign,args)

(* [keep_hyps sign ids] keeps the part of the signature [sign] which 
   contains the variables of the set [ids], and recursively the variables 
   contained in the types of the needed variables. *)

let rec keep_hyps needed = function
  | (id,copt,t as d) ::sign when Idset.mem id needed ->
      let globc = 
	match copt with
	  | None -> Idset.empty
	  | Some c -> global_vars_set c in
      let needed' =
	Idset.union (global_vars_set (body_of_type t)) 
	  (Idset.union globc needed) in
      d :: (keep_hyps needed' sign)
  | _::sign -> keep_hyps needed sign
  | [] -> []

(*************************)
(*   Names environments  *)
(*************************)
type names_context = name list
let add_name n nl = n::nl
let lookup_name_of_rel p names =
  try List.nth names (p-1)
  with Failure "nth" -> raise Not_found
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
    | IsProd (x,t,c)  -> prodec_rec (add_rel_assum (x,t) l) c
    | IsLetIn (x,b,t,c) -> prodec_rec (add_rel_def (x,b,t) l) c
    | IsCast (c,_)    -> prodec_rec l c
    | _               -> l,c
  in 
  prodec_rec empty_rel_context

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam_assum = 
  let rec lamdec_rec l c =
    match kind_of_term c with
    | IsLambda (x,t,c) -> lamdec_rec (add_rel_assum (x,t) l) c
    | IsLetIn (x,b,t,c) -> lamdec_rec (add_rel_def (x,b,t) l) c
    | IsCast (c,_)     -> lamdec_rec l c
    | _                -> l,c
  in 
  lamdec_rec empty_rel_context

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n_assum n =
  if n < 0 then error "decompose_prod_n: integer parameter must be positive";
  let rec prodec_rec l n c = 
    if n=0 then l,c 
    else match kind_of_term c with 
    | IsProd (x,t,c) -> prodec_rec (add_rel_assum(x,t) l) (n-1) c
    | IsLetIn (x,b,t,c) ->
	prodec_rec (add_rel_def (x,b,t) l) (n-1) c
    | IsCast (c,_)   -> prodec_rec l n c
    | c -> error "decompose_prod_n: not enough products"
  in 
  prodec_rec empty_rel_context n 

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n_assum n =
  if n < 0 then error "decompose_lam_n: integer parameter must be positive";
  let rec lamdec_rec l n c = 
    if n=0 then l,c 
    else match kind_of_term c with 
    | IsLambda (x,t,c) -> lamdec_rec (add_rel_assum (x,t) l) (n-1) c
    | IsLetIn (x,b,t,c) ->
	lamdec_rec (add_rel_def (x,b,t) l) (n-1) c
    | IsCast (c,_)     -> lamdec_rec l n c
    | c -> error "decompose_lam_n: not enough abstractions"
  in 
  lamdec_rec empty_rel_context n 
