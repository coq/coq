(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Util
open Names
open Nameops
open Term
open Termops
open Pattern
open Matching
open Hipattern
open Environ

open Pmisc
open Ptype
open Past
open Penv
open Prename

let is_mutable = function Ref _ | Array _ -> true | _ -> false
let is_pure = function TypePure _ -> true | _ -> false

let named_app f x = { a_name = x.a_name; a_value = (f x.a_value) }

let pre_app f x = 
  { p_assert = x.p_assert; p_name = x.p_name; p_value = f x.p_value }

let post_app = named_app

let anonymous x = { a_name = Anonymous; a_value = x }

let anonymous_pre b x = { p_assert = b; p_name = Anonymous; p_value = x }

let force_name f x =
  Option.map (fun q -> { a_name = Name (f q.a_name); a_value = q.a_value }) x

let force_post_name x = force_name post_name x

let force_bool_name x = 
  force_name (function Name id -> id | Anonymous -> bool_name()) x

let out_post = function
    Some { a_value = x } -> x
  | None -> invalid_arg "out_post"

let pre_of_assert b x =
  { p_assert = b; p_name = x.a_name; p_value = x.a_value }

let assert_of_pre x =
  { a_name = x.p_name; a_value = x.p_value }

(* Some generic functions on programs *)

let is_mutable_in_env env id =
  (is_in_env env id) & (is_mutable (type_in_env env id))

let now_vars env c =
  Util.map_succeed 
    (function id -> if is_mutable_in_env env id then id else failwith "caught")
    (global_vars (Global.env()) c)

let make_before_after c =
  let ids = global_vars (Global.env()) c in
  let al = 
    Util.map_succeed
      (function id -> 
	 if is_at id then 
	   match un_at id with (uid,"") -> (id,uid) | _ -> failwith "caught"
	 else failwith "caught")
      ids
  in
  subst_in_constr al c

(* [apply_pre] and [apply_post] instantiate pre- and post- conditions
 * according to a given renaming of variables (and a date that means
 * `before' in the case of the post-condition).
 *)

let make_assoc_list ren env on_prime ids =
  List.fold_left
    (fun al id ->
       if is_mutable_in_env env id then
	 (id,current_var ren id)::al
       else if is_at id then
	 let uid,d = un_at id in
	   if is_mutable_in_env env uid then
	     (match d with
		  "" -> (id,on_prime ren uid)
		| _  -> (id,var_at_date ren d uid))::al
	   else
	     al
       else
	 al) 
    [] ids

let apply_pre ren env c =
  let ids = global_vars (Global.env()) c.p_value in
  let al = make_assoc_list ren env current_var ids in
  { p_assert = c.p_assert; p_name = c.p_name; 
    p_value = subst_in_constr al c.p_value }

let apply_assert ren env c =
  let ids = global_vars (Global.env()) c.a_value in
  let al = make_assoc_list ren env current_var ids in
  { a_name = c.a_name; a_value = subst_in_constr al c.a_value }
 
let apply_post ren env before c =
  let ids = global_vars (Global.env()) c.a_value in
  let al = 
    make_assoc_list ren env (fun r uid -> var_at_date r before uid) ids in
  { a_name = c.a_name; a_value = subst_in_constr al c.a_value }

(* [traverse_binder ren env bl] updates renaming [ren] and environment [env]
 * as we cross the binders [bl]
 *)

let rec traverse_binders env = function
    [] -> env
  | (id,BindType v)::rem ->
      traverse_binders (add (id,v) env) rem
  | (id,BindSet)::rem ->
      traverse_binders (add_set id env) rem
  | (_,Untyped)::_ ->
      invalid_arg "traverse_binders"
	  
let initial_renaming env =
  let ids = Penv.fold_all (fun (id,_) l -> id::l) env [] in
    update empty_ren "0" ids


(* Substitutions *)

let rec type_c_subst s ((id,t),e,p,q) =
  let s' = s @ List.map (fun (x,x') -> (at_id x "", at_id x' "")) s in
  (id, type_v_subst s t), Peffect.subst s e,
  List.map (pre_app (subst_in_constr s)) p,
  Option.map (post_app (subst_in_constr s')) q

and type_v_subst s = function
    Ref v -> Ref (type_v_subst s v)
  | Array (n,v) -> Array (n,type_v_subst s v)
  | Arrow (bl,c) -> Arrow(List.map (binder_subst s) bl, type_c_subst s c)
  | (TypePure _) as v -> v

and binder_subst s = function
    (n, BindType v) -> (n, BindType (type_v_subst s v))
  | b -> b

(* substitution of constr by others *)

let rec type_c_rsubst s ((id,t),e,p,q) =
  (id, type_v_rsubst s t), e,
    List.map (pre_app (real_subst_in_constr s)) p,
    Option.map (post_app (real_subst_in_constr s)) q

and type_v_rsubst s = function
    Ref v -> Ref (type_v_rsubst s v)
  | Array (n,v) -> Array (real_subst_in_constr s n,type_v_rsubst s v)
  | Arrow (bl,c) -> Arrow(List.map (binder_rsubst s) bl, type_c_rsubst s c)
  | TypePure c -> TypePure (real_subst_in_constr s c)

and binder_rsubst s = function
  | (n, BindType v) -> (n, BindType (type_v_rsubst s v))
  | b -> b

(* make_arrow bl c = (x1:V1)...(xn:Vn)c *)

let make_arrow bl c = match bl with
  | [] -> invalid_arg "make_arrow: no binder"
  | _ -> Arrow (bl,c)

(* misc. functions *)

let deref_type = function
  | Ref v -> v
  | _ -> invalid_arg "deref_type"

let dearray_type = function
  | Array (size,v) -> size,v
  | _ -> invalid_arg "dearray_type"

let constant_unit () = TypePure (constant "unit")

let id_from_name = function Name id -> id | Anonymous -> (id_of_string "X")

(* v_of_constr : traduit un type CCI en un type ML *)

(* TODO: faire un test plus serieux sur le type des objets Coq *)
let rec is_pure_cci c = match kind_of_term c with
  | Cast (c,_) -> is_pure_cci c
  | Prod(_,_,c') -> is_pure_cci c'
  | Rel _ | Ind _ | Const _ -> true (* heu... *)
  | App _ -> not (is_matching_sigma c)
  | _ -> Util.error "CCI term not acceptable in programs"

let rec v_of_constr c = match kind_of_term c with
  | Cast (c,_) -> v_of_constr c
  | Prod _ ->
      let revbl,t2 = Term.decompose_prod c in
      let bl =
	List.map
	  (fun (name,t1) -> (id_from_name name, BindType (v_of_constr t1)))
	  (List.rev revbl)
      in
      let vars = List.rev (List.map (fun (id,_) -> mkVar id) bl) in
      Arrow (bl, c_of_constr (substl vars t2))
  | Ind _ | Const _ | App _ ->
      TypePure c
  | _ -> 
      failwith "v_of_constr: TODO"

and c_of_constr c =
  if is_matching_sigma c then
    let (a,q) = match_sigma c in
    (result_id, v_of_constr a), Peffect.bottom, [], Some (anonymous q)
  else
    (result_id, v_of_constr c), Peffect.bottom, [], None


(* pretty printers (for debugging purposes) *)

open Pp
open Util

let pr_lconstr x = Printer.pr_lconstr_env (Global.env()) x

let pp_pre = function
    [] -> (mt ())
  | l  ->
      hov 0 (str"pre " ++ 
	       prlist_with_sep (fun () -> (spc ())) 
		 (fun x -> pr_lconstr x.p_value) l)

let pp_post = function
    None -> (mt ())
  | Some c -> hov 0 (str"post " ++ pr_lconstr c.a_value)

let rec pp_type_v = function
    Ref v -> hov 0 (pp_type_v v ++ spc () ++ str"ref")
  | Array (cc,v) -> hov 0 (str"array " ++ pr_lconstr cc ++ str" of " ++ pp_type_v v)
  | Arrow (b,c) -> 
      hov 0 (prlist_with_sep (fun () -> (mt ())) pp_binder b ++ 
	       pp_type_c c)
  | TypePure c -> pr_lconstr c

and pp_type_c ((id,v),e,p,q) =
  hov 0 (str"returns " ++ pr_id id ++ str":" ++ pp_type_v v ++ spc () ++ 
	   Peffect.pp e ++ spc () ++ pp_pre p ++ spc () ++ pp_post q ++
	   spc () ++ str"end")

and pp_binder = function
    id,BindType v -> (str"(" ++ pr_id id ++ str":" ++ pp_type_v v ++ str")")
  | id,BindSet -> (str"(" ++ pr_id id ++ str":Set)")
  | id,Untyped -> (str"(" ++ pr_id id ++ str")")

(* pretty-print of cc-terms (intermediate terms) *)

let rec pp_cc_term = function
    CC_var id -> pr_id id
  | CC_letin (_,_,bl,c,c1) ->
      hov 0 (hov 2 (str"let " ++
		  	prlist_with_sep (fun () -> (str","))
			  (fun (id,_) -> pr_id id) bl ++
		  	str" =" ++ spc () ++
		  	pp_cc_term c ++
		  	str " in") ++
	       fnl () ++
	       pp_cc_term c1)
  | CC_lam (bl,c) ->
      hov 2 (prlist (fun (id,_) -> (str"[" ++ pr_id id ++ str"]")) bl ++
	       cut () ++
	       pp_cc_term c)
  | CC_app (f,args) ->
      hov 2 (str"(" ++ 
	       pp_cc_term f ++ spc () ++
	       prlist_with_sep (fun () -> (spc ())) pp_cc_term args ++
	       str")")
  | CC_tuple (_,_,cl) ->
      hov 2 (str"(" ++
	       prlist_with_sep (fun () -> (str"," ++ cut ()))
		 pp_cc_term cl ++
	       str")")
  | CC_case (_,b,[e1;e2]) ->
      hov 0 (str"if " ++ pp_cc_term b ++ str" then" ++ fnl () ++
	       str"  " ++ hov 0 (pp_cc_term e1) ++ fnl () ++
	       str"else" ++ fnl () ++
	       str"  " ++ hov 0 (pp_cc_term e2))
  | CC_case _ ->
      hov 0 (str"<Case: not yet implemented>")
  | CC_expr c ->
      hov 0 (pr_lconstr c)
  | CC_hole c ->
      (str"(?::" ++ pr_lconstr c ++ str")")

