(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Names
open Libnames
(*i*)

type loc = int * int

type t =
  | Node of loc * string * t list
  | Nmeta of loc * string
  | Nvar of loc * identifier
  | Slam of loc * identifier option * t
  | Smetalam of loc * string * t
  | Num of loc * int
  | Str of loc * string
  | Id of loc * string
  | Path of loc * kernel_name
  | Dynamic of loc * Dyn.t

type the_coq_ast = t

let subst_meta bl ast =
  let rec aux = function
    | Node (_,"META", [Num(_, n)]) -> List.assoc n bl
    | Node(loc, node_name, args) -> 
	Node(loc, node_name, List.map aux args)
    | Slam(loc, var, arg) -> Slam(loc, var, aux arg)
    | Smetalam(loc, var, arg) -> Smetalam(loc, var, aux arg)
    | other -> other
  in 
  aux ast

let rec collect_metas = function
  | Node (_,"META", [Num(_, n)]) -> [n]
  | Node(_, _, args) -> List.concat (List.map collect_metas args)
  | Slam(loc, var, arg) -> collect_metas arg
  | Smetalam(loc, var, arg) -> collect_metas arg
  | _ -> []

(* Hash-consing *)
module Hloc = Hashcons.Make(
  struct
    type t = loc
    type u = unit
    let equal (b1,e1) (b2,e2) = b1=b2 & e1=e2
    let hash_sub () x = x
    let hash = Hashtbl.hash
  end)

module Hast = Hashcons.Make(
  struct
    type t = the_coq_ast
    type u = 
	(the_coq_ast -> the_coq_ast) *
	((loc -> loc) * (string -> string)
	 * (identifier -> identifier) * (kernel_name -> kernel_name))
    let hash_sub (hast,(hloc,hstr,hid,hsp)) = function
      | Node(l,s,al) -> Node(hloc l, hstr s, List.map hast al)
      | Nmeta(l,s) -> Nmeta(hloc l, hstr s)
      | Nvar(l,s) -> Nvar(hloc l, hid s)
      | Slam(l,None,t) -> Slam(hloc l, None, hast t)
      | Slam(l,Some s,t) -> Slam(hloc l, Some (hid s), hast t)
      | Smetalam(l,s,t) -> Smetalam(hloc l, hstr s, hast t)
      | Num(l,n) -> Num(hloc l, n)
      | Id(l,s) -> Id(hloc l, hstr s)
      | Str(l,s) -> Str(hloc l, hstr s)
      | Path(l,d) -> Path(hloc l, hsp d)
      | Dynamic(l,d) -> Dynamic(hloc l, d)
    let equal a1 a2 =
      match (a1,a2) with
        | (Node(l1,s1,al1), Node(l2,s2,al2)) ->
            (l1==l2 & s1==s2 & List.length al1 = List.length al2)
            & List.for_all2 (==) al1 al2
        | (Nmeta(l1,s1), Nmeta(l2,s2)) -> l1==l2 & s1==s2
        | (Nvar(l1,s1), Nvar(l2,s2)) -> l1==l2 & s1==s2
        | (Slam(l1,None,t1), Slam(l2,None,t2)) -> l1==l2 & t1==t2
        | (Slam(l1,Some s1,t1), Slam(l2,Some s2,t2)) ->l1==l2 & s1==s2 & t1==t2
        | (Smetalam(l1,s1,t1), Smetalam(l2,s2,t2)) -> l1==l2 & s1==s2 & t1==t2
        | (Num(l1,n1), Num(l2,n2)) -> l1==l2 & n1=n2
        | (Id(l1,s1), Id(l2,s2)) -> l1==l2 & s1==s2
        | (Str(l1,s1),Str(l2,s2)) -> l1==l2 & s1==s2
        | (Path(l1,d1), Path(l2,d2)) -> (l1==l2 & d1==d2)
        | _ -> false
    let hash = Hashtbl.hash
  end)

let hcons_ast (hstr,hid,hpath) =
  let hloc = Hashcons.simple_hcons Hloc.f () in
  let hast = Hashcons.recursive_hcons Hast.f (hloc,hstr,hid,hpath) in
  (hast,hloc)

let rec subst_ast subst ast = match ast with
  | Node (l,s,astl) ->
      let astl' = Util.list_smartmap (subst_ast subst) astl in
	if astl' == astl then ast else
	  Node (l,s,astl')
  | Slam (l,ido,ast1) ->
      let ast1' = subst_ast subst ast1 in
	if ast1' == ast1 then ast else
	  Slam (l,ido,ast1')
  | Smetalam (l,s,ast1) ->
      let ast1' = subst_ast subst ast1 in
	if ast1' == ast1 then ast else
	  Smetalam (l,s,ast1')
  | Path (loc,kn) -> 
      let kn' = Names.subst_kn subst kn in
	if kn' == kn then ast else
	  Path(loc,kn')
  | Nmeta _
  | Nvar _ -> ast
  | Num _
  | Str _
  | Id _
  | Dynamic _ -> ast

open Util
open Rawterm
open Term

type scope_name = string

type reference_expr = 
  | RQualid of qualid located
  | RIdent of identifier located

type explicitation = int

type cases_pattern =
  | CPatAlias of loc * cases_pattern * identifier
  | CPatCstr of loc * reference_expr * cases_pattern list
  | CPatAtom of loc * reference_expr option
  | CPatNumeral of loc * Bignat.bigint

type ordered_case_style = CIf | CLet | CMatch | CCase

type constr_ast =
  | CRef of reference_expr
  | CFix of loc * identifier located * fixpoint_expr list
  | CCoFix of loc * identifier located * cofixpoint_expr list
  | CArrow of loc * constr_ast * constr_ast
  | CProdN of loc * (name located list * constr_ast) list * constr_ast
  | CLambdaN of loc * (name located list * constr_ast) list * constr_ast
  | CLetIn of loc * identifier located * constr_ast * constr_ast
  | CAppExpl of loc * reference_expr * constr_ast list
  | CApp of loc * constr_ast * (constr_ast * explicitation option) list
  | CCases of loc * case_style * constr_ast option * constr_ast list *
      (loc * cases_pattern list * constr_ast) list
  | COrderedCase of loc * ordered_case_style * constr_ast option * constr_ast * constr_ast list
  | CHole of loc
  | CMeta of loc * int
  | CSort of loc * rawsort
  | CCast of loc * constr_ast * constr_ast
  | CNotation of loc * string * constr_ast list
  | CNumeral of loc * Bignat.bigint
  | CDelimiters of loc * scope_name * constr_ast
  | CDynamic of loc * Dyn.t

and local_binder = name located list * constr_ast 

and fixpoint_expr = identifier * local_binder list * constr_ast * constr_ast

and cofixpoint_expr = identifier * constr_ast * constr_ast

let constr_loc = function
  | CRef (RIdent (loc,_)) -> loc
  | CRef (RQualid (loc,_)) -> loc
  | CFix (loc,_,_) -> loc
  | CCoFix (loc,_,_) -> loc
  | CArrow (loc,_,_) -> loc
  | CProdN (loc,_,_) -> loc
  | CLambdaN (loc,_,_) -> loc
  | CLetIn (loc,_,_,_) -> loc
  | CAppExpl (loc,_,_) -> loc
  | CApp (loc,_,_) -> loc
  | CCases (loc,_,_,_,_) -> loc
  | COrderedCase (loc,_,_,_,_) -> loc
  | CHole loc -> loc
  | CMeta (loc,_) -> loc
  | CSort (loc,_) -> loc
  | CCast (loc,_,_) -> loc
  | CNotation (loc,_,_) -> loc
  | CNumeral (loc,_) -> loc
  | CDelimiters (loc,_,_) -> loc
  | CDynamic _ -> dummy_loc

let cases_pattern_loc = function
  | CPatAlias (loc,_,_) -> loc
  | CPatCstr (loc,_,_) -> loc
  | CPatAtom (loc,_) -> loc
  | CPatNumeral (loc,_) -> loc

let replace_vars_constr_ast l t =
  if l = [] then t else failwith "replace_constr_ast: TODO"

let occur_var_constr_ast id t = Pp.warning "occur_var_constr_ast:TODO"; true
