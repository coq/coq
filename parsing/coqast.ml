(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*i*)
open Util
open Names
open Libnames
(*i*)

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
