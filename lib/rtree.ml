(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)


(* Type of regular trees:
   - Param denotes tree variables (like de Bruijn indices)
   - Node denotes the usual tree node, labelled with 'a
   - Rec(j,v1..vn) introduces infinite tree. It denotes
     v(j+1) with parameters 0..n-1 replaced by
     Rec(0,v1..vn)..Rec(n-1,v1..vn) respectively.
     Parameters n and higher denote parameters global to the
     current Rec node (as usual in de Bruijn binding system)
 *)
type 'a t =
    Param of int 
  | Node of 'a * 'a t array
  | Rec of int * 'a t array

(* Building trees *)
let mk_param i = Param i
let mk_node lab sons = Node (lab, sons)

(* Given a vector of n bodies, builds the n mutual recursive trees.
   Recursive calls are made with parameters 0 to n-1. We check
   the bodies actually build something by checking it is not
   directly one of the parameters 0 to n-1. *)
let mk_rec defs =
  Array.mapi
    (fun i d ->
      (match d with
          Param k when k < Array.length defs -> failwith "invalid rec call"
        | _ -> ());
      Rec(i,defs))
    defs

(* The usual lift operation *)
let rec lift_rtree_rec depth n = function
    Param i -> if i < depth then Param i else Param (i+n)
  | Node (l,sons) -> Node (l,Array.map (lift_rtree_rec depth n) sons)
  | Rec(j,defs) ->
      Rec(j, Array.map (lift_rtree_rec (depth+Array.length defs) n) defs)

let lift n t = if n=0 then t else lift_rtree_rec 0 n t

(* The usual subst operation *)
let rec subst_rtree_rec depth sub = function
    Param i ->
      if i < depth then Param i
      else if i-depth < Array.length sub then lift depth sub.(i-depth)
      else Param (i-Array.length sub)
  | Node (l,sons) -> Node (l,Array.map (subst_rtree_rec depth sub) sons)
  | Rec(j,defs) ->
      Rec(j, Array.map (subst_rtree_rec (depth+Array.length defs) sub) defs)

let subst_rtree sub t = subst_rtree_rec 0 sub t

let rec map f t = match t with
    Param i -> Param i
  | Node (a,sons) -> Node (f a, Array.map (map f) sons)
  | Rec(j,defs) -> Rec (j, Array.map (map f) defs)

let rec smartmap f t = match t with
    Param i -> t
  | Node (a,sons) -> 
      let a'=f a and sons' = Util.array_smartmap (map f) sons in
	if a'==a && sons'==sons then
	  t
	else
	  Node (a',sons')
  | Rec(j,defs) -> 
      let defs' = Util.array_smartmap (map f) defs in
	if defs'==defs then
	  t
	else
	  Rec(j,defs')

(* To avoid looping, we must check that every body introduces a node 
   or a parameter *)
let rec expand_rtree = function
  | Rec(j,defs) ->
      let sub = Array.init (Array.length defs) (fun i -> Rec(i,defs)) in
      expand_rtree (subst_rtree sub defs.(j))
  | t -> t

(* Tree destructors, expanding loops when necessary *)
let dest_param t = 
  match expand_rtree t with
      Param i -> i
    | _ -> failwith "dest_param"

let dest_node t = 
  match expand_rtree t with
      Node (l,sons) -> (l,sons)
    | _ -> failwith "dest_node"

(* Tests if a given tree is infinite or not. It proceeds *)
let rec is_infinite = function
    Param i -> i = (-1)
  | Node(_,sons) -> Util.array_exists is_infinite sons
  | Rec(j,defs) ->
      let newdefs =
        Array.mapi (fun i def -> if i=j then Param (-1) else def) defs in
      let sub =
        Array.init (Array.length defs)
          (fun i -> if i=j then Param (-1) else Rec(i,newdefs)) in
      is_infinite (subst_rtree sub defs.(j))

(* Pretty-print a tree (not so pretty) *)
open Pp

let rec pp_tree prl t =
  match t with
      Param k -> str"#"++int k
    | Node(lab,[||]) -> hov 2 (str"("++prl lab++str")")
    | Node(lab,v) ->
        hov 2 (str"("++prl lab++str","++brk(1,0)++
               Util.prvect_with_sep Util.pr_coma (pp_tree prl) v++str")")
    | Rec(i,v) ->
        if Array.length v = 0 then str"Rec{}"
        else if Array.length v = 1 then
          hov 2 (str"Rec{"++pp_tree prl v.(0)++str"}")
        else
          hov 2 (str"Rec{"++int i++str","++brk(1,0)++
                 Util.prvect_with_sep Util.pr_coma (pp_tree prl) v++str"}")
