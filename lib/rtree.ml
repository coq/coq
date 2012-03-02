(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Errors
open Util


(* Type of regular trees:
   - Param denotes tree variables (like de Bruijn indices)
     the first int is the depth of the occurrence, and the second int
     is the index in the array of trees introduced at that depth
   - Node denotes the usual tree node, labelled with 'a
   - Rec(j,v1..vn) introduces infinite tree. It denotes
     v(j+1) with parameters 0..n-1 replaced by
     Rec(0,v1..vn)..Rec(n-1,v1..vn) respectively.
     Parameters n and higher denote parameters global to the
     current Rec node (as usual in de Bruijn binding system)
 *)
type 'a t =
    Param of int * int
  | Node of 'a * 'a t array
  | Rec of int * 'a t array

(* Building trees *)
let mk_rec_calls i = Array.init i (fun j -> Param(0,j))
let mk_node lab sons = Node (lab, sons)

(* The usual lift operation *)
let rec lift_rtree_rec depth n = function
    Param (i,j) as t -> if i < depth then t else Param (i+n,j)
  | Node (l,sons) -> Node (l,Array.map (lift_rtree_rec depth n) sons)
  | Rec(j,defs) ->
      Rec(j, Array.map (lift_rtree_rec (depth+1) n) defs)

let lift n t = if n=0 then t else lift_rtree_rec 0 n t

(* The usual subst operation *)
let rec subst_rtree_rec depth sub = function
    Param (i,j) as t ->
      if i < depth then t
      else if i-depth < Array.length sub then
        lift depth sub.(i-depth).(j)
      else Param (i-Array.length sub,j)
  | Node (l,sons) -> Node (l,Array.map (subst_rtree_rec depth sub) sons)
  | Rec(j,defs) ->
      Rec(j, Array.map (subst_rtree_rec (depth+1) sub) defs)

let subst_rtree sub t = subst_rtree_rec 0 [|sub|] t

(* To avoid looping, we must check that every body introduces a node
   or a parameter *)
let rec expand = function
  | Rec(j,defs) ->
      let sub = Array.init (Array.length defs) (fun i -> Rec(i,defs)) in
      expand (subst_rtree sub defs.(j))
  | t -> t

(* Given a vector of n bodies, builds the n mutual recursive trees.
   Recursive calls are made with parameters (0,0) to (0,n-1). We check
   the bodies actually build something by checking it is not
   directly one of the parameters of depth 0. Some care is taken to
   accept definitions like  rec X=Y and Y=f(X,Y) *)
let mk_rec defs =
  let rec check histo d =
    match expand d with
        Param(0,j) when List.mem j histo -> failwith "invalid rec call"
      | Param(0,j) -> check (j::histo) defs.(j)
      | _ -> () in
  Array.mapi (fun i d -> check [i] d; Rec(i,defs)) defs
(*
let v(i,j) = lift i (mk_rec_calls(j+1)).(j);;
let r = (mk_rec[|(mk_rec[|v(1,0)|]).(0)|]).(0);;
let r = mk_rec[|v(0,1);v(1,0)|];;
the last one should be accepted
*)

(* Tree destructors, expanding loops when necessary *)
let dest_param t =
  match expand t with
      Param (i,j) -> (i,j)
    | _ -> failwith "Rtree.dest_param"

let dest_node t =
  match expand t with
      Node (l,sons) -> (l,sons)
    | _ -> failwith "Rtree.dest_node"

let is_node t =
  match expand t with
      Node _ -> true
    | _ -> false


let rec map f t = match t with
    Param(i,j) -> Param(i,j)
  | Node (a,sons) -> Node (f a, Array.map (map f) sons)
  | Rec(j,defs) -> Rec (j, Array.map (map f) defs)

let rec smartmap f t = match t with
    Param _ -> t
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

(* Fixpoint operator on trees:
   f is the body of the fixpoint. Arguments passed to f are:
   - a boolean telling if the subtree has already been seen
   - the current subtree
   - a function to make recursive calls on subtrees
 *)
let fold f t =
  let rec fold histo t =
    let seen = List.mem t histo in
    let nhisto = if not seen then t::histo else histo in
    f seen (expand t) (fold nhisto) in
  fold [] t


(* Tests if a given tree is infinite, i.e. has an branch of infinte length. *)
let is_infinite t = fold
  (fun seen t is_inf ->
    seen ||
    (match t with
        Node(_,v) -> array_exists is_inf v
      | Param _ -> false
      | _ -> assert false))
  t

let fold2 f t x =
  let rec fold histo t x =
    let seen = List.mem (t,x) histo in
    let nhisto = if not seen then (t,x)::histo else histo in
    f seen (expand t) x (fold nhisto) in
  fold [] t x

let compare_rtree f = fold2
  (fun seen t1 t2 cmp ->
    seen ||
    let b = f t1 t2 in
    if b < 0 then false
    else if b > 0 then true
    else match expand t1, expand t2 with
        Node(_,v1), Node(_,v2) when Array.length v1 = Array.length v2 ->
          array_for_all2 cmp v1 v2
      | _ -> false)

let eq_rtree cmp t1 t2 =
  t1 == t2 || t1=t2 ||
  compare_rtree
    (fun t1 t2 ->
      if cmp (fst(dest_node t1)) (fst(dest_node t2)) then 0
      else (-1)) t1 t2

(* Pretty-print a tree (not so pretty) *)
open Pp

let rec pp_tree prl t =
  match t with
      Param (i,j) -> str"#"++int i++str","++int j
    | Node(lab,[||]) -> hov 2 (str"("++prl lab++str")")
    | Node(lab,v) ->
        hov 2 (str"("++prl lab++str","++brk(1,0)++
               prvect_with_sep pr_comma (pp_tree prl) v++str")")
    | Rec(i,v) ->
        if Array.length v = 0 then str"Rec{}"
        else if Array.length v = 1 then
          hov 2 (str"Rec{"++pp_tree prl v.(0)++str"}")
        else
          hov 2 (str"Rec{"++int i++str","++brk(1,0)++
                 prvect_with_sep pr_comma (pp_tree prl) v++str"}")
