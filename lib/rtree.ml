(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util

(* Type of regular trees:
   - Param denotes tree variables (like de Bruijn indices)
     the first int is the depth of the occurrence, and the second int
     is the index in the array of trees introduced at that depth.
     Warning: Param's indices both start at 0!
   - Node denotes the usual tree node, labelled with 'a
   - Rec(j,v1..vn) introduces infinite tree. It denotes
     v(j+1) with parameters 0..n-1 replaced by
     Rec(0,v1..vn)..Rec(n-1,v1..vn) respectively.
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

let lift n t = if Int.equal n 0 then t else lift_rtree_rec 0 n t

(* The usual subst operation *)
let rec subst_rtree_rec depth sub = function
    Param (i,j) as t ->
      if i < depth then t
      else if i = depth then
        lift depth (Rec (j, sub))
      else Param (i - 1, j)
  | Node (l,sons) -> Node (l,Array.map (subst_rtree_rec depth sub) sons)
  | Rec(j,defs) ->
      Rec(j, Array.map (subst_rtree_rec (depth+1) sub) defs)

let subst_rtree sub t = subst_rtree_rec 0 sub t

(* To avoid looping, we must check that every body introduces a node
   or a parameter *)
let rec expand = function
  | Rec(j,defs) ->
      expand (subst_rtree defs defs.(j))
  | t -> t

(* Given a vector of n bodies, builds the n mutual recursive trees.
   Recursive calls are made with parameters (0,0) to (0,n-1). We check
   the bodies actually build something by checking it is not
   directly one of the parameters of depth 0. Some care is taken to
   accept definitions like  rec X=Y and Y=f(X,Y) *)
let mk_rec defs =
  let rec check histo d = match expand d with
  | Param (0, j) ->
    if Int.Set.mem j histo then failwith "invalid rec call"
    else check (Int.Set.add j histo) defs.(j)
  | _ -> ()
  in
  Array.mapi (fun i d -> check (Int.Set.singleton i) d; Rec(i,defs)) defs
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

module Smart =
struct

  let map f t = match t with
      Param _ -> t
    | Node (a,sons) ->
        let a'=f a and sons' = Array.Smart.map (map f) sons in
        if a'==a && sons'==sons then t
        else Node (a',sons')
    | Rec(j,defs) ->
        let defs' = Array.Smart.map (map f) defs in
        if defs'==defs then t
        else Rec(j,defs')

end

let smartmap = Smart.map

(** Structural equality test, parametrized by an equality on elements *)

let rec raw_eq cmp t t' = match t, t' with
  | Param (i,j), Param (i',j') -> Int.equal i i' && Int.equal j j'
  | Node (x, a), Node (x', a') -> cmp x x' && Array.equal (raw_eq cmp) a a'
  | Rec (i, a), Rec (i', a') -> Int.equal i i' && Array.equal (raw_eq cmp) a a'
  | _ -> false

let raw_eq2 cmp (t,u) (t',u') = raw_eq cmp t t' && raw_eq cmp u u'

(** Equivalence test on expanded trees. It is parametrized by two
    equalities on elements:
    - [cmp] is used when checking for already seen trees
    - [cmp'] is used when comparing node labels. *)

let equiv cmp cmp' =
  let rec compare histo t t' =
    List.mem_f (raw_eq2 cmp) (t,t') histo ||
    match expand t, expand t' with
    | Node(x,v), Node(x',v') ->
        cmp' x x' &&
        Int.equal (Array.length v) (Array.length v') &&
        Array.for_all2 (compare ((t,t')::histo)) v v'
    | _ -> false
  in compare []

(** The main comparison on rtree tries first physical equality, then
    the structural one, then the logical equivalence *)

let equal cmp t t' =
  t == t' || raw_eq cmp t t' || equiv cmp cmp t t'

(** Deprecated alias *)
let eq_rtree = equal

(** Intersection of rtrees of same arity *)
let rec inter cmp interlbl def n histo t t' =
  try
    let (i,j) = List.assoc_f (raw_eq2 cmp) (t,t') histo in
    Param (n-i-1,j)
  with Not_found ->
  match t, t' with
  | Param (i,j), Param (i',j') ->
      assert (Int.equal i i' && Int.equal j j'); t
  | Node (x, a), Node (x', a') ->
      (match interlbl x x' with
      | None -> mk_node def [||]
      | Some x'' -> Node (x'', Array.map2 (inter cmp interlbl def n histo) a a'))
  | Rec (i,v), Rec (i',v') ->
     (* If possible, we preserve the shape of input trees *)
     if Int.equal i i' && Int.equal (Array.length v) (Array.length v') then
       let histo = ((t,t'),(n,i))::histo in
       Rec(i, Array.map2 (inter cmp interlbl def (n+1) histo) v v')
     else
     (* Otherwise, mutually recursive trees are transformed into nested trees *)
       let histo = ((t,t'),(n,0))::histo in
       Rec(0, [|inter cmp interlbl def (n+1) histo (expand t) (expand t')|])
  | Rec _, _ -> inter cmp interlbl def n histo (expand t) t'
  | _ , Rec _ -> inter cmp interlbl def n histo t (expand t')
  | _ -> assert false

let inter cmp interlbl def t t' = inter cmp interlbl def 0 [] t t'

(** Inclusion of rtrees. We may want a more efficient implementation. *)
let incl cmp interlbl def t t' =
  equal cmp t (inter cmp interlbl def t t')

(** Tests if a given tree is infinite, i.e. has a branch of infinite length.
   This corresponds to a cycle when visiting the expanded tree.
   We use a specific comparison to detect already seen trees. *)

let is_infinite cmp t =
  let rec is_inf histo t =
    List.mem_f (raw_eq cmp) t histo ||
    match expand t with
    | Node (_,v) -> Array.exists (is_inf (t::histo)) v
    | _ -> false
  in
  is_inf [] t

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
        if Int.equal (Array.length v) 0 then str"Rec{}"
        else if Int.equal (Array.length v) 1 then
          hov 2 (str"Rec{"++pp_tree prl v.(0)++str"}")
        else
          hov 2 (str"Rec{"++int i++str","++brk(1,0)++
                 prvect_with_sep pr_comma (pp_tree prl) v++str"}")
