(***************************************************************************

Balanced trees with one data info

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

type 'a t = Empty | Node of 'a t * 'a * 'a t * int

  
let height = function
    Empty -> 0
  | Node(_, _, _, h) -> h
;;

(* Creates a new node with left son l, value x and right son r.
   l and r must be balanced and | height l - height r | <= 2.
   Inline expansion of height for better speed. *)

let create l x r =
  let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
  Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))
;;

(* Same as create, but performs one step of rebalancing if necessary.
   Assumes l and r balanced.
   Inline expansion of create for better speed in the most frequent case
   where no rebalancing is required. *)

let bal l x r =
  let hl = match l with Empty -> 0 | Node(_,_,_,h) -> h in
  let hr = match r with Empty -> 0 | Node(_,_,_,h) -> h in
  if hl > hr + 2 then begin
    match l with
        Empty -> invalid_arg "Balanced_trees.bal"
      | Node(ll, lv, lr, _) ->
          if height ll >= height lr then
            create ll lv (create lr x r)
          else begin
            match lr with
                Empty -> invalid_arg "Balanced_trees.bal"
              | Node(lrl, lrv, lrr, _)->
                  create (create ll lv lrl) lrv (create lrr x r)
          end
  end else if hr > hl + 2 then begin
    match r with
        Empty -> invalid_arg "Balanced_trees.bal"
      | Node(rl, rv, rr, _) ->
          if height rr >= height rl then
            create (create l x rl) rv rr
          else begin
            match rl with
                Empty -> invalid_arg "Balanced_trees.bal"
              | Node(rll, rlv, rlr, _) ->
                  create (create l x rll) rlv (create rlr rv rr)
          end
  end else
    Node(l, x, r, (if hl >= hr then hl + 1 else hr + 1))
;;


(* Same as bal, but repeat rebalancing until the final result
   is balanced. *)

let rec join l x r =
  match bal l x r with
      Empty -> invalid_arg "Balanced_trees.join"
    | Node(l', x', r', _) as t' ->
        let d = height l' - height r' in
        if d < -2 or d > 2 then join l' x' r' else t'
;;


(* Merge two trees l and r into one.
   All elements of l must precede the elements of r.
   Assumes | height l - height r | <= 2. *)

let rec merge t1 t2 =
  match (t1, t2) with
      (Empty, t) -> t
    | (t, Empty) -> t
    | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
        bal l1 v1 (bal (merge r1 l2) v2 r2)
;;


(* Same as merge, but does not assume anything about l and r. *)

let rec concat t1 t2 =
  match (t1, t2) with
      (Empty, t) -> t
    | (t, Empty) -> t
    | (Node(l1, v1, r1, h1), Node(l2, v2, r2, h2)) ->
        join l1 v1 (join (concat r1 l2) v2 r2)
;;



