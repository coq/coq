(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names
open Nameops
open Pmisc

(* The type of effects.
 *
 * An effect is composed of two lists (r,w) of variables.
 * The first one is the list of read-only variables
 * and the second one is the list of read-write variables.
 *
 * INVARIANT: 1. each list is sorted in decreasing order for Pervasives.compare
 *            2. there are no duplicate elements in each list
 *            3. the two lists are disjoint
 *)

type t = identifier list * identifier list


(* the empty effect *)

let bottom = ([], [])

(* basic operations *)

let push x l =
  let rec push_rec = function
      [] -> [x]
    | (y::rem) as l ->
	if x = y then l else if x > y then x::l else y :: push_rec rem
  in
    push_rec l

let basic_remove x l =
  let rec rem_rec = function
      [] -> []
    | y::l -> if x = y then l else y :: rem_rec l
  in
    rem_rec l

let mem x (r,w) = (List.mem x r) or (List.mem x w)

let rec basic_union = function
    [], s2 -> s2
  | s1, [] -> s1
  | ((v1::l1) as s1), ((v2::l2) as s2) ->
      if v1 > v2 then
	v1 :: basic_union (l1,s2)
      else if v1 < v2 then
	v2 :: basic_union (s1,l2)
      else
	v1 :: basic_union (l1,l2)

(* adds reads and writes variables *)

let add_read id ((r,w) as e) =
  (* if the variable is already a RW it is ok, otherwise adds it as a RO. *)
  if List.mem id w then
    e
  else
    push id r, w

let add_write id (r,w) =
  (* if the variable is a RO then removes it from RO. Adds it to RW. *)
  if List.mem id r then
    basic_remove id r, push id w
  else
    r, push id w

(* access *)

let get_reads = basic_union
let get_writes = snd
let get_repr e = (get_reads e, get_writes e)

(* tests *)

let is_read  (r,_) id = List.mem id r
let is_write (_,w) id = List.mem id w

(* union and disjunction *)

let union (r1,w1) (r2,w2) = basic_union (r1,r2), basic_union (w1,w2)

let rec diff = function
    [], s2 -> []
  | s1, [] -> s1
  | ((v1::l1) as s1), ((v2::l2) as s2) ->
      if v1 > v2 then
	v1 :: diff (l1,s2)
      else if v1 < v2 then
	diff (s1,l2)
      else
	diff (l1,l2)

let disj (r1,w1) (r2,w2) =
  let w1_w2 = diff (w1,w2) and w2_w1 = diff (w2,w1) in
  let r = basic_union (basic_union (r1,r2), basic_union (w1_w2,w2_w1))
  and w = basic_union (w1,w2) in
  r,w

(* comparison relation *)

let le e1 e2 = failwith "effects: le: not yet implemented"

let inf e1 e2 = failwith "effects: inf: not yet implemented"

(* composition *)

let compose (r1,w1) (r2,w2) =
  let r = basic_union (r1, diff (r2,w1)) in
  let w = basic_union (w1,w2) in
    r,w

(* remove *)

let remove (r,w) name = basic_remove name r, basic_remove name w

(* substitution *)

let subst_list (x,x') l =
  if List.mem x l then push x' (basic_remove x l) else l

let subst_one (r,w) s = subst_list s r, subst_list s w

let subst s e = List.fold_left subst_one e s

(* pretty-print *)

open Pp
open Util
open Himsg

let pp (r,w) =
  hov 0 (if r<>[] then
	     (str"reads " ++
		prlist_with_sep (fun () -> (str"," ++ spc ())) pr_id r)
	   else (mt ()) ++
	   spc () ++
	   if w<>[] then
	     (str"writes " ++
		prlist_with_sep (fun ()-> (str"," ++ spc ())) pr_id w)
	   else (mt ())
)

let ppr e =
  Pp.pp (pp e)

