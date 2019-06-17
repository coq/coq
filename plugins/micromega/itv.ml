(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Intervals (extracted from mfourier.ml) *)

open Num

  (** The type of intervals is *)
  type interval = num option * num option
      (** None models the absence of bound i.e. infinity
          As a result,
          - None , None   -> \]-oo,+oo\[
          - None , Some v -> \]-oo,v\]
          - Some v, None  -> \[v,+oo\[
          - Some v, Some v' -> \[v,v'\]
      Intervals needs to be explicitly normalised.
      *)

  let pp o (n1,n2) =
      (match n1 with
       | None -> output_string o "]-oo"
       | Some n  -> Printf.fprintf o "[%s" (string_of_num n)
      );
      output_string o ",";
      (match n2 with
       | None -> output_string o "+oo["
       | Some n -> Printf.fprintf o "%s]" (string_of_num n)
      )



  (** if then interval [itv] is empty, [norm_itv itv] returns [None]
      otherwise, it returns [Some itv] *)

  let norm_itv itv =
    match itv with
      | Some a , Some b -> if a <=/ b then Some itv else None
      |   _             -> Some itv

(** [inter i1 i2 = None] if the intersection of intervals is empty
    [inter i1 i2 = Some i] if [i] is the intersection of the intervals [i1] and [i2] *)
  let inter i1 i2 =
    let (l1,r1) = i1
    and (l2,r2) = i2 in

    let inter f o1 o2 =
      match o1 , o2 with
        | None , None -> None
        | Some _ , None -> o1
        | None  , Some _ -> o2
        | Some n1 , Some n2 -> Some (f n1 n2) in

    norm_itv (inter max_num l1 l2 , inter min_num r1 r2)

  let range = function
    | None,_ | _,None -> None
    | Some i,Some j -> Some (floor_num j -/ceiling_num i +/ (Int 1))


  let smaller_itv i1 i2 =
    match  range i1 ,  range i2  with
      | None , _ -> false
      |  _   , None -> true
      | Some i , Some j -> i <=/ j


(** [in_bound bnd v] checks whether [v] is within the bounds [bnd] *)
let in_bound bnd v =
  let (l,r) = bnd in
  match l , r with
    | None , None -> true
    | None , Some a -> v <=/ a
    | Some a , None -> a <=/ v
    | Some a , Some b -> a <=/ v && v <=/ b
