(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type t = int

let repr x = x
let unsafe_of_int x = x
let compare = Int.compare
let equal = Int.equal
let hash = Int.hash
let print x = Pp.(str "?X" ++ int x)

module Cache =
struct
  type t = int
  let none = -1
  let make n =
    let () = assert (n >= 0) in
    n
  let length n = if n < 0 then None else Some n

  let is_none n = n < 0

  module List =
  struct

    let map n f l =
      if is_none n then none, CList.Smart.map f l
      else
        let rec map_loop f l = match l with
        | [] -> 0, []
        | x :: r ->
          let x' = f x in
          let n, r' = map_loop f r in
          if x == x' && r == r' then n, l
          else n + 1, x' :: r'
        in
        let m, l = map_loop f l in
        let n = if n < m then m else n in
        n, l

    let map_prefix n f l =
      if is_none n then CList.Smart.map f l
      else
        let rec map_prefix_loop i f l =
          if Int.equal i 0 then l
          else match l with
          | [] -> assert false
          | x :: r ->
            let x' = f x in
            let r' = map_prefix_loop (i - 1) f r in
            if x == x' && r == r' then l else x' :: r'
        in
        map_prefix_loop n f l

    let iter_prefix n f l =
      if is_none n then List.iter f l
      else
        let rec iter n f l =
          if Int.equal n 0 then ()
          else match l with
          | [] -> assert false
          | x :: l -> f x; iter (n - 1) f l
        in
        iter n f l

    let prefix n l =
      if is_none n then l else CList.firstn n l
  end
end

module Set = Int.Set
module Map = Int.Map
