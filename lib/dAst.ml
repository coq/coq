(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CAst

type ('a, _) thunk =
| Value : 'a -> ('a, 'b) thunk
| Thunk : 'a Lazy.t -> ('a, [ `thunk ]) thunk

type ('a, 'b) t = ('a, 'b) thunk CAst.t

let map_thunk (type s) f : (_, s) thunk -> (_, s) thunk = function
| Value x -> Value (f x)
| Thunk k -> Thunk (lazy (f (Lazy.force k)))

let get_thunk (type s) : ('a, s) thunk -> 'a = function
| Value x -> x
| Thunk k -> Lazy.force k

let get x = get_thunk x.v

let make ?loc v = CAst.make ?loc (Value v)

let delay ?loc v = CAst.make ?loc (Thunk (Lazy.from_fun v))

let map f n = CAst.map (fun x -> map_thunk f x) n

let map_with_loc f n =
  CAst.map_with_loc (fun ?loc x -> map_thunk (fun x -> f ?loc x) x) n

let map_from_loc f (loc, x) =
  make ?loc (f ?loc x)

let with_val f n = f (get n)

let with_loc_val f n = f ?loc:n.CAst.loc (get n)
