(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a content =
| Unset
| Set of 'a

type 'a t = 'a content ref

type 'a value = 'a t

let get (hook : 'a value) = match !hook with
| Unset -> assert false
| Set data -> data

let set (hook : 'a t) data = match !hook with
| Unset -> hook := Set data
| Set _ -> assert false

let make () =
  let ans = ref Unset in
  (ans, ans)
