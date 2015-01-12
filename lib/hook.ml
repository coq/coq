(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a content =
| Unset
| Default of 'a
| Set of 'a

type 'a t = 'a content ref

type 'a value = 'a t

let get (hook : 'a value) = match !hook with
| Unset -> assert false
| Default data | Set data -> data

let set (hook : 'a t) data = match !hook with
| Unset | Default _ -> hook := Set data
| Set _ -> assert false

let make ?default () =
  let data = match default with
  | None -> Unset
  | Some data -> Default data
  in
  let ans = ref data in
  (ans, ans)
