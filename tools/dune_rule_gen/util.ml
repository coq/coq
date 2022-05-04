(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*             Xavier Leroy, projet Cristal, INRIA Rocquencourt           *)
(*                                                                        *)
(*   Copyright 1996 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file keeps coq_dune self-contained as it is a "bootstrap" utility *)
(* Taken from OCaml's stdlib                                              *)

(* From OCaml's Stdlib >= 4.10 *)
let list_concat_map f l =
  let rec aux f acc = function
    | [] -> List.rev acc
    | x :: l ->
       let xs = f x in
       aux f (List.rev_append xs acc) l
  in aux f [] l

let rec pmap f = function
  | [] -> []
  | x :: xs ->
    match f x with
    | None -> pmap f xs
    | Some x -> x :: pmap f xs
