(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type state_id = int
let initial_state_id = 1
let dummy_state_id = 0
let fresh_state_id, in_range =
  let cur = ref initial_state_id in
  (fun () -> incr cur; !cur), (fun id -> id >= 0 && id <= !cur)
let string_of_state_id = string_of_int
let state_id_of_int id = assert(in_range id); id
let int_of_state_id id = id
let newer_than id1 id2 = id1 > id2

let to_state_id = function
  | Element ("state_id",["val",i],[]) ->
      let id = int_of_string i in
      (* Coqide too to parse ids too, but cannot check if they are valid.
       * Hence we check for validity only if we are an ide slave. *)
      if !Flags.ide_slave then assert(in_range id);
      id
  | _ -> raise (Invalid_argument "to_state_id")
let of_state_id i = Element ("state_id",["val",string_of_int i],[])

let state_id_info : (state_id * state_id) Exninfo.t = Exninfo.make ()
let add_state_id exn ?(valid = initial_state_id) id =
  Exninfo.add exn state_id_info (valid, id)
let get_state_id exn = Exninfo.get exn state_id_info

module StateidOrderedType = struct type t = state_id let compare = compare end
