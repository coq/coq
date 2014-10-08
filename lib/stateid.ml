(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Xml_datatype

type t = int
let initial = 1
let dummy = 0
let fresh, in_range =
  let cur = ref initial in
  (fun () -> incr cur; !cur), (fun id -> id >= 0 && id <= !cur)
let to_string = string_of_int
let of_int id = assert(in_range id); id
let to_int id = id
let newer_than id1 id2 = id1 > id2

let of_xml = function
  | Element ("state_id",["val",i],[]) ->
      let id = int_of_string i in
      (* Coqide too to parse ids too, but cannot check if they are valid.
       * Hence we check for validity only if we are an ide slave. *)
      if !Flags.ide_slave then assert(in_range id);
      id
  | _ -> raise (Invalid_argument "to_state_id")
let to_xml i = Element ("state_id",["val",string_of_int i],[])

let state_id_info : (t * t) Exninfo.t = Exninfo.make ()
let add exn ?(valid = initial) id =
  Exninfo.add exn state_id_info (valid, id)
let get exn = Exninfo.get exn state_id_info

let equal = Int.equal
let compare = Int.compare

module Set = Set.Make(struct type t = int let compare = compare end)

type ('a,'b) request = {
  exn_info : t * t;
  stop : t;
  document : 'b;
  loc : Loc.t;
  uuid     : 'a;
  name     : string
}

