(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Errors

(* Table of vernac entries *)
let vernac_tab =
  (Hashtbl.create 51 :
    (Vernacexpr.extend_name, (Genarg.raw_generic_argument list -> unit -> unit)) Hashtbl.t)

let vinterp_add s f =
  try
    Hashtbl.add vernac_tab s f
  with Failure _ ->
    errorlabstrm "vinterp_add"
      (str"Cannot add the vernac command " ++ str (fst s) ++ str" twice.")

let overwriting_vinterp_add s f =
  begin
    try
      let _ = Hashtbl.find vernac_tab s in Hashtbl.remove vernac_tab s
    with Not_found -> ()
  end;
  Hashtbl.add vernac_tab s f

let vinterp_map s =
  try
    Hashtbl.find vernac_tab s
  with Failure _ | Not_found ->
    errorlabstrm "Vernac Interpreter"
      (str"Cannot find vernac command " ++ str (fst s) ++ str".")

let vinterp_init () = Hashtbl.clear vernac_tab

(* Interpretation of a vernac command *)

let call ?locality (opn,converted_args) =
  let loc = ref "Looking up command" in
  try
    let callback = vinterp_map opn in
    loc:= "Checking arguments";
    let hunk = callback converted_args in
    loc:= "Executing command";
    Locality.LocalityFixme.set locality;
    hunk();
    Locality.LocalityFixme.assert_consumed()
  with
    | Drop -> raise Drop
    | reraise ->
        let reraise = Errors.push reraise in
        if !Flags.debug then
	  msg_debug (str"Vernac Interpreter " ++ str !loc);
        iraise reraise
