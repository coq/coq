(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Libnames
open Himsg
open Proof_type
open Tacinterp
open Vernacexpr

let disable_drop e =
  if e <> Drop then e
  else UserError("Vernac.disable_drop",(str"Drop is forbidden."))

(* Table of vernac entries *)
let vernac_tab =
  (Hashtbl.create 51 :
    (string, Tacexpr.raw_generic_argument list -> unit -> unit) Hashtbl.t)

let vinterp_add s f =
  try 
    Hashtbl.add vernac_tab s f
  with Failure _ ->
    errorlabstrm "vinterp_add"
      (str"Cannot add the vernac command " ++ str s ++ str" twice")

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
  with Not_found -> 
    errorlabstrm "Vernac Interpreter"
      (str"Cannot find vernac command " ++ str s)

let vinterp_init () = Hashtbl.clear vernac_tab

(* Interpretation of a vernac command *)

let call (opn,converted_args) =
  let loc = ref "Looking up command" in
  try
    let callback = vinterp_map opn in
    loc:= "Checking arguments";
    let hunk = callback converted_args in
    loc:= "Executing command";
    hunk()
  with
    | Drop -> raise Drop
    | ProtectedLoop -> raise ProtectedLoop
    | e ->
        if !Flags.debug then
	  msgnl (str"Vernac Interpreter " ++ str !loc);
        raise e

let bad_vernac_args s =
  anomalylabstrm s
    (str"Vernac " ++ str s ++ str" called with bad arguments")
