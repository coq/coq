(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util

let boot = ref false

let batch_mode = ref false

let debug = ref false

let print_emacs = ref false

let emacs_str s = if !print_emacs then s else "" 

let term_quality = ref false

(* Silent / Verbose *)
let silent = ref false
let make_silent flag = silent := flag; ()
let is_silent () = !silent
let is_verbose () = not !silent

let silently f x =
  let oldsilent = !silent in
  try 
    silent := true;
    let rslt = f x in
    silent := oldsilent; 
    rslt
  with e -> begin
    silent := oldsilent; raise e
  end

let if_silent f x = if !silent then f x
let if_verbose f x = if not !silent then f x

(* The number of printed hypothesis in a goal *)

let print_hyps_limit = ref (None : int option)
let set_print_hyps_limit n = print_hyps_limit := Some n
let unset_print_hyps_limit () = print_hyps_limit := None
let print_hyps_limit () = !print_hyps_limit

(* A list of the areas of the system where "unsafe" operation
 * has been requested *)
let unsafe_set = ref Stringset.empty
let add_unsafe s = unsafe_set := Stringset.add s !unsafe_set
let is_unsafe s = Stringset.mem s !unsafe_set
