(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ *)

(*i*)
open Util
open Names
open Closure
open Summary
open Term
open Declarations
(*i*)

let tr_state = ref all_transparent

let state () = !tr_state

let _ = 
  declare_summary "Transparent constants and variables"
    { freeze_function = state;
      unfreeze_function = (fun ts -> tr_state := ts);
      init_function = (fun () -> tr_state := all_transparent);
      survive_section = false }

let is_evaluable env ref =
  match ref with
      EvalConstRef sp ->
        let (ids,sps) = !tr_state in
        Sppred.mem sp sps &
        let cb = Environ.lookup_constant sp env in
        cb.const_body <> None & not cb.const_opaque
    | EvalVarRef id ->
        let (ids,sps) = !tr_state in
        Idpred.mem id ids &
        Environ.lookup_named_value id env <> None

(* Modifying this state *)
let set_opaque_const sp =
  let (ids,sps) = !tr_state in
  tr_state := (ids, Sppred.remove sp sps)
let set_transparent_const sp =
  let (ids,sps) = !tr_state in
  let cb = Global.lookup_constant sp in
  if cb.const_body <> None & cb.const_opaque then
    error ("Cannot make "^Global.string_of_global (ConstRef sp)^
           " transparent because it was declared opaque.");
  tr_state := (ids, Sppred.add sp sps)

let set_opaque_var id =
  let (ids,sps) = !tr_state in
  tr_state := (Idpred.remove id ids, sps)
let set_transparent_var id =
  let (ids,sps) = !tr_state in
  tr_state := (Idpred.add id ids, sps)
