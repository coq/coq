(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Util
open Term
open Environ
open Declarations

let isSymbol f env = match kind_of_term f with
  | Const kn ->
      let cb = lookup_constant kn env in
      cb.const_body = None & not cb.const_opaque
  | _ -> false

let head_symbol c env =
  match kind_of_term c with
    | App (f,_) when isSymbol f env -> destConst f
    | _ when isSymbol c env -> destConst c
    | _ -> error "Ill-formed rule"
   
let check_rule env (l,r as rule) =
  let kn = head_symbol l env in
  (* TODO *)
  kn, rule
