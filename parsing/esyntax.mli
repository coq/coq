(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Pp
open Extend
(*i*)

(* Syntax entry tables. *)

type frozen_t

(* pretty-printer summary operations *)
val init : unit -> unit
val freeze : unit -> frozen_t
val unfreeze : frozen_t -> unit

(* Search and add a PP rule for an ast in the summary *)
val find_syntax_entry :
  string -> Coqast.t -> (syntax_entry * Ast.env) option
val add_rule : string -> syntax_entry -> unit
val add_ppobject : syntax_command -> unit
val warning_verbose : bool ref

(* Pretty-printing *)

type std_printer = Coqast.t -> std_ppcmds
type unparsing_subfunction = string -> tolerability option -> std_printer

(* Module of primitive printers *)
module Ppprim :
  sig
    type t = std_printer -> std_printer
    val add : string * t -> unit
  end

(* Generic printing functions *) 
val token_printer: std_printer -> std_printer
val print_syntax_entry : 
  string -> unparsing_subfunction -> Ast.env -> syntax_entry -> std_ppcmds
val genprint : std_printer -> unparsing_subfunction
