(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Environ
open Rawterm
open Termops
(*i*)

(* [detype env avoid nenv c] turns [c], typed in [env], into a rawconstr. *)
(* De Bruijn indexes are turned to bound names, avoiding names in [avoid] *)

val detype : bool * env -> identifier list -> names_context -> constr -> 
  rawconstr

val detype_case : 
  bool -> ('a -> rawconstr) ->
  (constructor -> int -> 'a -> loc * identifier list * cases_pattern list *
    rawconstr) -> ('a -> int -> bool) ->
    env -> identifier list -> inductive -> case_style ->
      'a option -> int -> 'a -> 'a array -> rawconstr

(* look for the index of a named var or a nondep var as it is renamed *)
val lookup_name_as_renamed  : env -> constr -> identifier -> int option
val lookup_index_as_renamed : env -> constr -> int -> int option


val force_wildcard : unit -> bool
val synthetize_type : unit -> bool
val force_if : case_info -> bool
val force_let : case_info -> bool
