(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pp
open Util
open Names
open Ptype
open Past

val unbound_variable : identifier -> loc option -> 'a
val unbound_reference : identifier -> loc option -> 'a

val clash : identifier -> loc option -> 'a
val not_defined : identifier -> 'a

val check_for_reference : loc -> identifier -> type_v -> unit
val check_for_array     : loc -> identifier -> type_v -> unit

val check_for_index_type : loc -> type_v -> unit
val check_no_effect : loc -> Peffect.t -> unit
val should_be_boolean : loc -> 'a
val test_should_be_annotated : loc -> 'a
val if_branches : loc -> 'a

val check_for_not_mutable : loc -> type_v -> unit
val check_for_pure_type : loc -> type_v -> unit
val check_for_let_ref : loc -> type_v -> unit

val variant_informative : loc -> 'a
val should_be_informative : loc -> 'a

val app_of_non_function : loc -> 'a
val partial_app : loc -> 'a
val expected_type : loc -> std_ppcmds -> 'a
val expects_a_type : identifier -> loc -> 'a
val expects_a_term : identifier -> 'a
val should_be_a_variable : loc -> 'a
val should_be_a_reference : loc -> 'a
