(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*s This module declares the extraction commands. *)

open Names
open Libnames

val extraction : reference -> unit
val extraction_rec : reference list -> unit
val extraction_file : string -> reference list -> unit
val extraction_module : identifier -> unit
val recursive_extraction_module : identifier -> unit

(* debug modules -- en cours *)

open Declarations

val cur_env : Environ.env ref 
val mp_short : module_path ref 
val toplevel : unit -> module_expr_body
val environment_until : dir_path option -> (dir_path * module_expr_body) list 
val print_seb : label * structure_elem_body -> unit 
val print_msb : module_structure_body -> unit 
val print_module : label -> module_body -> unit
val print_meb : module_expr_body  -> unit
val print_modtype : label -> module_type_body  -> unit
val print_sign : module_signature_body  -> unit
val print_spec : label * specification_body  -> unit
val print_all : unit -> unit
