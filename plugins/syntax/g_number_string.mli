(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Number_string

val wit_number_string_mapping :
  (bool * Libnames.qualid * Libnames.qualid) Genarg.vernac_genarg_type

val number_string_mapping :
  (bool * Libnames.qualid * Libnames.qualid) Procq.Entry.t

val wit_number_string_via : number_string_via Genarg.vernac_genarg_type

val number_string_via : number_string_via Procq.Entry.t

val wit_number_modifier : number_option Genarg.vernac_genarg_type

val number_modifier : number_option Procq.Entry.t

val wit_number_options : number_option list Genarg.vernac_genarg_type

val number_options :
  number_option list Procq.Entry.t

val wit_string_option : number_string_via Genarg.vernac_genarg_type

val string_option : number_string_via Procq.Entry.t
