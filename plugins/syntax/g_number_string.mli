(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val wit_number_string_mapping :
  (bool * Libnames.qualid * Libnames.qualid, unit, unit) Genarg.genarg_type

val number_string_mapping :
  (bool * Libnames.qualid * Libnames.qualid) Pcoq.Entry.t

val wit_number_string_via :
  (Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list,
   unit, unit)
  Genarg.genarg_type

val number_string_via :
  (Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list)
  Pcoq.Entry.t

val wit_number_modifier :
  (Number.number_option, unit, unit)
  Genarg.genarg_type

val number_modifier :
  Number.number_option Pcoq.Entry.t

val wit_number_options :
  (Number.number_option list, unit, unit)
  Genarg.genarg_type

val number_options :
  Number.number_option list Pcoq.Entry.t

val wit_string_option :
  (Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list,
   unit, unit)
  Genarg.genarg_type

val string_option :
  (Libnames.qualid * (bool * Libnames.qualid * Libnames.qualid) list)
  Pcoq.Entry.t
