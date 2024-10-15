(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val ppripos : Vmemitcodes.reloc_info * 'a -> unit
val ppsort : Sorts.t -> unit
val print_idkey : Vmvalues.id_key -> unit
val ppzipper : Vmvalues.zipper -> unit
val ppstack : Vmvalues.stack -> unit
val ppatom : Vmvalues.atom -> unit
val ppwhd : Vmvalues.kind -> unit
val ppvblock : Vmvalues.vblock -> unit
val ppvarray : Vmvalues.values Parray.t -> unit
val ppvalues : Vmvalues.values -> unit
