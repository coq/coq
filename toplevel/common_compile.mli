(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* [fatal_error msg] prints msg and exits 1 *)
val fatal_error : Pp.t -> 'a

(* [ensure ext src tgt] checks that, once stripped by ext, both [src] and
   [tgt] have the same basename, and returns [tgt] with the extension.
   [ext] is expected to begin with dot, eg [".v"]. *)
val ensure : ext:string -> src:string -> tgt:string -> string

(* [ensure_exists f] fails if f does not exist *)
val ensure_exists : string -> unit

(* [ensure_exists_with_prefix src tgt src_ext tgt_ext] checks that [src] exists
   (if needed adding the extension) and that [tgt] exists (if needed adding the
   extension) and returns [src] and [tgt] with their respective extensions.
   If [tgt] is [None], then it defaults to [src] (with [tgt_ext] as extension).
   [src_ext] and [tgt_ext] are expected to begin with dot, eg [".v"]. *)
val ensure_exists_with_prefix : src:string -> tgt:string option -> src_ext:string -> tgt_ext:string -> string * string

(* [chop_extension f] is like Filename.chop_extension but fail safe *)
val safe_chop_extension : string -> string

(* [ensure_no_pending_proofs ~filename] checks that no proof or obligation
   is open *)
val ensure_no_pending_proofs : filename:string -> Vernacstate.t -> unit
