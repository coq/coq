(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val output : out_channel -> vname:string ->
  data_files:string array ->
  (BenchUtil.source_loc * BenchUtil.measure array) array -> unit

val max_data_count : int
(** Max length supported for the inner [measure array]. *)

val raw_output : out_channel -> min_diff:Q.t ->
  (BenchUtil.source_loc * BenchUtil.measure array) array -> unit
