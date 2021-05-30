(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** [load_init_vernaculars opts ~state] Load vernaculars from
   the init (rc) file *)
val load_init_vernaculars : Coqargs.t -> state:Vernac.State.t-> Vernac.State.t

(** [compile_file opts] compile file specified in [opts] *)
val compile_file : Coqargs.t -> Stm.AsyncOpts.stm_opt -> Coqcargs.t -> Coqargs.injection_command list -> unit

(** [do_vio opts] process [.vio] files in [opts] *)
val do_vio : Coqargs.t -> Coqcargs.t -> Coqargs.injection_command list -> unit
