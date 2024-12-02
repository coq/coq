(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

[@@@warning "-32"]

(** We need to declare an external from each C file to convince ocaml
    to include the C code in the cmxs for dynlink.

    NB: it seems in practice we don't actually need one from each C
    file, I guess if we have a.c and b.c and declare an external from
    b.c whose implementation involves a.c it is enough to work.
*)

(* rocq_fix_code.c *)
external accumulate : unit -> Obj.t = "rocq_accumulate"

(* rocq_interp.c *)
external push_val : Obj.t -> unit = "rocq_push_val"

(* rocq_values.c *)
external is_accumulate : Obj.t -> bool = "rocq_is_accumulate_code"

(* rocq_float64.c *)
external mul : float -> float -> float = "rocq_fmul_byte" "rocq_fmul"
[@@unboxed] [@@noalloc]

(* rocq_memory.c *)
external init_vm : unit -> unit = "init_rocq_vm"
