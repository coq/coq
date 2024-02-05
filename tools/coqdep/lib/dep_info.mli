(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Dep : sig
  type ml_kind = Pack | Lib
  (** Whether a plugin is using -pack (matters for the bytecode file extension).
      Note that dune (wrapped) is not using -pack. *)

  val byte_suff : ml_kind -> string

  type t =
  | Require of string
  (** module basename, to which we later append .vo or .vio or .vos *)
  | Ml of string * ml_kind
  (** plugin basename and whether it's using -pack, resolved from Declare Ml Module *)
  | Other of string
  (** load, meta, and external dependencies *)
end

type t =
  { name : string  (* This should become [module : Coq_module.t] eventually *)
  ; deps : Dep.t list
  }

val make : name:string -> deps:Dep.t list -> t
