(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Names

(* The abstract type of effects *)

type t

val bottom : t
val add_read  : identifier -> t -> t
val add_write : identifier -> t -> t

val get_reads : t -> identifier list
val get_writes : t -> identifier list
val get_repr : t -> (identifier list) * (identifier list)

val is_read  : t -> identifier -> bool    (* read-only *)
val is_write : t -> identifier -> bool    (* read-write *)

val compose : t -> t -> t

val union : t -> t -> t
val disj : t -> t -> t

val remove : t -> identifier -> t

val subst : (identifier * identifier) list -> t -> t


val pp : t -> Pp.std_ppcmds
val ppr : t -> unit

