(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Interpretation functions for generic arguments. *)

open Names
open Genarg

(** {6 Dynamic toplevel values} *)

module Val :
sig
  type 'a typ

  val create : string -> 'a typ

  type _ tag =
  | Base : 'a typ -> 'a tag
  | List : 'a tag -> 'a list tag
  | Opt : 'a tag -> 'a option tag
  | Pair : 'a tag * 'b tag -> ('a * 'b) tag

  type t = Dyn : 'a typ * 'a -> t

  val eq : 'a typ -> 'b typ -> ('a, 'b) CSig.eq option
  val repr : 'a typ -> string
  val pr : 'a typ -> Pp.std_ppcmds

  val list_tag : t list typ
  val opt_tag : t option typ
  val pair_tag : (t * t) typ

  val inject : 'a tag -> 'a -> t

end
(** Dynamic types for toplevel values. While the generic types permit to relate
    objects at various levels of interpretation, toplevel values are wearing
    their own type regardless of where they came from. This allows to use the
    same runtime representation for several generic types. *)

val val_tag : 'a typed_abstract_argument_type -> 'a Val.tag
(** Retrieve the dynamic type associated to a toplevel genarg. *)

val register_val0 : ('raw, 'glb, 'top) genarg_type -> 'top Val.tag option -> unit
(** Register the representation of a generic argument. If no tag is given as
    argument, a new fresh tag with the same name as the argument is associated
    to the generic type. *)

(** {6 Interpretation functions} *)

module TacStore : Store.S

type interp_sign = {
  lfun : Val.t Id.Map.t;
  extra : TacStore.t }

type ('glb, 'top) interp_fun = interp_sign -> 'glb -> 'top Ftactic.t

val interp : ('raw, 'glb, 'top) genarg_type -> ('glb, Val.t) interp_fun

val register_interp0 :
  ('raw, 'glb, 'top) genarg_type -> ('glb, 'top) interp_fun -> unit
