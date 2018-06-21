(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Interpretation functions for generic arguments and interpreted Ltac
    values. *)

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
  val pr : 'a typ -> Pp.t

  val typ_list : t list typ
  val typ_opt : t option typ
  val typ_pair : (t * t) typ

  val inject : 'a tag -> 'a -> t

end

module ValTMap (Value : Dyn.ValueS) :
  Dyn.MapS with type 'a key = 'a Val.typ and type 'a value = 'a Value.t

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
  ('raw, 'glb, 'top) genarg_type -> ('glb, Val.t) interp_fun -> unit
