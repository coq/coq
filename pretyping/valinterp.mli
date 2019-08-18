(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Interpretation functions for generic arguments and interpreted Ltac
    values. *)

(** {6 Dynamic toplevel values} *)

module ValT : Dyn.S

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
