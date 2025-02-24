(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tac2expr

(** {5 Hardwired data} *)

module Core :
sig

val t_unit : type_constant
val v_unit : Tac2val.valexpr

val t_list : type_constant
val c_nil : ltac_constructor
val c_cons : ltac_constructor

val t_int : type_constant
val t_option : type_constant
val t_string : type_constant
val t_array : type_constant

val c_true : ltac_constructor
val c_false : ltac_constructor

end

val throw : ?info:Exninfo.info -> exn -> 'a Proofview.tactic

val pf_apply : ?catch_exceptions:bool -> (Environ.env -> Evd.evar_map -> 'a Proofview.tactic) -> 'a Proofview.tactic

module type MapType = sig
  (** to have less boilerplate we use S.elt rather than declaring a toplevel type t *)
  module S : CSig.USetS
  module M : CMap.UExtS with type key = S.elt and module Set := S
  type valmap
  val valmap_eq : (valmap, Tac2val.valexpr M.t) Util.eq
  val repr : S.elt Tac2ffi.repr
end

type ('a,'set,'map) map_tag

val map_tag_eq : ('a,'set1,'map1) map_tag -> ('b,'set2,'map2) map_tag ->
  ('a * 'set1 * 'map1, 'b * 'set2 * 'map2) Util.eq option

type any_map_tag = Any : _ map_tag -> any_map_tag
type tagged_set = TaggedSet : (_,'set,_) map_tag * 'set -> tagged_set
type tagged_map = TaggedMap : (_,_,'map) map_tag * 'map -> tagged_map

val map_tag_repr : any_map_tag Tac2ffi.repr
val set_repr : tagged_set Tac2ffi.repr
val map_repr : tagged_map Tac2ffi.repr

val tag_set : (_,'set,_) map_tag -> 'set -> Tac2val.valexpr
val tag_map : (_,_,'map) map_tag -> 'map -> Tac2val.valexpr

val register_map : ?plugin:string -> tag_name:string
  -> (module MapType with type S.elt = 'a and type S.t = 'set and type valmap = 'map)
  -> ('a,'set,'map) map_tag
(** Register a type on which we can use finite sets and maps.
    [tag_name] is the name used for the external to make the
    [Ltac2.FSet.Tags.tag] available. *)

val get_map : ('a,'set,'map) map_tag ->
  (module MapType with type S.elt = 'a and type S.t = 'set and type valmap = 'map)

(** Default registered maps *)

val ident_map_tag : (Id.t, Id.Set.t, Tac2val.valexpr Id.Map.t) map_tag
val int_map_tag : (int, Int.Set.t, Tac2val.valexpr Int.Map.t) map_tag
val string_map_tag : (string, CString.Set.t, Tac2val.valexpr CString.Map.t) map_tag
val inductive_map_tag : (inductive, Indset_env.t, Tac2val.valexpr Indmap_env.t) map_tag
val constructor_map_tag : (constructor, Constrset_env.t, Tac2val.valexpr Constrmap_env.t) map_tag
val constant_map_tag : (Constant.t, Cset_env.t, Tac2val.valexpr Cmap_env.t) map_tag
