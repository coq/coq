(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

type t
(** Flexible universe data.
    A level is flexible if [UnivFlex.mem] returns [true] on it.
    Flexible levels may have a definition, this induces a universe substitution.

    Only some flexible levels may be defined as algebraic universes. *)

val empty : t

val is_empty : t -> bool

val domain : t -> Level.Set.t
(** Contains both defined and undefined flexible levels. *)

val fold : (Level.t -> is_defined:bool -> 'a -> 'a) -> t -> 'a -> 'a
(** For universe minimization. *)

val mem : Level.t -> t -> bool
(** Returns [true] for both defined and undefined flexible levels. *)

val is_algebraic : Level.t -> t -> bool
(** Is the level allowed to be defined by an algebraic universe? *)

val make_nonalgebraic_variable : t -> Level.t -> t
(** Make the level non algebraic. Undefined behaviour on
    already-defined algebraics. *)

val make_all_undefined_nonalgebraic : t -> t
(** Turn all undefined flexible algebraic variables into simply flexible
    ones. Can be used in case the variables might appear in universe instances
    (typically for polymorphic program obligations). *)

val fix_undefined_variables : t -> t
(** Make all undefined flexible levels into rigid levels, ie remove them. *)

val add : Level.t -> algebraic:bool -> t -> t
(** Makes a level flexible with no definition.
    It must not already be flexible. *)

val remove :  Level.t -> t -> t

val add_levels : Level.Set.t -> algebraic:bool -> t -> t
(** Make the levels flexible with no definitions.
    They must not already be flexible.  *)

val define : Level.t -> Universe.t -> t -> t
(** Define the level to the given universe. The level must already
    be flexible and must be undefined. *)

val constrain_variables : Level.Set.t -> t -> ContextSet.t -> ContextSet.t * t
(** [constrain_variables diff subst ctx] removes bindings [l := l']
    from the substitution where [l] is in [diff] and [l'] is a
    level, and adds [l, l = l'] to [ctx]. *)

val biased_union : t -> t -> t
(** [biased_union x y] favors the bindings of the first map that are defined,
    otherwise takes the second's bindings. *)

val normalize : t -> t
(** Return an optimized representation of the input *)

val normalize_univ_variables : t -> t * Level.Set.t * UnivSubst.universe_subst_fn
(** As [normalize] and also returns the set of defined variables
    and a function which is equivalent to calling [normalize_univ_variable]
    on the substitution but may be faster. *)

val normalize_univ_variable : t -> UnivSubst.universe_subst_fn
(** Apply the substitution to a variable. *)

val normalize_universe : t -> Universe.t -> Universe.t
(** Apply the substitution to an algebraic universe. *)

val pr : (Level.t -> Pp.t) -> t -> Pp.t
(** "Show Universes"-style printing.  *)
