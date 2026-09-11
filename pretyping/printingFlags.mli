(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Detype : sig
  type t = {
    universes : bool;
    sorts : bool;
    (** Should we print hidden sort quality variables? *)
    qualities : bool;
    relevances : bool;
    (** If true, prints full local context of evars *)
    evar_instances : bool;
    wildcard : bool;
    fast_names : bool;
    synth_match_return : bool;
    matching : bool;
    primproj_params : bool;
    unfolded_primproj_as_match : bool;
    match_paramunivs : bool;
    always_regular_match_style : bool;
    nonpropositional_letin_types : bool;
  }

  val make_raw : t -> t

  val current : unit -> t

  val current_ignore_raw : unit -> t
end

module Extern : sig
  module FactorizeEqns : sig
    type t = {
      (* If true, contract branches with same r.h.s. and same matching
          variables in a disjunctive pattern *)
      factorize_match_patterns : bool;
      (* If this flag is true and the last non unique clause of a
          "match" is a variable-free disjunctive pattern, turn it into a
          catch-call case *)
      allow_match_default_clause : bool;
    }

    val make_raw : t -> t

    val current : unit -> t

    val current_ignore_raw : unit -> t
  end

  module Records : sig
    type t

    val make_raw : t -> t

    val current : unit -> t

    val current_ignore_raw : unit -> t

    (** Tells whether record syntax should be used for some record. If
        the inductive is not a record, the result is meaningless. *)
    val use_record_syntax : t -> Names.inductive -> bool
  end

  type t = {
    (* This tells to skip types if a variable has this type by default *)
    use_implicit_types : bool;
    records : Records.t;
    implicits : bool;
    (** When [implicits] is on then [implicits_explicit_args] tells
        how implicit args are printed. If on, implicit args are
        printed with the form (id:=arg) otherwise arguments are
        printed normally and the function is prefixed by "@". *)
    implicits_explicit_args : bool;
    (* Tells if implicit arguments not known to be inferable from a rigid
        position are systematically printed *)
    implicits_defensive : bool;
    coercions : bool;
    parentheses : bool;
    notations : bool;
    (* primitive tokens, like strings *)
    raw_literals : bool;
    (* This governs printing of projections using the dot notation symbols *)
    projections : bool;
    float : bool;
    factorize_eqns : FactorizeEqns.t;
    (* None = unlimited *)
    depth : int option;
  }

  val make_raw : t -> t

  val current : unit -> t

  val current_ignore_raw : unit -> t
end

(** Combined detyping and extern flags. *)
type t = {
  detype : Detype.t;
  extern : Extern.t;
}

val make_raw : t -> t

val current : unit -> t

val current_ignore_raw : unit -> t

(** The following flags are still accessed directly, but not when printing constr. *)
val print_universes : bool ref
val print_sorts : bool ref

module PrintingInductiveMake (_ : sig
    val encode : Environ.env -> Libnames.qualid -> Names.inductive
    val member_message : Pp.t -> bool -> Pp.t
    val field : string
    val title : string
  end)
  : Goptions.RefConvertArg
    with type t = Names.inductive
     and module Set = Names.Indset_env

val set_extern_depth : int option -> unit
