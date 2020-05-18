(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type status = Disabled | Enabled | AsError

(** The list of warnings categories that are used in the code of Coq.
    The Other category may be used by external plugin authors who do
    not wish to be limited to this list.  *)
type category =
  | Automation
  | Bytecode_compiler
  | Debug
  | Deprecated
  | Dev
  | Extraction
  | Filesystem
  | Fixpoints
  | Fragile
  | Funind
  | Implicits
  | Loadpath
  | Ltac
  | Native_compiler
  | Non_interactive
  | Notation
  | Numbers
  | Option
  | Parsing
  | Pattern_matching
  | Pedantic
  | Records
  | Require
  | Schemes
  | Scope
  | Ssr
  | Syntax
  | Tactics
  | Typechecker
  | Typeclasses
  | Vernacular
  | Other of string

val create : name:string -> category:category -> ?default:status ->
             ('a -> Pp.t) -> ?loc:Loc.t -> 'a -> unit

val get_flags : unit -> string
val set_flags : string -> unit

(** Cleans up a user provided warnings status string, e.g. removing unknown
    warnings (in which case a warning is emitted) or subsumed warnings . *)
val normalize_flags_string : string -> string
