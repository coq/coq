(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This module implements the syntactic interpretation phase of vernacular
commands. The main entry point is [synterp_control], which transforms a
vernacexpr into a [vernac_control_entry]. *)

open Names
open Libnames

val module_locality : bool Attributes.attribute

val with_locality : atts:Attributes.vernac_flags -> (local:bool option -> 'a) -> 'a

val with_module_locality :
  atts:Attributes.vernac_flags -> (module_local:bool -> 'a) -> 'a

val with_generic_atts :
  check:bool -> Attributes.vernac_flags -> (atts:Attributes.vernac_flags -> 'a) -> 'a

type module_entry = Modintern.module_struct_expr * Names.ModPath.t * Modintern.module_kind * Entries.inline

type synterp_entry =
  | EVernacNoop
  | EVernacNotation of { local : bool; decl : Metasyntax.notation_interpretation_decl }
  | EVernacBeginSection of Names.lident
  | EVernacEndSegment of Names.lident
  | EVernacRequire of
      Library.library_t list * DirPath.t list * Vernacexpr.export_with_cats option * (qualid * Vernacexpr.import_filter_expr) list
  | EVernacImport of (Vernacexpr.export_flag * Libobject.open_filter) *
      (Names.ModPath.t CAst.t * Vernacexpr.import_filter_expr) list
  | EVernacDeclareModule of Lib.export * lident *
      Declaremods.module_params_expr *
      module_entry
  | EVernacDefineModule of Lib.export * lident *
      Declaremods.module_params_expr *
      ((Vernacexpr.export_flag * Libobject.open_filter) * Names.ModPath.t) list *
      module_entry Declaremods.module_signature *
      module_entry list
  | EVernacDeclareModuleType of lident *
      Declaremods.module_params_expr *
      ((Vernacexpr.export_flag * Libobject.open_filter) * Names.ModPath.t) list *
      module_entry list *
      module_entry list
  | EVernacInclude of Declaremods.module_expr list
  | EVernacSetOption of { export : bool; key : Goptions.option_name; value : Vernacexpr.option_setting }
  | EVernacLoad of Vernacexpr.verbose_flag * (vernac_control_entry * Vernacstate.Synterp.t) list
  | EVernacExtend of Vernactypes.typed_vernac

and vernac_entry = synterp_entry Vernacexpr.vernac_expr_gen

(** [vernac_control_entry] defines elaborated vernacular expressions, after the
    syntactic interpretation phase and before full interpretation *)
and vernac_control_entry =
  (Vernacstate.Synterp.t VernacControl.control_entry, synterp_entry)
    Vernacexpr.vernac_control_gen_r CAst.t

exception UnmappedLibrary of Names.DirPath.t option * Libnames.qualid
exception NotFoundLibrary of Names.DirPath.t option * Libnames.qualid

(** [synterp_require] performs the syntactic interpretation phase of `Require`
    commands *)
val synterp_require :
  intern:Library.Intern.t ->
  Libnames.qualid option ->
  Vernacexpr.export_with_cats option ->
  (Libnames.qualid * Vernacexpr.import_filter_expr) list ->
  Library.library_t list * DirPath.t list

(** [synterp_control] is the main entry point of the syntactic interpretation phase *)
val synterp_control :
  intern:Library.Intern.t ->
  Vernacexpr.vernac_control ->
  vernac_control_entry

(** Default proof mode set by `start_proof` *)
val get_default_proof_mode : unit -> Pvernac.proof_mode
val proof_mode_opt_name : string list
