(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Libnames

module DefAttributes :
  sig
    type t = {
      locality : bool option;
      polymorphic : bool;
      program : bool;
      deprecated : Deprecation.t option;
      canonical_instance : bool;
      typing_flags : Declarations.typing_flags option;
      using : Vernacexpr.section_subset_expr option;
      nonuniform : bool;
      reversible : bool;
    }
    val parse : ?coercion:bool -> Attributes.vernac_flags -> t
  end
val module_locality : bool Attributes.Notations.t
val with_locality :
  atts:Attributes.vernac_flags -> (local:bool option -> 'a) -> 'a
val with_section_locality :
  atts:Attributes.vernac_flags -> (section_local:bool -> 'a) -> 'a
val with_module_locality :
  atts:Attributes.vernac_flags -> (module_local:bool -> 'a) -> 'a
val with_def_attributes :
  ?coercion:bool -> atts:Attributes.vernac_flags -> (atts:DefAttributes.t -> 'a) -> 'a

type module_entry = Modintern.module_struct_expr * Names.ModPath.t * Modintern.module_kind * Entries.inline
type module_binder_entry = Declaremods.module_params_expr * (Lib.export * Names.Id.t)

type synterp_entry =
  | EVernacNoop
  | EVernacNotation of
      Constrexpr.constr_expr * Metasyntax.notation_main_data * Notation.notation_symbols * Constrexpr.notation CAst.t *
      Metasyntax.syntax_rules * Notation.delimiters * Notation_term.scope_name option
  | EVernacBeginSection of Names.lident
  | EVernacEndSegment of Names.lident
  | EVernacRequire of
      qualid option * Vernacexpr.export_with_cats option * (qualid * Vernacexpr.import_filter_expr) list
  | EVernacImport of (Vernacexpr.export_flag *
      Libobject.open_filter) *
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
  | EVernacSetOption of bool (* Export modifier? *) * Goptions.option_name * Vernacexpr.option_setting
  | EVernacExtend of Vernacextend.typed_vernac

type vernac_entry = synterp_entry Vernacexpr.vernac_expr_gen

type vernac_entry_control_r =
  { control : Vernacexpr.control_flag list
  ; attrs : Attributes.vernac_flags
  ; entry : vernac_entry
  }
and vernac_entry_control = vernac_entry_control_r CAst.t

val err_unmapped_library : ?from:Names.DirPath.t -> Libnames.qualid -> Pp.t
val err_notfound_library : ?from:Names.DirPath.t -> Libnames.qualid -> Pp.t
exception UnmappedLibrary of Names.DirPath.t option * Libnames.qualid
exception NotFoundLibrary of Names.DirPath.t option * Libnames.qualid
val vernac_require_syntax
  : Libnames.qualid option
  -> Vernacexpr.export_with_cats option
  -> (Libnames.qualid * Vernacexpr.import_filter_expr) list
  -> unit
val expand : string -> string
val warn_add_loadpath : ?loc:Loc.t -> unit -> unit
val vernac_add_loadpath : implicit:bool -> string -> Names.DirPath.t -> unit
val vernac_remove_loadpath : string -> unit
val vernac_add_ml_path : string -> unit
val vernac_declare_ml_module :
  local:Vernacexpr.locality_flag option -> string list -> unit
val synterp :
  ?loc:Loc.t ->
  atts:Attributes.vernac_flags ->
  Vernacexpr.vernac_expr -> bool * vernac_entry
