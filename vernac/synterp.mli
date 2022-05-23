(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

type vernac_entry =
    EVernacLoad of Vernacexpr.verbose_flag * string
  | EVernacReservedNotation of Vernacexpr.infix_flag *
      (Names.lstring * Vernacexpr.syntax_modifier CAst.t list)
  | EVernacOpenCloseScope of bool * Vernacexpr.scope_name
  | EVernacDeclareScope of Vernacexpr.scope_name
  | EVernacDelimiters of Vernacexpr.scope_name * string option
  | EVernacBindScope of Vernacexpr.scope_name * Vernacexpr.class_rawexpr list
  | EVernacNotation of
      Constrexpr.constr_expr * Metasyntax.notation_main_data * Notation.notation_symbols * Constrexpr.notation CAst.t *
      Metasyntax.syntax_rules * Notation.delimiters * Notation_term.scope_name option
  | EVernacDeclareCustomEntry of string
  | EVernacEnableNotation of bool * (string, Libnames.qualid) Util.union option * Constrexpr.constr_expr option * Vernacexpr.notation_enable_modifier list * Constrexpr.notation_with_optional_scope option
  | EVernacDefinition of
      (Vernacexpr.discharge * Decls.definition_object_kind) *
      Constrexpr.name_decl * Vernacexpr.definition_expr
  | EVernacStartTheoremProof of Decls.theorem_kind *
      Vernacexpr.proof_expr list
  | EVernacEndProof of Vernacexpr.proof_end
  | EVernacExactProof of Constrexpr.constr_expr
  | EVernacAssumption of
      (Vernacexpr.discharge * Decls.assumption_object_kind) *
      Declaremods.inline *
      (Constrexpr.ident_decl list * Constrexpr.constr_expr)
      Vernacexpr.with_coercion list
  | EVernacInductive of Vernacexpr.inductive_kind *
      (Vernacexpr.inductive_expr * Vernacexpr.decl_notation list) list
  | EVernacFixpoint of Vernacexpr.discharge * Vernacexpr.fixpoint_expr list
  | EVernacCoFixpoint of Vernacexpr.discharge *
      Vernacexpr.cofixpoint_expr list
  | EVernacScheme of (Names.lident option * Vernacexpr.scheme) list
  | EVernacSchemeEquality of Vernacexpr.equality_scheme_type *
      Libnames.qualid Constrexpr.or_by_notation
  | EVernacCombinedScheme of Names.lident * Names.lident list
  | EVernacUniverse of Names.lident list
  | EVernacConstraint of Constrexpr.univ_constraint_expr list
  | EVernacBeginSection of Names.lident
  | EVernacEndSegment of Names.lident
  | EVernacExtraDependency of Libnames.qualid * string * Names.Id.t option
  | EVernacRequire of Libnames.qualid option *
      Vernacexpr.export_with_cats option * (Libnames.qualid * Vernacexpr.import_filter_expr) list
  | EVernacImport of (Vernacexpr.export_flag * Libobject.open_filter) *
      (Names.ModPath.t CAst.t * Vernacexpr.import_filter_expr) list
  | EVernacCanonical of Libnames.qualid Constrexpr.or_by_notation
  | EVernacCoercion of Libnames.qualid Constrexpr.or_by_notation *
      (Vernacexpr.class_rawexpr * Vernacexpr.class_rawexpr) option
  | EVernacIdentityCoercion of Names.lident * Vernacexpr.class_rawexpr *
      Vernacexpr.class_rawexpr
  | EVernacNameSectionHypSet of Names.lident * Vernacexpr.section_subset_expr
  | EVernacInstance of Constrexpr.name_decl *
      Constrexpr.local_binder_expr list * Constrexpr.constr_expr *
      (bool * Constrexpr.constr_expr) option * Vernacexpr.hint_info_expr
  | EVernacDeclareInstance of Constrexpr.ident_decl *
      Constrexpr.local_binder_expr list * Constrexpr.constr_expr *
      Vernacexpr.hint_info_expr
  | EVernacContext of Constrexpr.local_binder_expr list
  | EVernacExistingInstance of
      (Libnames.qualid * Vernacexpr.hint_info_expr) list
  | EVernacExistingClass of Libnames.qualid
  | EVernacDeclareModule of Lib.export * Names.lident *
      Declaremods.module_params_expr *
      module_entry
  | EVernacDefineModule of Lib.export * Names.lident *
      Declaremods.module_params_expr *
      ((Vernacexpr.export_flag * Libobject.open_filter) * Names.ModPath.t) list *
      module_entry Declaremods.module_signature *
      module_entry list
  | EVernacDeclareModuleType of Names.lident *
      Declaremods.module_params_expr *
      ((Vernacexpr.export_flag * Libobject.open_filter) * Names.ModPath.t) list *
      module_entry list *
      module_entry list
  | EVernacInclude of Declaremods.module_expr list
  | EVernacAddLoadPath of { implicit : bool;
      physical_path : CUnix.physical_path; logical_path : Names.DirPath.t;
    }
  | EVernacRemoveLoadPath of string
  | EVernacAddMLPath of string
  | EVernacDeclareMLModule of string list
  | EVernacChdir of string option
  | EVernacResetName of Names.lident
  | EVernacResetInitial
  | EVernacBack of int
  | EVernacCreateHintDb of string * bool
  | EVernacRemoveHints of string list * Libnames.qualid list
  | EVernacHints of string list * Vernacexpr.hints_expr
  | EVernacSyntacticDefinition of Names.lident *
      (Names.Id.t list * Constrexpr.constr_expr) *
      Vernacexpr.syntax_modifier CAst.t list
  | EVernacArguments of Libnames.qualid Constrexpr.or_by_notation *
      Vernacexpr.vernac_argument_status list *
      (Names.Name.t * Glob_term.binding_kind) list list *
      Vernacexpr.arguments_modifier list
  | EVernacReserve of Vernacexpr.simple_binder list
  | EVernacGeneralizable of Names.lident list option
  | EVernacSetOpacity of
      (Conv_oracle.level * Libnames.qualid Constrexpr.or_by_notation list)
  | EVernacSetStrategy of
      (Conv_oracle.level * Libnames.qualid Constrexpr.or_by_notation list)
      list
  | EVernacSetOption of bool * Goptions.option_name *
      Vernacexpr.option_setting
  | EVernacAddOption of Goptions.option_name * Goptions.table_value list
  | EVernacRemoveOption of Goptions.option_name * Goptions.table_value list
  | EVernacMemOption of Goptions.option_name * Goptions.table_value list
  | EVernacPrintOption of Goptions.option_name
  | EVernacCheckMayEval of Genredexpr.raw_red_expr option *
      Goal_select.t option * Constrexpr.constr_expr
  | EVernacGlobalCheck of Constrexpr.constr_expr
  | EVernacDeclareReduction of string * Genredexpr.raw_red_expr
  | EVernacPrint of Vernacexpr.printable
  | EVernacSearch of Vernacexpr.searchable * Goal_select.t option *
      Vernacexpr.search_restriction
  | EVernacLocate of Vernacexpr.locatable
  | EVernacRegister of Libnames.qualid * Vernacexpr.register_kind
  | EVernacPrimitive of Constrexpr.ident_decl * CPrimitives.op_or_type *
      Constrexpr.constr_expr option
  | EVernacComments of Vernacexpr.comment list
  | EVernacAbort
  | EVernacAbortAll
  | EVernacRestart
  | EVernacUndo of int
  | EVernacUndoTo of int
  | EVernacFocus of int option
  | EVernacUnfocus
  | EVernacUnfocused
  | EVernacBullet of Proof_bullet.t
  | EVernacSubproof of Goal_select.t option
  | EVernacEndSubproof
  | EVernacShow of Vernacexpr.showable
  | EVernacCheckGuard
  | EVernacProof of Genarg.raw_generic_argument option *
      Vernacexpr.section_subset_expr option
  | EVernacNoop
  | EVernacExtend of Vernacextend.typed_vernac
type vernac_entry_control_r = {
  control : Vernacexpr.control_flag list;
  attrs : Attributes.vernac_flags;
  entry : vernac_entry;
}
and vernac_entry_control = Vernacexpr.vernac_control_r CAst.t
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
