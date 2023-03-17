(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val check_may_eval :
  Environ.env ->
  Evd.evar_map ->
  Genredexpr.raw_red_expr option ->
  Constrexpr.constr_expr ->
  Pp.t

(** Vernac Translation into the Vernac DSL *)
val translate_vernac
  : ?loc:Loc.t
  -> atts:Attributes.vernac_flags
  -> Synterp.vernac_entry
  -> Vernactypes.typed_vernac

(** Vernacular require command, used by the command line *)
val vernac_require
  : intern:(Names.DirPath.t -> Library.library_t)
  -> Libnames.qualid option
  -> Vernacexpr.export_with_cats option
  -> (Libnames.qualid * Vernacexpr.import_filter_expr) list
  -> unit

(** Interp phase of the require command *)
val vernac_require_interp
  : Library.library_t list
  -> Names.DirPath.t list
  -> Vernacexpr.export_with_cats option
  -> (Libnames.qualid * Vernacexpr.import_filter_expr) list
  -> unit

(** Miscellaneous stuff *)
val command_focus : unit Proof.focus_kind

val allow_sprop_opt_name : string list

(** pre-processing and validation of VernacInductive *)
module Preprocessed_Mind_decl : sig
  type flags = {
    template : bool option;
    udecl : Constrexpr.cumul_univ_decl_expr option;
    cumulative : bool;
    poly : bool;
    finite : Declarations.recursivity_kind;
  }
  type record = {
    flags : flags;
    primitive_proj : bool;
    kind : Vernacexpr.inductive_kind;
    records : Record.Ast.t list;
  }
  type inductive = {
    flags : flags;
    typing_flags : Declarations.typing_flags option;
    private_ind : bool;
    uniform : ComInductive.uniform_inductive_flag;
    inductives : (Vernacexpr.one_inductive_expr * Vernacexpr.notation_declaration list) list;
  }
  type t =
    | Record of record
    | Inductive of inductive
end

val preprocess_inductive_decl
  :  atts:Attributes.vernac_flags
  -> Vernacexpr.inductive_kind
  -> (Vernacexpr.inductive_expr * Vernacexpr.notation_declaration list) list
  -> Preprocessed_Mind_decl.t
