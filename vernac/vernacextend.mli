(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Vernacular Extension data *)

(* A vernac classifier provides information about the exectuion of a
   command:

   - vernac_when: encodes if the vernac may alter the parser [thus
     forcing immediate execution], or if indeed it is pure and parsing
     can continue without its execution.

   - vernac_type: if it is starts, ends, continues a proof or
     alters the global state or is a control command like BackTo or is
     a query like Check.

   The classification works on the assumption that we have 3 states:
   parsing, execution (global environment, etc...), and proof
   state. For example, commands that only alter the proof state are
   considered safe to delegate to a worker.

*)

type vernac_keep_as = VtKeepAxiom | VtKeepDefined | VtKeepOpaque

type vernac_qed_type = VtKeep of vernac_keep_as | VtDrop

type vernac_when =
  | VtNow
  | VtLater

type vernac_classification =
  (* Start of a proof *)
  | VtStartProof of vernac_start
  (* Command altering the global state, bad for parallel
     processing. *)
  | VtSideff of vernac_sideff_type
  (* End of a proof *)
  | VtQed of vernac_qed_type
  (* A proof step *)
  | VtProofStep of {
      proof_block_detection : proof_block_name option
    }
  (* Queries are commands assumed to be "pure", that is to say, they
     don't modify the interpretation state. *)
  | VtQuery
  (* Commands that change the current proof mode *)
  | VtProofMode of Pvernac.proof_mode
  (* To be removed *)
  | VtMeta
and vernac_start = opacity_guarantee * Names.Id.t list
and vernac_sideff_type = Names.Id.t list * vernac_when
and opacity_guarantee =
  | GuaranteesOpacity (** Only generates opaque terms at [Qed] *)
  | Doesn'tGuaranteeOpacity (** May generate transparent terms even with [Qed].*)

and solving_tac = bool (** a terminator *)

and anon_abstracting_tac = bool (** abstracting anonymously its result *)

and proof_block_name = string (** open type of delimiters *)

type vernac_command = ?loc:Loc.t -> atts:Attributes.vernac_flags -> unit -> Vernactypes.typed_vernac

type plugin_args = Genarg.raw_generic_argument list

val type_vernac : Vernacexpr.extend_name -> plugin_args -> vernac_command

(** {5 VERNAC EXTEND} *)

type classifier = Genarg.raw_generic_argument list -> vernac_classification

type (_, _) ty_sig =
| TyNil : (vernac_command, vernac_classification) ty_sig
| TyTerminal : string * ('r, 's) ty_sig -> ('r, 's) ty_sig
| TyNonTerminal :
  ('a, 'b, 'c) Extend.ty_user_symbol * ('r, 's) ty_sig ->
    ('a -> 'r, 'a -> 's) ty_sig

type ty_ml = TyML : bool (* deprecated *) * ('r, 's) ty_sig * 'r * 's option -> ty_ml

(** Statically extend vernacular commands.

    This is used by coqpp VERNAC EXTEND.
    It should not be used directly, use [declare_dynamic_vernac_extend] instead.

    Commands added by plugins at Declare ML Module / Require time should provide [plugin].

    Commands added without providing [plugin] cannot be removed from
    the grammar or modified. Not passing [plugin] is possible for
    non-plugin rocq-runtime commands and deprecated for all other callers.
*)
val static_vernac_extend :
  plugin:string option ->
  command:string ->
  ?classifier:(string -> vernac_classification) ->
  ?entry:Vernacexpr.vernac_expr Procq.Entry.t ->
  ty_ml list -> unit

(** Used to tell the system that all future vernac extends are from plugins. *)
val static_linking_done : unit -> unit

(** Dynamically extend vernacular commands (for instance when importing some module).

    Reusing a [command] string will replace previous uses. The result
    is undefined and probably produces anomalies if the previous
    grammar rule is still active and was different from the new one.

    The polymorphic arguments are as in [TyML].

    The declared grammar extension is disabled, one needs to call
    [Egramml.extend_vernac_command_grammar] in order to enable it.
    That call should use [undoable:true] to make it possible to
    disable the extension, e.g. by backtracking over the command which
    enabled it.
*)
val declare_dynamic_vernac_extend
  : command:Vernacexpr.extend_name
  -> ?entry:Vernacexpr.vernac_expr Procq.Entry.t
  -> depr:bool
  -> 's (* classifier *)
  -> ('r, 's) ty_sig (* grammar *)
  -> 'r (* command interpretation *)
  -> Vernacexpr.extend_name

(** {5 VERNAC ARGUMENT EXTEND} *)

type 'a argument_rule =
| Arg_alias of 'a Procq.Entry.t
  (** This is used because CAMLP5 parser can be dumb about rule factorization,
      which sometimes requires two entries to be the same. *)
| Arg_rules of 'a Procq.Production.t list
  (** There is a discrepancy here as we use directly extension rules and thus
    entries instead of ty_user_symbol and thus arguments as roots. *)

type 'a vernac_argument = {
  arg_printer : Environ.env -> Evd.evar_map -> 'a -> Pp.t;
  arg_parsing : 'a argument_rule;
}

val vernac_argument_extend : plugin:string -> name:string -> 'a vernac_argument ->
  'a Genarg.vernac_genarg_type * 'a Procq.Entry.t

(** {5 STM classifiers} *)
val get_vernac_classifier : Vernacexpr.extend_name -> classifier

(** Standard constant classifiers *)
val classify_as_query : vernac_classification
val classify_as_sideeff : vernac_classification
val classify_as_proofstep : vernac_classification
