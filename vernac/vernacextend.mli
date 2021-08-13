(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
  | VtProofMode of string
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

(** Interpretation of extended vernac phrases. *)

module InProg : sig
  type _ t =
    | Ignore : unit t
    | Use : Declare.OblState.t t

  val cast : Declare.OblState.t -> 'a t -> 'a
end

module OutProg : sig
  type _ t =
    | No : unit t
    | Yes : Declare.OblState.t t
    | Push
    | Pop

  val cast : 'a -> 'a t -> Declare.OblState.t NeList.t -> Declare.OblState.t NeList.t
end

module InProof : sig
  type _ t =
    | Ignore : unit t
    | Reject : unit t
    | Use : Declare.Proof.t t
    | UseOpt : Declare.Proof.t option t

  val cast : Declare.Proof.t option -> 'a t -> 'a
end

module OutProof : sig
  type _ t =
    | No : unit t
    | Close : unit t
    | Yes : Declare.Proof.t t

  type result =
    | Ignored
    | Closed
    | Open of Declare.Proof.t

  val cast : 'a -> 'a t -> result
end

type ('inprog,'outprog,'inproof,'outproof) vernac_type = {
  inprog : 'inprog InProg.t;
  outprog : 'outprog InProg.t;
  inproof : 'inproof InProof.t;
  outproof : 'outproof OutProof.t;
}

type typed_vernac =
    TypedVernac : {
      inprog : 'inprog InProg.t;
      outprog : 'outprog OutProg.t;
      inproof : 'inproof InProof.t;
      outproof : 'outproof OutProof.t;
      run : pm:'inprog -> proof:'inproof -> 'outprog * 'outproof;
    } -> typed_vernac

(** Some convenient typed_vernac constructors *)

val vtdefault : (unit -> unit) -> typed_vernac
val vtnoproof : (unit -> unit) -> typed_vernac
val vtcloseproof : (lemma:Declare.Proof.t -> pm:Declare.OblState.t -> Declare.OblState.t) -> typed_vernac
val vtopenproof : (unit -> Declare.Proof.t) -> typed_vernac
val vtmodifyproof : (pstate:Declare.Proof.t -> Declare.Proof.t) -> typed_vernac
val vtreadproofopt : (pstate:Declare.Proof.t option -> unit) -> typed_vernac
val vtreadproof : (pstate:Declare.Proof.t -> unit) -> typed_vernac
val vtreadprogram : (pm:Declare.OblState.t -> unit) -> typed_vernac
val vtmodifyprogram : (pm:Declare.OblState.t -> Declare.OblState.t) -> typed_vernac
val vtdeclareprogram : (pm:Declare.OblState.t -> Declare.Proof.t) -> typed_vernac
val vtopenproofprogram : (pm:Declare.OblState.t -> Declare.OblState.t * Declare.Proof.t) -> typed_vernac

type vernac_command = ?loc:Loc.t -> atts:Attributes.vernac_flags -> unit -> typed_vernac

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

(** Wrapper to dynamically extend vernacular commands. *)
val vernac_extend :
  command:string ->
  ?classifier:(string -> vernac_classification) ->
  ?entry:Vernacexpr.vernac_expr Pcoq.Entry.t ->
  ty_ml list -> unit

(** {5 VERNAC ARGUMENT EXTEND} *)

type 'a argument_rule =
| Arg_alias of 'a Pcoq.Entry.t
  (** This is used because CAMLP5 parser can be dumb about rule factorization,
      which sometimes requires two entries to be the same. *)
| Arg_rules of 'a Pcoq.Production.t list
  (** There is a discrepancy here as we use directly extension rules and thus
    entries instead of ty_user_symbol and thus arguments as roots. *)

type 'a vernac_argument = {
  arg_printer : Environ.env -> Evd.evar_map -> 'a -> Pp.t;
  arg_parsing : 'a argument_rule;
}

val vernac_argument_extend : name:string -> 'a vernac_argument ->
  ('a, unit, unit) Genarg.genarg_type * 'a Pcoq.Entry.t

(** {5 STM classifiers} *)
val get_vernac_classifier : Vernacexpr.extend_name -> classifier

(** Standard constant classifiers *)
val classify_as_query : vernac_classification
val classify_as_sideeff : vernac_classification
val classify_as_proofstep : vernac_classification
