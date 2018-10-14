(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Extend
open Genarg
open Constrexpr
open Libnames

(** The parser of Coq *)

(** DO NOT USE EXTENSION FUNCTIONS IN THIS MODULE.
    We only have it here to work with Camlp5. Handwritten grammar extensions
    should use the safe [Pcoq.grammar_extend] function below. *)
module Gram : sig

  include Grammar.S with type te = Tok.t

  val gram_extend : 'a Entry.e -> 'a Extend.extend_statement -> unit

end with type 'a Entry.e = 'a Grammar.GMake(CLexer).Entry.e

module Parsable :
sig
  type t
  val make : ?file:Loc.source -> char Stream.t -> t
  (* Get comment parsing information from the Lexer *)
  val comment_state : t -> ((int * int) * string) list
end

module Entry : sig
  type 'a t = 'a Grammar.GMake(CLexer).Entry.e
  val create : string -> 'a t
  val parse : 'a t -> Parsable.t -> 'a
  val print : Format.formatter -> 'a t -> unit
end

(** The parser of Coq is built from three kinds of rule declarations:

   - dynamic rules declared at the evaluation of Coq files (using
     e.g. Notation, Infix, or Tactic Notation)
   - static rules explicitly defined in files g_*.ml4
   - static rules macro-generated by ARGUMENT EXTEND, TACTIC EXTEND and
     VERNAC EXTEND (see e.g. file extratactics.ml4)

   Note that parsing a Coq document is in essence stateful: the parser
   needs to recognize commands that start proofs and use a different
   parsing entry point for them.

   We thus provide two different interfaces: the "raw" parsing
   interface, in the style of camlp5, which provides more flexibility,
   and a more specialize "parse_vernac" one, which will indeed adjust
   the state as needed.

*)

(** Dynamic extension of rules

    For constr notations, dynamic addition of new rules is done in
    several steps:

    - "x + y" (user gives a notation string of type Topconstr.notation)
        |     (together with a constr entry level, e.g. 50, and indications of)
        |     (subentries, e.g. x in constr next level and y constr same level)
        |
        | splitting into tokens by Metasyntax.split_notation_string
        V
      [String "x"; String "+"; String "y"] : symbol_token list
        |
        | interpreted as a mixed parsing/printing production
        | by Metasyntax.analyse_notation_tokens
        V
      [NonTerminal "x"; Terminal "+"; NonTerminal "y"] : symbol list
        |
        | translated to a parsing production by Metasyntax.make_production
        V
      [GramConstrNonTerminal (ETConstr (NextLevel,(BorderProd Left,LeftA)),
                              Some "x");
       GramConstrTerminal ("","+");
       GramConstrNonTerminal (ETConstr (NextLevel,(BorderProd Right,LeftA)),
                              Some "y")]
       : grammar_constr_prod_item list
        |
        | Egrammar.make_constr_prod_item
        V
      Gramext.g_symbol list which is sent to camlp5

    For user level tactic notations, dynamic addition of new rules is
    also done in several steps:

    - "f" constr(x) (user gives a Tactic Notation command)
        |
        | parsing
        V
      [TacTerm "f"; TacNonTerm ("constr", Some "x")]
      : grammar_tactic_prod_item_expr list
        |
        | Metasyntax.interp_prod_item
        V
      [GramTerminal "f";
       GramNonTerminal (ConstrArgType, Aentry ("constr","constr"), Some "x")]
      : grammar_prod_item list
        |
        | Egrammar.make_prod_item
        V
      Gramext.g_symbol list

    For TACTIC/VERNAC/ARGUMENT EXTEND, addition of new rules is done as follows:

    - "f" constr(x) (developer gives an EXTEND rule)
        |
        | macro-generation in tacextend.ml4/vernacextend.ml4/argextend.ml4
        V
      [GramTerminal "f";
       GramNonTerminal (ConstrArgType, Aentry ("constr","constr"), Some "x")]
        |
        | Egrammar.make_prod_item
        V
      Gramext.g_symbol list

*)

(** Temporarily activate camlp5 verbosity *)

val camlp5_verbosity : bool -> ('a -> unit) -> 'a -> unit

(** Parse a string *)

val parse_string : 'a Entry.t -> string -> 'a
val eoi_entry : 'a Entry.t -> 'a Entry.t
val map_entry : ('a -> 'b) -> 'a Entry.t -> 'b Entry.t

type gram_universe

val get_univ : string -> gram_universe
val create_universe : string -> gram_universe

val new_entry : gram_universe -> string -> 'a Entry.t

val uprim : gram_universe
val uconstr : gram_universe
val utactic : gram_universe


val register_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Entry.t -> unit
val genarg_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Entry.t

val create_generic_entry : gram_universe -> string ->
  ('a, rlevel) abstract_argument_type -> 'a Entry.t

module Prim :
  sig
    open Names
    open Libnames
    val preident : string Entry.t
    val ident : Id.t Entry.t
    val name : lname Entry.t
    val identref : lident Entry.t
    val univ_decl : universe_decl_expr Entry.t
    val ident_decl : ident_decl Entry.t
    val pattern_ident : Id.t Entry.t
    val pattern_identref : lident Entry.t
    val base_ident : Id.t Entry.t
    val natural : int Entry.t
    val bigint : Constrexpr.raw_natural_number Entry.t
    val integer : int Entry.t
    val string : string Entry.t
    val lstring : lstring Entry.t
    val reference : qualid Entry.t
    val qualid : qualid Entry.t
    val fullyqualid : Id.t list CAst.t Entry.t
    val by_notation : (string * string option) Entry.t
    val smart_global : qualid or_by_notation Entry.t
    val dirpath : DirPath.t Entry.t
    val ne_string : string Entry.t
    val ne_lstring : lstring Entry.t
    val var : lident Entry.t
  end

module Constr :
  sig
    val constr : constr_expr Entry.t
    val constr_eoi : constr_expr Entry.t
    val lconstr : constr_expr Entry.t
    val binder_constr : constr_expr Entry.t
    val operconstr : constr_expr Entry.t
    val ident : Id.t Entry.t
    val global : qualid Entry.t
    val universe_level : Glob_term.glob_level Entry.t
    val sort : Glob_term.glob_sort Entry.t
    val sort_family : Sorts.family Entry.t
    val pattern : cases_pattern_expr Entry.t
    val constr_pattern : constr_expr Entry.t
    val lconstr_pattern : constr_expr Entry.t
    val closed_binder : local_binder_expr list Entry.t
    val binder : local_binder_expr list Entry.t (* closed_binder or variable *)
    val binders : local_binder_expr list Entry.t (* list of binder *)
    val open_binders : local_binder_expr list Entry.t
    val binders_fixannot : (local_binder_expr list * (lident option * recursion_order_expr)) Entry.t
    val typeclass_constraint : (lname * bool * constr_expr) Entry.t
    val record_declaration : constr_expr Entry.t
    val appl_arg : (constr_expr * explicitation CAst.t option) Entry.t
  end

module Module :
  sig
    val module_expr : module_ast Entry.t
    val module_type : module_ast Entry.t
  end

val epsilon_value : ('a -> 'self) -> ('self, 'a) Extend.symbol -> 'self option

(** {5 Extending the parser without synchronization} *)

type gram_reinit = gram_assoc * gram_position
(** Type of reinitialization data *)

val grammar_extend : 'a Entry.t -> gram_reinit option ->
  'a Extend.extend_statement -> unit
(** Extend the grammar of Coq, without synchronizing it with the backtracking
    mechanism. This means that grammar extensions defined this way will survive
    an undo. *)

(** {5 Extending the parser with summary-synchronized commands} *)

module GramState : Store.S
(** Auxiliary state of the grammar. Any added data must be marshallable. *)

(** {6 Extension with parsing rules} *)

type 'a grammar_command
(** Type of synchronized parsing extensions. The ['a] type should be
    marshallable. *)

type extend_rule =
| ExtendRule : 'a Entry.t * gram_reinit option * 'a extend_statement -> extend_rule

type 'a grammar_extension = 'a -> GramState.t -> extend_rule list * GramState.t
(** Grammar extension entry point. Given some ['a] and a current grammar state,
    such a function must produce the list of grammar extensions that will be
    applied in the same order and kept synchronized w.r.t. the summary, together
    with a new state. It should be pure. *)

val create_grammar_command : string -> 'a grammar_extension -> 'a grammar_command
(** Create a new grammar-modifying command with the given name. The extension
    function is called to generate the rules for a given data. *)

val extend_grammar_command : 'a grammar_command -> 'a -> unit
(** Extend the grammar of Coq with the given data. *)

(** {6 Extension with parsing entries} *)

type ('a, 'b) entry_command
(** Type of synchronized entry creation. The ['a] type should be
    marshallable. *)

type ('a, 'b) entry_extension = 'a -> GramState.t -> string list * GramState.t
(** Entry extension entry point. Given some ['a] and a current grammar state,
    such a function must produce the list of entry extensions that will be
    created and kept synchronized w.r.t. the summary, together
    with a new state. It should be pure. *)

val create_entry_command : string -> ('a, 'b) entry_extension -> ('a, 'b) entry_command
(** Create a new entry-creating command with the given name. The extension
    function is called to generate the new entries for a given data. *)

val extend_entry_command : ('a, 'b) entry_command -> 'a -> 'b Entry.t list
(** Create new synchronized entries using the provided data. *)

val find_custom_entry : ('a, 'b) entry_command -> string -> 'b Entry.t
(** Find an entry generated by the synchronized system in the current state.
    @raise Not_found if non-existent. *)

(** {6 Protection w.r.t. backtrack} *)

val with_grammar_rule_protection : ('a -> 'b) -> 'a -> 'b

(** Vernacular and tactic parsing. The parser maintains a stateful
    stack of available tactic modes entries, and will try to parse
    using the entry at the top of the stack. An empty stack means no
    tactic mode.
  *)

val add_proof_tactic_entry : string -> vernac_expr Gram.entry -> unit
(** add a new entry to the proof parsing mode *)

val push_proof_tactic_entry : string -> unit
(** signal entering a proof *)
val pop_proof_tactic_entry : unit -> string
(** signal closing a proof *)

val get_proof_tactic_entry_stack : unit -> string list
(** mainly for debug purposes *)

(** Location Utils  *)
val of_coqloc : Loc.t -> Ploc.t
val to_coqloc : Ploc.t -> Loc.t
val (!@) : Ploc.t -> Loc.t

type frozen_t
val parser_summary_tag : frozen_t Summary.Dyn.tag

(** Registering grammars by name *)

type any_entry = AnyEntry : 'a Entry.t -> any_entry

val register_grammars_by_name : string -> any_entry list -> unit
val find_grammars_by_name : string -> any_entry list
