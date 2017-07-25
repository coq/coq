(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Warning, this file should respect the dependency order established
   in Coq. To see such order issue the comand:

   ```
   bash -c 'for i in kernel intf library engine pretyping interp proofs parsing printing tactics vernac stm toplevel; do echo -e "\n## $i files" && cat ${i}/${i}.mllib; done && echo -e "\n## highparsing files" && cat parsing/highparsing.mllib' > API/link
   ```

   Note however that files in intf/ are located manually now as their
   conceptual linking order in the Coq codebase is incorrect (but it
   works due to these files being implementation-free.

   See below in the file for their concrete position.
*)

open Kernel_API
open Intf_API
open Engine_API
open Library_API
open Pretyping_API

(************************************************************************)
(* Modules from parsing/                                                *)
(************************************************************************)

module Pcoq :
sig

  open Loc
  open Names
  open Extend
  open Vernacexpr
  open Genarg
  open Constrexpr
  open Libnames
  open Misctypes
  open Genredexpr

  module Gram : sig
    include Grammar.S with type te = Tok.t

    type 'a entry = 'a Entry.e
    type internal_entry = Tok.t Gramext.g_entry
    type symbol = Tok.t Gramext.g_symbol
    type action = Gramext.g_action
    type production_rule = symbol list * action
    type single_extend_statment =
      string option * Gramext.g_assoc option * production_rule list
    type extend_statment =
      Gramext.position option * single_extend_statment list

    type coq_parsable

    val parsable : ?file:string -> char Stream.t -> coq_parsable
    val action : 'a -> action
    val entry_create : string -> 'a entry
    val entry_parse : 'a entry -> coq_parsable -> 'a
    val entry_print : Format.formatter -> 'a entry -> unit
    val with_parsable : coq_parsable -> ('a -> 'b) -> 'a -> 'b

    (* Apparently not used *)
    val srules' : production_rule list -> symbol
    val parse_tokens_after_filter : 'a entry -> Tok.t Stream.t -> 'a

  end with type 'a Entry.e = 'a Grammar.GMake(CLexer).Entry.e

  val parse_string : 'a Gram.entry -> string -> 'a
  val eoi_entry : 'a Gram.entry -> 'a Gram.entry
  val map_entry : ('a -> 'b) -> 'a Gram.entry -> 'b Gram.entry

  type gram_universe

  val uprim   : gram_universe
  val uconstr : gram_universe
  val utactic : gram_universe
  val uvernac : gram_universe

  val register_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Gram.entry -> unit

  val genarg_grammar : ('raw, 'glb, 'top) genarg_type -> 'raw Gram.entry

  val create_generic_entry : gram_universe -> string ->
    ('a, rlevel) abstract_argument_type -> 'a Gram.entry

  module Prim :
  sig
    open Names
    open Libnames
    val preident : string Gram.entry
    val ident : Id.t Gram.entry
    val name : Name.t located Gram.entry
    val identref : Id.t located Gram.entry
    val pidentref : (Id.t located * (Id.t located list) option) Gram.entry
    val pattern_ident : Id.t Gram.entry
    val pattern_identref : Id.t located Gram.entry
    val base_ident : Id.t Gram.entry
    val natural : int Gram.entry
    val bigint : Constrexpr.raw_natural_number Gram.entry
    val integer : int Gram.entry
    val string : string Gram.entry
    val lstring : string located Gram.entry
    val qualid : qualid located Gram.entry
    val fullyqualid : Id.t list located Gram.entry
    val reference : reference Gram.entry
    val by_notation : (string * string option) Loc.located Gram.entry
    val smart_global : reference or_by_notation Gram.entry
    val dirpath : DirPath.t Gram.entry
    val ne_string : string Gram.entry
    val ne_lstring : string located Gram.entry
    val var : Id.t located Gram.entry
  end

  module Constr :
  sig
    val constr : constr_expr Gram.entry
    val constr_eoi : constr_expr Gram.entry
    val lconstr : constr_expr Gram.entry
    val binder_constr : constr_expr Gram.entry
    val operconstr : constr_expr Gram.entry
    val ident : Id.t Gram.entry
    val global : reference Gram.entry
    val universe_level : glob_level Gram.entry
    val sort : glob_sort Gram.entry
    val pattern : cases_pattern_expr Gram.entry
    val constr_pattern : constr_expr Gram.entry
    val lconstr_pattern : constr_expr Gram.entry
    val closed_binder : local_binder_expr list Gram.entry
    val binder : local_binder_expr list Gram.entry (* closed_binder or variable *)
    val binders : local_binder_expr list Gram.entry (* list of binder *)
    val open_binders : local_binder_expr list Gram.entry
    val binders_fixannot : (local_binder_expr list * (Id.t located option * recursion_order_expr)) Gram.entry
    val typeclass_constraint : (Name.t located * bool * constr_expr) Gram.entry
    val record_declaration : constr_expr Gram.entry
    val appl_arg : (constr_expr * explicitation located option) Gram.entry
  end

  module Vernac_ :
  sig
    val gallina : vernac_expr Gram.entry
    val gallina_ext : vernac_expr Gram.entry
    val command : vernac_expr Gram.entry
    val syntax : vernac_expr Gram.entry
    val vernac : vernac_expr Gram.entry
    val rec_definition : (fixpoint_expr * decl_notation list) Gram.entry
    val vernac_eoi : vernac_expr Gram.entry
    val noedit_mode : vernac_expr Gram.entry
    val command_entry : vernac_expr Gram.entry
    val red_expr : raw_red_expr Gram.entry
    val hint_info : Vernacexpr.hint_info_expr Gram.entry
  end

  val epsilon_value : ('a -> 'self) -> ('self, 'a) Extend.symbol -> 'self option

  val get_command_entry : unit -> vernac_expr Gram.entry
  val set_command_entry : vernac_expr Gram.entry -> unit

  type gram_reinit = gram_assoc * gram_position
  val grammar_extend : 'a Gram.entry -> gram_reinit option ->
    'a Extend.extend_statment -> unit

  module GramState : Store.S

  type 'a grammar_command

  type extend_rule =
    | ExtendRule : 'a Gram.entry * gram_reinit option * 'a extend_statment -> extend_rule

  type 'a grammar_extension = 'a -> GramState.t -> extend_rule list * GramState.t

  val create_grammar_command : string -> 'a grammar_extension -> 'a grammar_command

  val extend_grammar_command : 'a grammar_command -> 'a -> unit
  val recover_grammar_command : 'a grammar_command -> 'a list
  val with_grammar_rule_protection : ('a -> 'b) -> 'a -> 'b

  val to_coqloc : Ploc.t -> Loc.t
  val (!@) : Ploc.t -> Loc.t

end

module Egramml :
sig
  open Vernacexpr

  type 's grammar_prod_item =
    | GramTerminal of string
    | GramNonTerminal : ('a Genarg.raw_abstract_argument_type option *
                         ('s, 'a) Extend.symbol) Loc.located -> 's grammar_prod_item

  val extend_vernac_command_grammar :
    extend_name -> vernac_expr Pcoq.Gram.entry option ->
    vernac_expr grammar_prod_item list -> unit

  val make_rule :
    (Loc.t -> Genarg.raw_generic_argument list -> 'a) ->
    'a grammar_prod_item list -> 'a Extend.production_rule

end

(************************************************************************)
(* End of modules from parsing/                                         *)
(************************************************************************)
