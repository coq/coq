(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module Extend :
sig
  type 'a entry = 'a Pcoq.Gram.Entry.e
  type ('self, 'a) symbol = ('self, 'a) Extend.symbol =
                          | Atoken : Tok.t -> ('self, string) symbol
                          | Alist1 : ('self, 'a) symbol -> ('self, 'a list) symbol
                          | Alist1sep : ('self, 'a) symbol * ('self, _) symbol -> ('self, 'a list) symbol
                          | Alist0 : ('self, 'a) symbol -> ('self, 'a list) symbol
                          | Alist0sep : ('self, 'a) symbol * ('self, _) symbol -> ('self, 'a list) symbol
                          | Aopt : ('self, 'a) symbol -> ('self, 'a option) symbol
                          | Aself : ('self, 'self) symbol
                          | Anext : ('self, 'self) symbol
                          | Aentry : 'a entry -> ('self, 'a) symbol
                          | Aentryl : 'a entry * int -> ('self, 'a) symbol
                          | Arules : 'a rules list -> ('self, 'a) symbol
   and ('self, 'a, 'r) rule = ('self, 'a, 'r) Extend.rule =
                            | Stop : ('self, 'r, 'r) rule
                            | Next : ('self, 'a, 'r) rule * ('self, 'b) symbol -> ('self, 'b -> 'a, 'r) rule
   and ('a, 'r) norec_rule = ('a, 'r) Extend.norec_rule =
                               { norec_rule : 's. ('s, 'a, 'r) rule }
   and 'a rules = 'a Extend.rules =
                | Rules : ('act, Loc.t -> 'a) norec_rule * 'act -> 'a rules
  type gram_assoc = Extend.gram_assoc = NonA | RightA | LeftA
  type 'a production_rule = 'a Extend.production_rule =
                          | Rule : ('a, 'act, Loc.t -> 'a) rule * 'act -> 'a production_rule
  type 'a single_extend_statment = string option * gram_assoc option * 'a production_rule list
  type gram_position = Extend.gram_position =
    | First
    | Last
    | Before of string
    | After of string
    | Level of string
  type 'a extend_statment = gram_position option * 'a single_extend_statment list
  type 'a user_symbol = 'a Extend.user_symbol =
                      | Ulist1 of 'a user_symbol
                      | Ulist1sep of 'a user_symbol * string
                      | Ulist0 of 'a user_symbol
                      | Ulist0sep of 'a user_symbol * string
                      | Uopt of 'a user_symbol
                      | Uentry of 'a
                      | Uentryl of 'a * int
end

module Genintern :
sig
  open API
  module Store : module type of struct include Genintern.Store end
  type glob_sign = Genintern.glob_sign =
                     { ltacvars : Names.Id.Set.t;
                       genv : Environ.env;
                       extra : Store.t }
  type ('raw, 'glb) intern_fun = glob_sign -> 'raw -> glob_sign * 'glb
  type 'glb subst_fun = Mod_subst.substitution -> 'glb -> 'glb
  type 'glb ntn_subst_fun = Tactypes.glob_constr_and_expr Names.Id.Map.t -> 'glb -> 'glb
  val empty_glob_sign : Environ.env -> glob_sign
  val register_intern0 : ('raw, 'glb, 'top) Genarg.genarg_type ->
                         ('raw, 'glb) intern_fun -> unit
  val register_subst0 : ('raw, 'glb, 'top) Genarg.genarg_type ->
                        'glb subst_fun -> unit
  val register_ntn_subst0 : ('raw, 'glb, 'top) Genarg.genarg_type ->
                            'glb ntn_subst_fun -> unit
  val generic_substitute : Genarg.glob_generic_argument subst_fun
  val generic_intern : (Genarg.raw_generic_argument, Genarg.glob_generic_argument) intern_fun
end

module Tok :
sig
  type t = Tok.t =
         | KEYWORD of string
         | PATTERNIDENT of string
         | IDENT of string
         | FIELD of string
         | INT of string
         | STRING of string
         | LEFTQMARK
         | BULLET of string
         | EOI
end

module Pcoq :
sig
  type gram_universe = Pcoq.gram_universe
  module Gram :
  sig
    type te = Tok.t
    module Entry :
    sig
      type 'a e = 'a Extend.entry
      val of_parser : string -> (te Stream.t -> 'a) -> 'a e
      val obj : 'a e -> te Gramext.g_entry
      val create : string -> 'a e
    end
    type 'a entry = 'a Entry.e
    val extend : 'a Pcoq.Gram.Entry.e -> Gramext.position option ->
                 (string option * Gramext.g_assoc option *
                    (Tok.t Gramext.g_symbol list * Gramext.g_action) list) list -> unit
    val entry_create : string -> 'a Entry.e
  end
  module Prim : sig
    open Names
    open Loc
    val preident : string Gram.Entry.e
    val ident : Names.Id.t Gram.Entry.e
    val name : Name.t located Gram.Entry.e
    val identref : Names.Id.t located Gram.Entry.e
    val pidentref : (Names.Id.t located * (Names.Id.t located list) option) Gram.Entry.e
    val pattern_ident : Names.Id.t Gram.Entry.e
    val pattern_identref : Names.Id.t located Gram.Entry.e
    val base_ident : Names.Id.t Gram.Entry.e
    val natural : int Gram.Entry.e
    val bigint : Bigint.bigint Gram.Entry.e
    val integer : int Gram.Entry.e
    val string : string Gram.Entry.e
    val qualid : API.Libnames.qualid located Gram.Entry.e
    val fullyqualid : Names.Id.t list located Gram.Entry.e
    val reference : API.Libnames.reference Gram.Entry.e
    val by_notation : (string * string option) Loc.located Gram.entry
    val smart_global : API.Libnames.reference API.Misctypes.or_by_notation Gram.Entry.e
    val dirpath : DirPath.t Gram.Entry.e
    val ne_string : string Gram.Entry.e
    val ne_lstring : string located Gram.Entry.e
    val var : Names.Id.t located Gram.Entry.e
  end

  val eoi_entry : 'a Gram.Entry.e -> 'a Gram.Entry.e
  val create_generic_entry : gram_universe -> string ->
                             ('a, Genarg.rlevel) Genarg.abstract_argument_type -> 'a Gram.Entry.e
  val utactic : gram_universe
  type gram_reinit = Extend.gram_assoc * Extend.gram_position
  val grammar_extend : 'a Gram.Entry.e -> gram_reinit option ->
                       'a Extend.extend_statment -> unit
  val genarg_grammar : ('raw, 'glb, 'top) Genarg.genarg_type -> 'raw Gram.Entry.e
  val register_grammar : ('raw, 'glb, 'top) Genarg.genarg_type -> 'raw Gram.Entry.e -> unit
  module Constr :
  sig
    val sort : API.Misctypes.glob_sort Gram.Entry.e
    val lconstr : API.Constrexpr.constr_expr Gram.Entry.e
    val lconstr_pattern : API.Constrexpr.constr_expr Gram.Entry.e
    val ident : API.Names.Id.t Gram.Entry.e
    val constr : API.Constrexpr.constr_expr Gram.Entry.e
    val closed_binder : API.Constrexpr.local_binder_expr list Gram.Entry.e
    val constr_pattern : API.Constrexpr.constr_expr Gram.Entry.e
    val global : API.Libnames.reference Gram.Entry.e
    val binder_constr : API.Constrexpr.constr_expr Gram.Entry.e
    val operconstr : API.Constrexpr.constr_expr Gram.Entry.e
    val pattern : API.Constrexpr.cases_pattern_expr Gram.Entry.e
    val binders : API.Constrexpr.local_binder_expr list Gram.Entry.e
  end
  module Vernac_ :
  sig
    val gallina : API.Vernacexpr.vernac_expr Gram.Entry.e
    val gallina_ext : API.Vernacexpr.vernac_expr Gram.Entry.e
    val red_expr : API.Genredexpr.raw_red_expr Gram.Entry.e
    val noedit_mode : API.Vernacexpr.vernac_expr Gram.Entry.e
    val command : API.Vernacexpr.vernac_expr Gram.Entry.e
    val rec_definition : (API.Vernacexpr.fixpoint_expr * API.Vernacexpr.decl_notation list) Gram.Entry.e
    val vernac : API.Vernacexpr.vernac_expr Gram.Entry.e
  end

  type extend_rule =
    | ExtendRule : 'a Gram.Entry.e * gram_reinit option * 'a Extend.extend_statment -> extend_rule

  module GramState : module type of struct include Pcoq.GramState end
  type 'a grammar_command = 'a Pcoq.grammar_command
  type 'a grammar_extension = 'a -> GramState.t -> extend_rule list * GramState.t
  val create_grammar_command : string -> 'a grammar_extension -> 'a grammar_command
  val extend_grammar_command : 'a grammar_command -> 'a -> unit
  val epsilon_value : ('a -> 'self) -> ('self, 'a) Extend.symbol -> 'self option
  val parse_string : 'a Gram.Entry.e -> string -> 'a
  val (!@) : Ploc.t -> Loc.t
  val set_command_entry : API.Vernacexpr.vernac_expr Gram.Entry.e -> unit
end

module CLexer :
sig
  type keyword_state = CLexer.keyword_state
  val terminal : string -> Tok.t
  val add_keyword : string -> unit
  val is_keyword : string -> bool
  val check_ident : string -> unit
  val get_keyword_state : unit -> keyword_state
  val set_keyword_state : keyword_state -> unit
end

module Egramml :
sig
  type 's grammar_prod_item = 's Egramml.grammar_prod_item =
  | GramTerminal of string
  | GramNonTerminal : ('a Genarg.raw_abstract_argument_type option *
      ('s, 'a) Extend.symbol) Loc.located -> 's grammar_prod_item


  val extend_vernac_command_grammar :
    API.Vernacexpr.extend_name -> Vernacexpr.vernac_expr Pcoq.Gram.Entry.e option ->
    Vernacexpr.vernac_expr grammar_prod_item list -> unit

  val make_rule :
    (Loc.t -> Genarg.raw_generic_argument list -> 'a) ->
    'a grammar_prod_item list -> 'a Extend.production_rule
end

module Mltop :
sig
  val add_known_module : string -> unit
  val declare_cache_obj : (unit -> unit) -> string -> unit
end
module Vernacinterp :
sig
  type deprecation = bool
  type vernac_command = Genarg.raw_generic_argument list -> unit -> unit
  val vinterp_add : deprecation -> API.Vernacexpr.extend_name ->
                    vernac_command -> unit
end

module G_vernac :
sig
  val def_body : API.Vernacexpr.definition_expr Pcoq.Gram.Entry.e
  val section_subset_expr : API.Vernacexpr.section_subset_expr Pcoq.Gram.Entry.e
  val query_command :  (Vernacexpr.goal_selector option -> Vernacexpr.vernac_expr)
                         Pcoq.Gram.Entry.e
end

module G_proofs :
sig
  val hint : Vernacexpr.hints_expr Pcoq.Gram.Entry.e
  val hint_proof_using : 'a Pcoq.Gram.Entry.e -> 'a option -> 'a option
end

module Egramcoq :
sig
end

module Metasyntax :
sig
  type any_entry = Metasyntax.any_entry =
    | AnyEntry : 'a Pcoq.Gram.Entry.e -> any_entry
  val register_grammar : string -> any_entry list -> unit
  val add_token_obj : string -> unit
end
