(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Extend
open Genarg
open Gramlib

(** The parser of Coq *)
module G : sig

  include Grammar.S with type te = Tok.t and type 'c pattern = 'c Tok.p

(* where Grammar.S

module type S =
  sig
    type te = 'x;
    type parsable = 'x;
    value parsable : Stream.t char -> parsable;
    value tokens : string -> list (string * int);
    value glexer : Plexing.lexer te;
    value set_algorithm : parse_algorithm -> unit;
    module Entry :
      sig
        type e 'a = 'y;
        value create : string -> e 'a;
        value parse : e 'a -> parsable -> 'a;
        value parse_token_stream : e 'a -> Stream.t te -> 'a;
        value name : e 'a -> string;
        value of_parser : string -> (Stream.t te -> 'a) -> e 'a;
        value print : Format.formatter -> e 'a -> unit;
        external obj : e 'a -> Gramext.g_entry te = "%identity";
      end
    ;
    module Unsafe :
      sig
        value gram_reinit : Plexing.lexer te -> unit;
        value clear_entry : Entry.e 'a -> unit;
      end
    ;
    value extend :
      Entry.e 'a -> option Gramext.position ->
        list
          (option string * option Gramext.g_assoc *
           list (list (Gramext.g_symbol te) * Gramext.g_action)) ->
        unit;
    value delete_rule : Entry.e 'a -> list (Gramext.g_symbol te) -> unit;
  end
  *)

  type coq_parsable

  val coq_parsable : ?loc:Loc.t -> char Stream.t -> coq_parsable
  val entry_create : string -> 'a entry
  val entry_parse : 'a entry -> coq_parsable -> 'a

  val comment_state : coq_parsable -> ((int * int) * string) list

end with type 'a Entry.e = 'a Extend.entry = struct

  include Grammar.GMake(CLexer.Lexer)

  type coq_parsable = parsable * CLexer.lexer_state ref

  let coq_parsable ?loc c =
    let state = ref (CLexer.init_lexer_state ()) in
    CLexer.set_lexer_state !state;
    let a = parsable ?loc c in
    state := CLexer.get_lexer_state ();
    (a,state)

  let entry_create = Entry.create

  let entry_parse e (p,state) =
    CLexer.set_lexer_state !state;
    try
      let c = Entry.parse e p in
      state := CLexer.get_lexer_state ();
      c
    with Ploc.Exc (loc,e) ->
      CLexer.drop_lexer_state ();
      let loc' = Loc.get_loc (Exninfo.info e) in
      let loc = match loc' with None -> loc | Some loc -> loc in
      Loc.raise ~loc e

  let comment_state (p,state) =
    CLexer.get_comment_state !state

end

module Parsable =
struct
  type t = G.coq_parsable
  let make = G.coq_parsable
  let comment_state = G.comment_state
end

module Entry =
struct

  type 'a t = 'a Grammar.GMake(CLexer.Lexer).Entry.e

  let create = G.Entry.create
  let parse = G.entry_parse
  let print = G.Entry.print
  let of_parser = G.Entry.of_parser
  let name = G.Entry.name
  let parse_token_stream = G.Entry.parse_token_stream

end

(** Grammar extensions *)

(** NB: [extend_statement =
         gram_position option * single_extend_statement list]
    and [single_extend_statement =
         string option * gram_assoc option * production_rule list]
    and [production_rule = symbol list * action]

    In [single_extend_statement], first two parameters are name and
    assoc iff a level is created *)

(** Binding general entry keys to symbol *)

type ('s, 'trec, 'a, 'r) casted_rule =
| CastedRNo : ('s, G.ty_norec, 'b, 'r) G.ty_rule * ('a -> 'b) -> ('s, norec, 'a, 'r) casted_rule
| CastedRMay : ('s, G.ty_mayrec, 'b, 'r) G.ty_rule * ('a -> 'b) -> ('s, mayrec, 'a, 'r) casted_rule

type ('s, 'trec, 'a) casted_symbol =
| CastedSNo : ('s, G.ty_norec, 'a) G.ty_symbol -> ('s, norec, 'a) casted_symbol
| CastedSMay : ('s, G.ty_mayrec, 'a) G.ty_symbol -> ('s, mayrec, 'a) casted_symbol

let rec symbol_of_prod_entry_key : type s tr a. (s, tr, a) symbol -> (s, tr, a) casted_symbol =
function
| Atoken t -> CastedSNo (G.s_token t)
| Alist1 s ->
    begin match symbol_of_prod_entry_key s with
    | CastedSNo s -> CastedSNo (G.s_list1 s)
    | CastedSMay s -> CastedSMay (G.s_list1 s) end
| Alist1sep (s,sep) ->
    let CastedSNo sep = symbol_of_prod_entry_key sep in
    begin match symbol_of_prod_entry_key s with
    | CastedSNo s -> CastedSNo (G.s_list1sep s sep false)
    | CastedSMay s -> CastedSMay (G.s_list1sep s sep false) end
| Alist0 s ->
    begin match symbol_of_prod_entry_key s with
    | CastedSNo s -> CastedSNo (G.s_list0 s)
    | CastedSMay s -> CastedSMay (G.s_list0 s) end
| Alist0sep (s,sep) ->
    let CastedSNo sep = symbol_of_prod_entry_key sep in
    begin match symbol_of_prod_entry_key s with
    | CastedSNo s -> CastedSNo (G.s_list0sep s sep false)
    | CastedSMay s -> CastedSMay (G.s_list0sep s sep false) end
| Aopt s ->
    begin match symbol_of_prod_entry_key s with
    | CastedSNo s -> CastedSNo (G.s_opt s)
    | CastedSMay s -> CastedSMay (G.s_opt s) end
| Aself -> CastedSMay G.s_self
| Anext -> CastedSMay G.s_next
| Aentry e -> CastedSNo (G.s_nterm e)
| Aentryl (e, n) -> CastedSNo (G.s_nterml e n)
| Arules rs ->
  let warning msg = Feedback.msg_warning Pp.(str msg) in
  CastedSNo (G.s_rules ~warning:(Some warning) (List.map symbol_of_rules rs))

and symbol_of_rule : type s tr a r. (s, tr, a, Loc.t -> r) Extend.rule -> (s, tr, a, Loc.t -> r) casted_rule = function
| Stop -> CastedRNo (G.r_stop, fun act loc -> act loc)
| Next (r, s) ->
  begin match symbol_of_rule r, symbol_of_prod_entry_key s with
  | CastedRNo (r, cast), CastedSNo s -> CastedRMay (G.r_next r s, (fun act x -> cast (act x)))
  | CastedRNo (r, cast), CastedSMay s -> CastedRMay (G.r_next r s, (fun act x -> cast (act x)))
  | CastedRMay (r, cast), CastedSNo s -> CastedRMay (G.r_next r s, (fun act x -> cast (act x)))
  | CastedRMay (r, cast), CastedSMay s -> CastedRMay (G.r_next r s, (fun act x -> cast (act x))) end
| NextNoRec (r, s) ->
  let CastedRNo (r, cast) = symbol_of_rule r in
  let CastedSNo s = symbol_of_prod_entry_key s in
  CastedRNo (G.r_next_norec r s, (fun act x -> cast (act x)))

and symbol_of_rules : type a. a Extend.rules -> a G.ty_rules = function
| Rules (r, act) ->
  let CastedRNo (symb, cast) = symbol_of_rule r in
  G.rules (symb, cast act)

(** FIXME: This is a hack around a deficient camlp5 API *)
type 'a any_production = AnyProduction : ('a, 'tr, 'f, Loc.t -> 'a) G.ty_rule * 'f -> 'a any_production

let of_coq_production_rule : type a. a Extend.production_rule -> a any_production = function
| Rule (toks, act) ->
  match symbol_of_rule toks with
  | CastedRNo (symb, cast) -> AnyProduction (symb, cast act)
  | CastedRMay (symb, cast) -> AnyProduction (symb, cast act)

let of_coq_single_extend_statement (lvl, assoc, rule) =
  (lvl, assoc, List.map of_coq_production_rule rule)

let of_coq_extend_statement (pos, st) =
  (pos, List.map of_coq_single_extend_statement st)

let fix_extend_statement (pos, st) =
  let fix_single_extend_statement (lvl, assoc, rules) =
    let fix_production_rule (AnyProduction (s, act)) = G.production (s, act) in
    (lvl, assoc, List.map fix_production_rule rules)
  in
  (pos, List.map fix_single_extend_statement st)

(** Type of reinitialization data *)
type gram_reinit = Gramlib.Gramext.g_assoc * Gramlib.Gramext.position

type extend_rule =
| ExtendRule : 'a G.Entry.e * gram_reinit option * 'a extend_statement -> extend_rule

module EntryCommand = Dyn.Make ()
module EntryData = struct type _ t = Ex : 'b G.Entry.e String.Map.t -> ('a * 'b) t end
module EntryDataMap = EntryCommand.Map(EntryData)

type ext_kind =
  | ByGrammar of extend_rule
  | ByEXTEND of (unit -> unit) * (unit -> unit)
  | ByEntry : ('a * 'b) EntryCommand.tag * string * 'b G.Entry.e -> ext_kind

(** The list of extensions *)

let camlp5_state = ref []

let camlp5_entries = ref EntryDataMap.empty

(** Deletion *)

let grammar_delete e reinit (pos,rls) =
  List.iter
    (fun (n,ass,lev) ->
      List.iter (fun (AnyProduction (pil,_)) -> G.safe_delete_rule e pil) (List.rev lev))
    (List.rev rls);
  match reinit with
  | Some (a,ext) ->
    let lev = match pos with
    | Some (Gramext.Level n) -> n
    | _ -> assert false
    in
    let warning msg = Feedback.msg_warning Pp.(str msg) in
    (G.safe_extend ~warning:(Some warning) e) (Some ext) [Some lev,Some a,[]]
  | None -> ()

(** Extension *)

let grammar_extend e reinit ext =
  let ext = of_coq_extend_statement ext in
  let undo () = grammar_delete e reinit ext in
  let pos, ext = fix_extend_statement ext in
  let redo () = G.safe_extend ~warning:None e pos ext in
  camlp5_state := ByEXTEND (undo, redo) :: !camlp5_state;
  redo ()

let grammar_extend_sync e reinit ext =
  camlp5_state := ByGrammar (ExtendRule (e, reinit, ext)) :: !camlp5_state;
  let pos, ext = fix_extend_statement (of_coq_extend_statement ext) in
  G.safe_extend ~warning:None e pos ext

(** The apparent parser of Coq; encapsulate G to keep track
    of the extensions. *)

module Gram =
  struct
    include G
  end

(** Remove extensions

   [n] is the number of extended entries (not the number of Grammar commands!)
   to remove. *)

let rec remove_grammars n =
  if n>0 then
    match !camlp5_state with
       | [] -> anomaly ~label:"Pcoq.remove_grammars" (Pp.str "too many rules to remove.")
       | ByGrammar (ExtendRule (g, reinit, ext)) :: t ->
           grammar_delete g reinit (of_coq_extend_statement ext);
           camlp5_state := t;
           remove_grammars (n-1)
       | ByEXTEND (undo,redo)::t ->
           undo();
           camlp5_state := t;
           remove_grammars n;
           redo();
           camlp5_state := ByEXTEND (undo,redo) :: !camlp5_state
       | ByEntry (tag, name, e) :: t ->
           G.Unsafe.clear_entry e;
           camlp5_state := t;
           let EntryData.Ex entries =
             try EntryDataMap.find tag !camlp5_entries
             with Not_found -> EntryData.Ex String.Map.empty
           in
           let entries = String.Map.remove name entries in
           camlp5_entries := EntryDataMap.add tag (EntryData.Ex entries) !camlp5_entries;
           remove_grammars (n - 1)

let make_rule r = [None, None, r]

(** An entry that checks we reached the end of the input. *)

let eoi_entry en =
  let e = Entry.create ((Gram.Entry.name en) ^ "_eoi") in
  let symbs = G.r_next (G.r_next G.r_stop (G.s_nterm en)) (G.s_token Tok.PEOI) in
  let act = fun _ x loc -> x in
  let warning msg = Feedback.msg_warning Pp.(str msg) in
  Gram.safe_extend ~warning:(Some warning) e None (make_rule [G.production (symbs, act)]);
  e

let map_entry f en =
  let e = Entry.create ((Gram.Entry.name en) ^ "_map") in
  let symbs = G.r_next G.r_stop (G.s_nterm en) in
  let act = fun x loc -> f x in
  let warning msg = Feedback.msg_warning Pp.(str msg) in
  Gram.safe_extend ~warning:(Some warning) e None (make_rule [G.production (symbs, act)]);
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f ?loc x =
  let strm = Stream.of_string x in
  Gram.entry_parse f (Gram.coq_parsable ?loc strm)

type gram_universe = string

let utables : (string, unit) Hashtbl.t =
  Hashtbl.create 97

let create_universe u =
  let () = Hashtbl.add utables u () in
  u

let uprim   = create_universe "prim"
let uconstr = create_universe "constr"
let utactic = create_universe "tactic"

let get_univ u =
  if Hashtbl.mem utables u then u
  else raise Not_found

let new_entry u s =
  let ename = u ^ ":" ^ s in
  let e = Entry.create ename in
  e

let make_gen_entry u s = new_entry u s

module GrammarObj =
struct
  type ('r, _, _) obj = 'r Entry.t
  let name = "grammar"
  let default _ = None
end

module Grammar = Register(GrammarObj)

let warn_deprecated_intropattern =
  let open CWarnings in
  create ~name:"deprecated-intropattern-entry" ~category:"deprecated"
  (fun () -> Pp.strbrk "Entry name intropattern has been renamed in order \
  to be consistent with the documented grammar of tactics. Use \
  \"simple_intropattern\" instead.")

let check_compatibility = function
  | Genarg.ExtraArg s when ArgT.repr s = "intropattern" -> warn_deprecated_intropattern ()
  | _ -> ()

let register_grammar = Grammar.register0
let genarg_grammar x =
  check_compatibility x;
  Grammar.obj x

let create_generic_entry (type a) u s (etyp : a raw_abstract_argument_type) : a Entry.t =
  let e = new_entry u s in
  let Rawwit t = etyp in
  let () = Grammar.register0 t e in
  e

(* Initial grammar entries *)

module Prim =
  struct
    let gec_gen n = make_gen_entry uprim n

    (* Entries that can be referred via the string -> Entry.t table *)
    (* Typically for tactic or vernac extensions *)
    let preident = gec_gen "preident"
    let ident = gec_gen "ident"
    let natural = gec_gen "natural"
    let integer = gec_gen "integer"
    let bigint = Entry.create "Prim.bigint"
    let string = gec_gen "string"
    let lstring = Entry.create "Prim.lstring"
    let reference = make_gen_entry uprim "reference"
    let by_notation = Entry.create "by_notation"
    let smart_global = Entry.create "smart_global"

    (* parsed like ident but interpreted as a term *)
    let var = gec_gen "var"

    let name = Entry.create "Prim.name"
    let identref = Entry.create "Prim.identref"
    let univ_decl = Entry.create "Prim.univ_decl"
    let ident_decl = Entry.create "Prim.ident_decl"
    let pattern_ident = Entry.create "pattern_ident"
    let pattern_identref = Entry.create "pattern_identref"

    (* A synonym of ident - maybe ident will be located one day *)
    let base_ident = Entry.create "Prim.base_ident"

    let qualid = Entry.create "Prim.qualid"
    let fullyqualid = Entry.create "Prim.fullyqualid"
    let dirpath = Entry.create "Prim.dirpath"

    let ne_string = Entry.create "Prim.ne_string"
    let ne_lstring = Entry.create "Prim.ne_lstring"

    let bar_cbrace = Entry.create "'|}'"

  end

module Constr =
  struct
    let gec_constr = make_gen_entry uconstr

    (* Entries that can be referred via the string -> Entry.t table *)
    let constr = gec_constr "constr"
    let operconstr = gec_constr "operconstr"
    let constr_eoi = eoi_entry constr
    let lconstr = gec_constr "lconstr"
    let binder_constr = gec_constr "binder_constr"
    let ident = make_gen_entry uconstr "ident"
    let global = make_gen_entry uconstr "global"
    let universe_name = make_gen_entry uconstr "universe_name"
    let universe_level = make_gen_entry uconstr "universe_level"
    let sort = make_gen_entry uconstr "sort"
    let sort_family = make_gen_entry uconstr "sort_family"
    let pattern = Entry.create "constr:pattern"
    let constr_pattern = gec_constr "constr_pattern"
    let lconstr_pattern = gec_constr "lconstr_pattern"
    let closed_binder = Entry.create "constr:closed_binder"
    let binder = Entry.create "constr:binder"
    let binders = Entry.create "constr:binders"
    let open_binders = Entry.create "constr:open_binders"
    let binders_fixannot = Entry.create "constr:binders_fixannot"
    let typeclass_constraint = Entry.create "constr:typeclass_constraint"
    let record_declaration = Entry.create "constr:record_declaration"
    let appl_arg = Entry.create "constr:appl_arg"
  end

module Module =
  struct
    let module_expr = Entry.create "module_expr"
    let module_type = Entry.create "module_type"
  end
let epsilon_value (type s tr a) f (e : (s, tr, a) symbol) =
  let r =
    match symbol_of_prod_entry_key e with
    | CastedSNo s -> G.production (G.r_next G.r_stop s, (fun x _ -> f x))
    | CastedSMay s -> G.production (G.r_next G.r_stop s, (fun x _ -> f x)) in
  let ext = [None, None, [r]] in
  let entry = Gram.entry_create "epsilon" in
  let warning msg = Feedback.msg_warning Pp.(str msg) in
  let () = G.safe_extend ~warning:(Some warning) entry None ext in
  try Some (parse_string entry "") with _ -> None

(** Synchronized grammar extensions *)

module GramState = Store.Make ()

type 'a grammar_extension = 'a -> GramState.t -> extend_rule list * GramState.t

module GrammarCommand = Dyn.Make ()
module GrammarInterp = struct type 'a t = 'a grammar_extension end
module GrammarInterpMap = GrammarCommand.Map(GrammarInterp)

let grammar_interp = ref GrammarInterpMap.empty

type ('a, 'b) entry_extension = 'a -> GramState.t -> string list * GramState.t

module EntryInterp = struct type _ t = Ex : ('a, 'b) entry_extension -> ('a * 'b) t end
module EntryInterpMap = EntryCommand.Map(EntryInterp)

let entry_interp = ref EntryInterpMap.empty

type grammar_entry =
| GramExt of int * GrammarCommand.t
| EntryExt : int * ('a * 'b) EntryCommand.tag * 'a -> grammar_entry

let (grammar_stack : (grammar_entry * GramState.t) list ref) = ref []

type 'a grammar_command = 'a GrammarCommand.tag
type ('a, 'b) entry_command = ('a * 'b) EntryCommand.tag

let create_grammar_command name interp : _ grammar_command =
  let obj = GrammarCommand.create name in
  let () = grammar_interp := GrammarInterpMap.add obj interp !grammar_interp in
  obj

let create_entry_command name (interp : ('a, 'b) entry_extension) : ('a, 'b) entry_command =
  let obj = EntryCommand.create name in
  let () = entry_interp := EntryInterpMap.add obj (EntryInterp.Ex interp) !entry_interp in
  obj

let extend_grammar_command tag g =
  let modify = GrammarInterpMap.find tag !grammar_interp in
  let grammar_state = match !grammar_stack with
  | [] -> GramState.empty
  | (_, st) :: _ -> st
  in
  let (rules, st) = modify g grammar_state in
  let iter (ExtendRule (e, reinit, ext)) = grammar_extend_sync e reinit ext in
  let () = List.iter iter rules in
  let nb = List.length rules in
  grammar_stack := (GramExt (nb, GrammarCommand.Dyn (tag, g)), st) :: !grammar_stack

let extend_entry_command (type a) (type b) (tag : (a, b) entry_command) (g : a) : b Gram.Entry.e list =
  let EntryInterp.Ex modify = EntryInterpMap.find tag !entry_interp in
  let grammar_state = match !grammar_stack with
  | [] -> GramState.empty
  | (_, st) :: _ -> st
  in
  let (names, st) = modify g grammar_state in
  let entries = List.map (fun name -> Gram.entry_create name) names in
  let iter name e =
    camlp5_state := ByEntry (tag, name, e) :: !camlp5_state;
    let EntryData.Ex old =
      try EntryDataMap.find tag !camlp5_entries
      with Not_found -> EntryData.Ex String.Map.empty
    in
    let entries = String.Map.add name e old in
    camlp5_entries := EntryDataMap.add tag (EntryData.Ex entries) !camlp5_entries
  in
  let () = List.iter2 iter names entries in
  let nb = List.length entries in
  let () = grammar_stack := (EntryExt (nb, tag, g), st) :: !grammar_stack in
  entries

let find_custom_entry tag name =
  let EntryData.Ex map = EntryDataMap.find tag !camlp5_entries in
  String.Map.find name map

let extend_dyn_grammar (e, _) = match e with
| GramExt (_, (GrammarCommand.Dyn (tag, g))) -> extend_grammar_command tag g
| EntryExt (_, tag, g) -> ignore (extend_entry_command tag g)

(** Registering extra grammar *)

type any_entry = AnyEntry : 'a Gram.Entry.e -> any_entry

let grammar_names : any_entry list String.Map.t ref = ref String.Map.empty

let register_grammars_by_name name grams =
  grammar_names := String.Map.add name grams !grammar_names

let find_grammars_by_name name =
  try String.Map.find name !grammar_names
  with Not_found ->
    let fold (EntryDataMap.Any (tag, EntryData.Ex map)) accu =
      try AnyEntry (String.Map.find name map) :: accu
      with Not_found -> accu
    in
    EntryDataMap.fold fold !camlp5_entries []

(** Summary functions: the state of the lexer is included in that of the parser.
   Because the grammar affects the set of keywords when adding or removing
   grammar rules. *)
type frozen_t =
  (grammar_entry * GramState.t) list *
  CLexer.keyword_state

let freeze ~marshallable : frozen_t =
  (!grammar_stack, CLexer.get_keyword_state ())

(* We compare the current state of the grammar and the state to unfreeze,
   by computing the longest common suffixes *)
let factorize_grams l1 l2 =
  if l1 == l2 then ([], [], l1) else List.share_tails l1 l2

let rec number_of_entries accu = function
| [] -> accu
| ((GramExt (p, _) | EntryExt (p, _, _)), _) :: rem ->
  number_of_entries (p + accu) rem

let unfreeze (grams, lex) =
  let (undo, redo, common) = factorize_grams !grammar_stack grams in
  let n = number_of_entries 0 undo in
  remove_grammars n;
  grammar_stack := common;
  CLexer.set_keyword_state lex;
  List.iter extend_dyn_grammar (List.rev redo)

(** No need to provide an init function : the grammar state is
    statically available, and already empty initially, while
    the lexer state should not be reset, since it contains
    keywords declared in g_*.ml4 *)

let parser_summary_tag =
  Summary.declare_summary_tag "GRAMMAR_LEXER"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = Summary.nop }

let with_grammar_rule_protection f x =
  let fs = freeze ~marshallable:false in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = CErrors.push reraise in
    let () = unfreeze fs in
    iraise reraise

(** Registering grammar of generic arguments *)

let () =
  let open Stdarg in
  Grammar.register0 wit_int (Prim.integer);
  Grammar.register0 wit_string (Prim.string);
  Grammar.register0 wit_pre_ident (Prim.preident);
  Grammar.register0 wit_ident (Prim.ident);
  Grammar.register0 wit_var (Prim.var);
  Grammar.register0 wit_ref (Prim.reference);
  Grammar.register0 wit_sort_family (Constr.sort_family);
  Grammar.register0 wit_constr (Constr.constr);
  ()
