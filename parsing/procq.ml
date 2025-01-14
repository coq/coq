(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Genarg
open Gramlib

(** The parser of Rocq *)
include Grammar.GMake(CLexer.Lexer)

let keyword_state = ref CLexer.empty_keyword_state
let get_keyword_state () = !keyword_state
let set_keyword_state s = keyword_state := s

(** Not marshallable! *)
let estate = ref EState.empty

let gstate () = { GState.estate = !estate; kwstate = !keyword_state; }

module Parsable = struct
  include Parsable
  let consume x len = consume x len !keyword_state
end

module Entry = struct
  include Entry
  let make na =
    let estate', e = make na !estate in
    estate := estate';
    e
  let parse e p = parse e p (gstate())
  let of_parser na p =
    let estate', e = of_parser na p !estate in
    estate := estate';
    e
  let parse_token_stream e strm = parse_token_stream e strm (gstate())
  let print fmt e = print fmt e !estate
  let is_empty e = is_empty e !estate
  let accumulate_in e = accumulate_in e !estate
end

module Lookahead =
struct

  let err () = raise Stream.Failure

  type t = int -> CLexer.keyword_state -> (CLexer.keyword_state,Tok.t) LStream.t -> int option

  let rec contiguous n m strm =
    n == m ||
    let (_, ep) = Loc.unloc (LStream.get_loc n strm) in
    let (bp, _) = Loc.unloc (LStream.get_loc (n + 1) strm) in
    Int.equal ep bp && contiguous (succ n) m strm

  let check_no_space m _kwstate strm =
    let n = LStream.count strm in
    if contiguous n (n+m-1) strm then Some m else None

  let to_entry s (lk : t) =
    let run kwstate strm = match lk 0 kwstate strm with None -> err () | Some _ -> () in
    Entry.(of_parser s { parser_fun = run })

  let (>>) (lk1 : t) lk2 n kwstate strm = match lk1 n kwstate strm with
  | None -> None
  | Some n -> lk2 n kwstate strm

  let (<+>) (lk1 : t) lk2 n kwstate strm = match lk1 n kwstate strm with
  | None -> lk2 n kwstate strm
  | Some n -> Some n

  let lk_empty n kwstate strm = Some n

  let lk_kw kw n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Tok.KEYWORD kw' | Tok.IDENT kw' -> if String.equal kw kw' then Some (n + 1) else None
  | _ -> None

  let lk_kws kws n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Tok.KEYWORD kw | Tok.IDENT kw -> if List.mem_f String.equal kw kws then Some (n + 1) else None
  | _ -> None

  let lk_ident n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Tok.IDENT _ -> Some (n + 1)
  | _ -> None

  let lk_name = lk_ident <+> lk_kw "_"

  let lk_ident_except idents n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Tok.IDENT ident when not (List.mem_f String.equal ident idents) -> Some (n + 1)
  | _ -> None

  let lk_nat n kwstate strm = match LStream.peek_nth kwstate n strm with
  | Tok.NUMBER p when NumTok.Unsigned.is_nat p -> Some (n + 1)
  | _ -> None

  let rec lk_list lk_elem n kwstate strm =
    ((lk_elem >> lk_list lk_elem) <+> lk_empty) n kwstate strm

  let lk_ident_list = lk_list lk_ident

  let lk_field n kwstate strm = match LStream.peek_nth kwstate n strm with
    | Tok.FIELD _ -> Some (n+1)
    | _ -> None

  let lk_qualid = lk_ident >> lk_list lk_field

end

(** Grammar extensions *)

(** NB: [extend_statement =
         gram_position option * single_extend_statement list]
    and [single_extend_statement =
         string option * gram_assoc option * production_rule list]
    and [production_rule = symbol list * action]

    In [single_extend_statement], first two parameters are name and
    assoc iff a level is created *)

(** Type of reinitialization data *)
type gram_reinit = Gramlib.Gramext.g_assoc * Gramlib.Gramext.position

type extend_rule =
| ExtendRule : 'a Entry.t * 'a extend_statement -> extend_rule
| ExtendRuleReinit : 'a Entry.t * gram_reinit * 'a extend_statement -> extend_rule

module EntryCommand = Dyn.Make ()
module EntryData = struct type _ t = Ex : 'b Entry.t String.Map.t -> ('a * 'b) t end
module EntryDataMap = EntryCommand.Map(EntryData)

type ext_kind =
  | ByGrammar of extend_rule
  | ByEXTEND of string * (unit -> unit) * (unit -> unit)
  | ByEntry : ('a * 'b) EntryCommand.tag * string * 'b Entry.t -> ext_kind

(** The list of extensions *)

let terminal s = CLexer.terminal !keyword_state s

let camlp5_state = ref []

let camlp5_entries = ref EntryDataMap.empty

(** Deletion *)

let grammar_delete e r =
  let data = match r with
  | Fresh (_, r) -> List.map (fun (_, _, r) -> r) r
  | Reuse (_, r) -> [r]
  in
  List.iter
    (fun lev ->
      List.iter (fun pil -> estate := safe_delete_rule !estate e pil) (List.rev lev))
    (List.rev data)

let no_add_kw = { add_kw = fun () _ -> () }

(* TODO use this for ssr instead of messing with set_keyword_state
   (needs some API design) *)
let _safe_extend_no_kw e ext =
  let estate', () = safe_extend no_add_kw !estate () e ext in
  estate := estate'

let add_kw = { add_kw = CLexer.add_keyword_tok }

let safe_extend e ext =
  let estate', kwstate' = safe_extend add_kw !estate !keyword_state e ext in
  estate := estate';
  keyword_state := kwstate'

let grammar_delete_reinit e reinit d =
  grammar_delete e d;
  let a, ext = reinit in
  let lev = match d with
  | Reuse (Some n, _) -> n
  | _ -> assert false
  in
  let ext = Fresh (ext, [Some lev,Some a,[]]) in
  safe_extend e ext

(** Extension *)

let grammar_extend e ext =
  let undo () = grammar_delete e ext in
  let redo () = safe_extend e ext in
  camlp5_state := ByEXTEND (Entry.name e, undo, redo) :: !camlp5_state;
  redo ()

let grammar_extend_sync e ext =
  camlp5_state := ByGrammar (ExtendRule (e, ext)) :: !camlp5_state;
  safe_extend e ext

let grammar_extend_sync_reinit e reinit ext =
  camlp5_state := ByGrammar (ExtendRuleReinit (e, reinit, ext)) :: !camlp5_state;
  safe_extend e ext

(** Remove extensions

   [n] is the number of extended entries (not the number of Grammar commands!)
   to remove. *)

let rec remove_grammars n =
  if n>0 then
    match !camlp5_state with
       | [] -> anomaly ~label:"Procq.remove_grammars" (Pp.str "too many rules to remove.")
       | ByGrammar (ExtendRuleReinit (g, reinit, ext)) :: t ->
           grammar_delete_reinit g reinit ext;
           camlp5_state := t;
           remove_grammars (n-1)
       | ByGrammar (ExtendRule (g, ext)) :: t ->
         (try grammar_delete g ext
          with Not_found -> Feedback.msg_info Pp.(str "failed on " ++ str (Entry.name g));
            raise Not_found);
         camlp5_state := t;
         remove_grammars (n-1)
       | ByEXTEND (name, undo,redo)::t ->
           undo();
           camlp5_state := t;
           remove_grammars n;
           redo();
           camlp5_state := ByEXTEND (name, undo,redo) :: !camlp5_state
       | ByEntry (tag, name, e) :: t ->
           estate := Unsafe.clear_entry !estate e;
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

(* used by the Tactician plugin *)
let eoi_entry en =
  let e = Entry.make ((Entry.name en) ^ "_eoi") in
  let symbs = Rule.next (Rule.next Rule.stop (Symbol.nterm en)) (Symbol.token Tok.PEOI) in
  let act = fun _ x loc -> x in
  let ext = Fresh (Gramlib.Gramext.First, make_rule [Production.make symbs act]) in
  safe_extend e ext;
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f ?loc x =
  let strm = Stream.of_string x in
  Entry.parse f (Parsable.make ?loc strm)

module GrammarObj =
struct
  type ('r, _, _) obj = 'r Entry.t
  let name = "grammar"
  let default _ = None
end

module Grammar = Register(GrammarObj)

let warn_deprecated_intropattern =
  CWarnings.create ~name:"deprecated-intropattern-entry" ~category:Deprecation.Version.v8_11
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

let create_generic_entry2 (type a) s (etyp : a raw_abstract_argument_type) : a Entry.t =
  let e = Entry.make s in
  let Rawwit t = etyp in
  let () = Grammar.register0 t e in
  e

(* Initial grammar entries *)
module Prim =
  struct

    (* Entries that can be referred via the string -> Entry.t table *)
    (* Typically for tactic or vernac extensions *)
    let preident = Entry.make "preident"
    let ident = Entry.make "ident"
    let natural = Entry.make "natural"
    let integer = Entry.make "integer"
    let bignat = Entry.make "bignat"
    let bigint = Entry.make "bigint"
    let string = Entry.make "string"
    let lstring = Entry.make "lstring"
    let reference = Entry.make "reference"
    let fields = Entry.make "fields"
    let by_notation = Entry.make "by_notation"
    let smart_global = Entry.make "smart_global"
    let strategy_level = Entry.make "strategy_level"

    (* parsed like ident but interpreted as a term *)
    let hyp = Entry.make "hyp"
    let var = hyp

    let name = Entry.make "name"
    let identref = Entry.make "identref"
    let univ_decl = Entry.make "univ_decl"
    let ident_decl = Entry.make "ident_decl"
    let pattern_ident = Entry.make "pattern_ident"

    (* A synonym of ident - maybe ident will be located one day *)
    let base_ident = Entry.make "base_ident"

    let qualid = Entry.make "qualid"
    let fullyqualid = Entry.make "fullyqualid"
    let dirpath = Entry.make "dirpath"

    let ne_string = Entry.make "ne_string"
    let ne_lstring = Entry.make "ne_lstring"

    let bar_cbrace = Entry.make "'|}'"

  end

module Constr =
  struct

    (* Entries that can be referred via the string -> Entry.t table *)
    let constr = Entry.make "constr"
    let term = Entry.make "term"
    let constr_eoi = eoi_entry constr
    let lconstr = Entry.make "lconstr"
    let binder_constr = Entry.make "binder_constr"
    let ident = Entry.make "ident"
    let global = Entry.make "global"
    let universe_name = Entry.make "universe_name"
    let sort = Entry.make "sort"
    let sort_family = Entry.make "sort_family"
    let pattern = Entry.make "pattern"
    let constr_pattern = Entry.make "constr_pattern"
    let cpattern = Entry.make "cpattern"
    let closed_binder = Entry.make "closed_binder"
    let binder = Entry.make "binder"
    let binders = Entry.make "binders"
    let open_binders = Entry.make "open_binders"
    let one_open_binder = Entry.make "one_open_binder"
    let one_closed_binder = Entry.make "one_closed_binder"
    let binders_fixannot = Entry.make "binders_fixannot"
    let typeclass_constraint = Entry.make "typeclass_constraint"
    let record_declaration = Entry.make "record_declaration"
    let arg = Entry.make "arg"
    let type_cstr = Entry.make "type_cstr"
  end

module Module =
  struct
    let module_expr = Entry.make "module_expr"
    let module_type = Entry.make "module_type"
  end

let epsilon_value (type s tr a) f (e : (s, tr, a) Symbol.t) =
  let r = Production.make (Rule.next Rule.stop e) (fun x _ -> f x) in
  let entry = Entry.make "epsilon" in
  let ext = Fresh (Gramlib.Gramext.First, [None, None, [r]]) in
  safe_extend entry ext;
  try Some (parse_string entry "") with e when CErrors.noncritical e -> None

(** Synchronized grammar extensions *)

module GramState = Store.Make ()

type 'a grammar_extension = {
  gext_fun : 'a -> GramState.t -> extend_rule list * GramState.t;
  gext_eq : 'a -> 'a -> bool;
}

module GrammarCommand = Dyn.Make ()
module GrammarInterp = struct type 'a t = 'a grammar_extension end
module GrammarInterpMap = GrammarCommand.Map(GrammarInterp)

let grammar_interp = ref GrammarInterpMap.empty

type ('a, 'b) entry_extension = {
  eext_fun : 'a -> GramState.t -> string list * GramState.t;
  eext_eq : 'a -> 'a -> bool;
}

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

let iter_extend_sync = function
  | ExtendRule (e, ext) ->
    grammar_extend_sync e ext
  | ExtendRuleReinit (e, reinit, ext) ->
    grammar_extend_sync_reinit e reinit ext

let extend_grammar_command tag g =
  let modify = GrammarInterpMap.find tag !grammar_interp in
  let grammar_state = match !grammar_stack with
  | [] -> GramState.empty
  | (_, st) :: _ -> st
  in
  let (rules, st) = modify.gext_fun g grammar_state in
  let () = List.iter iter_extend_sync rules in
  let nb = List.length rules in
  grammar_stack := (GramExt (nb, GrammarCommand.Dyn (tag, g)), st) :: !grammar_stack

let extend_entry_command (type a) (type b) (tag : (a, b) entry_command) (g : a) : b Entry.t list =
  let EntryInterp.Ex modify = EntryInterpMap.find tag !entry_interp in
  let grammar_state = match !grammar_stack with
  | [] -> GramState.empty
  | (_, st) :: _ -> st
  in
  let (names, st) = modify.eext_fun g grammar_state in
  let entries = List.map (fun name -> Entry.make name) names in
  let iter name e =
    camlp5_state := ByEntry (tag, name, e) :: !camlp5_state;
    let EntryData.Ex old =
      try EntryDataMap.find tag !camlp5_entries
      with Not_found -> EntryData.Ex String.Map.empty
    in
    let () = assert (not @@ String.Map.mem name old) in
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

let grammar_names : Entry.any_t list String.Map.t ref = ref String.Map.empty

let register_grammars_by_name name grams =
  grammar_names := String.Map.add name grams !grammar_names

let find_grammars_by_name name =
  try String.Map.find name !grammar_names
  with Not_found ->
    let fold (EntryDataMap.Any (tag, EntryData.Ex map)) accu =
      try Entry.Any (String.Map.find name map) :: accu
      with Not_found -> accu
    in
    EntryDataMap.fold fold !camlp5_entries []

(** Summary functions: the state of the lexer is included in that of the parser.
   Because the grammar affects the set of keywords when adding or removing
   grammar rules. *)
type frozen_t =
  (grammar_entry * GramState.t) list *
  CLexer.keyword_state

let freeze () : frozen_t =
  (!grammar_stack, !keyword_state)

let eq_grams (g1, _) (g2, _) = match g1, g2 with
| GramExt (_, GrammarCommand.Dyn (t1, v1)), GramExt (_, GrammarCommand.Dyn (t2, v2)) ->
  begin match GrammarCommand.eq t1 t2 with
  | None -> false
  | Some Refl ->
    let data = GrammarInterpMap.find t1 !grammar_interp in
    data.gext_eq v1 v2
  end
| EntryExt (_, t1, v1), EntryExt (_, t2, v2) ->
  begin match EntryCommand.eq t1 t2 with
  | None -> false
  | Some Refl ->
    let EntryInterp.Ex data = EntryInterpMap.find t1 !entry_interp in
    data.eext_eq v1 v2
  end
| (GramExt _, EntryExt _) | (EntryExt _, GramExt _) -> false

(* We compare the current state of the grammar and the state to unfreeze,
   by computing the longest common suffixes *)
let factorize_grams l1 l2 =
  if l1 == l2 then ([], [], l1) else List.share_tails eq_grams l1 l2

let rec number_of_entries accu = function
| [] -> accu
| ((GramExt (p, _) | EntryExt (p, _, _)), _) :: rem ->
  number_of_entries (p + accu) rem

let unfreeze (grams, lex) =
  let (undo, redo, common) = factorize_grams !grammar_stack grams in
  let n = number_of_entries 0 undo in
  remove_grammars n;
  grammar_stack := common;
  keyword_state := lex;
  List.iter extend_dyn_grammar (List.rev redo)

(** No need to provide an init function : the grammar state is
    statically available, and already empty initially, while
    the lexer state should not be reset, since it contains
    keywords declared in g_*.mlg *)

let parser_summary_tag =
  Summary.declare_summary_tag "GRAMMAR_LEXER"
    { stage = Summary.Stage.Synterp;
      Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = Summary.nop }

let with_grammar_rule_protection f x =
  let fs = freeze () in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = unfreeze fs in
    Exninfo.iraise reraise
