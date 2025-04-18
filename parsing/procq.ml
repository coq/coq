(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Genarg
open Gramlib

(** The parser of Rocq *)
include Grammar.GMake(CLexer.Lexer)

(** Marshallable representation of grammar extensions *)

module EntryCommand = Dyn.Make ()
module GrammarCommand = Dyn.Make ()
module GramState = Store.Make ()

type grammar_entry =
| GramExt of GrammarCommand.t
| EntryExt : 'a EntryCommand.tag * string -> grammar_entry

(** State handling (non marshallable!) *)

module EntryData = struct type _ t = Ex : 'a Entry.t String.Map.t -> 'a t end
module EntryDataMap = EntryCommand.Map(EntryData)

type full_state = {
  (* the state used for parsing *)
  current_state : GState.t;
  (* grammar state containing only non-marshallable extensions
     (NB: this includes entries from Entry.make) *)
  base_state : GState.t;
  (* current_state = List.fold_right add_entry current_sync_extensions base_state
     this means the list is in reverse order of addition *)
  current_sync_extensions : grammar_entry list;
  (* some user data tied to the grammar state, typically contains info on declared levels *)
  user_state : GramState.t;
  (* map to find custom entries *)
  custom_entries : EntryDataMap.t;
}

let empty_full_state =
  let empty_gstate = { GState.estate = EState.empty; kwstate = CLexer.empty_keyword_state } in
  {
    current_state = empty_gstate;
    base_state = empty_gstate;
    current_sync_extensions = [];
    user_state = GramState.empty;
    custom_entries = EntryDataMap.empty;
  }

(** Not marshallable! *)
let state = ref empty_full_state

let gstate () = (!state).current_state

let get_keyword_state () = (gstate()).kwstate

let terminal s = CLexer.terminal (get_keyword_state()) s

let reset_to_base state = {
  base_state = state.base_state;
  current_state = state.base_state;
  current_sync_extensions = [];
  user_state = GramState.empty;
  custom_entries = EntryDataMap.empty;
}

let modify_state_unsync f state =
  let is_base = state.base_state == state.current_state in
  let base_state = f state.base_state in
  let current_state = if is_base then base_state else f state.current_state in
  { state with base_state; current_state }

let modify_state_unsync f () = state := modify_state_unsync f !state

let add_keyword_tok tok =
  modify_state_unsync (fun {estate;kwstate} ->
      let kwstate = CLexer.add_keyword_tok kwstate tok in
      {estate; kwstate})
    ()

let make_entry_unsync make remake state =
  let is_base = state.base_state == state.current_state in
  let base_estate, e = make state.base_state.estate in
  let base_state = { state.base_state with estate = base_estate } in
  let current_state = if is_base then base_state else
      let current_estate = remake state.current_state.estate e in
      { state.current_state with estate = current_estate }
  in
  { state with base_state; current_state }, e

let make_entry_unsync make remake () =
  let statev, e = make_entry_unsync make remake !state in
  state := statev;
  e

let add_kw = { add_kw = CLexer.add_keyword_tok }

let epsilon_value (type s tr a) f (e : (s, tr, a) Symbol.t) =
  let r = Production.make (Rule.next Rule.stop e) (fun x _ -> f x) in
  let { GState.estate; kwstate } = gstate() in
  let estate, entry = Entry.make "epsilon" estate in
  let ext = Fresh (Gramlib.Gramext.First, [None, None, [r]]) in
  let estate, kwstate = safe_extend add_kw estate kwstate entry ext in
  let strm = Stream.empty () in
  let strm = Parsable.make strm in
  try Some (Entry.parse entry strm {estate;kwstate}) with e when CErrors.noncritical e -> None

let extend_gstate {GState.kwstate; estate} e ext =
  let estate, kwstate = safe_extend add_kw estate kwstate e ext in
  {GState.kwstate; estate}

(* XXX rename to grammar_extend_unsync? *)
let grammar_extend e ext =
  let extend_one g = extend_gstate g e ext in
  modify_state_unsync extend_one ()

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

let grammar_extend_sync user_state entry rules state =
  let extend_one_sync state = function
    (* NB: ocaml 4.14 is not smart enough to factorize these 2 GADT match cases *)
    | ExtendRule (e, ext) -> extend_gstate state e ext
    | ExtendRuleReinit (e, _, ext) -> extend_gstate state e ext
  in
  let current_state = List.fold_left extend_one_sync state.current_state rules in
  { state with
    current_state;
    user_state;
    current_sync_extensions = GramExt entry :: state.current_sync_extensions;
  }

let grammar_extend_sync st e r () = state := grammar_extend_sync st e r !state

let extend_entry_sync (type a) (tag : a EntryCommand.tag) (name : string) state : _ * a Entry.t =
  let current_estate, e = Entry.make name state.current_state.estate in
  let current_state = { state.current_state with estate = current_estate } in
  let custom_entries =
    let EntryData.Ex old =
      try EntryDataMap.find tag state.custom_entries
      with Not_found -> EntryData.Ex String.Map.empty
    in
    let () = assert (not @@ String.Map.mem name old) in
    let entries = String.Map.add name e old in
    EntryDataMap.add tag (EntryData.Ex entries) state.custom_entries
  in
  let state = {
    state with
    current_state;
    current_sync_extensions = EntryExt (tag,name) :: state.current_sync_extensions;
    custom_entries;
  }
  in
  state, e

let extend_entry_command tag name =
  let statev, e = extend_entry_sync tag name !state in
  state := statev;
  e

module Parsable = struct
  include Parsable
  let consume x len = consume x len (get_keyword_state())
end

module Entry = struct
  include Entry
  let make name = make_entry_unsync (fun estate -> Entry.make name estate) Unsafe.existing_entry ()
  let parse e p = parse e p (gstate())
  let of_parser na p = make_entry_unsync
      (fun estate -> of_parser na p estate)
      (fun estate e -> Unsafe.existing_of_parser estate e p)
      ()
  let parse_token_stream e strm = parse_token_stream e strm (gstate())
  let print fmt e = print fmt e (gstate()).estate
  let is_empty e = is_empty e (gstate()).estate
  let accumulate_in e = accumulate_in e (gstate()).estate
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

(** An entry that checks we reached the end of the input. *)
(* used by the Tactician plugin *)
let eoi_entry en =
  let e = Entry.make ((Entry.name en) ^ "_eoi") in
  let symbs = Rule.next (Rule.next Rule.stop (Symbol.nterm en)) (Symbol.token Tok.PEOI) in
  let act = fun _ x loc -> x in
  let ext = Fresh (Gramlib.Gramext.First, [None, None, [Production.make symbs act]]) in
  grammar_extend e ext;
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
    let sort_quality_or_set = Entry.make "sort_quality_or_set"
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

(** Synchronized grammar extensions *)

type 'a grammar_extension = {
  gext_fun : 'a -> GramState.t -> extend_rule list * GramState.t;
  gext_eq : 'a -> 'a -> bool;
}

module GrammarInterp = struct type 'a t = 'a grammar_extension end
module GrammarInterpMap = GrammarCommand.Map(GrammarInterp)

let grammar_interp = ref GrammarInterpMap.empty

type 'a grammar_command = 'a GrammarCommand.tag
type 'a entry_command = 'a EntryCommand.tag

let create_grammar_command name interp : _ grammar_command =
  let obj = GrammarCommand.create name in
  let () = grammar_interp := GrammarInterpMap.add obj interp !grammar_interp in
  obj

let create_entry_command name : 'a entry_command =
  EntryCommand.create name

let extend_grammar_command tag g =
  let modify = GrammarInterpMap.find tag !grammar_interp in
  let grammar_state = (!state).user_state in
  let (rules, st) = modify.gext_fun g grammar_state in
  grammar_extend_sync st (Dyn (tag,g)) rules ()

let find_custom_entry tag name =
  let EntryData.Ex map = EntryDataMap.find tag (!state).custom_entries in
  String.Map.find name map

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
    EntryDataMap.fold fold (!state).custom_entries []

(** Summary functions: the state of the lexer is included in that of the parser.
   Because the grammar affects the set of keywords when adding or removing
   grammar rules. *)
type frozen_t =
  | FreezeFull of full_state
  | FreezeMarshallable of grammar_entry list * CLexer.keyword_state * CLexer.keyword_state

let freeze () : frozen_t = FreezeFull !state

let replay_sync_extension = function
  | GramExt (Dyn (tag,g)) -> extend_grammar_command tag g
  | EntryExt (tag,name) -> ignore (extend_entry_command tag name : _ Entry.t)

let unfreeze_only_keywords = function
  | FreezeFull v ->
    let is_base =
      !(state).base_state == (!state).current_state
      && v.base_state.kwstate == v.current_state.kwstate
    in
    let base_state = { (!state).base_state with kwstate = v.base_state.kwstate } in
    let current_state = if is_base then base_state else
        { (!state).current_state with kwstate = v.current_state.kwstate }
    in
    state := {
      !state with
      base_state;
      current_state;
    }
  | FreezeMarshallable (_,base_kw,current_kw) ->
    let is_base = !(state).base_state == (!state).current_state && base_kw == current_kw in
    let base_state = { (!state).base_state with kwstate = base_kw } in
    let current_state = if is_base then base_state else
        { (!state).current_state with kwstate = current_kw }
    in
    state := {
      !state with
      base_state;
      current_state;
    }

let unfreeze = function
  | FreezeFull v as frozen ->
    if (!state).base_state.estate == v.base_state.estate then state := v
    else begin
      (* there are new non backtrackable extensions in (!state).base_state
         compared to v.base_state (can't be the other way as we never remove them from !state) *)
      state := reset_to_base !state;
      List.iter replay_sync_extension (List.rev v.current_sync_extensions);
      unfreeze_only_keywords frozen
    end
  | FreezeMarshallable (sync,base_kw,current_kw) as frozen ->
    state := reset_to_base !state;
    List.iter replay_sync_extension (List.rev sync);
    (* put back the keyword state, needed to support ssr hacks *)
    unfreeze_only_keywords frozen

let make_marshallable = function
  | FreezeFull state ->
    FreezeMarshallable
      (state.current_sync_extensions,
       state.base_state.kwstate,
       state.current_state.kwstate)
  | FreezeMarshallable _ as v -> v

(** No need to provide an init function : the grammar state is
    statically available, and already empty initially, while
    the lexer state should not be reset, since it contains
    keywords declared in g_*.mlg

    XXX is this still true? if not we can do (fun () -> unfreeze (FreezeFull empty_full_state)) *)

let parser_summary_tag =
  Summary.declare_summary_tag "GRAMMAR_LEXER"
    ~make_marshallable
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
