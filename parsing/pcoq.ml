(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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

(** The parser of Coq *)
include Grammar.GMake(CLexer.Lexer)

module Lookahead =
struct

  let err () = raise Stream.Failure

  type t = Gramlib.Plexing.location_function -> int -> Tok.t Stream.t -> int option

  let rec contiguous tok n m =
    n == m ||
    let (_, ep) = Loc.unloc (tok n) in
    let (bp, _) = Loc.unloc (tok (n + 1)) in
    Int.equal ep bp && contiguous tok (succ n) m

  let check_no_space tok m strm =
    let n = Stream.count strm in
    if contiguous tok n (n+m-1) then Some m else None

  let to_entry s (lk : t) =
    let run tok strm = match lk tok 0 strm with None -> err () | Some _ -> () in
    Entry.of_parser s run

  let (>>) (lk1 : t) lk2 tok n strm = match lk1 tok n strm with
  | None -> None
  | Some n -> lk2 tok n strm

  let (<+>) (lk1 : t) lk2 tok n strm = match lk1 tok n strm with
  | None -> lk2 tok n strm
  | Some n -> Some n

  let lk_empty tok n strm = Some n

  let lk_kw kw tok n strm = match stream_nth n strm with
  | Tok.KEYWORD kw' | Tok.IDENT kw' -> if String.equal kw kw' then Some (n + 1) else None
  | _ -> None

  let lk_kws kws tok n strm = match stream_nth n strm with
  | Tok.KEYWORD kw | Tok.IDENT kw -> if List.mem_f String.equal kw kws then Some (n + 1) else None
  | _ -> None

  let lk_ident tok n strm = match stream_nth n strm with
  | Tok.IDENT _ -> Some (n + 1)
  | _ -> None

  let lk_ident_except idents tok n strm = match stream_nth n strm with
  | Tok.IDENT ident when not (List.mem_f String.equal ident idents) -> Some (n + 1)
  | _ -> None

  let lk_nat tok n strm = match stream_nth n strm with
  | Tok.NUMERAL p when NumTok.Unsigned.is_nat p -> Some (n + 1)
  | _ -> None

  let rec lk_list lk_elem n strm =
    ((lk_elem >> lk_list lk_elem) <+> lk_empty) n strm

  let lk_ident_list = lk_list lk_ident

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
  | ByEXTEND of (unit -> unit) * (unit -> unit)
  | ByEntry : ('a * 'b) EntryCommand.tag * string * 'b Entry.t -> ext_kind

(** The list of extensions *)

let camlp5_state = ref []

let camlp5_entries = ref EntryDataMap.empty

(** Deletion *)

let grammar_delete e { pos; data } =
  List.iter
    (fun (n,ass,lev) ->
      List.iter (fun pil -> safe_delete_rule e pil) (List.rev lev))
    (List.rev data)

let grammar_delete_reinit e reinit ({ pos; data } as d)=
  grammar_delete e d;
  let a, ext = reinit in
  let lev = match pos with
    | Some (Gramext.Level n) -> n
    | _ -> assert false
  in
  let ext = { pos = Some ext; data = [Some lev,Some a,[]] } in
  safe_extend e ext

(** Extension *)

let grammar_extend e ext =
  let undo () = grammar_delete e ext in
  let redo () = safe_extend e ext in
  camlp5_state := ByEXTEND (undo, redo) :: !camlp5_state;
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
       | [] -> anomaly ~label:"Pcoq.remove_grammars" (Pp.str "too many rules to remove.")
       | ByGrammar (ExtendRuleReinit (g, reinit, ext)) :: t ->
           grammar_delete_reinit g reinit ext;
           camlp5_state := t;
           remove_grammars (n-1)
       | ByGrammar (ExtendRule (g, ext)) :: t ->
           grammar_delete g ext;
           camlp5_state := t;
           remove_grammars (n-1)
       | ByEXTEND (undo,redo)::t ->
           undo();
           camlp5_state := t;
           remove_grammars n;
           redo();
           camlp5_state := ByEXTEND (undo,redo) :: !camlp5_state
       | ByEntry (tag, name, e) :: t ->
           Unsafe.clear_entry e;
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
  let e = Entry.make ((Entry.name en) ^ "_eoi") in
  let symbs = Rule.next (Rule.next Rule.stop (Symbol.nterm en)) (Symbol.token Tok.PEOI) in
  let act = fun _ x loc -> x in
  let ext = { pos = None; data = make_rule [Production.make symbs act] } in
  safe_extend e ext;
  e

let map_entry f en =
  let e = Entry.make ((Entry.name en) ^ "_map") in
  let symbs = Rule.next Rule.stop (Symbol.nterm en) in
  let act = fun x loc -> f x in
  let ext = { pos = None; data = make_rule [Production.make symbs act] } in
  safe_extend e ext;
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f ?loc x =
  let strm = Stream.of_string x in
  Entry.parse f (Parsable.make ?loc strm)

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
  let e = Entry.make ename in
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
    let bignat = Entry.create "Prim.bignat"
    let bigint = Entry.create "Prim.bigint"
    let string = gec_gen "string"
    let lstring = Entry.create "Prim.lstring"
    let reference = make_gen_entry uprim "reference"
    let by_notation = Entry.create "by_notation"
    let smart_global = Entry.create "smart_global"
    let strategy_level = gec_gen "strategy_level"

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
    let type_cstr = Entry.create "constr:type_cstr"
  end

module Module =
  struct
    let module_expr = Entry.create "module_expr"
    let module_type = Entry.create "module_type"
  end

let epsilon_value (type s tr a) f (e : (s, tr, a) Symbol.t) =
  let r = Production.make (Rule.next Rule.stop e) (fun x _ -> f x) in
  let entry = Entry.make "epsilon" in
  let ext = { pos = None; data = [None, None, [r]] } in
  let () = safe_extend entry ext in
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
  let (rules, st) = modify g grammar_state in
  let () = List.iter iter_extend_sync rules in
  let nb = List.length rules in
  grammar_stack := (GramExt (nb, GrammarCommand.Dyn (tag, g)), st) :: !grammar_stack

let extend_entry_command (type a) (type b) (tag : (a, b) entry_command) (g : a) : b Entry.t list =
  let EntryInterp.Ex modify = EntryInterpMap.find tag !entry_interp in
  let grammar_state = match !grammar_stack with
  | [] -> GramState.empty
  | (_, st) :: _ -> st
  in
  let (names, st) = modify g grammar_state in
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

type any_entry = AnyEntry : 'a Entry.t -> any_entry

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
    keywords declared in g_*.mlg *)

let parser_summary_tag =
  Summary.declare_summary_tag "GRAMMAR_LEXER"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = Summary.nop }

let with_grammar_rule_protection f x =
  let fs = freeze ~marshallable:false in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = unfreeze fs in
    Exninfo.iraise reraise

(** Registering grammar of generic arguments *)

let () =
  let open Stdarg in
  Grammar.register0 wit_int (Prim.integer);
  Grammar.register0 wit_string (Prim.string);
  Grammar.register0 wit_pre_ident (Prim.preident);
  Grammar.register0 wit_ident (Prim.ident);
  Grammar.register0 wit_var (Prim.var);
  Grammar.register0 wit_ref (Prim.reference);
  Grammar.register0 wit_smart_global (Prim.smart_global);
  Grammar.register0 wit_sort_family (Constr.sort_family);
  Grammar.register0 wit_constr (Constr.constr);
  ()
