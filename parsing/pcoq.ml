(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CErrors
open Util
open Extend
open Genarg

let curry f x y = f (x, y)
let uncurry f (x,y) = f x y

(** Location Utils  *)
let to_coqloc loc =
  { Loc.fname = Ploc.file_name loc;
    Loc.line_nb = Ploc.line_nb loc;
    Loc.bol_pos = Ploc.bol_pos loc;
    Loc.bp = Ploc.first_pos loc;
    Loc.ep = Ploc.last_pos loc;
    Loc.line_nb_last = Ploc.line_nb_last loc;
    Loc.bol_pos_last = Ploc.bol_pos_last loc; }

let (!@) = to_coqloc

(** The parser of Coq *)
module G : sig

  include Grammar.S with type te = Tok.t

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
        value parse_token : e 'a -> Stream.t te -> 'a;
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
  val srules' : production_rule list -> symbol
  val parse_tokens_after_filter : 'a entry -> Tok.t Stream.t -> 'a

end with type 'a Entry.e = 'a Grammar.GMake(CLexer).Entry.e = struct

  include Grammar.GMake(CLexer)

  type 'a entry = 'a Entry.e
  type internal_entry = Tok.t Gramext.g_entry
  type symbol = Tok.t Gramext.g_symbol
  type action = Gramext.g_action
  type production_rule = symbol list * action
  type single_extend_statment =
      string option * Gramext.g_assoc option * production_rule list
  type extend_statment =
      Gramext.position option * single_extend_statment list
  type coq_parsable = parsable * CLexer.lexer_state ref

  let parsable ?file c =
    let state = ref (CLexer.init_lexer_state file) in
    CLexer.set_lexer_state !state;
    let a = parsable c in
    state := CLexer.release_lexer_state ();
    (a,state)

  let action = Gramext.action
  let entry_create = Entry.create

  let entry_parse e (p,state) =
    CLexer.set_lexer_state !state;
    try
      let c = Entry.parse e p in
      state := CLexer.release_lexer_state ();
      c
    with Ploc.Exc (loc,e) ->
      CLexer.drop_lexer_state ();
      let loc' = Loc.get_loc (Exninfo.info e) in
      let loc = match loc' with None -> to_coqloc loc | Some loc -> loc in
      Loc.raise ~loc e

  let with_parsable (p,state) f x =
    CLexer.set_lexer_state !state;
    try
      let a = f x in
      state := CLexer.release_lexer_state ();
      a
    with e ->
      CLexer.drop_lexer_state ();
      raise e

  let entry_print ft x = Entry.print ft x

  (* Not used *)
  let srules' = Gramext.srules
  let parse_tokens_after_filter = Entry.parse_token

end


let warning_verbose = Gramext.warning_verbose

let of_coq_assoc = function
| Extend.RightA -> Gramext.RightA
| Extend.LeftA -> Gramext.LeftA
| Extend.NonA -> Gramext.NonA

let of_coq_position = function
| Extend.First -> Gramext.First
| Extend.Last -> Gramext.Last
| Extend.Before s -> Gramext.Before s
| Extend.After s -> Gramext.After s
| Extend.Level s -> Gramext.Level s

module Symbols : sig
  val stoken : Tok.t -> G.symbol
  val sself : G.symbol
  val snext : G.symbol
  val slist0 : G.symbol -> G.symbol
  val slist0sep : G.symbol * G.symbol -> G.symbol
  val slist1 : G.symbol -> G.symbol
  val slist1sep : G.symbol * G.symbol -> G.symbol
  val sopt : G.symbol -> G.symbol
  val snterml : G.internal_entry * string -> G.symbol
  val snterm : G.internal_entry -> G.symbol
end = struct

  let stoken tok =
    let pattern = match tok with
    | Tok.KEYWORD s -> "", s
    | Tok.IDENT s -> "IDENT", s
    | Tok.PATTERNIDENT s -> "PATTERNIDENT", s
    | Tok.FIELD s -> "FIELD", s
    | Tok.INT s -> "INT", s
    | Tok.STRING s -> "STRING", s
    | Tok.LEFTQMARK -> "LEFTQMARK", ""
    | Tok.BULLET s -> "BULLET", s
    | Tok.EOI -> "EOI", ""
    in
    Gramext.Stoken pattern

     let slist0sep (x, y) = Gramext.Slist0sep (x, y, false)
     let slist1sep (x, y) = Gramext.Slist1sep (x, y, false)

  let snterml (x, y) = Gramext.Snterml (x, y)
  let snterm x = Gramext.Snterm x
  let sself = Gramext.Sself
  let snext = Gramext.Snext
  let slist0 x = Gramext.Slist0 x
  let slist1 x = Gramext.Slist1 x
  let sopt x = Gramext.Sopt x

end

let camlp4_verbosity silent f x =
  let a = !warning_verbose in
  warning_verbose := silent;
  f x;
  warning_verbose := a

(** Grammar extensions *)

(** NB: [extend_statment =
         gram_position option * single_extend_statment list]
    and [single_extend_statment =
         string option * gram_assoc option * production_rule list]
    and [production_rule = symbol list * action]

    In [single_extend_statement], first two parameters are name and
    assoc iff a level is created *)

(** Binding general entry keys to symbol *)

let rec of_coq_action : type a r. (r, a, Loc.t -> r) Extend.rule -> a -> G.action = function
| Stop -> fun f -> G.action (fun loc -> f (!@ loc))
| Next (r, _) -> fun f -> G.action (fun x -> of_coq_action r (f x))

let rec symbol_of_prod_entry_key : type s a. (s, a) symbol -> _ = function
  | Atoken t -> Symbols.stoken t
  | Alist1 s -> Symbols.slist1 (symbol_of_prod_entry_key s)
  | Alist1sep (s,sep) ->
      Symbols.slist1sep (symbol_of_prod_entry_key s, symbol_of_prod_entry_key sep)
  | Alist0 s -> Symbols.slist0 (symbol_of_prod_entry_key s)
  | Alist0sep (s,sep) ->
      Symbols.slist0sep (symbol_of_prod_entry_key s, symbol_of_prod_entry_key sep)
  | Aopt s -> Symbols.sopt (symbol_of_prod_entry_key s)
  | Aself -> Symbols.sself
  | Anext -> Symbols.snext
  | Aentry e ->
    Symbols.snterm (G.Entry.obj e)
  | Aentryl (e, n) ->
    Symbols.snterml (G.Entry.obj e, string_of_int n)
  | Arules rs ->
    G.srules' (List.map symbol_of_rules rs)

and symbol_of_rule : type s a r. (s, a, r) Extend.rule -> _ = function
| Stop -> fun accu -> accu
| Next (r, s) -> fun accu -> symbol_of_rule r (symbol_of_prod_entry_key s :: accu)

and symbol_of_rules : type a. a Extend.rules -> _ = function
| Rules (r, act) ->
  let symb = symbol_of_rule r.norec_rule [] in
  let act = of_coq_action r.norec_rule act in
  (symb, act)

let of_coq_production_rule : type a. a Extend.production_rule -> _ = function
| Rule (toks, act) -> (symbol_of_rule toks [], of_coq_action toks act)

let of_coq_single_extend_statement (lvl, assoc, rule) =
  (lvl, Option.map of_coq_assoc assoc, List.map of_coq_production_rule rule)

let of_coq_extend_statement (pos, st) =
  (Option.map of_coq_position pos, List.map of_coq_single_extend_statement st)

(** Type of reinitialization data *)
type gram_reinit = gram_assoc * gram_position

type extend_rule =
| ExtendRule : 'a G.entry * gram_reinit option * 'a extend_statment -> extend_rule

type ext_kind =
  | ByGrammar of extend_rule
  | ByEXTEND of (unit -> unit) * (unit -> unit)

(** The list of extensions *)

let camlp4_state = ref []

(** Deletion *)

let grammar_delete e reinit (pos,rls) =
  List.iter
    (fun (n,ass,lev) ->
      List.iter (fun (pil,_) -> G.delete_rule e pil) (List.rev lev))
    (List.rev rls);
  match reinit with
  | Some (a,ext) ->
    let a = of_coq_assoc a in
    let ext = of_coq_position ext in
    let lev = match pos with
    | Some (Gramext.Level n) -> n
    | _ -> assert false
    in
    (G.extend e) (Some ext) [Some lev,Some a,[]]
  | None -> ()

(** Extension *)

let grammar_extend e reinit ext =
  let ext = of_coq_extend_statement ext in
  let undo () = grammar_delete e reinit ext in
  let redo () = camlp4_verbosity false (uncurry (G.extend e)) ext in
  camlp4_state := ByEXTEND (undo, redo) :: !camlp4_state;
  redo ()

let grammar_extend_sync e reinit ext =
  camlp4_state := ByGrammar (ExtendRule (e, reinit, ext)) :: !camlp4_state;
  camlp4_verbosity false (uncurry (G.extend e)) (of_coq_extend_statement ext)

(** The apparent parser of Coq; encapsulate G to keep track
    of the extensions. *)

module Gram =
  struct
    include G
    let extend e =
      curry
	(fun ext ->
	   camlp4_state :=
	     (ByEXTEND ((fun () -> grammar_delete e None ext),
			(fun () -> uncurry (G.extend e) ext)))
	   :: !camlp4_state;
	   uncurry (G.extend e) ext)
    let delete_rule e pil =
      (* spiwack: if you use load an ML module which contains GDELETE_RULE
	  in a section, God kills a kitty. As it would corrupt remove_grammars.
          There does not seem to be a good way to undo a delete rule. As deleting
	  takes fewer arguments than extending. The production rule isn't returned
	  by delete_rule. If we could retrieve the necessary information, then
	  ByEXTEND provides just the framework we need to allow this in section.
	  I'm not entirely sure it makes sense, but at least it would be more correct.
          *)
      G.delete_rule e pil
  end

(** Remove extensions

   [n] is the number of extended entries (not the number of Grammar commands!)
   to remove. *)

let rec remove_grammars n =
  if n>0 then
    (match !camlp4_state with
       | [] -> anomaly ~label:"Pcoq.remove_grammars" (Pp.str "too many rules to remove")
       | ByGrammar (ExtendRule (g, reinit, ext)) :: t ->
           grammar_delete g reinit (of_coq_extend_statement ext);
           camlp4_state := t;
           remove_grammars (n-1)
       | ByEXTEND (undo,redo)::t ->
           undo();
           camlp4_state := t;
           remove_grammars n;
           redo();
           camlp4_state := ByEXTEND (undo,redo) :: !camlp4_state)

let make_rule r = [None, None, r]

(** An entry that checks we reached the end of the input. *)

let eoi_entry en =
  let e = Gram.entry_create ((Gram.Entry.name en) ^ "_eoi") in
  let symbs = [Symbols.snterm (Gram.Entry.obj en); Symbols.stoken Tok.EOI] in
  let act = Gram.action (fun _ x loc -> x) in
  uncurry (Gram.extend e) (None, make_rule [symbs, act]);
  e

let map_entry f en =
  let e = Gram.entry_create ((Gram.Entry.name en) ^ "_map") in
  let symbs = [Symbols.snterm (Gram.Entry.obj en)] in
  let act = Gram.action (fun x loc -> f x) in
  uncurry (Gram.extend e) (None, make_rule [symbs, act]);
  e

(* Parse a string, does NOT check if the entire string was read
   (use eoi_entry) *)

let parse_string f x =
  let strm = Stream.of_string x in Gram.entry_parse f (Gram.parsable strm)

type gram_universe = string

let utables : (string, unit) Hashtbl.t =
  Hashtbl.create 97

let create_universe u =
  let () = Hashtbl.add utables u () in
  u

let uprim   = create_universe "prim"
let uconstr = create_universe "constr"
let utactic = create_universe "tactic"
let uvernac = create_universe "vernac"

let get_univ u =
  if Hashtbl.mem utables u then u
  else raise Not_found

let new_entry u s =
  let ename = u ^ ":" ^ s in
  let e = Gram.entry_create ename in
  e

let make_gen_entry u s = new_entry u s

module GrammarObj =
struct
  type ('r, _, _) obj = 'r Gram.entry
  let name = "grammar"
  let default _ = None
end

module Grammar = Register(GrammarObj)

let register_grammar = Grammar.register0
let genarg_grammar = Grammar.obj

let create_generic_entry (type a) u s (etyp : a raw_abstract_argument_type) : a Gram.entry =
  let e = new_entry u s in
  let Rawwit t = etyp in
  let () = Grammar.register0 t e in
  e

(* Initial grammar entries *)

module Prim =
  struct
    let gec_gen n = make_gen_entry uprim n

    (* Entries that can be referred via the string -> Gram.entry table *)
    (* Typically for tactic or vernac extensions *)
    let preident = gec_gen "preident"
    let ident = gec_gen "ident"
    let natural = gec_gen "natural"
    let integer = gec_gen "integer"
    let bigint = Gram.entry_create "Prim.bigint"
    let string = gec_gen "string"
    let lstring = Gram.entry_create "Prim.lstring"
    let reference = make_gen_entry uprim "reference"
    let by_notation = Gram.entry_create "by_notation"
    let smart_global = Gram.entry_create "smart_global"

    (* parsed like ident but interpreted as a term *)
    let var = gec_gen "var"

    let name = Gram.entry_create "Prim.name"
    let identref = Gram.entry_create "Prim.identref"
    let pidentref = Gram.entry_create "Prim.pidentref"
    let pattern_ident = Gram.entry_create "pattern_ident"
    let pattern_identref = Gram.entry_create "pattern_identref"

    (* A synonym of ident - maybe ident will be located one day *)
    let base_ident = Gram.entry_create "Prim.base_ident"

    let qualid = Gram.entry_create "Prim.qualid"
    let fullyqualid = Gram.entry_create "Prim.fullyqualid"
    let dirpath = Gram.entry_create "Prim.dirpath"

    let ne_string = Gram.entry_create "Prim.ne_string"
    let ne_lstring = Gram.entry_create "Prim.ne_lstring"

  end

module Constr =
  struct
    let gec_constr = make_gen_entry uconstr

    (* Entries that can be referred via the string -> Gram.entry table *)
    let constr = gec_constr "constr"
    let operconstr = gec_constr "operconstr"
    let constr_eoi = eoi_entry constr
    let lconstr = gec_constr "lconstr"
    let binder_constr = gec_constr "binder_constr"
    let ident = make_gen_entry uconstr "ident"
    let global = make_gen_entry uconstr "global"
    let universe_level = make_gen_entry uconstr "universe_level"
    let sort = make_gen_entry uconstr "sort"
    let pattern = Gram.entry_create "constr:pattern"
    let constr_pattern = gec_constr "constr_pattern"
    let lconstr_pattern = gec_constr "lconstr_pattern"
    let closed_binder = Gram.entry_create "constr:closed_binder"
    let binder = Gram.entry_create "constr:binder"
    let binders = Gram.entry_create "constr:binders"
    let open_binders = Gram.entry_create "constr:open_binders"
    let binders_fixannot = Gram.entry_create "constr:binders_fixannot"
    let typeclass_constraint = Gram.entry_create "constr:typeclass_constraint"
    let record_declaration = Gram.entry_create "constr:record_declaration"
    let appl_arg = Gram.entry_create "constr:appl_arg"
  end

module Module =
  struct
    let module_expr = Gram.entry_create "module_expr"
    let module_type = Gram.entry_create "module_type"
  end

module Vernac_ =
  struct
    let gec_vernac s = Gram.entry_create ("vernac:" ^ s)

    (* The different kinds of vernacular commands *)
    let gallina = gec_vernac "gallina"
    let gallina_ext = gec_vernac "gallina_ext"
    let command = gec_vernac "command"
    let syntax = gec_vernac "syntax_command"
    let vernac = gec_vernac "Vernac.vernac"
    let vernac_eoi = eoi_entry vernac
    let rec_definition = gec_vernac "Vernac.rec_definition"
    let red_expr = make_gen_entry utactic "red_expr"
    let hint_info = gec_vernac "hint_info"
    (* Main vernac entry *)
    let main_entry = Gram.entry_create "vernac"
    let noedit_mode = gec_vernac "noedit_command"

    let () =
      let act_vernac = Gram.action (fun v loc -> Some (to_coqloc loc, v)) in
      let act_eoi = Gram.action (fun _ loc -> None) in
      let rule = [
        ([ Symbols.stoken Tok.EOI ], act_eoi);
        ([ Symbols.snterm (Gram.Entry.obj vernac) ], act_vernac );
      ] in
      uncurry (Gram.extend main_entry) (None, make_rule rule)

    let command_entry_ref = ref noedit_mode
    let command_entry =
      Gram.Entry.of_parser "command_entry"
        (fun strm -> Gram.parse_tokens_after_filter !command_entry_ref strm)

  end

let main_entry = Vernac_.main_entry

let set_command_entry e = Vernac_.command_entry_ref := e
let get_command_entry () = !Vernac_.command_entry_ref

let epsilon_value f e =
  let r = Rule (Next (Stop, e), fun x _ -> f x) in
  let ext = of_coq_extend_statement (None, [None, None, [r]]) in
  let entry = G.entry_create "epsilon" in
  let () = uncurry (G.extend entry) ext in
  try Some (parse_string entry "") with _ -> None

(** Synchronized grammar extensions *)

module GramState = Store.Make(struct end)

type 'a grammar_extension = 'a -> GramState.t -> extend_rule list * GramState.t

module GrammarCommand = Dyn.Make(struct end)
module GrammarInterp = struct type 'a t = 'a grammar_extension end
module GrammarInterpMap = GrammarCommand.Map(GrammarInterp)

let grammar_interp = ref GrammarInterpMap.empty

let (grammar_stack : (int * GrammarCommand.t * GramState.t) list ref) = ref []

type 'a grammar_command = 'a GrammarCommand.tag

let create_grammar_command name interp : _ grammar_command =
  let obj = GrammarCommand.create name in
  let () = grammar_interp := GrammarInterpMap.add obj interp !grammar_interp in
  obj

let extend_grammar_command tag g =
  let modify = GrammarInterpMap.find tag !grammar_interp in
  let grammar_state = match !grammar_stack with
  | [] -> GramState.empty
  | (_, _, st) :: _ -> st
  in
  let (rules, st) = modify g grammar_state in
  let iter (ExtendRule (e, reinit, ext)) = grammar_extend_sync e reinit ext in
  let () = List.iter iter rules in
  let nb = List.length rules in
  grammar_stack := (nb, GrammarCommand.Dyn (tag, g), st) :: !grammar_stack

let recover_grammar_command (type a) (tag : a grammar_command) : a list =
  let filter : _ -> a option = fun (_, GrammarCommand.Dyn (tag', v), _) ->
    match GrammarCommand.eq tag tag' with
    | None -> None
    | Some Refl -> Some v
  in
  List.map_filter filter !grammar_stack

let extend_dyn_grammar (GrammarCommand.Dyn (tag, g)) = extend_grammar_command tag g

(* Summary functions: the state of the lexer is included in that of the parser.
   Because the grammar affects the set of keywords when adding or removing
   grammar rules. *)
type frozen_t = (int * GrammarCommand.t * GramState.t) list * CLexer.keyword_state

let freeze _ : frozen_t = (!grammar_stack, CLexer.get_keyword_state ())

(* We compare the current state of the grammar and the state to unfreeze,
   by computing the longest common suffixes *)
let factorize_grams l1 l2 =
  if l1 == l2 then ([], [], l1) else List.share_tails l1 l2

let number_of_entries gcl =
  List.fold_left (fun n (p,_,_) -> n + p) 0 gcl

let unfreeze (grams, lex) =
  let (undo, redo, common) = factorize_grams !grammar_stack grams in
  let n = number_of_entries undo in
  remove_grammars n;
  grammar_stack := common;
  CLexer.set_keyword_state lex;
  List.iter extend_dyn_grammar (List.rev_map pi2 redo)

(** No need to provide an init function : the grammar state is
    statically available, and already empty initially, while
    the lexer state should not be resetted, since it contains
    keywords declared in g_*.ml4 *)

let _ =
  Summary.declare_summary "GRAMMAR_LEXER"
    { Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = Summary.nop }

let with_grammar_rule_protection f x =
  let fs = freeze false in
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
  Grammar.register0 wit_constr (Constr.constr);
  Grammar.register0 wit_red_expr (Vernac_.red_expr);
  ()
