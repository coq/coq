(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Lexing
open Coqpp_ast
open Format

let fatal msg =
  let () = Format.eprintf "Error: %s@\n%!" msg in
  exit 1

let pr_loc loc =
  let file = loc.loc_start.pos_fname in
  let line = loc.loc_start.pos_lnum in
  let bpos = loc.loc_start.pos_cnum - loc.loc_start.pos_bol in
  let epos = loc.loc_end.pos_cnum - loc.loc_start.pos_bol in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d:" file line bpos epos

let parse_file f =
  let chan = open_in f in
  let lexbuf = Lexing.from_channel chan in
  let () = lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = f } in
  let ans =
    try Coqpp_parse.file Coqpp_lex.token lexbuf
    with
    | Coqpp_lex.Lex_error (loc, msg) ->
      let () = close_in chan in
      let () = Printf.eprintf "%s\n%!" (pr_loc loc) in
      fatal msg
    | Parsing.Parse_error ->
      let () = close_in chan in
      let loc = Coqpp_lex.loc lexbuf in
      let () = Printf.eprintf "%s\n%!" (pr_loc loc) in
      fatal "syntax error"
  in
  let () = close_in chan in
  ans

module StringSet = Set.Make(String)

let string_split s =
  let len = String.length s in
  let rec split n =
    try
      let pos = String.index_from s n '.' in
      let dir = String.sub s n (pos-n) in
      dir :: split (succ pos)
    with
      | Not_found -> [String.sub s n (len-n)]
  in
  if len == 0 then [] else split 0

let plugin_name = "__coq_plugin_name"

module GramExt :
sig

val print_ast : Format.formatter -> grammar_ext -> unit

end =
struct

let is_uident s = match s.[0] with
| 'A'..'Z' -> true
| _ -> false

let is_qualified = is_uident

let get_local_entries ext =
  let global = StringSet.of_list ext.gramext_globals in
  let map e = e.gentry_name in
  let entries = List.map map ext.gramext_entries in
  let local = List.filter (fun e -> not (is_qualified e || StringSet.mem e global)) entries in
  let rec uniquize seen = function
  | [] -> []
  | id :: rem ->
    let rem = uniquize (StringSet.add id seen) rem in
    if StringSet.mem id seen then rem else id :: rem
  in
  uniquize StringSet.empty local

let print_local fmt ext =
  let locals = get_local_entries ext in
  match locals with
  | [] -> ()
  | e :: locals ->
    let mk_e fmt e = fprintf fmt "%s.Entry.create \"%s\"" ext.gramext_name e in
    let () = fprintf fmt "@[<hv 2>let %s =@ @[%a@]@]@ " e mk_e e in
    let iter e = fprintf fmt "@[<hv 2>and %s =@ @[%a@]@]@ " e mk_e e in
    let () = List.iter iter locals in
    fprintf fmt "in@ "

let print_string fmt s = fprintf fmt "\"%s\"" s

let print_list fmt pr l =
  let rec prl fmt = function
  | [] -> ()
  | [x] -> fprintf fmt "%a" pr x
  | x :: l -> fprintf fmt "%a;@ %a" pr x prl l
  in
  fprintf fmt "@[<hv>[%a]@]" prl l

let print_opt fmt pr = function
| None -> fprintf fmt "None"
| Some x -> fprintf fmt "Some@ (%a)" pr x

let print_position fmt pos = match pos with
| First -> fprintf fmt "Extend.First"
| Last -> fprintf fmt "Extend.Last"
| Before s -> fprintf fmt "Extend.Before@ \"%s\"" s
| After s -> fprintf fmt "Extend.After@ \"%s\"" s
| Level s -> fprintf fmt "Extend.Level@ \"%s\"" s

let print_assoc fmt = function
| LeftA -> fprintf fmt "Extend.LeftA"
| RightA -> fprintf fmt "Extend.RightA"
| NonA -> fprintf fmt "Extend.NonA"

type symb =
| SymbToken of string * string option
| SymbEntry of string * string option
| SymbSelf
| SymbNext
| SymbList0 of symb * symb option
| SymbList1 of symb * symb option
| SymbOpt of symb
| SymbRules of ((string option * symb) list * code) list

let is_token s = match string_split s with
| [s] -> is_uident s
| _ -> false

let rec parse_tokens = function
| [GSymbString s] -> SymbToken ("", Some s)
| [GSymbQualid ("SELF", None)] -> SymbSelf
| [GSymbQualid ("NEXT", None)] -> SymbNext
| [GSymbQualid ("LIST0", None); tkn] ->
  SymbList0 (parse_token tkn, None)
| [GSymbQualid ("LIST1", None); tkn] ->
  SymbList1 (parse_token tkn, None)
| [GSymbQualid ("LIST0", None); tkn; GSymbQualid ("SEP", None); tkn'] ->
  SymbList0 (parse_token tkn, Some (parse_token tkn'))
| [GSymbQualid ("LIST1", None); tkn; GSymbQualid ("SEP", None); tkn'] ->
  SymbList1 (parse_token tkn, Some (parse_token tkn'))
| [GSymbQualid ("OPT", None); tkn] ->
  SymbOpt (parse_token tkn)
| [GSymbQualid (e, None)] when is_token e -> SymbToken (e, None)
| [GSymbQualid (e, None); GSymbString s] when is_token e -> SymbToken (e, Some s)
| [GSymbQualid (e, lvl)] when not (is_token e) -> SymbEntry (e, lvl)
| [GSymbParen tkns] -> parse_tokens tkns
| [GSymbProd prds] ->
  let map p =
    let map (pat, tkns) = (pat, parse_tokens tkns) in
    (List.map map p.gprod_symbs, p.gprod_body)
  in
  SymbRules (List.map map prds)
| t ->
  let rec db_token = function
  | GSymbString s -> Printf.sprintf "\"%s\"" s
  | GSymbQualid (s, _) -> Printf.sprintf "%s" s
  | GSymbParen s -> Printf.sprintf "(%s)" (db_tokens s)
  | GSymbProd _ -> Printf.sprintf "[...]"
  and db_tokens tkns =
    let s = List.map db_token tkns in
    String.concat " " s
  in
  fatal (Printf.sprintf "Invalid token: %s" (db_tokens t))

and parse_token tkn = parse_tokens [tkn]

let print_fun fmt (vars, body) =
  let vars = List.rev vars in
  let iter = function
  | None -> fprintf fmt "_@ "
  | Some id -> fprintf fmt "%s@ " id
  in
  let () = fprintf fmt "fun@ " in
  let () = List.iter iter vars in
  (** FIXME: use Coq locations in the macros *)
  let () = fprintf fmt "loc ->@ @[%s@]" body.code in
  ()

(** Meta-program instead of calling Tok.of_pattern here because otherwise
    violates value restriction *)
let print_tok fmt = function
| "", s -> fprintf fmt "Tok.KEYWORD %a" print_string s
| "IDENT", s -> fprintf fmt "Tok.IDENT %a" print_string s
| "PATTERNIDENT", s -> fprintf fmt "Tok.PATTERNIDENT %a" print_string s
| "FIELD", s -> fprintf fmt "Tok.FIELD %a" print_string s
| "INT", s -> fprintf fmt "Tok.INT %a" print_string s
| "STRING", s -> fprintf fmt "Tok.STRING %a" print_string s
| "LEFTQMARK", _ -> fprintf fmt "Tok.LEFTQMARK"
| "BULLET", s -> fprintf fmt "Tok.BULLET %a" print_string s
| "EOI", _ -> fprintf fmt "Tok.EOI"
| _ -> failwith "Tok.of_pattern: not a constructor"

let rec print_prod fmt p =
  let (vars, tkns) = List.split p.gprod_symbs in
  let f = (vars, p.gprod_body) in
  let tkn = List.rev_map parse_tokens tkns in
  fprintf fmt "@[Extend.Rule@ (@[%a@],@ @[(%a)@])@]" print_symbols tkn print_fun f

and print_symbols fmt = function
| [] -> fprintf fmt "Extend.Stop"
| tkn :: tkns ->
  fprintf fmt "Extend.Next @[(%a,@ %a)@]" print_symbols tkns print_symbol tkn

and print_symbol fmt tkn = match tkn with
| SymbToken (t, s) ->
  let s = match s with None -> "" | Some s -> s in
  fprintf fmt "(Extend.Atoken (%a))" print_tok (t, s)
| SymbEntry (e, None) ->
  fprintf fmt "(Extend.Aentry %s)" e
| SymbEntry (e, Some l) ->
  fprintf fmt "(Extend.Aentryl (%s, %a))" e print_string l
| SymbSelf ->
  fprintf fmt "Extend.Aself"
| SymbNext ->
  fprintf fmt "Extend.Anext"
| SymbList0 (s, None) ->
  fprintf fmt "(Extend.Alist0 %a)" print_symbol s
| SymbList0 (s, Some sep) ->
  fprintf fmt "(Extend.Alist0sep (%a, %a))" print_symbol s print_symbol sep
| SymbList1 (s, None) ->
  fprintf fmt "(Extend.Alist1 %a)" print_symbol s
| SymbList1 (s, Some sep) ->
  fprintf fmt "(Extend.Alist1sep (%a, %a))" print_symbol s print_symbol sep
| SymbOpt s ->
  fprintf fmt "(Extend.Aopt %a)" print_symbol s
| SymbRules rules ->
  let pr fmt (r, body) =
    let (vars, tkn) = List.split r in
    let tkn = List.rev tkn in
    fprintf fmt "Extend.Rules @[({ Extend.norec_rule = %a },@ (%a))@]" print_symbols tkn print_fun (vars, body)
  in
  let pr fmt rules = print_list fmt pr rules in
  fprintf fmt "(Extend.Arules %a)" pr (List.rev rules)

let print_rule fmt r =
  let pr_lvl fmt lvl = print_opt fmt print_string lvl in
  let pr_asc fmt asc = print_opt fmt print_assoc asc in
  let pr_prd fmt prd = print_list fmt print_prod prd in
  fprintf fmt "@[(%a,@ %a,@ %a)@]" pr_lvl r.grule_label pr_asc r.grule_assoc pr_prd (List.rev r.grule_prods)

let print_entry fmt gram e =
  let print_position_opt fmt pos = print_opt fmt print_position pos in
  let print_rules fmt rules = print_list fmt print_rule rules in
  fprintf fmt "let () =@ @[%s.gram_extend@ %s@ @[(%a, %a)@]@]@ in@ "
    gram e.gentry_name print_position_opt e.gentry_pos print_rules e.gentry_rules

let print_ast fmt ext =
  let () = fprintf fmt "let _ = @[" in
  let () = fprintf fmt "@[<v>%a@]" print_local ext in
  let () = List.iter (fun e -> print_entry fmt ext.gramext_name e) ext.gramext_entries in
  let () = fprintf fmt "()@]@\n" in
  ()

end

module TacticExt :
sig

val print_ast : Format.formatter -> tactic_ext -> unit

end =
struct

let rec print_symbol fmt = function
| Ulist1 s ->
  fprintf fmt "@[Extend.TUlist1 (%a)@]" print_symbol s
| Ulist1sep (s, sep) ->
  fprintf fmt "@[Extend.TUlist1sep (%a, \"%s\")@]" print_symbol s sep
| Ulist0 s ->
  fprintf fmt "@[Extend.TUlist0 (%a)@]" print_symbol s
| Ulist0sep (s, sep) ->
  fprintf fmt "@[Extend.TUlist0sep (%a, \"%s\")@]" print_symbol s sep
| Uopt s ->
  fprintf fmt "@[Extend.TUopt (%a)@]" print_symbol s
| Uentry e ->
  fprintf fmt "@[Extend.TUentry (Genarg.get_arg_tag wit_%s)@]" e
| Uentryl (e, l) ->
  assert (e = "tactic");
  fprintf fmt "@[Extend.TUentryl (Genarg.get_arg_tag wit_%s, %i)@]" e l

let rec print_clause fmt = function
| [] -> fprintf fmt "@[TyNil@]"
| ExtTerminal s :: cl -> fprintf fmt "@[TyIdent (\"%s\", %a)@]" s print_clause cl
| ExtNonTerminal (g, TokNone) :: cl ->
  fprintf fmt "@[TyAnonArg (%a, %a)@]"
    print_symbol g print_clause cl
| ExtNonTerminal (g, TokName id) :: cl ->
  fprintf fmt "@[TyArg (%a, \"%s\", %a)@]"
    print_symbol g id print_clause cl

let rec print_binders fmt = function
| [] -> fprintf fmt "ist@ "
| (ExtTerminal _ | ExtNonTerminal (_, TokNone)) :: rem -> print_binders fmt rem
| (ExtNonTerminal (_, TokName id)) :: rem ->
  fprintf fmt "%s@ %a" id print_binders rem

let print_rule fmt r =
  fprintf fmt "@[TyML (%a, @[fun %a -> %s@])@]"
    print_clause r.tac_toks print_binders r.tac_toks r.tac_body.code

let rec print_rules fmt = function
| [] -> ()
| [r] -> fprintf fmt "(%a)@\n" print_rule r
| r :: rem -> fprintf fmt "(%a);@\n%a" print_rule r print_rules rem

let print_rules fmt rules =
  fprintf fmt "Tacentries.([@[<v>%a@]])" print_rules rules

let print_ast fmt ext =
  let deprecation fmt =
    function
    | None -> ()
    | Some { code } -> fprintf fmt "~deprecation:(%s) " code
  in
  let pr fmt () =
    let level = match ext.tacext_level with None -> 0 | Some i -> i in
    fprintf fmt "Tacentries.tactic_extend %s \"%s\" ~level:%i %a%a"
      plugin_name ext.tacext_name level
      deprecation ext.tacext_deprecated
      print_rules ext.tacext_rules
  in
  let () = fprintf fmt "let () = @[%a@]\n" pr () in
  ()

end

let declare_plugin fmt name =
  fprintf fmt "let %s = \"%s\"@\n" plugin_name name;
  fprintf fmt "let _ = Mltop.add_known_module %s@\n" plugin_name

let pr_ast fmt = function
| Code s -> fprintf fmt "%s@\n" s.code
| Comment s -> fprintf fmt "%s@\n" s
| DeclarePlugin name -> declare_plugin fmt name
| GramExt gram -> fprintf fmt "%a@\n" GramExt.print_ast gram
| VernacExt -> fprintf fmt "VERNACEXT@\n"
| TacticExt tac -> fprintf fmt "%a@\n" TacticExt.print_ast tac

let () =
  let () =
    if Array.length Sys.argv <> 2 then fatal "Expected exactly one command line argument"
  in
  let file = Sys.argv.(1) in
  let output = Filename.chop_extension file ^ ".ml" in
  let ast = parse_file file in
  let chan = open_out output in
  let fmt = formatter_of_out_channel chan in
  let iter ast = Format.fprintf fmt "@[%a@]%!"pr_ast ast in
  let () = List.iter iter ast in
  let () = close_out chan in
  exit 0
