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

let print_local chan ext =
  let locals = get_local_entries ext in
  match locals with
  | [] -> ()
  | e :: locals ->
    let mk_e chan e = fprintf chan "%s.Entry.create \"%s\"" ext.gramext_name e in
    let () = fprintf chan "@[<hv 2>let %s =@ @[%a@]@]@ " e mk_e e in
    let iter e = fprintf chan "@[<hv 2>and %s =@ @[%a@]@]@ " e mk_e e in
    let () = List.iter iter locals in
    fprintf chan "in@ "

let print_string chan s = fprintf chan "\"%s\"" s

let print_list chan pr l =
  let rec prl chan = function
  | [] -> ()
  | [x] -> fprintf chan "%a" pr x
  | x :: l -> fprintf chan "%a;@ %a" pr x prl l
  in
  fprintf chan "@[<hv>[%a]@]" prl l

let print_opt chan pr = function
| None -> fprintf chan "None"
| Some x -> fprintf chan "Some@ (%a)" pr x

let print_position chan pos = match pos with
| First -> fprintf chan "Extend.First"
| Last -> fprintf chan "Extend.Last"
| Before s -> fprintf chan "Extend.Before@ \"%s\"" s
| After s -> fprintf chan "Extend.After@ \"%s\"" s
| Level s -> fprintf chan "Extend.Level@ \"%s\"" s

let print_assoc chan = function
| LeftA -> fprintf chan "Extend.LeftA"
| RightA -> fprintf chan "Extend.RightA"
| NonA -> fprintf chan "Extend.NonA"

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

let print_fun chan (vars, body) =
  let vars = List.rev vars in
  let iter = function
  | None -> fprintf chan "_@ "
  | Some id -> fprintf chan "%s@ " id
  in
  let () = fprintf chan "fun@ " in
  let () = List.iter iter vars in
  (** FIXME: use Coq locations in the macros *)
  let () = fprintf chan "loc ->@ @[%s@]" body.code in
  ()

(** Meta-program instead of calling Tok.of_pattern here because otherwise
    violates value restriction *)
let print_tok chan = function
| "", s -> fprintf chan "Tok.KEYWORD %a" print_string s
| "IDENT", s -> fprintf chan "Tok.IDENT %a" print_string s
| "PATTERNIDENT", s -> fprintf chan "Tok.PATTERNIDENT %a" print_string s
| "FIELD", s -> fprintf chan "Tok.FIELD %a" print_string s
| "INT", s -> fprintf chan "Tok.INT %a" print_string s
| "STRING", s -> fprintf chan "Tok.STRING %a" print_string s
| "LEFTQMARK", _ -> fprintf chan "Tok.LEFTQMARK"
| "BULLET", s -> fprintf chan "Tok.BULLET %a" print_string s
| "EOI", _ -> fprintf chan "Tok.EOI"
| _ -> failwith "Tok.of_pattern: not a constructor"

let rec print_prod chan p =
  let (vars, tkns) = List.split p.gprod_symbs in
  let f = (vars, p.gprod_body) in
  let tkn = List.rev_map parse_tokens tkns in
  fprintf chan "@[Extend.Rule@ (@[%a@],@ @[(%a)@])@]" print_symbols tkn print_fun f

and print_symbols chan = function
| [] -> fprintf chan "Extend.Stop"
| tkn :: tkns ->
  fprintf chan "Extend.Next @[(%a,@ %a)@]" print_symbols tkns print_symbol tkn

and print_symbol chan tkn = match tkn with
| SymbToken (t, s) ->
  let s = match s with None -> "" | Some s -> s in
  fprintf chan "(Extend.Atoken (%a))" print_tok (t, s)
| SymbEntry (e, None) ->
  fprintf chan "(Extend.Aentry %s)" e
| SymbEntry (e, Some l) ->
  fprintf chan "(Extend.Aentryl (%s, %a))" e print_string l
| SymbSelf ->
  fprintf chan "Extend.Aself"
| SymbNext ->
  fprintf chan "Extend.Anext"
| SymbList0 (s, None) ->
  fprintf chan "(Extend.Alist0 %a)" print_symbol s
| SymbList0 (s, Some sep) ->
  fprintf chan "(Extend.Alist0sep (%a, %a))" print_symbol s print_symbol sep
| SymbList1 (s, None) ->
  fprintf chan "(Extend.Alist1 %a)" print_symbol s
| SymbList1 (s, Some sep) ->
  fprintf chan "(Extend.Alist1sep (%a, %a))" print_symbol s print_symbol sep
| SymbOpt s ->
  fprintf chan "(Extend.Aopt %a)" print_symbol s
| SymbRules rules ->
  let pr chan (r, body) =
    let (vars, tkn) = List.split r in
    let tkn = List.rev tkn in
    fprintf chan "Extend.Rules @[({ Extend.norec_rule = %a },@ (%a))@]" print_symbols tkn print_fun (vars, body)
  in
  let pr chan rules = print_list chan pr rules in
  fprintf chan "(Extend.Arules %a)" pr (List.rev rules)

let print_rule chan r =
  let pr_lvl chan lvl = print_opt chan print_string lvl in
  let pr_asc chan asc = print_opt chan print_assoc asc in
  let pr_prd chan prd = print_list chan print_prod prd in
  fprintf chan "@[(%a,@ %a,@ %a)@]" pr_lvl r.grule_label pr_asc r.grule_assoc pr_prd (List.rev r.grule_prods)

let print_entry chan gram e =
  let print_position_opt chan pos = print_opt chan print_position pos in
  let print_rules chan rules = print_list chan print_rule rules in
  fprintf chan "let () =@ @[%s.safe_extend@ %s@ @[(%a, %a)@]@]@ in@ "
    gram e.gentry_name print_position_opt e.gentry_pos print_rules e.gentry_rules

let print_ast chan ext =
  let () = fprintf chan "let _ = @[" in
  let () = fprintf chan "@[<v>%a@]" print_local ext in
  let () = List.iter (fun e -> print_entry chan ext.gramext_name e) ext.gramext_entries in
  let () = fprintf chan "()@]@\n" in
  ()

end

module TacticExt :
sig

val print_ast : Format.formatter -> tactic_ext -> unit

end =
struct

let print_ident chan id =
  (** Workaround for badly-designed generic arguments lacking a closure *)
  fprintf chan "Names.Id.of_string_soft \"$%s\"" id

let rec print_symbol chan = function
| Ulist1 s ->
  fprintf chan "@[Extend.TUlist1 (%a)@]" print_symbol s
| Ulist1sep (s, sep) ->
  fprintf chan "@[Extend.TUlist1sep (%a, \"%s\")@]" print_symbol s sep
| Ulist0 s ->
  fprintf chan "@[Extend.TUlist0 (%a)@]" print_symbol s
| Ulist0sep (s, sep) ->
  fprintf chan "@[Extend.TUlist0sep (%a, \"%s\")@]" print_symbol s sep
| Uopt s ->
  fprintf chan "@[Extend.TUopt (%a)@]" print_symbol s
| Uentry e ->
  fprintf chan "@[Extend.TUentry (Genarg.get_arg_tag wit_%s)@]" e
| Uentryl (e, l) ->
  assert (e = "tactic");
  fprintf chan "@[Extend.TUentryl (Genarg.get_arg_tag wit_%s, %i)@]" e l

let rec print_clause chan = function
| [] -> fprintf chan "@[TyNil@]"
| ExtTerminal s :: cl -> fprintf chan "@[TyIdent (\"%s\", %a)@]" s print_clause cl
| ExtNonTerminal (g, TokNone) :: cl ->
  fprintf chan "@[TyAnonArg (Loc.tag (%a), %a)@]"
    print_symbol g print_clause cl
| ExtNonTerminal (g, TokName id) :: cl ->
  fprintf chan "@[TyArg (Loc.tag (%a, %a), %a)@]"
    print_symbol g print_ident id print_clause cl

let rec print_binders chan = function
| [] -> fprintf chan "ist@ "
| (ExtTerminal _ | ExtNonTerminal (_, TokNone)) :: rem -> print_binders chan rem
| (ExtNonTerminal (_, TokName id)) :: rem ->
  fprintf chan "%s@ %a" id print_binders rem

let print_rule chan r =
  fprintf chan "@[TyML (%a, @[fun %a -> %s@])@]"
    print_clause r.tac_toks print_binders r.tac_toks r.tac_body.code

let rec print_rules chan = function
| [] -> ()
| [r] -> fprintf chan "(%a)@\n" print_rule r
| r :: rem -> fprintf chan "(%a);@\n%a" print_rule r print_rules rem

let print_rules chan rules =
  fprintf chan "Tacentries.([@[<v>%a@]])" print_rules rules

let print_ast chan ext =
  let pr chan () =
    let level = match ext.tacext_level with None -> 0 | Some i -> i in
    fprintf chan "Tacentries.tactic_extend %s \"%s\" ~level:%i %a"
      plugin_name ext.tacext_name level print_rules ext.tacext_rules
  in
  let () = fprintf chan "let () = @[%a@]\n" pr () in
  ()

end

let pr_ast chan = function
| Code s -> fprintf chan "%s@\n" s.code
| Comment s -> fprintf chan "%s@\n" s
| DeclarePlugin name -> fprintf chan "let %s = \"%s\"@\n" plugin_name name
| GramExt gram -> fprintf chan "%a@\n" GramExt.print_ast gram
| VernacExt -> fprintf chan "VERNACEXT@\n"
| TacticExt tac -> fprintf chan "%a@\n" TacticExt.print_ast tac

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
