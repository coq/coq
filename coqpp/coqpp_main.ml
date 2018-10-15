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

let dummy_loc = { loc_start = Lexing.dummy_pos; loc_end = Lexing.dummy_pos }
let mk_code s = { code = s; loc = dummy_loc }

let pr_loc loc =
  let file = loc.loc_start.pos_fname in
  let line = loc.loc_start.pos_lnum in
  let bpos = loc.loc_start.pos_cnum - loc.loc_start.pos_bol in
  let epos = loc.loc_end.pos_cnum - loc.loc_start.pos_bol in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d:" file line bpos epos

let print_code fmt c =
  let loc = c.loc.loc_start in
  (** Print the line location as a source annotation *)
  let padding = String.make (loc.pos_cnum - loc.pos_bol + 1) ' ' in
  let code_insert = asprintf "\n# %i \"%s\"\n%s%s" loc.pos_lnum loc.pos_fname padding c.code in
  fprintf fmt "@[@<0>%s@]@\n" code_insert

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

let print_list fmt pr l =
  let rec prl fmt = function
  | [] -> ()
  | [x] -> fprintf fmt "%a" pr x
  | x :: l -> fprintf fmt "%a;@ %a" pr x prl l
  in
  fprintf fmt "@[<hv>[%a]@]" prl l

let rec print_binders fmt = function
| [] -> ()
| ExtTerminal _ :: rem -> print_binders fmt rem
| ExtNonTerminal (_, TokNone) :: rem ->
  fprintf fmt "_@ %a" print_binders rem
| ExtNonTerminal (_, TokName id) :: rem ->
  fprintf fmt "%s@ %a" id print_binders rem

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

let print_string fmt s = fprintf fmt "\"%s\"" s

let print_opt fmt pr = function
| None -> fprintf fmt "None"
| Some x -> fprintf fmt "Some@ @[(%a)@]" pr x

module GramExt :
sig

val print_extrule : Format.formatter -> (symb list * string option list * code) -> unit
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
  let () = fprintf fmt "loc ->@ @[%a@]" print_code body in
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
  let tkn = List.map parse_tokens tkns in
  print_extrule fmt (tkn, vars, p.gprod_body)

and print_extrule fmt (tkn, vars, body) =
  let tkn = List.rev tkn in
  fprintf fmt "@[Extend.Rule@ (@[%a@],@ @[(%a)@])@]" print_symbols tkn print_fun (vars, body)

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
| SymbQuote c ->
  fprintf fmt "(%s)" c

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

module VernacExt :
sig

val print_ast : Format.formatter -> vernac_ext -> unit

end =
struct

let print_rule_classifier fmt r = match r.vernac_class with
| None -> fprintf fmt "None"
| Some f ->
  let no_binder = function ExtTerminal _ -> true | ExtNonTerminal _ -> false in
  if List.for_all no_binder r.vernac_toks then
    fprintf fmt "Some @[%a@]" print_code f
  else
    fprintf fmt "Some @[(fun %a-> %a)@]" print_binders r.vernac_toks print_code f

let print_body fmt r =
  fprintf fmt "@[(fun %a~atts@ ~st@ -> let () = %a in st)@]"
    print_binders r.vernac_toks print_code r.vernac_body

let rec print_sig fmt = function
| [] -> fprintf fmt "@[Vernacentries.TyNil@]"
| ExtTerminal s :: rem ->
  fprintf fmt "@[Vernacentries.TyTerminal (\"%s\", %a)@]" s print_sig rem
| ExtNonTerminal (symb, _) :: rem ->
  fprintf fmt "@[Vernacentries.TyNonTerminal (%a, %a)@]"
    print_symbol symb print_sig rem

let print_rule fmt r =
  fprintf fmt "Vernacentries.TyML (%b, %a, %a, %a)"
    r.vernac_depr print_sig r.vernac_toks print_body r print_rule_classifier r

let print_rules fmt rules =
  print_list fmt (fun fmt r -> fprintf fmt "(%a)" print_rule r) rules

let print_classifier fmt = function
| ClassifDefault -> fprintf fmt ""
| ClassifName "QUERY" ->
  fprintf fmt "~classifier:(fun _ -> Vernac_classifier.classify_as_query)"
| ClassifName "SIDEFF" ->
  fprintf fmt "~classifier:(fun _ -> Vernac_classifier.classify_as_sideeff)"
| ClassifName s -> fatal (Printf.sprintf "Unknown classifier %s" s)
| ClassifCode c -> fprintf fmt "~classifier:(%s)" c.code

let print_entry fmt = function
| None -> fprintf fmt "None"
| Some e -> fprintf fmt "(Some (%s))" e.code

let print_ast fmt ext =
  let pr fmt () =
    fprintf fmt "Vernacentries.vernac_extend ~command:\"%s\" %a ?entry:%a %a"
      ext.vernacext_name print_classifier ext.vernacext_class
      print_entry ext.vernacext_entry print_rules ext.vernacext_rules
  in
  let () = fprintf fmt "let () = @[%a@]@\n" pr () in
  ()

end

module TacticExt :
sig

val print_ast : Format.formatter -> tactic_ext -> unit

end =
struct

let rec print_clause fmt = function
| [] -> fprintf fmt "@[Tacentries.TyNil@]"
| ExtTerminal s :: cl -> fprintf fmt "@[Tacentries.TyIdent (\"%s\", %a)@]" s print_clause cl
| ExtNonTerminal (g, _) :: cl ->
  fprintf fmt "@[Tacentries.TyArg (%a, %a)@]"
    print_symbol g print_clause cl

let print_rule fmt r =
  fprintf fmt "@[Tacentries.TyML (%a, @[(fun %aist@ -> %a)@])@]"
    print_clause r.tac_toks print_binders r.tac_toks print_code r.tac_body

let print_rules fmt rules =
  print_list fmt (fun fmt r -> fprintf fmt "(%a)" print_rule r) rules

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

module VernacArgumentExt :
sig

val print_ast : Format.formatter -> vernac_argument_ext -> unit
val print_rules : Format.formatter -> string * tactic_rule list -> unit

end =
struct

let terminal s =
  let c = Printf.sprintf "Extend.Atoken (CLexer.terminal \"%s\")" s in
  SymbQuote c

let rec parse_symb self = function
| Ulist1 s -> SymbList1 (parse_symb self s, None)
| Ulist1sep (s, sep) -> SymbList1 (parse_symb self s, Some (terminal sep))
| Ulist0 s -> SymbList0 (parse_symb self s, None)
| Ulist0sep (s, sep) -> SymbList0 (parse_symb self s, Some (terminal sep))
| Uopt s -> SymbOpt (parse_symb self s)
| Uentry e -> if e = self then SymbSelf else SymbEntry (e, None)
| Uentryl (e, l) ->
  assert (e = "tactic");
  if l = 5 then SymbEntry ("Pltac.binder_tactic", None)
  else SymbEntry ("Pltac.tactic_expr", Some (string_of_int l))

let parse_token self = function
| ExtTerminal s -> (terminal s, None)
| ExtNonTerminal (e, TokNone) -> (parse_symb self e, None)
| ExtNonTerminal (e, TokName s) -> (parse_symb self e, Some s)

let parse_rule self r =
  let symbs = List.map (fun t -> parse_token self t) r.tac_toks in
  let symbs, vars = List.split symbs in
  (symbs, vars, r.tac_body)

let print_rules fmt (name, rules) =
  (** Rules are reversed. *)
  let rules = List.rev rules in
  let rules = List.map (fun r -> parse_rule name r) rules in
  let pr fmt l = print_list fmt (fun fmt r -> fprintf fmt "(%a)" GramExt.print_extrule r) l in
  match rules with
  | [([SymbEntry (e, None)], [Some s], { code = c } )] when String.trim c = s ->
    (** This is a horrible hack to work aroud limitations of camlp5 regarding
        factorization of parsing rules. It allows to recognize rules of the
        form [ entry(x) ] -> [ x ] so as not to generate a proxy entry and
        reuse the same entry directly. *)
    fprintf fmt "@[Vernacentries.Arg_alias (%s)@]" e
  | _ -> fprintf fmt "@[Vernacentries.Arg_rules (%a)@]" pr rules

let print_printer fmt = function
| None -> fprintf fmt "@[fun _ -> Pp.str \"missing printer\"@]"
| Some f -> print_code fmt f

let print_ast fmt arg =
  let name = arg.vernacargext_name in
  let pr fmt () =
    fprintf fmt "Vernacentries.vernac_argument_extend ~name:%a @[{@\n\
      Vernacentries.arg_parsing = %a;@\n\
      Vernacentries.arg_printer = %a;@\n}@]"
      print_string name print_rules (name, arg.vernacargext_rules)
      print_printer arg.vernacargext_printer
  in
  fprintf fmt "let (wit_%s, %s) = @[%a@]@\nlet _ = (wit_%s, %s)@\n"
    name name pr () name name

end

module ArgumentExt :
sig

val print_ast : Format.formatter -> argument_ext -> unit

end =
struct

let rec print_argtype fmt = function
| ExtraArgType s ->
  fprintf fmt "Geninterp.val_tag (Genarg.topwit wit_%s)" s
| PairArgType (arg1, arg2) ->
  fprintf fmt "Geninterp.Val.Pair (@[(%a)@], @[(%a)@])" print_argtype arg1 print_argtype arg2
| ListArgType arg ->
  fprintf fmt "Geninterp.Val.List @[(%a)@]" print_argtype arg
| OptArgType arg ->
  fprintf fmt "Geninterp.Val.Opt @[(%a)@]" print_argtype arg

let rec print_wit fmt = function
| ExtraArgType s ->
  fprintf fmt "wit_%s" s
| PairArgType (arg1, arg2) ->
  fprintf fmt "Genarg.PairArg (@[(%a)@], @[(%a)@])" print_wit arg1 print_wit arg2
| ListArgType arg ->
  fprintf fmt "Genarg.ListArg @[(%a)@]" print_wit arg
| OptArgType arg ->
  fprintf fmt "Genarg.OptArg @[(%a)@]" print_wit arg

let print_ast fmt arg =
  let name = arg.argext_name in
  let pr_tag fmt t = print_opt fmt print_argtype t in
  let intern fmt () = match arg.argext_glob, arg.argext_type with
  | Some f, (None | Some _) ->
    fprintf fmt "@[Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (%a))@]" print_code f
  | None, Some t ->
    fprintf fmt "@[Tacentries.ArgInternWit (%a)@]" print_wit t
  | None, None ->
    fprintf fmt "@[Tacentries.ArgInternFun (fun ist v -> (ist, v))@]"
  in
  let subst fmt () = match arg.argext_subst, arg.argext_type with
  | Some f, (None | Some _) ->
    fprintf fmt "@[Tacentries.ArgSubstFun (%a)@]" print_code f
  | None, Some t ->
    fprintf fmt "@[Tacentries.ArgSubstWit (%a)@]" print_wit t
  | None, None ->
    fprintf fmt "@[Tacentries.ArgSubstFun (fun s v -> v)@]"
  in
  let interp fmt () = match arg.argext_interp, arg.argext_type with
  | Some f, (None | Some _) ->
    fprintf fmt "@[Tacentries.ArgInterpLegacy (%a)@]" print_code f
  | None, Some t ->
    fprintf fmt "@[Tacentries.ArgInterpWit (%a)@]" print_wit t
  | None, None ->
    fprintf fmt "@[Tacentries.ArgInterpRet@]"
  in
  let default_printer = mk_code "fun _ _ _ _ -> Pp.str \"missing printer\"" in
  let rpr = match arg.argext_rprinter, arg.argext_tprinter with
  | Some f, (None | Some _) -> f
  | None, Some f -> f
  | None, None -> default_printer
  in
  let gpr = match arg.argext_gprinter, arg.argext_tprinter with
  | Some f, (None | Some _) -> f
  | None, Some f -> f
  | None, None -> default_printer
  in
  let tpr = match arg.argext_tprinter with
  | Some f -> f
  | None -> default_printer
  in
  let pr fmt () =
    fprintf fmt "Tacentries.argument_extend ~name:%a @[{@\n\
      Tacentries.arg_parsing = %a;@\n\
      Tacentries.arg_tag = @[%a@];@\n\
      Tacentries.arg_intern = @[%a@];@\n\
      Tacentries.arg_subst = @[%a@];@\n\
      Tacentries.arg_interp = @[%a@];@\n\
      Tacentries.arg_printer = @[((%a), (%a), (%a))@];@\n}@]"
      print_string name
      VernacArgumentExt.print_rules (name, arg.argext_rules)
      pr_tag arg.argext_type
      intern () subst () interp () print_code rpr print_code gpr print_code tpr
  in
  fprintf fmt "let (wit_%s, %s) = @[%a@]@\nlet _ = (wit_%s, %s)@\n"
    name name pr () name name

end

let declare_plugin fmt name =
  fprintf fmt "let %s = \"%s\"@\n" plugin_name name;
  fprintf fmt "let _ = Mltop.add_known_module %s@\n" plugin_name

let pr_ast fmt = function
| Code s -> fprintf fmt "%a@\n" print_code s
| Comment s -> fprintf fmt "%s@\n" s
| DeclarePlugin name -> declare_plugin fmt name
| GramExt gram -> fprintf fmt "%a@\n" GramExt.print_ast gram
| VernacExt vernac -> fprintf fmt "%a@\n" VernacExt.print_ast vernac
| VernacArgumentExt arg -> fprintf fmt "%a@\n" VernacArgumentExt.print_ast arg
| TacticExt tac -> fprintf fmt "%a@\n" TacticExt.print_ast tac
| ArgumentExt arg -> fprintf fmt "%a@\n" ArgumentExt.print_ast arg

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
