(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Lexing
open Coqpp_ast
open Format
open Coqpp_parser

let fatal msg =
  let () = Format.eprintf "Error: %s@\n%!" msg in
  exit 1

let mk_code s = { code = s; loc = None }

let count_substring_newlines s offset len =
  let rec aux acc offset len =
    if len = 0 then acc
    else
      let acc = match s.[offset] with
        | '\n' -> acc+1
        | _ -> acc
      in
      aux acc (offset+1) (len-1)
  in
  aux 0 offset len

type line_counter = {
  fname : string;
  mutable lines : int;
}

(* NB: using [Format.pp_set_formatter_out_functions] doesn't work well because
   [Format.formatter_of_out_channel] does [out_newline = out_string fmt "\n"]
   so if we update the line count in both out_newline and out_string
   then we double count newlines from out_newline
   ([out_string fmt "\n"] will use our wrapper).

   OTOH if we update the line count only in [out_string] we would miss
   newlines output by formatters created by [Format.formatter_of_out_functions]

   (not a big concern for coqpp but it's not a nice API to take
   [Format.formatter] but only work properly when it was created in a specific way)
*)
let of_out_channel_with_line_count fname oc =
  let v = { fname; lines = 1 } in

  let out_string s offset len =
    v.lines <- v.lines + count_substring_newlines s offset len;
    output_substring oc s offset len
  in
  let out_newline () =
    v.lines <- v.lines + 1;
    output_char oc '\n'
  in
  let out_spaces n = output_string oc (String.make n ' ') in
  let fmt = Format.formatter_of_out_functions {
    out_string;
    out_flush = (fun () -> flush oc);
    out_newline;
    out_spaces;
    out_indent = out_spaces;
  }
  in
  fmt, v

let exit_code counter fmt () =
  (* this flush makes the formatting of the generated code worse but
     is probably worth it for better error locations *)
  Format.pp_print_flush fmt ();
  let lines = counter.lines in
  (* lines+1 because we are setting the position for the next line  *)
  let msg = asprintf "# %i \"%s\"" (lines+1) counter.fname in
  fprintf fmt "@<0>%s@\n" msg

let print_code counter fmt c =
  match c.loc with
  | None -> fprintf fmt "%s" c.code
  | Some loc ->
    (* Print the line location as a source annotation *)
    let loc = loc.loc_start in
    let padding = String.make (loc.pos_cnum - loc.pos_bol + 1) ' ' in
    let code_insert = asprintf "\n# %i \"%s\"\n%s%s\n" loc.pos_lnum loc.pos_fname padding c.code in
    fprintf fmt "@<0>%s" code_insert;
    exit_code counter fmt ()

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

(* Used to generate unique ids *)
let file_name = ref ""

(* We used to output __plugin_name = "bla" then refer to __plugin_name in generated code
   but this is not robust to eg

   DECLARE PLUGIN "bla"
   open G_ltac
   use the plugin name

   since g_ltac has no mli its __plugin_name will shadow the local one and wreak havoc
*)
let plugin_name = ref None

let force_is_plugin ~what () = match !plugin_name with
  | Some (Some n) -> n
  | Some None | None -> fatal ("DECLARE PLUGIN required before "^what)

let check_is_plugin ~what () = match !plugin_name with
  | Some b -> b
  | None -> fatal ("DECLARE PLUGIN required before "^what)

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

val print_extrule : line_counter -> Format.formatter -> (symb list * string option list * code) -> unit
val print_ast : line_counter -> Format.formatter -> grammar_ext -> unit

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
    let mk_e fmt e = fprintf fmt "Procq.Entry.make \"%s\"" e in
    let () = fprintf fmt "@[<hv 2>let %s =@ @[%a@]@]@ " e mk_e e in
    let iter e = fprintf fmt "@[<hv 2>and %s =@ @[%a@]@]@ " e mk_e e in
    let () = List.iter iter locals in
    fprintf fmt "in@ "

let print_position fmt pos = match pos with
| First -> fprintf fmt "Gramlib.Gramext.First"
| Last -> fprintf fmt "Gramlib.Gramext.Last"
| Before s -> fprintf fmt "Gramlib.Gramext.Before@ \"%s\"" s
| After s -> fprintf fmt "Gramlib.Gramext.After@ \"%s\"" s

let print_assoc fmt = function
| LeftA -> fprintf fmt "Gramlib.Gramext.LeftA"
| RightA -> fprintf fmt "Gramlib.Gramext.RightA"
| NonA -> fprintf fmt "Gramlib.Gramext.NonA"

let is_token s = match string_split s with
| [s] -> is_uident s
| _ -> false

let rec parse_tokens ?(in_anon=false) =
let err_anon () =
  if in_anon then
    fatal (Printf.sprintf "'SELF' or 'NEXT' illegal in anonymous entry level") in
function
| [GSymbString s] -> SymbToken ("", Some s)
| [GSymbQualid ("QUOTATION", None); GSymbString s] ->
    SymbToken ("QUOTATION", Some s)
| [GSymbQualid ("SELF", None)] -> err_anon (); SymbSelf
| [GSymbQualid ("NEXT", None)] -> err_anon (); SymbNext
| [GSymbQualid ("LIST0", None); tkn] ->
  SymbList0 (parse_token ~in_anon tkn, None)
| [GSymbQualid ("LIST1", None); tkn] ->
  SymbList1 (parse_token ~in_anon tkn, None)
| [GSymbQualid ("LIST0", None); tkn; GSymbQualid ("SEP", None); tkn'] ->
  SymbList0 (parse_token ~in_anon tkn, Some (parse_token ~in_anon tkn'))
| [GSymbQualid ("LIST1", None); tkn; GSymbQualid ("SEP", None); tkn'] ->
  SymbList1 (parse_token ~in_anon tkn, Some (parse_token ~in_anon tkn'))
| [GSymbQualid ("OPT", None); tkn] ->
  SymbOpt (parse_token ~in_anon tkn)
| [GSymbQualid (e, None)] when is_token e -> SymbToken (e, None)
| [GSymbQualid (e, None); GSymbString s] when is_token e -> SymbToken (e, Some s)
| [GSymbQualid (e, lvl)] when not (is_token e) -> SymbEntry (e, lvl)
| [GSymbParen tkns] -> parse_tokens ~in_anon tkns
| [GSymbProd prds] ->
  let map p =
    let map (pat, tkns) = (pat, parse_tokens ~in_anon:true tkns) in
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

and parse_token ~in_anon tkn = parse_tokens ~in_anon [tkn]

let print_fun counter fmt (vars, body) =
  let vars = List.rev vars in
  let iter = function
  | None -> fprintf fmt "_@ "
  | Some id -> fprintf fmt "%s@ " id
  in
  let () = fprintf fmt "fun@ " in
  let () = List.iter iter vars in
  let () = fprintf fmt "loc ->@ @[%a@]" (print_code counter) body in
  ()

(** Meta-program instead of calling Tok.of_pattern here because otherwise
    violates value restriction *)
let print_tok fmt =
let print_pat fmt = print_opt fmt print_string in
function
| "", Some s -> fprintf fmt "Tok.PKEYWORD (%a)" print_string s
| "IDENT", s -> fprintf fmt "Tok.PIDENT (%a)" print_pat s
| "FIELD", s -> fprintf fmt "Tok.PFIELD (%a)" print_pat s
| "NUMBER", None -> fprintf fmt "Tok.PNUMBER None"
| "NUMBER", Some s -> fprintf fmt "Tok.PNUMBER (Some (NumTok.Unsigned.of_string %a))" print_string s
| "STRING", s -> fprintf fmt "Tok.PSTRING (%a)" print_pat s
| "LEFTQMARK", None -> fprintf fmt "Tok.PLEFTQMARK"
| "BULLET", s -> fprintf fmt "Tok.PBULLET (%a)" print_pat s
| "QUOTATION", Some s -> fprintf fmt "Tok.PQUOTATION %a" print_string s
| "EOI", None -> fprintf fmt "Tok.PEOI"
| _ -> failwith "Tok.of_pattern: not a constructor"

let rec print_prod counter fmt p =
  let (vars, tkns) = List.split p.gprod_symbs in
  let tkn = List.map parse_tokens tkns in
  print_extrule counter fmt (tkn, vars, p.gprod_body)

and print_extrule counter fmt (tkn, vars, body) =
  let tkn = List.rev tkn in
  fprintf fmt "@[Procq.Production.make@ @[(%a)@]@ @[(%a)@]@]" (print_symbols ~norec:false counter) tkn (print_fun counter) (vars, body)

and print_symbols ~norec counter fmt = function
| [] -> fprintf fmt "Procq.Rule.stop"
| tkn :: tkns ->
  let c = if norec then "Procq.Rule.next_norec" else "Procq.Rule.next" in
  fprintf fmt "@[%s@ (%a)@ (%a)@]" c (print_symbols ~norec counter) tkns (print_symbol counter) tkn

and print_symbol counter fmt tkn = match tkn with
| SymbToken (t, s) ->
  fprintf fmt "(Procq.Symbol.token (%a))" print_tok (t, s)
| SymbEntry (e, None) ->
  fprintf fmt "(Procq.Symbol.nterm %s)" e
| SymbEntry (e, Some l) ->
  fprintf fmt "(Procq.Symbol.nterml %s (%a))" e print_string l
| SymbSelf ->
  fprintf fmt "Procq.Symbol.self"
| SymbNext ->
  fprintf fmt "Procq.Symbol.next"
| SymbList0 (s, None) ->
  fprintf fmt "(Procq.Symbol.list0 %a)" (print_symbol counter) s
| SymbList0 (s, Some sep) ->
  fprintf fmt "(Procq.Symbol.list0sep (%a) (%a) false)" (print_symbol counter) s (print_anonymized_symbol counter) sep
| SymbList1 (s, None) ->
  fprintf fmt "(Procq.Symbol.list1 (%a))" (print_symbol counter) s
| SymbList1 (s, Some sep) ->
  fprintf fmt "(Procq.Symbol.list1sep (%a) (%a) false)" (print_symbol counter) s (print_anonymized_symbol counter) sep
| SymbOpt s ->
  fprintf fmt "(Procq.Symbol.opt %a)" (print_symbol counter) s
| SymbRules rules ->
  let pr fmt (r, body) =
    let (vars, tkn) = List.split r in
    let tkn = List.rev tkn in
    fprintf fmt "Procq.Rules.make @[(%a)@ (%a)@]" (print_symbols ~norec:true counter) tkn (print_fun counter) (vars, body)
  in
  let pr fmt rules = print_list fmt pr rules in
  fprintf fmt "(Procq.Symbol.rules %a)" pr (List.rev rules)
| SymbQuote c ->
  fprintf fmt "(%s)" c

and print_anonymized_symbol counter fmt tkn = match tkn with
| SymbToken (t, s) ->
  fprintf fmt "(Procq.Symbol.tokens [Procq.TPattern (%a)])" print_tok (t, s)
| _ -> print_symbol counter fmt (SymbRules [[None, tkn], mk_code "()"])

let print_rule counter fmt r =
  let pr_lvl fmt lvl = print_opt fmt print_string lvl in
  let pr_asc fmt asc = print_opt fmt print_assoc asc in
  let pr_prd fmt prd = print_list fmt (print_prod counter) prd in
  fprintf fmt "@[(%a,@ %a,@ %a)@]" pr_lvl r.grule_label pr_asc r.grule_assoc pr_prd (List.rev r.grule_prods)

let gramext_count = ref 0

let gramext_plugin_uid name =
  let cnt = !gramext_count in
  incr gramext_count;
  " ~plugin_uid:(\""^name^"\", \""^(!file_name)^":"^string_of_int cnt^"\")"

let grammar_extend () =
  match check_is_plugin ~what:"GRAMMAR EXTEND" () with
  | Some name -> "Egramml.grammar_extend"^gramext_plugin_uid name
  | None -> "Procq.grammar_extend"

let print_entry counter fmt e = match e.gentry_rules with
| GDataReuse (pos, r) ->
  let rules = List.rev r in
  let pr_pos fmt pos = print_opt fmt print_string pos in
  let pr_prd fmt prd = print_list fmt (print_prod counter) prd in
  fprintf fmt "let () =@ @[%s@ %s@ @[(Procq.Reuse (%a, %a))@]@]@ in@ "
    (grammar_extend ()) e.gentry_name pr_pos pos pr_prd rules
| GDataFresh (pos, rules) ->
  let print_rules fmt rules = print_list fmt (print_rule counter) rules in
  let pr_check fmt () = match pos with
  | None -> fprintf fmt "let () =@ @[assert@ (Procq.Entry.is_empty@ %s)@]@ in@\n" e.gentry_name
  | Some _ -> fprintf fmt ""
  in
  let pos = match pos with None -> First | Some pos -> pos in
  fprintf fmt "%alet () =@ @[%s@ %s@ @[(Procq.Fresh@ (%a, %a))@]@]@ in@ "
    pr_check () (grammar_extend ()) e.gentry_name print_position pos print_rules rules

let print_ast counter fmt ext =
  let () = fprintf fmt "@[<2>let _ =@ " in
  let () = fprintf fmt "@[<v>%a@]" print_local ext in
  let () = List.iter (fun e -> print_entry counter fmt e) ext.gramext_entries in
  let () = fprintf fmt "()@]@\n" in
  ()

end

module VernacExt :
sig

val print_ast : line_counter -> Format.formatter -> vernac_ext -> unit

end =
struct

let print_rule_classifier counter fmt r = match r.vernac_class with
| None -> fprintf fmt "None"
| Some f ->
  let no_binder = function ExtTerminal _ -> true | ExtNonTerminal _ -> false in
  if List.for_all no_binder r.vernac_toks then
    fprintf fmt "Some @[%a@]" (print_code counter) f
  else
    fprintf fmt "Some @[(fun %a-> %a)@]" print_binders r.vernac_toks (print_code counter) f

(* let print_atts fmt = function *)
(*   | None -> fprintf fmt "@[let () = Attributes.unsupported_attributes atts in@] " *)
(*   | Some atts -> *)
(*     let rec print_left fmt = function *)
(*       | [] -> assert false *)
(*       | [x,_] -> fprintf fmt "%s" x *)
(*       | (x,_) :: rem -> fprintf fmt "(%s, %a)" x print_left rem *)
(*     in *)
(*     let rec print_right fmt = function *)
(*       | [] -> assert false *)
(*       | [_,y] -> fprintf fmt "%s" y *)
(*       | (_,y) :: rem -> fprintf fmt "(%s ++ %a)" y print_right rem *)
(*     in *)
(*     let nota = match atts with [_] -> "" | _ -> "Attributes.Notations." in *)
(*     fprintf fmt "@[let %a = Attributes.parse %s(%a) atts in@] " *)
(*       print_left atts nota print_right atts *)

let print_atts_left fmt = function
  | None -> fprintf fmt "()"
  | Some atts ->
    let rec aux fmt = function
      | [] -> assert false
      | [x,_] -> fprintf fmt "%s" x
      | (x,_) :: rem -> fprintf fmt "(%s, %a)" x aux rem
    in
    aux fmt atts

let print_atts_right counter fmt = function
  | None -> fprintf fmt "(Attributes.unsupported_attributes atts)"
  | Some atts ->
    let rec aux fmt = function
      | [] -> assert false
      | [_,y] -> print_code counter fmt y
      | (_,y) :: rem -> fprintf fmt "(%a ++ %a)" (print_code counter) y aux rem
    in
    let nota = match atts with [_] -> "" | _ -> "Attributes.Notations." in
    fprintf fmt "(Attributes.parse %s%a atts)" nota aux atts

let understand_state = function
  | "close_proof" -> "vtcloseproof", ["lemma"; "pm"]
  | "open_proof" -> "vtopenproof", []
  | "proof" -> "vtmodifyproof", ["pstate"]
  | "proof_opt_query" -> "vtreadproofopt", ["pstate"]
  | "proof_query" -> "vtreadproof", ["pstate"]
  | "read_program" -> "vtreadprogram", ["pm"]
  | "program" -> "vtmodifyprogram", ["pm"]
  | "declare_program" -> "vtdeclareprogram", ["pm"]
  | "program_interactive" -> "vtopenproofprogram", ["pm"]
  | "opaque_access" -> "vtopaqueaccess", ["opaque_access"]
  | s -> fatal ("unsupported state specifier: " ^ s)

let rec pr_named_arguments fmt = function
| [] -> assert false
| [s] -> fprintf fmt "~%s" s
| s :: l -> fprintf fmt "~%s@ %a" s pr_named_arguments l

let pr_begin_wrapper fmt = function
| [] -> fprintf fmt "fun () ->"
| args -> fprintf fmt "fun %a ->" pr_named_arguments args

let pr_end_wrapper fmt = function
| [] -> fprintf fmt ""
| args -> fprintf fmt "@ %a" pr_named_arguments args

let print_body_state counter state fmt r =
  let state = match r.vernac_state with Some _ as s -> s | None -> state in
  match state with
  | None -> fprintf fmt "Vernactypes.vtdefault (fun () -> %a)" (print_code counter) r.vernac_body
  | Some "CUSTOM" -> print_code counter fmt r.vernac_body
  | Some state ->
    let state, wrap = understand_state state in
    fprintf fmt "Vernactypes.%s (%a (%a)%a)" state pr_begin_wrapper wrap
      (print_code counter) r.vernac_body pr_end_wrapper wrap

let print_body_fun counter state fmt r =
  match r.vernac_synterp with
  | None ->
    fprintf fmt "let coqpp_body %a%a =@ @[%a@] in@ "
      print_binders r.vernac_toks print_atts_left r.vernac_atts (print_body_state counter state) r
  | Some (id,pe) ->
    fprintf fmt "let coqpp_body %a%a =@ @[(let %s = %a in %a)@] in@ "
      print_binders r.vernac_toks print_atts_left r.vernac_atts id (print_code counter) pe  (print_body_state counter state) r

let print_body counter state fmt r =
  fprintf fmt "@[<2>(%a@[<2>fun %a?loc ~atts () ->@]@ @[<2>coqpp_body@ %a%a@])@]"
    (print_body_fun counter state) r print_binders r.vernac_toks
    print_binders r.vernac_toks (print_atts_right counter) r.vernac_atts

let rec print_sig fmt = function
| [] -> fprintf fmt "@[Vernacextend.TyNil@]"
| ExtTerminal s :: rem ->
  fprintf fmt "@[Vernacextend.TyTerminal@ @[<1>(\"%s\",@ %a)@]@]" s print_sig rem
| ExtNonTerminal (symb, _) :: rem ->
  fprintf fmt "@[Vernacextend.TyNonTerminal (%a,@ %a)@]"
    print_symbol symb print_sig rem

let print_rule counter state fmt r =
  fprintf fmt "Vernacextend.TyML@ @[<v1>(%b,@ %a,@ %a,@ %a)@]"
    r.vernac_depr print_sig r.vernac_toks (print_body counter state) r (print_rule_classifier counter) r

let print_rules counter state fmt rules =
  print_list fmt (fun fmt r -> fprintf fmt "(%a)" (print_rule counter state) r) rules

let print_classifier fmt = function
| ClassifDefault -> fprintf fmt ""
| ClassifName "QUERY" ->
  fprintf fmt "~classifier:(fun _ -> Vernacextend.classify_as_query)"
| ClassifName "SIDEFF" ->
  fprintf fmt "~classifier:(fun _ -> Vernacextend.classify_as_sideeff)"
| ClassifName s -> fatal (Printf.sprintf "Unknown classifier %s" s)
| ClassifCode c -> fprintf fmt "~classifier:(%s)" c.code

let print_entry fmt = function
| None -> fprintf fmt "None"
| Some e -> fprintf fmt "(Some (%s))" e.code

let print_ast counter fmt ext =
  let pr fmt () =
    fprintf fmt "Vernacextend.static_vernac_extend ~plugin:%s ~command:\"%s\" %a ?entry:%a %a"
      (match check_is_plugin ~what:"VERNAC EXTEND" () with | Some name -> "(Some \""^name^"\")" | None -> "None")
      ext.vernacext_name print_classifier ext.vernacext_class
      print_entry ext.vernacext_entry (print_rules counter ext.vernacext_state) ext.vernacext_rules
  in
  let () = fprintf fmt "let () = @[%a@]@\n" pr () in
  ()

end

module TacticExt :
sig

val print_ast : line_counter -> Format.formatter -> tactic_ext -> unit

end =
struct

let rec print_clause fmt = function
| [] -> fprintf fmt "@[Tacentries.TyNil@]"
| ExtTerminal s :: cl -> fprintf fmt "@[Tacentries.TyIdent (\"%s\", %a)@]" s print_clause cl
| ExtNonTerminal (g, _) :: cl ->
  fprintf fmt "@[Tacentries.TyArg (%a, %a)@]"
    print_symbol g print_clause cl

let print_rule counter fmt r =
  fprintf fmt "@[Tacentries.TyML (%a, @[(fun %aist@ -> %a)@])@]"
    print_clause r.tac_toks print_binders r.tac_toks (print_code counter) r.tac_body

let print_rules counter fmt rules =
  print_list fmt (fun fmt r -> fprintf fmt "(%a)" (print_rule counter) r) rules

let print_ast counter fmt ext =
  let deprecation fmt =
    function
    | None -> ()
    | Some { code } -> fprintf fmt "~deprecation:(%s) " code
  in
  let pr fmt () =
    let level = match ext.tacext_level with None -> 0 | Some i -> i in
    let name = force_is_plugin ~what:"TACTIC EXTEND" () in
    fprintf fmt "Tacentries.tactic_extend \"%s\" \"%s\" ~level:%i %a%a"
      name ext.tacext_name level
      deprecation ext.tacext_deprecated
      (print_rules counter) ext.tacext_rules
  in
  let () = fprintf fmt "let () = @[%a@]\n" pr () in
  ()

end

module VernacArgumentExt :
sig

val print_ast : line_counter -> Format.formatter -> vernac_argument_ext -> unit
val print_rules : line_counter -> Format.formatter -> string * tactic_rule list -> unit

end =
struct

let terminal s =
  let p =
    if s <> "" && s.[0] >= '0' && s.[0] <= '9' then "CLexer.terminal_number"
    else "Procq.terminal" in
  let c = Printf.sprintf "Procq.Symbol.token (%s \"%s\")" p s in
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
  else SymbEntry ("Pltac.ltac_expr", Some (string_of_int l))

let parse_token self = function
| ExtTerminal s -> (terminal s, None)
| ExtNonTerminal (e, TokNone) -> (parse_symb self e, None)
| ExtNonTerminal (e, TokName s) -> (parse_symb self e, Some s)

let parse_rule self r =
  let symbs = List.map (fun t -> parse_token self t) r.tac_toks in
  let symbs, vars = List.split symbs in
  (symbs, vars, r.tac_body)

let print_rules counter fmt (name, rules) =
  (* Rules are reversed. *)
  let rules = List.rev rules in
  let rules = List.map (fun r -> parse_rule name r) rules in
  let pr fmt l = print_list fmt (fun fmt r -> fprintf fmt "(%a)" (GramExt.print_extrule counter) r) l in
  match rules with
  | [([SymbEntry (e, None)], [Some s], { code = c } )] when String.trim c = s ->
    (* This is a horrible hack to work around limitations of camlp5 regarding
       factorization of parsing rules. It allows to recognize rules of the
       form [ entry(x) ] -> [ x ] so as not to generate a proxy entry and
       reuse the same entry directly. *)
    fprintf fmt "@[Vernacextend.Arg_alias@ @[<2>(%s)@]@]" e
  | _ -> fprintf fmt "@[Vernacextend.Arg_rules@ @[<2>(%a)@]@]" pr rules

let print_printer counter fmt = function
| None -> fprintf fmt "@[fun _ -> Pp.str \"missing printer\"@]"
| Some f -> print_code counter fmt f

let print_ast counter fmt arg =
  let name = arg.vernacargext_name in
  let pr fmt () =
    fprintf fmt "Vernacextend.vernac_argument_extend ~plugin:\"%s\" ~name:%a @[<2>{@\n\
      Vernacextend.arg_parsing =@ %a;@\n\
      Vernacextend.arg_printer = fun env sigma ->@ %a;@\n}@]"
      (force_is_plugin ~what:"VERNAC ARGUMENT EXTEND" ())
      print_string name (print_rules counter) (name, arg.vernacargext_rules)
      (print_printer counter) arg.vernacargext_printer
  in
  fprintf fmt "@[<2>let (wit_%s, %s) =@ @[%a@]@]@\nlet _ = (wit_%s, %s)@\n"
    name name pr () name name

end

module ArgumentExt :
sig

val print_ast : line_counter -> Format.formatter -> argument_ext -> unit

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

let print_ast counter fmt arg =
  let name = arg.argext_name in
  let pr_tag fmt t = print_opt fmt print_argtype t in
  let intern fmt () = match arg.argext_glob, arg.argext_type with
  | Some f, (None | Some _) ->
    fprintf fmt "@[Tacentries.ArgInternFun ((fun f ist v -> (ist, f ist v)) (%a))@]" (print_code counter) f
  | None, Some t ->
    fprintf fmt "@[Tacentries.ArgInternWit (%a)@]" print_wit t
  | None, None ->
    fprintf fmt "@[Tacentries.ArgInternFun (fun ist v -> (ist, v))@]"
  in
  let subst fmt () = match arg.argext_subst, arg.argext_type with
  | Some f, (None | Some _) ->
    fprintf fmt "@[Tacentries.ArgSubstFun (%a)@]" (print_code counter) f
  | None, Some t ->
    fprintf fmt "@[Tacentries.ArgSubstWit (%a)@]" print_wit t
  | None, None ->
    fprintf fmt "@[Tacentries.ArgSubstFun (fun s v -> v)@]"
  in
  let interp fmt () = match arg.argext_interp, arg.argext_type with
  | Some (None, f), (None | Some _) ->
    fprintf fmt "@[Tacentries.ArgInterpSimple (%a)@]" (print_code counter) f
  | Some (Some kind, f), (None | Some _) ->
    fatal (Printf.sprintf "Unknown kind %s of interpretation function" kind)
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
    fprintf fmt "Tacentries.argument_extend ~plugin:\"%s\" ~name:%a @[{@\n\
      Tacentries.arg_parsing = %a;@\n\
      Tacentries.arg_tag = @[%a@];@\n\
      Tacentries.arg_intern = @[%a@];@\n\
      Tacentries.arg_subst = @[%a@];@\n\
      Tacentries.arg_interp = @[%a@];@\n\
                 Tacentries.arg_printer = @[((fun env sigma -> %a), (fun env sigma -> %a), (fun env sigma -> %a))@];@\n}@]"
      (force_is_plugin ~what:"ARGUMENT EXTEND" ())
      print_string name
      (VernacArgumentExt.print_rules counter) (name, arg.argext_rules)
      pr_tag arg.argext_type
      intern () subst () interp () (print_code counter) rpr (print_code counter) gpr (print_code counter) tpr
  in
  fprintf fmt "let (wit_%s, %s) = @[%a@]@\nlet _ = (wit_%s, %s)@\n"
    name name pr () name name

end

let declare_plugin fmt name =
  Option.iter (fprintf fmt "let _ = Mltop.add_known_module \"%s\"@\n") name;
  let () = match !plugin_name with
    | None -> plugin_name := Some name
    | Some _ -> fatal "Multiple DECLARE PLUGIN not allowed";
  in
  ()

let pr_ast counter fmt = function
| Code s -> fprintf fmt "%a@\n" (print_code counter) s
| Comment s -> fprintf fmt "%s@\n" s
| DeclarePlugin name -> declare_plugin fmt name
| GramExt gram -> fprintf fmt "%a@\n" (GramExt.print_ast counter) gram
| VernacExt vernac -> fprintf fmt "%a@\n" (VernacExt.print_ast counter) vernac
| VernacArgumentExt arg -> fprintf fmt "%a@\n" (VernacArgumentExt.print_ast counter) arg
| TacticExt tac -> fprintf fmt "%a@\n" (TacticExt.print_ast counter) tac
| ArgumentExt arg -> fprintf fmt "%a@\n" (ArgumentExt.print_ast counter) arg

let help () =
  Format.eprintf "Usage: coqpp file.mlg@\n%!";
  exit 1

let parse () =
  let () =
    if Array.length Sys.argv <> 2
    then help ()
  in
  match Sys.argv.(1) with
  | "-help" | "--help" -> help ()
  | file -> file

let output_name file =
  try
    Filename.chop_extension file ^ ".ml"
  with
  | Invalid_argument _ ->
    fatal "Input file must have an extension for coqpp [input.ext -> input.ml]"

let () =
  let file = parse () in
  let output = output_name file in
  let ast = parse_file file in
  let chan = open_out output in
  let () = file_name := Filename.basename file in
  let fmt, counter = of_out_channel_with_line_count output chan in
  let iter ast = Format.fprintf fmt "@[%a@]%!" (pr_ast counter) ast in
  let () = List.iter iter ast in
  let () = close_out chan in
  exit 0
