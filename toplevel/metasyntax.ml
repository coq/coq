
(* $Id$ *)

open Pp
open Util
open Coqast
open Ast
open Pcoq
open Extend
open Esyntax
open Libobject
open Library
open Summary

(*************************
 **** PRETTY-PRINTING ****
 *************************)

(* Done here to get parsing/g_*.ml4 non dependent from kernel *)
let constr_parser_with_glob = map_entry Astterm.globalize_constr Constr.constr
let tactic_parser_with_glob = map_entry Astterm.globalize_ast Tactic.tactic
let vernac_parser_with_glob = map_entry Astterm.globalize_ast Vernac.vernac

(* This updates default parsers for Grammar actions and Syntax *)
(* patterns by inserting globalization *)
let _ = update_constr_parser constr_parser_with_glob
let _ = update_tactic_parser tactic_parser_with_glob
let _ = update_vernac_parser vernac_parser_with_glob

(* This installs default quotations parsers to escape the ast parser *)
(* "constr" is used by default in quotations found in the ast parser *) 
let _ = define_quotation true "constr" constr_parser_with_glob
let _ = define_quotation false "tactic" tactic_parser_with_glob
let _ = define_quotation false "vernac" vernac_parser_with_glob

(* Pretty-printer state summary *)
let _ = 
  declare_summary "syntax"
    { freeze_function = Esyntax.freeze;
      unfreeze_function = Esyntax.unfreeze;
      init_function = Esyntax.init }

(* Pretty-printing objects = syntax_entry *)
let cache_syntax (_,ppobj) = Esyntax.add_ppobject ppobj

let (inPPSyntax,outPPSyntax) =
  declare_object
    ("PPSYNTAX",
     { load_function = (fun _ -> ());
       open_function = cache_syntax;
       cache_function = cache_syntax;
       export_function = (fun x -> Some x) })

(* Syntax extension functions (registered in the environnement) *)

(* Checking the pretty-printing rules against free meta-variables.
 * Note that object are checked before they are added in the environment.
 * Syntax objects in compiled modules are not re-checked. *)

let add_syntax_obj whatfor sel =
  Lib.add_anonymous_leaf (inPPSyntax (interp_syntax_entry whatfor sel))


(************************
 ******* GRAMMAR ********
 ************************)

let _ = 
  declare_summary "GRAMMAR_LEXER"
    { freeze_function = Egrammar.freeze;
      unfreeze_function = Egrammar.unfreeze;
      init_function = Egrammar.init}

(* Tokens *)

let cache_token (_,s) = Pcoq.lexer.Token.using ("", s)

let (inToken, outToken) =
  declare_object
    ("TOKEN",
     { load_function = (fun _ -> ());
       open_function = cache_token;
       cache_function = cache_token;
       export_function = (fun x -> Some x)})

let add_token_obj s = Lib.add_anonymous_leaf (inToken s)

(* Grammar rules *)
let cache_grammar (_,a) = Egrammar.extend_grammar a

let (inGrammar, outGrammar) =
  declare_object
    ("GRAMMAR",
     { load_function = (fun _ -> ());
       open_function = cache_grammar;
       cache_function = cache_grammar;
       export_function = (fun x -> Some x)})

let add_grammar_obj univ al =
   Lib.add_anonymous_leaf (inGrammar (Extend.interp_grammar_command univ al))

(* printing grammar entries *)
let print_grammar univ entry =
  let u = get_univ univ in
  let te = get_entry u entry in
  match te with
    | Ast e -> Gram.Entry.print e
    | ListAst e -> Gram.Entry.print e

(* Infix, distfix *)

let split str =
  let rec loop beg i =
    if i < String.length str then
      if str.[i] == ' ' then
        if beg == i then 
	  loop (succ beg) (succ i)
        else 
	  String.sub str beg (i - beg) :: loop (succ i) (succ i)
      else 
	loop beg (succ i)
    else if beg == i then 
      []
    else 
      [String.sub str beg (i - beg)]
  in
  loop 0 0


(* An infix or a distfix is a pair of a grammar rule and a pretty-printing rule
 *)
let cache_infix (_,(gr,se)) =
  Egrammar.extend_grammar gr;
  Esyntax.add_ppobject {sc_univ="constr";sc_entries=se}

let (inInfix, outInfix) =
  declare_object
    ("INFIX",
     { load_function = (fun _ -> ());
       open_function = cache_infix;
       cache_function = cache_infix;
       export_function = (fun x -> Some x)})

let prec_assoc = function
  | Some(Gramext.RightA) -> (":L",":E")
  | Some(Gramext.LeftA) -> (":E",":L")
  | Some(Gramext.NonA) -> (":L",":L")
  | None -> (":E",":L")  (* LEFTA by default *)

let constr_tab =
  [| "constr0"; "constr1"; "constr2"; "constr3"; "lassoc_constr4";
     "constr5"; "constr6"; "constr7"; "constr8"; "constr9"; "constr10" |]
  
let constr_rule n p = if p = ":E" then constr_tab.(n) else constr_tab.(n-1)

let nonterm_meta nt var = NonTerm(NtShort nt, ETast, Some var)

(* infix_syntax_entry : int -> string -> string -> grammar_entry
 *    takes precedence, infix op and prefix op and returns
 *    the corresponding Syntax entry *)

let infix_syntax_entry assoc n inf prefname astpref =
  let (lp,rp) =  match assoc with 
    | Some(Gramext.RightA) -> (Extend.L,Extend.E)
    | Some(Gramext.LeftA) -> (Extend.E,Extend.L)
    | Some(Gramext.NonA) -> (Extend.L,Extend.L)
    | None -> (Extend.E,Extend.L)  (* LEFTA by default *)
  in
  [{Extend.syn_id = prefname;
    Extend.syn_prec = n,0,0;
    Extend.syn_astpat = 
      Pnode
    	("APPLIST",
	 Pcons
	   (Pquote astpref,
	    Pcons (Pmeta ("$e1", Tany), Pcons (Pmeta ("$e2", Tany), Pnil))));
    Extend.syn_hunks =
      [Extend.UNP_BOX
	 (Extend.PpHOVB 1,
	  [Extend.PH (Pmeta ("$e1", Tany), None, lp);
	   Extend.UNP_BRK (0, 1); Extend.RO inf;
	   Extend.PH (Pmeta ("$e2", Tany), None, rp)])]}]

(* infix_gram_entry : int -> string -> string -> grammar_entry
 *    takes precedence, infix op and prefix op and returns
 *    the corresponding Grammar entry *)

let gram_infix assoc n infl prefname astpref =
  let (lp,rp) = prec_assoc assoc in
  let action =
    Aast(Pnode("APPLIST",
               Pcons(Pquote astpref,
                     Pcons(Pmeta("$a",Tany),
                           Pcons(Pmeta("$b",Tany),Pnil)))))
  in
  { gc_univ = "constr";
    gc_entries =
      [ { ge_name = constr_rule n ":E";
          ge_type = ETast;
          gl_assoc = None;
          gl_rules =
            [ { gr_name = prefname;
                gr_production =
                  (nonterm_meta (constr_rule n lp) "$a")
                  ::(List.map (fun s -> Term("", s)) infl)
                  @[nonterm_meta (constr_rule n rp) "$b"];
                gr_action = action} ]
        }
      ]
  }

let add_infix assoc n inf pr =
  (* check the precedence *)
  if n<1 or n>10 then
    errorlabstrm "Metasyntax.infix_grammar_entry"
      [< 'sTR"Precedence must be between 1 and 10." >];
  if (assoc<>None) & (n<6 or n>9) then
    errorlabstrm "Vernacentries.infix_grammar_entry"
      [< 'sTR"Associativity Precedence must be 6,7,8 or 9." >];
  (* check the grammar entry *)
  let prefast = Astterm.ast_of_qualid dummy_loc pr in
  let prefname = (Names.string_of_qualid pr)^"_infix" in
  let gram_rule = gram_infix assoc n (split inf) prefname prefast in
  (* check the syntax entry *)
  let syntax_rule = infix_syntax_entry assoc n inf prefname prefast in
  Lib.add_anonymous_leaf (inInfix(gram_rule,syntax_rule))

(* Distfix *)
(* Distfix LEFTA 7 "/ _ / _ /" app.*)

let rec make_symbols c_first c_next c_last new_var = function
  | [] -> []
  | ["_"] -> [nonterm_meta c_last ("$e"^(string_of_int new_var))]
  | ("_"::sl) ->
      let symb = nonterm_meta c_first ("$e"^(string_of_int new_var)) in
      symb :: make_symbols c_next c_next c_last (new_var+1) sl
  | s :: sl ->
      let symb = Term("", s) in
      symb :: make_symbols c_next c_next c_last new_var sl

let collect_metas sl =
  List.fold_right
    (fun it metatl ->
       match it with
         | NonTerm(_,_,Some m) -> Pcons(Pmeta(m,Tany),metatl)
         | _ -> metatl)
    sl Pnil

let distfix assoc n sl fname astf  =
  let (lp,rp) = prec_assoc assoc in
  let symbols =
    make_symbols (constr_rule n lp) constr_tab.(8) (constr_rule n rp) 0 sl in
  let action =
    Aast(Pnode("APPLIST",Pcons(Pquote astf, collect_metas symbols)))
  in
  { gc_univ = "constr";
    gc_entries =
      [ { ge_name = constr_rule n ":E";
          ge_type = ETast;
          gl_assoc = None;
          gl_rules =
            [ { gr_name = fname;
                gr_production = symbols;
                gr_action = action} ]
        }
      ]
  }

let add_distfix a n df f =
  let fname = (Names.string_of_qualid f)^"_distfix" in
  let astf = Astterm.ast_of_qualid dummy_loc f in
  Lib.add_anonymous_leaf (inInfix(distfix a n (split df) fname astf, []))

