(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Pp
open Util
open Coqast
open Ast
open Extend
open Esyntax
open Libobject
open Library
open Summary
open Astterm
open Vernacexpr
open Pcoq

(*************************
 **** PRETTY-PRINTING ****
 *************************)

let globalize_typed_ast t =
  let sign = Global.named_context () in
  match t with
  | Ast.PureAstNode t -> Ast.PureAstNode (globalize_constr t)
  | _ -> (* TODO *) t

(* This updates default parsers for Grammar actions and Syntax *)
(* patterns by inserting globalization *)
(* Done here to get parsing/g_*.ml4 non dependent from kernel *)
let _ = Pcoq.set_globalizer globalize_typed_ast

(* This installs default quotations parsers to escape the ast parser *)
(* "constr" is used by default in quotations found in the ast parser *) 
let constr_parser_with_glob = Pcoq.map_entry Astterm.globalize_constr Constr.constr
let tactic_parser_with_glob = (*map_entry Astterm.globalize_tactic*) Tactic.tactic
let vernac_parser_with_glob = (*map_entry Astterm.globalize_vernac*) Vernac_.vernac

let _ = define_quotation true "constr" constr_parser_with_glob
(*
let _ = define_quotation false "tactic" tactic_parser_with_glob
let _ = define_quotation false "vernac" vernac_parser_with_glob
*)

(* Pretty-printer state summary *)
let _ = 
  declare_summary "syntax"
    { freeze_function = Esyntax.freeze;
      unfreeze_function = Esyntax.unfreeze;
      init_function = Esyntax.init;
      survive_section = false }

(* Pretty-printing objects = syntax_entry *)
let cache_syntax (_,ppobj) = Esyntax.add_ppobject ppobj

let (inPPSyntax,outPPSyntax) =
  declare_object {(default_object "PPSYNTAX") with
       open_function = (fun i o -> if i=1 then cache_syntax o);
       cache_function = cache_syntax;
       export_function = (fun x -> Some x) }

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
      init_function = Egrammar.init;
      survive_section = false }

(* Tokens *)

let cache_token (_,s) = Pcoq.lexer.Token.using ("", s)

let (inToken, outToken) =
  declare_object {(default_object "TOKEN") with
       open_function = (fun i o -> if i=1 then cache_token o);
       cache_function = cache_token;
       export_function = (fun x -> Some x)}

let add_token_obj s = Lib.add_anonymous_leaf (inToken s)

(* Grammar rules *)
let cache_grammar (_,a) = Egrammar.extend_grammar a

let (inGrammar, outGrammar) =
  declare_object {(default_object "GRAMMAR") with
       open_function = (fun i o -> if i=1 then cache_grammar o);
       cache_function = cache_grammar;
       export_function = (fun x -> Some x)}

let gram_define_entry (u,_ as univ) ((ntl,nt),et,assoc,rl) =
  let etyp = match et with None -> entry_type_from_name u | Some e -> e in
  create_entry_if_new univ nt etyp;
  let etyp = match etyp with 
    | AstListType -> ETastl
    | GenAstType Genarg.ConstrArgType -> ETast
    | PureAstType -> ETast
    | _ -> error "Cannot arbitrarily extend non ast entries" in
  (nt, etyp, assoc, rl)

let add_grammar_obj univ l =
  let u = create_univ_if_new univ in
  let entryl = List.map (gram_define_entry u) l in
  let g = interp_grammar_command univ get_entry_type entryl in
  Lib.add_anonymous_leaf (inGrammar (Egrammar.AstGrammar g))

let add_tactic_grammar g = 
  Lib.add_anonymous_leaf (inGrammar (Egrammar.TacticGrammar g))

(* printing grammar entries *)
let print_grammar univ entry =
  let u = get_univ univ in
  let te = get_entry u entry in
  Gram.Entry.print (object_of_typed_entry te)

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
  declare_object {(default_object "INFIX") with
       open_function = (fun i o -> if i=1 then cache_infix o);
       cache_function = cache_infix;
       export_function = (fun x -> Some x)}

(* Build the syntax and grammar rules *)

type symbol =
  | Terminal of string
  | NonTerminal of (int * parenRelation) * string

let prec_assoc = function
  | Some(Gramext.RightA) -> (L,E)
  | Some(Gramext.LeftA) -> (E,L)
  | Some(Gramext.NonA) -> (L,L)
  | None -> (E,L)  (* LEFTA by default *)

let constr_tab =
  [| "constr0"; "constr1"; "constr2"; "constr3"; "lassoc_constr4";
     "constr5"; "constr6"; "constr7"; "constr8"; "constr9"; "constr10" |]
  
let constr_rule (n,p) = if p = E then constr_tab.(n) else constr_tab.(n-1)

let nonterm_meta nt var =
  NonTerm(ProdPrimitive ("constr",nt), Some (var,ETast))

let meta_pattern m = Pmeta(m,Tany)

let collect_metas sl =
  List.fold_right
    (fun it metatl -> match it with
      | NonTerminal (_,m) -> Pcons(meta_pattern m, metatl)
      | _ -> metatl)
    sl Pnil

let make_pattern astf symbols =
  Pnode("APPLIST",Pcons(Pquote astf, collect_metas symbols))

let make_hunks symbols =
  List.fold_right
    (fun it l -> match it with
      | NonTerminal ((_,lp),m) -> PH (meta_pattern m, None, lp) :: l
      | Terminal s ->
	  let n,s =
	    if is_letter (s.[String.length s -1]) or is_letter (s.[0])
	    then 1,s^" " else 0,s
	  in
	  UNP_BRK (n, 1) :: RO s :: l)
    symbols []

let make_production =
  List.map (function
    | NonTerminal (lp,m) -> nonterm_meta (constr_rule lp) m
    | Terminal s -> Term ("",s))

let make_syntax_rule n prefname symbols astpref =
  [{syn_id = prefname;
    syn_prec = n,0,0;
    syn_astpat = make_pattern astpref symbols;
    syn_hunks = [UNP_BOX (PpHOVB 1, make_hunks symbols)]}]

let make_infix_syntax_rule n prefname symbols astpref ref =
  let hunk = match symbols with
    | [NonTerminal ((_,lp),e1);Terminal s;NonTerminal ((_,rp),e2)] ->
	UNP_INFIX (ref,e1,e2,(lp,rp))
    | _ -> error "Don't know to handle this infix rule" in
  [{syn_id = prefname;
    syn_prec = n,0,0;
    syn_astpat = make_pattern astpref symbols;
    syn_hunks = [hunk]}]
    

let make_grammar_rule n fname symbols astpref =
  let prod = make_production symbols in
  let action = Act (PureAstPat (make_pattern astpref symbols)) in
  Egrammar.AstGrammar
  { gc_univ = "constr";
    gc_entries =
      [ { ge_name = constr_rule (n, E);
          ge_type = ETast;
          gl_assoc = None;
          gl_rules =
            [ { gr_name = fname;
                gr_production = prod;
                gr_action = action} ]
        }
      ]
  }

let make_infix_symbols assoc n sl =
  let (lp,rp) = prec_assoc assoc in
  NonTerminal ((n,lp),"$a")::(List.map (fun s -> Terminal s) sl)
  @[NonTerminal ((n,rp),"$b")]

let subst_infix2 (_, subst, (ref,inf as node)) = 
  let ref' = Libnames.subst_ext subst ref in
    if ref' == ref then node else
      (ref', inf)

let cache_infix2 (_,(ref,inf)) =
  let sp = match ref with
  | Libnames.TrueGlobal r -> Nametab.sp_of_global None r
  | Libnames.SyntacticDef kn -> Nametab.sp_of_syntactic_definition kn in
  declare_infix_symbol sp inf

let (inInfix2, outInfix2) =
  declare_object {(default_object "INFIX2") with
       open_function = (fun i o -> if i=1 then cache_infix2 o);
       cache_function = cache_infix2;
       subst_function = subst_infix2;
       classify_function = (fun (_,o) -> Substitute o);
       export_function = (fun x -> Some x)}

let add_infix assoc n inf (loc,qid) =
  let ref = 
    try
      Nametab.extended_locate qid
    with Not_found ->
      error ("Unknown reference: "^(Libnames.string_of_qualid qid)) in
  let pr = Astterm.ast_of_extended_ref_loc loc ref in
  (* check the precedence *)
  if n<1 or n>10 then
    errorlabstrm "Metasyntax.infix_grammar_entry"
      (str"Precedence must be between 1 and 10.");
(* Pourquoi ??
  if (assoc<>None) & (n<6 or n>9) then
    errorlabstrm "Vernacentries.infix_grammar_entry"
      (str"Associativity Precedence must be 6,7,8 or 9.");
*)
  let prefname = inf^"_infix" in
  let symbols = make_infix_symbols assoc n (split inf) in
  let gram_rule = make_grammar_rule n prefname symbols pr in
  let syntax_rule = make_infix_syntax_rule n prefname symbols pr ref in
  Lib.add_anonymous_leaf (inInfix(gram_rule,syntax_rule));
  Lib.add_anonymous_leaf (inInfix2(ref,inf))

(* Distfix *)
(* Distfix LEFTA 7 "/ _ / _ /" app.*)
(* TODO add boxes information in the expression *)

let create_meta n = "$e"^(string_of_int n)

let rec find_symbols c_first c_next c_last new_var = function
  | []    -> []
  | ["_"] -> [NonTerminal (c_last, create_meta new_var)]
  | ("_"::sl) ->
      let symb = NonTerminal (c_first, create_meta new_var) in
      symb :: find_symbols c_next c_next c_last (new_var+1) sl
  | s :: sl ->
      let symb = Terminal s in
      symb :: find_symbols c_next c_next c_last new_var sl

let add_distfix assoc n df astf =
  let fname = df^"_distfix" in
  let (lp,rp) = prec_assoc assoc in
  let symbols = find_symbols (n,lp) (8,E) (n,rp) 0 (split df) in
  let gram_rule = make_grammar_rule n fname symbols astf in
  let syntax_rule = make_syntax_rule n fname symbols astf in
  Lib.add_anonymous_leaf (inInfix(gram_rule,syntax_rule))

