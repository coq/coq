(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)


(*i $Id$ i*)

open Util
open Gramext
open Pp
open Ast

type nonterm_prod =
  | ProdList0 of nonterm_prod
  | ProdList1 of nonterm_prod
  | ProdOpt of nonterm_prod
  | ProdPrimitive of (string * string)

type prod_item =
  | Term of Token.pattern
  | NonTerm of nonterm_prod * (string * ast_action_type) option

type grammar_rule = {
  gr_name : string; 
  gr_production : prod_item list; 
  gr_action : act }

type grammar_entry = { 
  ge_name : string;
  ge_type : ast_action_type;
  gl_assoc : Gramext.g_assoc option;
  gl_rules : grammar_rule list }

type grammar_command = { 
  gc_univ : string; 
  gc_entries : grammar_entry list }

type grammar_associativity = Gramext.g_assoc option
type nonterm =
  | NtShort of string
  | NtQual of string * string
type grammar_production =
  | VTerm of string
  | VNonTerm of loc * nonterm * string option
type raw_grammar_rule = string * grammar_production list * grammar_action
type raw_grammar_entry = 
  string * ast_action_type * grammar_associativity * raw_grammar_rule list

let subst_grammar_rule subst gr =
  { gr with gr_action = subst_act subst gr.gr_action }

let subst_grammar_entry subst ge =
  { ge with gl_rules = List.map (subst_grammar_rule subst) ge.gl_rules }

let subst_grammar_command subst gc =
  { gc with gc_entries = List.map (subst_grammar_entry subst) gc.gc_entries }


(*s Terminal symbols interpretation *)

let is_ident_not_keyword s =
  match s.[0] with
    | 'a'..'z' | 'A'..'Z' | '_' -> not (Lexer.is_keyword s)
    | _ -> false

let is_number s =
  match s.[0] with
    | '0'..'9' -> true
    | _ -> false

let strip s =
  let len =
    let rec loop i len =
      if i = String.length s then len
      else if s.[i] == ' ' then loop (i + 1) len
      else loop (i + 1) (len + 1)
    in
    loop 0 0
  in
  if len == String.length s then s
  else
    let s' = String.create len in
    let rec loop i i' =
      if i == String.length s then s'
      else if s.[i] == ' ' then loop (i + 1) i'
      else begin s'.[i'] <- s.[i]; loop (i + 1) (i' + 1) end
    in
    loop 0 0

let terminal s =
  let s = strip s in
  if s = "" then failwith "empty token";
  if is_ident_not_keyword s then ("IDENT", s)
  else if is_number s then ("INT", s)
  else ("", s)

(*s Non-terminal symbols interpretation *)

(* For compatibility *)
let warn nt nt' =
  warning ("'"^nt^"' grammar entry is obsolete; use name '"^nt'^"' instead");
  nt'

let rename_command nt =
  if String.length nt >= 7 & String.sub nt 0 7 = "command"
  then warn nt ("constr"^(String.sub nt 7 (String.length nt - 7)))
  else if nt = "lcommand" then warn nt "lconstr"
  else if nt = "lassoc_command4" then warn nt "lassoc_constr4"
  else nt

let qualified_nterm current_univ = function
  | NtQual (univ, en) -> (rename_command univ, rename_command en)
  | NtShort en -> (current_univ, rename_command en)

let nterm loc (get_entry_type,univ) nont =
  let nt = qualified_nterm univ nont in
  try 
    let et = match get_entry_type nt with
      | PureAstType -> ETast
      | GenAstType Genarg.ConstrArgType -> ETast
      | AstListType -> ETastl
      | _ -> error "Cannot arbitrarily extend non ast entries"
    in (nt,et)
  with Not_found -> 
    let (s,n) = nt in
    user_err_loc(loc,"Externd.nterm",str("unknown grammar entry: "^s^":"^n))

let prod_item univ env = function
  | VTerm s -> env, Term (terminal s)
  | VNonTerm (loc, nt, Some p) ->
      let (nont, etyp) = nterm loc univ nt in
      ((p, etyp) :: env, NonTerm (ProdPrimitive nont, Some (p,etyp)))
  | VNonTerm (loc, nt, None) ->
      let (nont, etyp) = nterm loc univ nt in 
      env, NonTerm (ProdPrimitive nont, None)

let rec prod_item_list univ penv pil =
  match pil with
    | [] -> [], penv
    | pi :: pitl ->
	let (env, pic) = prod_item univ penv pi in
	let (pictl, act_env) = prod_item_list univ env pitl in
        (pic :: pictl, act_env)

let gram_rule univ etyp (name,pil,act) =
  let (pilc, act_env) = prod_item_list univ [] pil in
  let a = Ast.to_act_check_vars act_env etyp act in
  { gr_name = name; gr_production = pilc; gr_action = a }

let gram_entry univ (nt, etyp, ass, rl) =
  { ge_name = rename_command nt;
    ge_type = etyp;
    gl_assoc = ass;
    gl_rules = List.map (gram_rule univ etyp) rl }

let interp_grammar_command univ ge entryl =
  let univ = rename_command univ in
  { gc_univ = univ;
    gc_entries = List.map (gram_entry (ge,univ)) entryl }

(*s Pretty-print. *)

(* Dealing with precedences *)

type precedence = int * int * int

type parenRelation = L | E | Any | Prec of precedence

type ppbox =
  | PpHB of int
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int
  | PpTB

(* unparsing objects *)

type 'pat unparsing_hunk = 
  | PH of 'pat * string option * parenRelation
  | RO of string
  | UNP_BOX of ppbox * 'pat unparsing_hunk list
  | UNP_BRK of int * int
  | UNP_TBRK of int * int
  | UNP_TAB
  | UNP_FNL
  | UNP_SYMBOLIC of string * string * 'pat unparsing_hunk

let rec subst_hunk subst_pat subst hunk = match hunk with
  | PH (pat,so,pr) ->
      let pat' = subst_pat subst pat in
	if pat'==pat then hunk else
	  PH (pat',so,pr)
  | RO _ -> hunk
  | UNP_BOX (ppbox, hunkl) ->
      let hunkl' = list_smartmap (subst_hunk subst_pat subst) hunkl in
	if hunkl' == hunkl then hunk else
	  UNP_BOX (ppbox, hunkl')
  | UNP_BRK _
  | UNP_TBRK _
  | UNP_TAB
  | UNP_FNL -> hunk
  | UNP_SYMBOLIC (s1, s2, pat) ->
      let pat' = subst_hunk subst_pat subst pat in
	if pat' == pat then hunk else
	  UNP_SYMBOLIC (s1, s2, pat')

(* Checks if the precedence of the parent printer (None means the
   highest precedence), and the child's one, follow the given
   relation. *)

type tolerability = (string * precedence) * parenRelation

let compare_prec (a1,b1,c1) (a2,b2,c2) =
  match (a1=a2),(b1=b2),(c1=c2) with
    | true,true,true -> 0
    | true,true,false -> c1-c2
    | true,false,_ -> b1-b2
    | false,_,_ -> a1-a2

let tolerable_prec oparent_prec_reln (_,child_prec) =
  match oparent_prec_reln with
    | Some ((_,pprec), L) -> (compare_prec child_prec pprec) < 0
    | Some ((_,pprec), E) -> (compare_prec child_prec pprec) <= 0
    | Some (_, Prec level) -> (compare_prec child_prec level) <= 0
    | _ -> true

let ppcmd_of_box = function
  | PpHB n -> h n
  | PpHOVB n -> hov n
  | PpHVB n -> hv n
  | PpVB n -> v n
  | PpTB   -> t

type 'pat syntax_entry = {
  syn_id : string;
  syn_prec: precedence;
  syn_astpat : 'pat;
  syn_hunks : 'pat unparsing_hunk list }

let subst_syntax_entry subst_pat subst sentry = 
  let syn_astpat' = subst_pat subst sentry.syn_astpat in
  let syn_hunks' = list_smartmap (subst_hunk subst_pat subst) sentry.syn_hunks 
  in
    if syn_astpat' == sentry.syn_astpat 
      && syn_hunks' == sentry.syn_hunks then sentry 
    else
      { sentry with
	  syn_astpat = syn_astpat' ;
	  syn_hunks = syn_hunks' ;
      }
      
type 'pat syntax_command = { 
  sc_univ : string; 
  sc_entries : 'pat syntax_entry list }

let subst_syntax_command subst_pat subst scomm = 
  let sc_entries' = 
    list_smartmap (subst_syntax_entry subst_pat subst) scomm.sc_entries 
  in
    if sc_entries' == scomm.sc_entries then scomm else
      { scomm with sc_entries = sc_entries' }
      
type syntax_rule = string * Coqast.t * Coqast.t unparsing_hunk list
type syntax_entry_ast = precedence * syntax_rule list

let rec interp_unparsing env = function
  | PH (ast,ext,pr) -> PH (Ast.val_of_ast env ast,ext,pr)
  | UNP_BOX (b,ul) -> UNP_BOX (b,List.map (interp_unparsing env) ul)
  | UNP_BRK _ | RO _ | UNP_TBRK _ | UNP_TAB | UNP_FNL as x -> x
  | UNP_SYMBOLIC (x,y,u) -> UNP_SYMBOLIC (x,y,interp_unparsing env u)

let rule_of_ast univ prec (s,spat,unp) =
  let (astpat,meta_env) = Ast.to_pat [] spat in
  let hunks = List.map (interp_unparsing meta_env) unp in
  { syn_id = s;
    syn_prec = prec;
    syn_astpat = astpat;
    syn_hunks = hunks }

let level_of_ast univ (prec,rl) = List.map (rule_of_ast univ prec) rl

let interp_syntax_entry univ sel =
  { sc_univ = univ;
    sc_entries = List.flatten (List.map (level_of_ast univ) sel)}


