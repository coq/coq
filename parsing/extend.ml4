(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(*i $Id$ i*)

open Util
open Gramext
open Pp
open Pcoq
open Coqast
open Ast

(* Converting and checking grammar command *)

type nonterm =
  | NtShort of string
  | NtQual of string * string

type prod_item =
  | Term of Token.pattern
  | NonTerm of nonterm * entry_type * string option

type grammar_rule = {
  gr_name : string; 
  gr_production : prod_item list; 
  gr_action : Ast.act }

type grammar_entry = { 
  ge_name : string;
  ge_type : entry_type;
  gl_assoc : g_assoc option;
  gl_rules : grammar_rule list }

type grammar_command = { 
  gc_univ : string; 
  gc_entries : grammar_entry list }

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



let qualified_nterm current_univ ntrm =
  match ntrm with
      NtQual (univ, en) -> (get_univ univ, en)
    | NtShort en -> (current_univ, en)

(* For compatibility *)
let rename_command nt =
  if String.length nt >= 7 & String.sub nt 0 7 = "command"
  then "constr"^(String.sub nt 7 (String.length nt - 7))
  else if nt = "lcommand" then "lconstr"
  else if nt = "lassoc_command4" then "lassoc_constr4"
  else nt

let nterm univ ast =

  let nont =
    match ast with
      | Node (_, "QUAL", [Id (_, u); Id (_, nt)]) ->
	  NtQual (rename_command u, rename_command nt)
      | Id (_, nt) -> NtShort (rename_command nt)
      | _ -> invalid_arg_loc (Ast.loc ast, "Extend.nterm") 
  in
  let (u,n) = qualified_nterm univ nont in
  let e =
    try 
      get_entry u n
    with UserError _ -> 
      user_err_loc(loc ast,"Externd.nterm", str "unknown grammar entry")
  in
  (nont, type_of_entry e)

let prod_item univ env ast =
  match ast with
    | Str (_, s) -> env, Term (terminal s)
    | Node (_, "NT", [nt; Nmeta (locp, p)]) ->
	let (nont, etyp) = nterm univ nt in
	((p, etyp) :: env, NonTerm (nont, etyp, Some p))
    | Node (_, "NT", [nt]) ->
	let (nont, etyp) = nterm univ nt in 
	env, NonTerm (nont, etyp, None)
    | _ -> invalid_arg_loc (Ast.loc ast, "Extend.prod_item")

let rec prod_item_list univ penv pil =
  match pil with
    | [] -> [], penv
    | pi :: pitl ->
	let (env, pic) = prod_item univ penv pi in
	let (pictl, act_env) = prod_item_list univ env pitl in
        (pic :: pictl, act_env)

let gram_rule univ etyp ast =
  match ast with
    | Node (_, "GRAMMARRULE", (Id (_, name) :: act :: pil)) ->
	let (pilc, act_env) = prod_item_list univ [] pil in
	let a = Ast.to_act_check_vars act_env etyp act in
        { gr_name=name; gr_production=pilc; gr_action=a }
    | _ -> invalid_arg_loc (Ast.loc ast, "Extend.gram_rule")

let gram_entry univ (nt, etyp, ass, rl) =
  { ge_name = nt;
    ge_type = etyp;
    gl_assoc = ass;
    gl_rules = List.map (gram_rule univ etyp) rl }

let gram_assoc = function
  | Node (_, "LEFTA", []) -> Some LeftA
  | Node (_, "RIGHTA", []) -> Some RightA
  | Node (_, "NONA", []) -> Some NonA
  | Node (_, "NONE", []) -> None
  | ast -> invalid_arg_loc (Ast.loc ast, "Egrammar.assoc")

let gram_define_entry univ = function
  | Node (_, "GRAMMARENTRY", (Id (ntl, nt) :: et :: ass :: rl)) ->
      let etyp = entry_type et in
      let assoc = gram_assoc ass in

      (* For compatibility *)
      let nt = rename_command nt in

      let _ =
        try 
	  create_entry univ nt etyp
        with Failure s ->
          user_err_loc (ntl,"gram_define_entry", str s )
      in 
      (nt, etyp, assoc, rl)
  | ast -> invalid_arg_loc (Ast.loc ast, "gram_define_entry")

let interp_grammar_command univ astl =

      (* For compatibility *)
      let univ = rename_command univ in

  let u = get_univ univ in
  let entryl = List.map (gram_define_entry u) astl in
  { gc_univ = univ;
    gc_entries = List.map (gram_entry u) entryl }


(* Converting and checking pretty-printing command *)

type precedence = int * int * int
type parenRelation = L | E | Any | Prec of precedence

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

type ppbox =
  | PpHB of int
  | PpHOVB of int
  | PpHVB of int
  | PpVB of int
  | PpTB

type tolerability = (string * precedence) * parenRelation

type unparsing_hunk = 
  | PH of Ast.pat * string option * parenRelation
  | RO of string
  | UNP_BOX of ppbox * unparsing_hunk list
  | UNP_BRK of int * int
  | UNP_TBRK of int * int
  | UNP_TAB
  | UNP_FNL

let ppcmd_of_box = function
  | PpHB n -> h n
  | PpHOVB n -> hov n
  | PpHVB n -> hv n
  | PpVB n -> v n
  | PpTB   -> t

(* Parsing the unparsing specifications *)

let box_of_ast = function
  | Node (_, "PpHB", [Num (_, n)]) -> (PpHB n)
  | Node (_, "PpHOVB", [Num (_, n)]) -> (PpHOVB n)
  | Node (_, "PpHVB", [Num (_, n)]) -> (PpHVB n)
  | Node (_, "PpVB", [Num (_, n)]) -> (PpVB n)
  | Node (_, "PpTB", [])           -> PpTB
  | p -> invalid_arg_loc (Ast.loc p,"Syntaxext.box_of_ast")

let prec_of_ast = function
  | Node(_,"PREC",[Num(_,a1); Num(_,a2); Num(_,a3)]) -> (a1,a2,a3)
  | ast -> invalid_arg_loc (Ast.loc ast,"Syntaxext.prec_of_ast")

let extern_of_ast loc = function
  | [Str(_,ppextern)] -> (ppextern, Any)
  | [Str(_,ppextern);p] ->
      (ppextern, Prec (prec_of_ast p))
  |  _ -> invalid_arg_loc (loc,"Syntaxext.extern_of_ast")

let rec unparsing_hunk_of_ast vars = function
  | Node(_, "PH", [e; Node (loc,"EXTERN", ext_args)]) ->
      let (ppex, rel) = extern_of_ast loc ext_args in
      PH (Ast.val_of_ast vars e, Some ppex, rel)
  | Node(loc, "PH", [e; Node(_,pr, [])]) ->
      let reln =
        (match pr with
           | "L" -> L
           | "E" -> E
           | "Any" -> Any
           | _ -> invalid_arg_loc (loc,"Syntaxext.paren_reln_of_ast")) in
      PH (Ast.val_of_ast vars e, None, reln)
  | Node (_, "RO", [Str(_,s)]) -> RO s
  | Node (_, "UNP_FNL", []) -> UNP_FNL
  | Node (_, "UNP_TAB", []) -> UNP_TAB
  | Node (_, "UNP_BRK", [Num(_, n1); Num(_, n2)]) -> UNP_BRK(n1,n2)
  | Node (_, "UNP_TBRK", [Num(_, n1); Num(_, n2)]) -> UNP_TBRK(n1,n2)
  | Node (_, "UNP_BOX", (box::sub)) ->
      UNP_BOX(box_of_ast box,
              List.map (unparsing_hunk_of_ast vars) sub)
  | h -> invalid_arg_loc (Ast.loc h,"Syntaxext.unparsing_hunk_of_ast")

let unparsing_of_ast vars = function
  | Node(_,"UNPARSING",ll) ->
      List.map (unparsing_hunk_of_ast vars) ll
  | u -> invalid_arg_loc (Ast.loc u,"Syntaxext.unp_of_ast")

type syntax_entry = {
  syn_id : string;
  syn_prec: precedence;
  syn_astpat : Ast.pat;
  syn_hunks : unparsing_hunk list }

type syntax_command = { 
  sc_univ : string; 
  sc_entries : syntax_entry list }

let rule_of_ast whatfor prec = function
  | Node(_,"SYNTAXRULE",[Id(_,s); spat; unp]) ->
      let (astpat,meta_env) = Ast.to_pat [] spat in
      let hunks = unparsing_of_ast meta_env unp in
      { syn_id = s;
	syn_prec = prec;
        syn_astpat = astpat;
        syn_hunks = hunks }
  | ast -> invalid_arg_loc (Ast.loc ast,"Metasyntax.rule_of_ast")

let level_of_ast whatfor = function
  | Node(_,"SYNTAXENTRY",(pr::rl)) ->
      let prec = prec_of_ast pr in
      List.map (rule_of_ast whatfor prec) rl
  | ast -> invalid_arg_loc (Ast.loc ast,"Metasyntax.level_of_ast")

let interp_syntax_entry univ sel =
  { sc_univ = univ;
    sc_entries = List.flatten (List.map (level_of_ast univ) sel)}


