(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Ast
open Topconstr
open Rawterm
open Tacexpr
open Vernacexpr
open Ast
open Pcoq
open Prim
open Tactic

type let_clause_kind =
  | LETTOPCLAUSE of Names.identifier * constr_expr
  | LETCLAUSE of
      (Names.identifier Util.located * raw_tactic_expr option * raw_tactic_arg)

let fail_default_value = Genarg.ArgArg 0

let out_letin_clause loc = function
  | LETTOPCLAUSE _ -> user_err_loc (loc, "", (str "Syntax Error"))
  | LETCLAUSE (id,c,d) -> (id,c,d)

let make_letin_clause loc = List.map (out_letin_clause loc)

let arg_of_expr = function
    TacArg a -> a
  | e -> Tacexp (e:raw_tactic_expr)
    
(* Tactics grammar rules *)

let tactic_expr = Gram.Entry.create "tactic:tactic_expr"

if not !Options.v7 then
GEXTEND Gram
  GLOBAL: tactic Vernac_.command tactic_expr tactic_arg;

  tactic_expr:
    [ "5" LEFTA
      [ ta0 = tactic_expr; ";"; ta1 = tactic_expr -> TacThen (ta0, ta1)
      | ta = tactic_expr; ";"; "["; lta = LIST0 tactic_expr SEP "|"; "]" ->
          TacThens (ta, lta) ]
    | "4"
      [ ]
    | "3" RIGHTA
      [ IDENT "try"; ta = tactic_expr -> TacTry ta
      | IDENT "do"; n = int_or_var; ta = tactic_expr -> TacDo (n,ta)
      | IDENT "repeat"; ta = tactic_expr -> TacRepeat ta
      | IDENT "progress"; ta = tactic_expr -> TacProgress ta
      | IDENT "info"; tc = tactic_expr -> TacInfo tc
(*To do: put Abstract in Refiner*)
      | IDENT "abstract"; tc = NEXT -> TacAbstract (tc,None)
      | IDENT "abstract"; tc = NEXT; "using";  s = base_ident ->
          TacAbstract (tc,Some s) ]
(*End of To do*)
    | "2" RIGHTA
      [ ta0 = tactic_expr; "||"; ta1 = tactic_expr -> TacOrelse (ta0,ta1) ]
    | "1" RIGHTA
      [ "fun"; it = LIST1 input_fun ; "=>"; body = tactic_expr ->
          TacFun (it,body)
      | "let"; IDENT "rec"; rcl = LIST1 rec_clause SEP "with"; "in";
          body = tactic_expr -> TacLetRecIn (rcl,body)
      | "let"; llc = LIST1 let_clause SEP "with"; "in";
          u = tactic_expr -> TacLetIn (make_letin_clause loc llc,u)
      | "match"; IDENT "goal"; "with"; mrl = match_context_list; "end" ->
          TacMatchContext (false,mrl)
      | "match"; IDENT "reverse"; IDENT "goal"; "with";
        mrl = match_context_list; "end" ->
          TacMatchContext (true,mrl)
      |	"match"; c = tactic_expr; "with"; mrl = match_list; "end" ->
          TacMatch (c,mrl)
      | IDENT "first" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacFirst l
      | IDENT "solve" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacSolve l
      | IDENT "idtac"; s = [ s = STRING -> s | -> ""] -> TacId s		
      | IDENT "fail"; n = [ n = int_or_var -> n | -> fail_default_value ];
	  s = [ s = STRING -> s | -> ""] -> TacFail (n,s)
      | st = simple_tactic -> TacAtom (loc,st)
      | a = may_eval_arg -> TacArg(a)
      | IDENT "constr"; ":"; c = Constr.constr ->
          TacArg(ConstrMayEval(ConstrTerm c))
      | IDENT "ipattern"; ":"; ipat = simple_intropattern -> 
	  TacArg(IntroPattern ipat)
      | r = reference; la = LIST1 tactic_arg ->
          TacArg(TacCall (loc,r,la))
      | r = reference -> TacArg (Reference r) ]
    | "0"
      [ "("; a = tactic_expr; ")" -> a
      | a = tactic_atom -> TacArg a ] ]
  ;
  (* Tactic arguments *)
  tactic_arg:
    [ [ IDENT "ltac"; ":"; a = tactic_expr LEVEL "0" -> arg_of_expr a
      | IDENT "ipattern"; ":"; ipat = simple_intropattern -> IntroPattern ipat
      | a = may_eval_arg -> a
      | a = tactic_atom -> a
      | c = Constr.constr -> ConstrMayEval (ConstrTerm c) ] ]
  ;
  may_eval_arg:
    [ [ IDENT "eval"; rtc = red_expr; "in"; c = Constr.constr ->
	  ConstrMayEval (ConstrEval (rtc,c))
      | IDENT "context"; id = identref; "["; c = Constr.lconstr; "]" ->
	  ConstrMayEval (ConstrContext (id,c))
      | IDENT "type"; IDENT "of"; c = Constr.constr ->
	  ConstrMayEval (ConstrTypeOf c)
      | IDENT "fresh"; s = OPT STRING ->
	  TacFreshId s ] ]
  ;
  tactic_atom:
    [ [ id = METAIDENT -> MetaIdArg (loc,id)
      | r = reference -> Reference r
      | "()" -> TacVoid ] ]
  ;
  input_fun:
    [ [ "_" -> None 
      | l = base_ident -> Some l ] ]
  ;
  let_clause:
    [ [ id = identref; ":="; te = tactic_expr ->
          LETCLAUSE (id, None, arg_of_expr te)
      | id = identref; args = LIST1 input_fun; ":="; te = tactic_expr ->
          LETCLAUSE (id, None, arg_of_expr (TacFun(args,te))) ] ]
  ;
  rec_clause:
    [ [ name = identref; it = LIST1 input_fun; ":="; body = tactic_expr ->
          (name,(it,body)) ] ]
  ;
  match_pattern:
    [ [ IDENT "context";  oid = OPT Constr.ident;
          "["; pc = Constr.lconstr_pattern; "]" ->
        Subterm (oid, pc)
      | pc = Constr.lconstr_pattern -> Term pc ] ]
  ;
  match_hyps:
    [ [ na = name; ":"; mp =  match_pattern -> Hyp (na, mp) ] ]
  ;
  match_context_rule:
    [ [ largs = LIST0 match_hyps SEP ","; "|-"; mp = match_pattern;
        "=>"; te = tactic_expr -> Pat (largs, mp, te)
      | "["; largs = LIST0 match_hyps SEP ","; "|-"; mp = match_pattern;
        "]"; "=>"; te = tactic_expr -> Pat (largs, mp, te)
      | "_"; "=>"; te = tactic_expr -> All te ] ]
  ;
  match_context_list:
    [ [ mrl = LIST1 match_context_rule SEP "|" -> mrl
      | "|"; mrl = LIST1 match_context_rule SEP "|" -> mrl ] ]
  ;
  match_rule:
    [ [ mp = match_pattern; "=>"; te = tactic_expr -> Pat ([],mp,te)
      | "_"; "=>"; te = tactic_expr -> All te ] ]
  ;
  match_list:
    [ [ mrl = LIST1 match_rule SEP "|" -> mrl
      | "|"; mrl = LIST1 match_rule SEP "|" -> mrl ] ]
  ;

  (* Definitions for tactics *)
(*
  deftok:
    [ [ IDENT "Meta"
      | IDENT "Tactic" ] ]
  ;
*)
  tacdef_body:
    [ [ name = identref; it=LIST1 input_fun; ":="; body = tactic_expr ->
	  (name, TacFun (it, body))
      | name = identref; ":="; body = tactic_expr ->
	  (name, body) ] ]
  ;
  tactic:
    [ [ tac = tactic_expr -> tac ] ]
  ;
  Vernac_.command: 
    [ [ IDENT "Ltac";
        l = LIST1 tacdef_body SEP "with" ->
          VernacDeclareTacticDefinition (true, l) ] ]
  ;
  END
