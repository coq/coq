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
open Ast
open Topconstr
open Rawterm
open Tacexpr
open Vernacexpr
open Ast

ifdef Quotify then
open Qast
else
open Pcoq

open Prim
open Tactic

ifdef Quotify then
open Q

type let_clause_kind =
  | LETTOPCLAUSE of Names.identifier * constr_expr
  | LETCLAUSE of
      (Names.identifier Util.located * (constr_expr, Libnames.reference) may_eval option * raw_tactic_arg)

ifdef Quotify then
module Prelude = struct
let fail_default_value = Qast.Int "0"

let out_letin_clause loc = function
  | Qast.Node ("LETTOPCLAUSE", _) -> user_err_loc (loc, "", (str "Syntax Error"))
  | Qast.Node ("LETCLAUSE", [id;c;d]) ->
      Qast.Tuple [id;c;d]
  | _ -> anomaly "out_letin_clause"

let make_letin_clause _ = function
  | Qast.List l -> Qast.List (List.map (out_letin_clause dummy_loc) l)
  | _ -> anomaly "make_letin_clause"
end
else
module Prelude = struct
let fail_default_value = 0

let out_letin_clause loc = function
  | LETTOPCLAUSE _ -> user_err_loc (loc, "", (str "Syntax Error"))
  | LETCLAUSE (id,c,d) -> (id,c,d)

let make_letin_clause loc = List.map (out_letin_clause loc)
end

let arg_of_expr = function
    TacArg a -> a
  | e -> Tacexp (e:raw_tactic_expr)
    
open Prelude

(* Tactics grammar rules *)

let tactic_expr = Gram.Entry.create "tactic:tactic_expr"

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
      | IDENT "do"; n = natural; ta = tactic_expr -> TacDo (n,ta)
      | IDENT "repeat"; ta = tactic_expr -> TacRepeat ta
      | IDENT "progress"; ta = tactic_expr -> TacProgress ta
      | IDENT "info"; tc = tactic_expr -> TacInfo tc ]
    | "2" RIGHTA
      [ ta0 = tactic_expr; "||"; ta1 = tactic_expr -> TacOrelse (ta0,ta1) ]
    | "1" RIGHTA
      [ "fun"; it = LIST1 input_fun ; "=>"; body = tactic_expr ->
          TacFun (it,body)
      | "let"; IDENT "rec"; rcl = LIST1 rec_clause SEP "with"; "in";
          body = tactic_expr -> TacLetRecIn (rcl,body)
      | "let"; llc = LIST1 let_clause SEP "with"; "in";
          u = tactic_expr -> TacLetIn (make_letin_clause loc llc,u)
      | "match"; IDENT "context"; "with"; mrl = match_context_list; "end" ->
          TacMatchContext (false,mrl)
      | "match"; IDENT "reverse"; IDENT "context"; "with";
        mrl = match_context_list; "end" ->
          TacMatchContext (true,mrl)
      |	"match"; c = constrarg; "with"; mrl = match_list; "end" ->
          TacMatch (c,mrl)
(*To do: put Abstract in Refiner*)
      | IDENT "abstract"; tc = tactic_expr -> TacAbstract (tc,None)
      | IDENT "abstract"; tc = tactic_expr; "using";  s = base_ident ->
          TacAbstract (tc,Some s)
(*End of To do*)
      | IDENT "first" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacFirst l
      | IDENT "solve" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacSolve l
      | IDENT "idtac" -> TacId
      | IDENT "fail"; n = [ n = natural -> n | -> fail_default_value ];
	  s = [ s = STRING -> s | -> ""] -> TacFail (n,s)
      | st = simple_tactic -> TacAtom (loc,st)
      | IDENT "eval"; rtc = red_expr; "in"; c = Constr.lconstr ->
	  TacArg(ConstrMayEval (ConstrEval (rtc,c)))
      | IDENT "inst"; id = identref; "["; c = Constr.lconstr; "]" ->
	  TacArg(ConstrMayEval (ConstrContext (id,c)))
      | IDENT "check"; c = Constr.lconstr ->
	  TacArg(ConstrMayEval (ConstrTypeOf c))
      | IDENT "fresh"; s = OPT STRING ->
	  TacArg (TacFreshId s)
      | "'"; c = Constr.constr -> TacArg(ConstrMayEval(ConstrTerm c))
      | r = reference; la = LIST1 tactic_arg ->
          TacArg(TacCall (loc,r,la))
      | r = reference -> TacArg (Reference r) ]
    | "0"
      [ "("; a = tactic_expr; ")" -> a
      | a = tactic_atom -> TacArg a ] ]
  ;
  (* Tactic arguments *)
  tactic_arg:
    [ [ "'"; a = tactic_expr LEVEL "0" -> arg_of_expr a
      | a = tactic_atom -> a
      | c = Constr.constr -> ConstrMayEval (ConstrTerm c) ] ]
  ;
  tactic_atom:
    [ [ id = METAIDENT -> MetaIdArg (loc,id)
      | r = reference -> Reference r
      | "()" -> TacVoid ] ]
  ;
  input_fun:
    [ [ IDENT "_" -> None 
      | l = base_ident -> Some l ] ]
  ;
  let_clause:
    [ [ id = identref; ":="; te = tactic_expr ->
          LETCLAUSE (id, None, arg_of_expr te)
      | (_,id) = identref; ":"; c = Constr.constr; ":="; IDENT "proof" ->
          LETTOPCLAUSE (id, c)
      | id = identref; ":"; c = constrarg; ":="; te = tactic_expr ->
          LETCLAUSE (id, Some c, arg_of_expr te)
      |	(_,id) = identref; ":"; c = Constr.lconstr ->
	  LETTOPCLAUSE (id, c) ] ]
  ;
  rec_clause:
    [ [ name = identref; it = LIST1 input_fun; ":="; body = tactic_expr ->
          (name,(it,body)) ] ]
  ;
  match_pattern:
    [ [ id = Constr.constr_pattern; "["; pc = Constr.constr_pattern; "]" ->
        let s = coerce_to_id id in Subterm (Some s, pc)
      | "["; pc = Constr.constr_pattern; "]" -> Subterm (None,pc)
      | pc = Constr.constr_pattern -> Term pc ] ]
  ;
  match_hyps:
    [ [ na = name; ":"; mp =  match_pattern -> Hyp (na, mp) ] ]
  ;
  match_context_rule:
    [ [ "["; largs = LIST0 match_hyps SEP ","; "|-"; mp = match_pattern; "]";
        "=>"; te = tactic_expr -> Pat (largs, mp, te)
      | IDENT "_"; "=>"; te = tactic_expr -> All te ] ]
  ;
  match_context_list:
    [ [ mrl = LIST1 match_context_rule SEP "|" -> mrl
      | "|"; mrl = LIST1 match_context_rule SEP "|" -> mrl ] ]
  ;
  match_rule:
    [ [ "["; mp = match_pattern; "]"; "=>"; te = tactic_expr -> Pat ([],mp,te)
      | IDENT "_"; "=>"; te = tactic_expr -> All te ] ]
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
