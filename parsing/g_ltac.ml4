(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

(* $Id$ *)

open Pp
open Util
open Ast
open Coqast
open Rawterm
open Tacexpr
open Ast

ifdef Quotify then
open Qast
else
open Pcoq

open Tactic

ifdef Quotify then
open Q

type let_clause_kind =
  | LETTOPCLAUSE of Names.identifier * Genarg.constr_ast
  | LETCLAUSE of
      (Names.identifier Util.located * Genarg.constr_ast may_eval option * raw_tactic_arg)

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

open Prelude

(* Tactics grammar rules *)

GEXTEND Gram
  GLOBAL: tactic Vernac_.command tactic_arg;

(*
  GLOBAL: tactic_atom tactic_atom0 tactic_expr input_fun;
*)
  input_fun:
    [ [ l = Prim.ident -> Some l
      | "()" -> None ] ]
  ;
  let_clause:
    [ [ id = Prim.rawident; "="; te = tactic_letarg -> LETCLAUSE (id, None, te)
      | id = Prim.ident; ":"; c = Constr.constr; ":="; "Proof" ->
          LETTOPCLAUSE (id, c)
      | id = Prim.rawident; ":"; c = constrarg; ":="; te = tactic_letarg ->
          LETCLAUSE (id, Some c, te)
      |	id = Prim.ident; ":"; c = Constr.constr ->
	  LETTOPCLAUSE (id, c) ] ]
  ;
  rec_clause:
    [ [ name = Prim.rawident; it = LIST1 input_fun; "->"; body = tactic_expr ->
          (name,(it,body)) ] ]
  ;
  match_pattern:
    [ [ id = Constr.constr_pattern; "["; pc = Constr.constr_pattern; "]" ->
        let s = coerce_to_id id in Subterm (Some s, pc)
      | "["; pc = Constr.constr_pattern; "]" -> Subterm (None,pc)
      | pc = Constr.constr_pattern -> Term pc ] ]
  ;
  match_hyps:
    [ [ id = Prim.rawident; ":"; mp =  match_pattern -> Hyp (id, mp)
      | IDENT "_"; ":"; mp = match_pattern -> NoHypId mp ] ]
  ;
  match_context_rule:
    [ [ "["; largs = LIST0 match_hyps SEP ";"; "|-"; mp = match_pattern; "]";
        "->"; te = tactic_expr -> Pat (largs, mp, te)
      | IDENT "_"; "->"; te = tactic_expr -> All te ] ]
  ;
  match_context_list:
    [ [ mrl = LIST1 match_context_rule SEP "|" -> mrl
      | "|"; mrl = LIST1 match_context_rule SEP "|" -> mrl ] ]
  ;
  match_rule:
    [ [ "["; mp = match_pattern; "]"; "->"; te = tactic_expr -> Pat ([],mp,te)
      | IDENT "_"; "->"; te = tactic_expr -> All te ] ]
  ;
  match_list:
    [ [ mrl = LIST1 match_rule SEP "|" -> mrl
      | "|"; mrl = LIST1 match_rule SEP "|" -> mrl ] ]
  ;
  tactic_expr:
    [ [ ta = tactic_expr5 -> ta ] ]
  ;
  tactic_expr5:
    [ [ ta0 = tactic_expr5; ";"; ta1 = tactic_expr4 -> TacThen (ta0, ta1)
      | ta = tactic_expr5; ";"; "["; lta = LIST0 tactic_expr SEP "|"; "]" ->
          TacThens (ta, lta)
      | y = tactic_expr4 -> y ] ]
  ;
  tactic_expr4:
    [ [ ta = tactic_expr3 -> ta ] ]
  ;
  tactic_expr3:
    [ [ IDENT "Try"; ta = tactic_expr3 -> TacTry ta
      | IDENT "Do"; n = Prim.natural; ta = tactic_expr3 -> TacDo (n,ta)
      | IDENT "Repeat"; ta = tactic_expr3 -> TacRepeat ta
      | IDENT "Progress"; ta = tactic_expr3 -> TacProgress ta
      | IDENT "Info"; tc = tactic_expr3 -> TacInfo tc
      | ta = tactic_expr2 -> ta ] ]
  ;
  tactic_expr2:
    [ [ ta0 = tactic_atom; "Orelse"; ta1 = tactic_expr3 -> TacOrelse (ta0,ta1)
      | ta = tactic_atom -> ta ] ]
  ;
  tactic_atom:
    [ [ IDENT "Fun"; it = LIST1 input_fun ; "->"; body = tactic_expr ->
          TacFun (it,body)
      | IDENT "Rec"; rc = rec_clause ->
	  TacFunRec rc
      |	IDENT "Rec"; rc = rec_clause; IDENT "In"; body = tactic_expr ->
          TacLetRecIn ([rc],body)
      | IDENT "Rec"; rc = rec_clause; "And";
          rcl = LIST1 rec_clause SEP "And"; IDENT "In";
          body = tactic_expr -> TacLetRecIn (rc::rcl,body)
      | IDENT "Let"; llc = LIST1 let_clause SEP "And"; IDENT "In";
          u = tactic_expr -> TacLetIn (make_letin_clause loc llc,u)
(* Let cas LetCut est subsumé par "Assert id := c" tandis que le cas
   StartProof ne fait pas vraiment de sens en tant que sous-expression
   d'une tactique complexe... 
      |	IDENT "Let"; llc = LIST1 let_clause SEP "And" -> 
        (match llc with
	| [LETTOPCLAUSE (id,c)] ->
	    VernacStartProof ((NeverDischarge,false),id,c,true,(fun _ _ -> ()))
        | l ->
	    let l = List.map (function
	      | LETCLAUSE (id,Some a,t) -> (id,a,t)
	      | _ -> user_err_loc (loc, "", str "Syntax Error")) l in
	    TacLetCut (loc, l))
*)
(*
      |	IDENT "Let"; llc = LIST1 let_clause SEP "And";
        tb = Vernac_.theorem_body; "Qed" ->
          (match llc with
	    | [LETTOPCLAUSE (id,c)] ->
		EscapeVernac <:ast< (TheoremProof "LETTOP" $id $c $tb) >>
	    | _ ->
		errorlabstrm "Gram.tactic_atom" (str "Not a LETTOPCLAUSE"))
*)

      | IDENT "Match"; IDENT "Context"; IDENT "With"; mrl = match_context_list
        -> TacMatchContext (false,mrl)
      | IDENT "Match"; IDENT "Reverse"; IDENT "Context"; IDENT "With"; mrl = match_context_list
        -> TacMatchContext (true,mrl)
      |	IDENT "Match"; c = constrarg; IDENT "With"; mrl = match_list ->
        TacMatch (c,mrl)
(*To do: put Abstract in Refiner*)
      | IDENT "Abstract"; tc = tactic_expr -> TacAbstract (tc,None)
      | IDENT "Abstract"; tc = tactic_expr; "using";  s = Prim.ident ->
          TacAbstract (tc,Some s)
(*End of To do*)
      | IDENT "First" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacFirst l
      |	IDENT "Solve" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacSolve l
      |	IDENT "Idtac" -> TacId
      |	IDENT "Fail" -> TacFail fail_default_value
      |	IDENT "Fail"; n = Prim.natural -> TacFail n
      |	st = simple_tactic -> TacAtom (loc,st)
      | "("; a = tactic_expr; ")" -> a
      | a = tactic_arg -> TacArg a
    ] ]
  ;
  (* Tactic arguments *)
  tactic_arg:
    [ [ ta = tactic_arg1 -> ta ] ]
  ;
  tactic_letarg:
    (* Cannot be merged with tactic_arg1, since then "In"/"And" are 
       parsed as lqualid! *)
    [ [ IDENT "Eval"; rtc = red_expr; "in"; c = Constr.constr ->
	  ConstrMayEval (ConstrEval (rtc,c))
      | IDENT "Inst"; id = Prim.rawident; "["; c = Constr.constr; "]" ->
	  ConstrMayEval (ConstrContext (id,c))
      | IDENT "Check"; c = Constr.constr ->
	  ConstrMayEval (ConstrTypeOf c)
      | qid = lqualid -> qid
      | ta = tactic_arg0 -> ta ] ]
  ;
  tactic_arg1:
    [ [ IDENT "Eval"; rtc = red_expr; "in"; c = Constr.constr ->
	  ConstrMayEval (ConstrEval (rtc,c))
      | IDENT "Inst"; id = Prim.rawident; "["; c = Constr.constr; "]" ->
	  ConstrMayEval (ConstrContext (id,c))
      | IDENT "Check"; c = Constr.constr ->
	  ConstrMayEval (ConstrTypeOf c)
      | qid = lqualid; la = LIST1 tactic_arg0 -> TacCall (loc,qid,la)
      | qid = lqualid -> qid
      | ta = tactic_arg0 -> ta ] ]
  ;
  tactic_arg0:
    [ [ "("; a = tactic_expr; ")" -> Tacexp a
      | "()" -> TacVoid
      | qid = lqualid -> qid
      | n = Prim.integer -> Integer n
      | id = METAIDENT -> MetaIdArg (loc,id)
      |	"?" -> ConstrMayEval (ConstrTerm <:ast< (ISEVAR) >>)
      | "?"; n = Prim.natural -> MetaNumArg (loc,n)
      |	"'"; c = Constr.constr -> ConstrMayEval (ConstrTerm c) ] ]
  ;
  lqualid:
    [ [ qid = Prim.reference -> 
(*  match Nametab.repr_qualid qid with
  | (dir,id) when dir = Nameops.empty_dirpath -> Identifier id
  | _ -> Qualid *) Reference qid
    ] ]
  ;

  (* Definitions for tactics *)
  deftok:
    [ [ IDENT "Meta"
      | IDENT "Tactic" ] ]
  ;
  vrec_clause:
    [ [ name = Prim.rawident; it=LIST1 input_fun; ":="; body = tactic_expr ->
	  (name, TacFunRec (name, (it, body)))
      | name = Prim.rawident; ":="; body = tactic_expr ->
	  (name, body) ] ]
  ;
  tactic:
    [ [ tac = tactic_expr -> tac ] ]
  ;
  Vernac_.command: 
    [ [ deftok; "Definition"; name = Prim.rawident; ":="; body = tactic ->
        Vernacexpr.VernacDeclareTacticDefinition (loc, [name, body])
      | deftok; "Definition"; name = Prim.rawident; largs=LIST1 input_fun;
        ":="; body=tactic_expr ->
        Vernacexpr.VernacDeclareTacticDefinition
	  (loc, [name, TacFun (largs,body)])
      | IDENT "Recursive"; deftok; "Definition";
	vcl=LIST1 vrec_clause SEP "And" -> 
	  Vernacexpr.VernacDeclareTacticDefinition (loc, vcl) ] ]
  ;
  END
