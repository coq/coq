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
open Ast
open Pcoq
open Tactic
open Util

(* Tactics grammar rules *)

(* Tactics grammar rules *)

GEXTEND Gram
  input_fun:
    [ [ l = identarg -> l
      | "()" -> <:ast< (VOID) >> ] ]
  ;
  let_clause:
    [ [ id = identarg; "="; te=tactic_atom -> <:ast< (LETCLAUSE $id $te) >>
      | id = identarg; ":"; c = constrarg; ":="; "Proof" ->
        (match c with
        | Coqast.Node(_,"COMMAND",[csr]) ->
          <:ast< (LETTOPCLAUSE $id (CONSTR $csr)) >>
	| _ -> errorlabstrm "Gram.let_clause" [<'sTR "Not a COMMAND">])
      | id = identarg; ":"; c = constrarg; ":="; te = tactic_expr ->
        <:ast< (LETCUTCLAUSE $id $c $te) >> 
      |	id = identarg; ":"; c = constrarg ->
        (match c with
        | Coqast.Node(_,"COMMAND",[csr]) ->
          <:ast< (LETTOPCLAUSE $id (CONSTR $csr)) >>
	| _ -> errorlabstrm "Gram.let_clause" [<'sTR "Not a COMMAND">]) ] ]
  ;
  rec_clause:
    [ [ name = identarg; it = LIST1 input_fun; "->"; body = tactic_atom ->
          <:ast< (RECCLAUSE $name (FUNVAR ($LIST $it)) $body) >> ] ]
  ;
  match_pattern:
    [ [ id = constrarg; "["; pc = constrarg; "]" ->
        (match id with
        | Coqast.Node(_,"COMMAND",
            [Coqast.Node(_,"QUALID",[Coqast.Nvar(_,s)])]) ->
          <:ast< (SUBTERM ($VAR $s) $pc) >>
        | _ ->
          errorlabstrm "Gram.match_pattern" [<'sTR "Not a correct SUBTERM">])
      | "["; pc = constrarg; "]" -> <:ast< (SUBTERM $pc) >>
      | pc = constrarg -> <:ast< (TERM $pc) >> ] ]
  ;
  match_hyps:
    [ [ id = identarg; ":"; mp =  match_pattern ->
          <:ast< (MATCHCONTEXTHYPS $id $mp) >>
      | IDENT "_"; ":"; mp = match_pattern ->
          <:ast< (MATCHCONTEXTHYPS $mp) >> ] ]
  ;
  match_context_rule:
    [ [ "["; largs = LIST0 match_hyps SEP ";"; "|-"; mp = match_pattern; "]";
        "->"; te = tactic_expr ->
            <:ast< (MATCHCONTEXTRULE ($LIST $largs) $mp $te) >> 
      | IDENT "_"; "->"; te = tactic_expr -> <:ast< (MATCHCONTEXTRULE $te) >>
    ] ]
  ;
  match_context_list:
    [ [ mrl = LIST1 match_context_rule SEP "|" -> mrl
      | "|"; mrl = LIST1 match_context_rule SEP "|" -> mrl ] ]
  ;
  match_rule:
    [ [ "["; mp = match_pattern; "]"; "->"; te = tactic_expr ->
        <:ast<(MATCHRULE $mp $te)>>
      | IDENT "_"; "->"; te = tactic_expr -> <:ast< (MATCHRULE $te) >> ] ]
  ;
  match_list:
    [ [ mrl = LIST1 match_rule SEP "|" -> mrl
      | "|"; mrl = LIST1 match_rule SEP "|" -> mrl ] ]
  ;
  tactic_expr:
    [ [ ta0 = tactic_expr; ";"; ta1 = tactic_expr ->
         <:ast< (TACTICLIST $ta0 $ta1) >>
      | ta = tactic_expr; ";"; "["; lta = LIST0 tactic_expr SEP "|"; "]" ->
         <:ast< (TACTICLIST $ta (TACLIST ($LIST $lta))) >>
      | y = tactic_atom0 -> y ] ]
  ;
  tactic_atom0:
    [ [ la = LIST1 tactic_atom ->
        if (List.length la) = 1 then
          let el = List.hd la in <:ast< $el >>
        else
          <:ast< (APP ($LIST $la)) >> ] ]
  ;
  tactic_atom:
    [ [ IDENT "Fun"; it = LIST1 input_fun ; "->"; body = tactic_expr ->
          <:ast< (FUN (FUNVAR ($LIST $it)) $body) >>
      | IDENT "Rec"; rc = rec_clause -> <:ast< (REC $rc) >>
      |	IDENT "Rec"; rc = rec_clause; IDENT "In"; body = tactic_expr ->
          <:ast< (REC (RECDECL $rc) $body) >>
      | IDENT "Rec"; rc = rec_clause; "And";
          rcl = LIST1 rec_clause SEP "And"; IDENT "In";
          body = tactic_expr ->
            <:ast< (REC (RECDECL $rc ($LIST $rcl)) $body) >>
      | IDENT "Let"; llc = LIST1 let_clause SEP "And"; IDENT "In";
          u = tactic_expr -> <:ast< (LET (LETDECL ($LIST $llc)) $u) >>
      |	IDENT "Let"; llc = LIST1 let_clause SEP "And" ->
        (match llc with
	| [Coqast.Node(_,"LETTOPCLAUSE",[id;c])] ->
          <:ast< (StartProof "LETTOP" $id $c) >>
        | _ -> <:ast< (LETCUT (LETDECL ($LIST $llc))) >>)
      |	IDENT "Let"; llc = LIST1 let_clause SEP "And";
        tb = Vernac_.theorem_body; "Qed" ->
        (match llc with
	| [Coqast.Node(_,"LETTOPCLAUSE",[id;c])] ->
          <:ast< (TheoremProof "LETTOP" $id $c $tb) >>
	| _ -> errorlabstrm "Gram.tactic_atom" [<'sTR "Not a LETTOPCLAUSE">])
      |	IDENT "Match"; IDENT "Context"; IDENT "With"; mrl = match_context_list
        -> <:ast< (MATCHCONTEXT ($LIST $mrl)) >>
      |	IDENT "Match"; com = constrarg; IDENT "With"; mrl = match_list ->
        <:ast< (MATCH $com ($LIST $mrl)) >>
      |	"("; te = tactic_expr; ")" -> te
      |	"("; te = tactic_expr; tel=LIST1 tactic_expr; ")" ->
        <:ast< (APP $te ($LIST tel)) >>
      | IDENT "First" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
          <:ast<(FIRST ($LIST $l))>>
      | IDENT "Info"; tc = tactic_expr -> <:ast< (INFO $tc) >>
      |	IDENT "Solve" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
          <:ast<(TCLSOLVE ($LIST $l))>>
      |	IDENT "Try"; ta0 = tactic_atom; "Orelse"; ta1 = tactic_atom ->
        <:ast< (TRY (ORELSE $ta0 $ta1)) >>
      |	IDENT "Try"; ta = tactic_atom -> <:ast< (TRY $ta) >>
      | IDENT "Do"; n = pure_numarg; ta = tactic_atom -> <:ast< (DO $n $ta) >>
      |	IDENT "Repeat"; ta0 = tactic_atom; "Orelse"; ta1 = tactic_atom ->
        <:ast< (REPEAT (ORELSE $ta0 $ta1)) >>
      | IDENT "Repeat"; ta = tactic_atom -> <:ast< (REPEAT $ta) >>
      |	IDENT "Idtac" -> <:ast< (IDTAC) >>
      |	IDENT "Fail" -> <:ast<(FAIL)>>
      |	IDENT "Fail"; n = pure_numarg -> <:ast<(FAIL $n)>>
      |	ta0 = tactic_atom; "Orelse"; ta1 = tactic_atom ->
          <:ast< (ORELSE $ta0 $ta1) >>
      | IDENT "Progress"; ta = tactic_atom -> <:ast< (PROGRESS $ta) >>
      |	st = simple_tactic -> st
      |	tca = tactic_arg -> tca ] ]
  ;
  tactic_arg:
    [ [ "()" -> <:ast< (VOID) >>
      | n = pure_numarg -> n
      | l = Constr.qualid ->
        (match l with
	| [id] -> id
        | _ -> <:ast< (QUALIDARG ($LIST l)) >>)
      | id = METAIDENT -> <:ast< ($VAR $id) >>
      |	"?" -> <:ast< (COMMAND (ISEVAR)) >>
      | "?"; n = Prim.number -> <:ast< (COMMAND (META $n)) >>
      |	IDENT "Eval"; rtc = Tactic.red_tactic; "in"; c = Constr.constr ->
        <:ast< (COMMAND (EVAL $c (REDEXP $rtc))) >>
      | IDENT "Inst"; id = identarg; "["; c = Constr.constr; "]" ->
        <:ast< (COMMAND (CONTEXT $id $c)) >>
      |	"'"; c = constrarg -> c ] ];
    END
