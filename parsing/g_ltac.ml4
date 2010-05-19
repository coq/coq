(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Util
open Topconstr
open Rawterm
open Tacexpr
open Vernacexpr
open Pcoq
open Prim
open Tactic
open Tok

let fail_default_value = ArgArg 0

let arg_of_expr = function
    TacArg a -> a
  | e -> Tacexp (e:raw_tactic_expr)

(* Tactics grammar rules *)

GEXTEND Gram
  GLOBAL: tactic Vernac_.command tactic_expr binder_tactic tactic_arg
          constr_may_eval;

  tactic_then_last:
    [ [ "|"; lta = LIST0 OPT tactic_expr SEP "|" ->
          Array.map (function None -> TacId [] | Some t -> t) (Array.of_list lta)
      | -> [||]
    ] ]
  ;
  tactic_then_gen:
    [ [ ta = tactic_expr; "|"; (first,last) = tactic_then_gen -> (ta::first, last)
      | ta = tactic_expr; ".."; l = tactic_then_last -> ([], Some (ta, l))
      | ".."; l = tactic_then_last -> ([], Some (TacId [], l))
      | ta = tactic_expr -> ([ta], None)
      | "|"; (first,last) = tactic_then_gen -> (TacId [] :: first, last)
      | -> ([TacId []], None)
    ] ]
  ;
  tactic_expr:
    [ "5" RIGHTA
      [ te = binder_tactic -> te ]
    | "4" LEFTA
      [ ta0 = tactic_expr; ";"; ta1 = binder_tactic -> TacThen (ta0, [||], ta1, [||])
      | ta0 = tactic_expr; ";"; ta1 = tactic_expr -> TacThen (ta0,  [||], ta1, [||])
      | ta0 = tactic_expr; ";"; "["; (first,tail) = tactic_then_gen; "]" ->
	  match tail with
	  | Some (t,last) -> TacThen (ta0, Array.of_list first, t, last)
	  | None -> TacThens (ta0,first) ]
    | "3" RIGHTA
      [ IDENT "try"; ta = tactic_expr -> TacTry ta
      | IDENT "do"; n = int_or_var; ta = tactic_expr -> TacDo (n,ta)
      | IDENT "repeat"; ta = tactic_expr -> TacRepeat ta
      | IDENT "progress"; ta = tactic_expr -> TacProgress ta
(*To do: put Abstract in Refiner*)
      | IDENT "abstract"; tc = NEXT -> TacAbstract (tc,None)
      | IDENT "abstract"; tc = NEXT; "using";  s = ident ->
          TacAbstract (tc,Some s) ]
(*End of To do*)
    | "2" RIGHTA
      [ ta0 = tactic_expr; "||"; ta1 = binder_tactic -> TacOrelse (ta0,ta1)
      | ta0 = tactic_expr; "||"; ta1 = tactic_expr -> TacOrelse (ta0,ta1) ]
    | "1" RIGHTA
      [ b = match_key; IDENT "goal"; "with"; mrl = match_context_list; "end" ->
          TacMatchGoal (b,false,mrl)
      | b = match_key; IDENT "reverse"; IDENT "goal"; "with";
        mrl = match_context_list; "end" ->
          TacMatchGoal (b,true,mrl)
      |	b = match_key; c = tactic_expr; "with"; mrl = match_list; "end" ->
          TacMatch (b,c,mrl)
      | IDENT "first" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacFirst l
      | IDENT "solve" ; "["; l = LIST0 tactic_expr SEP "|"; "]" ->
	  TacSolve l
      | IDENT "complete" ; ta = tactic_expr -> TacComplete ta
      | IDENT "idtac"; l = LIST0 message_token -> TacId l
      | IDENT "fail"; n = [ n = int_or_var -> n | -> fail_default_value ];
	  l = LIST0 message_token -> TacFail (n,l)
      | IDENT "external"; com = STRING; req = STRING; la = LIST1 tactic_arg ->
	  TacArg (TacExternal (loc,com,req,la))
      | st = simple_tactic -> TacAtom (loc,st)
      | a = may_eval_arg -> TacArg(a)
      | IDENT "constr"; ":"; id = METAIDENT ->
          TacArg(MetaIdArg (loc,false,id))
      | IDENT "constr"; ":"; c = Constr.constr ->
          TacArg(ConstrMayEval(ConstrTerm c))
      | IDENT "ipattern"; ":"; ipat = simple_intropattern ->
	  TacArg(IntroPattern ipat)
      | r = reference; la = LIST0 tactic_arg ->
          TacArg(TacCall (loc,r,la)) ]
    | "0"
      [ "("; a = tactic_expr; ")" -> a
      | a = tactic_atom -> TacArg a ] ]
  ;
  (* binder_tactic: level 5 of tactic_expr *)
  binder_tactic:
    [ RIGHTA
      [ "fun"; it = LIST1 input_fun ; "=>"; body = tactic_expr LEVEL "5" ->
          TacFun (it,body)
      | "let"; isrec = [IDENT "rec" -> true | -> false];
          llc = LIST1 let_clause SEP "with"; "in";
          body = tactic_expr LEVEL "5" -> TacLetIn (isrec,llc,body)
      | IDENT "info"; tc = tactic_expr LEVEL "5" -> TacInfo tc ] ]
  ;
  (* Tactic arguments *)
  tactic_arg:
    [ [ IDENT "ltac"; ":"; a = tactic_expr LEVEL "0" -> arg_of_expr a
      | IDENT "ltac"; ":"; n = natural -> Integer n
      | IDENT "ipattern"; ":"; ipat = simple_intropattern -> IntroPattern ipat
      | a = may_eval_arg -> a
      | r = reference -> Reference r
      | c = Constr.constr -> ConstrMayEval (ConstrTerm c)
      (* Unambigous entries: tolerated w/o "ltac:" modifier *)
      | id = METAIDENT -> MetaIdArg (loc,true,id)
      | "()" -> TacVoid ] ]
  ;
  may_eval_arg:
    [ [ c = constr_eval -> ConstrMayEval c
      | IDENT "fresh"; l = LIST0 fresh_id -> TacFreshId l ] ]
  ;
  fresh_id:
    [ [ s = STRING -> ArgArg s | id = ident -> ArgVar (loc,id) ] ]
  ;
  constr_eval:
    [ [ IDENT "eval"; rtc = red_expr; "in"; c = Constr.constr ->
          ConstrEval (rtc,c)
      | IDENT "context"; id = identref; "["; c = Constr.lconstr; "]" ->
          ConstrContext (id,c)
      | IDENT "type"; IDENT "of"; c = Constr.constr ->
          ConstrTypeOf c ] ]
  ;
  constr_may_eval: (* For extensions *)
    [ [ c = constr_eval -> c
      | c = Constr.constr -> ConstrTerm c ] ]
  ;
  tactic_atom:
    [ [ id = METAIDENT -> MetaIdArg (loc,true,id)
      | n = integer -> Integer n
      | r = reference -> TacCall (loc,r,[])
      | "()" -> TacVoid ] ]
  ;
  match_key:
    [ [ "match" -> false | "lazymatch" -> true ] ]
  ;
  input_fun:
    [ [ "_" -> None
      | l = ident -> Some l ] ]
  ;
  let_clause:
    [ [ id = identref; ":="; te = tactic_expr ->
         (id, arg_of_expr te)
      | id = identref; args = LIST1 input_fun; ":="; te = tactic_expr ->
         (id, arg_of_expr (TacFun(args,te))) ] ]
  ;
  match_pattern:
    [ [ IDENT "context";  oid = OPT Constr.ident;
          "["; pc = Constr.lconstr_pattern; "]" ->
        Subterm (false,oid, pc)
      | IDENT "appcontext";  oid = OPT Constr.ident;
          "["; pc = Constr.lconstr_pattern; "]" ->
        Subterm (true,oid, pc)
      | pc = Constr.lconstr_pattern -> Term pc ] ]
  ;
  match_hyps:
    [ [ na = name; ":"; mp =  match_pattern -> Hyp (na, mp)
      | na = name; ":="; "["; mpv = match_pattern; "]"; ":"; mpt = match_pattern -> Def (na, mpv, mpt)
      | na = name; ":="; mpv = match_pattern ->
	  let t, ty =
	    match mpv with
	    | Term t -> (match t with
	      | CCast (loc, t, CastConv (_, ty)) -> Term t, Some (Term ty)
	      | _ -> mpv, None)
	    | _ -> mpv, None
	  in Def (na, t, Option.default (Term (CHole (dummy_loc, None))) ty)
    ] ]
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
  message_token:
    [ [ id = identref -> MsgIdent (AI id)
      | s = STRING -> MsgString s
      | n = integer -> MsgInt n ] ]
  ;

  ltac_def_kind:
    [ [ ":=" -> false
      | "::=" -> true ] ]
  ;

  (* Definitions for tactics *)
  tacdef_body:
    [ [ name = Constr.global; it=LIST1 input_fun; redef = ltac_def_kind; body = tactic_expr ->
	  (name, redef, TacFun (it, body))
      | name = Constr.global; redef = ltac_def_kind; body = tactic_expr ->
	  (name, redef, body) ] ]
  ;
  tactic:
    [ [ tac = tactic_expr -> tac ] ]
  ;
  Vernac_.command:
    [ [ IDENT "Ltac";
        l = LIST1 tacdef_body SEP "with" ->
          VernacDeclareTacticDefinition (use_module_locality (), true, l) ] ]
  ;
  END
