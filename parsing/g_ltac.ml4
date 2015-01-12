(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Compat
open Constrexpr
open Tacexpr
open Misctypes
open Genarg
open Genredexpr
open Tok (* necessary for camlp4 *)

open Pcoq
open Pcoq.Prim
open Pcoq.Tactic

let fail_default_value = ArgArg 0

let arg_of_expr = function
    TacArg (loc,a) -> a
  | e -> Tacexp (e:raw_tactic_expr)

let genarg_of_unit () = in_gen (rawwit Stdarg.wit_unit) ()
let genarg_of_int n = in_gen (rawwit Stdarg.wit_int) n
let genarg_of_ipattern pat = in_gen (rawwit Constrarg.wit_intro_pattern) pat

(* Tactics grammar rules *)

GEXTEND Gram
  GLOBAL: tactic tacdef_body tactic_expr binder_tactic tactic_arg
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
  tactic_then_locality: (* [true] for the local variant [TacThens] and [false]
                           for [TacExtend] *)
  [ [ "[" ; l = OPT">" -> if Option.is_empty l then true else false ] ]
  ;
  tactic_expr:
    [ "5" RIGHTA
      [ te = binder_tactic -> te ]
    | "4" LEFTA
      [ ta0 = tactic_expr; ";"; ta1 = binder_tactic -> TacThen (ta0, ta1)
      | ta0 = tactic_expr; ";"; ta1 = tactic_expr -> TacThen (ta0,ta1)
      | ta0 = tactic_expr; ";"; l = tactic_then_locality; (first,tail) = tactic_then_gen; "]" ->
	  match l , tail with
          | false , Some (t,last) -> TacThen (ta0,TacExtendTac (Array.of_list first, t, last))
	  | true  , Some (t,last) -> TacThens3parts (ta0, Array.of_list first, t, last)
          | false , None -> TacThen (ta0,TacDispatch first)
	  | true  , None -> TacThens (ta0,first) ]
    | "3" RIGHTA
      [ IDENT "try"; ta = tactic_expr -> TacTry ta
      | IDENT "do"; n = int_or_var; ta = tactic_expr -> TacDo (n,ta)
      | IDENT "timeout"; n = int_or_var; ta = tactic_expr -> TacTimeout (n,ta)
      | IDENT "time"; s = OPT string; ta = tactic_expr -> TacTime (s,ta)
      | IDENT "repeat"; ta = tactic_expr -> TacRepeat ta
      | IDENT "progress"; ta = tactic_expr -> TacProgress ta
      | IDENT "once"; ta = tactic_expr -> TacOnce ta
      | IDENT "exactly_once"; ta = tactic_expr -> TacExactlyOnce ta
      | IDENT "infoH"; ta = tactic_expr -> TacShowHyps ta
(*To do: put Abstract in Refiner*)
      | IDENT "abstract"; tc = NEXT -> TacAbstract (tc,None)
      | IDENT "abstract"; tc = NEXT; "using";  s = ident ->
          TacAbstract (tc,Some s) ]
(*End of To do*)
    | "2" RIGHTA
      [ ta0 = tactic_expr; "+"; ta1 = binder_tactic -> TacOr (ta0,ta1)
      | ta0 = tactic_expr; "+"; ta1 = tactic_expr -> TacOr (ta0,ta1) 
      | IDENT "tryif" ; ta = tactic_expr ;
              "then" ; tat = tactic_expr ;
              "else" ; tae = tactic_expr -> TacIfThenCatch(ta,tat,tae)
      | ta0 = tactic_expr; "||"; ta1 = binder_tactic -> TacOrelse (ta0,ta1)
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
      | IDENT "idtac"; l = LIST0 message_token -> TacId l
      | g=failkw; n = [ n = int_or_var -> n | -> fail_default_value ];
	  l = LIST0 message_token -> TacFail (g,n,l)
      | st = simple_tactic -> st
      | IDENT "constr"; ":"; c = Constr.constr ->
          TacArg(!@loc,ConstrMayEval(ConstrTerm c))
      | a = tactic_top_or_arg -> TacArg(!@loc,a)
      | r = reference; la = LIST0 tactic_arg ->
          TacArg(!@loc,TacCall (!@loc,r,la)) ]
    | "0"
      [ "("; a = tactic_expr; ")" -> a
      | "["; ">"; (tf,tail) = tactic_then_gen; "]" ->
          begin match tail with
          | Some (t,tl) -> TacExtendTac(Array.of_list tf,t,tl)
          | None -> TacDispatch tf
          end
      | a = tactic_atom -> TacArg (!@loc,a) ] ]
  ;
  failkw:
  [ [ IDENT "fail" -> TacLocal | IDENT "gfail" -> TacGlobal ] ]
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
      | IDENT "ltac"; ":"; n = natural -> TacGeneric (genarg_of_int n)
      | a = tactic_top_or_arg -> a
      | r = reference -> Reference r
      | c = Constr.constr -> ConstrMayEval (ConstrTerm c)
      (* Unambigous entries: tolerated w/o "ltac:" modifier *)
      | id = METAIDENT -> MetaIdArg (!@loc,true,id)
      | "()" -> TacGeneric (genarg_of_unit ()) ] ]
  ;
  (* Can be used as argument and at toplevel in tactic expressions. *)
  tactic_top_or_arg:
    [ [ IDENT "uconstr"; ":" ; c = uconstr -> UConstr c
      | IDENT "ipattern"; ":"; ipat = simple_intropattern ->
        TacGeneric (genarg_of_ipattern ipat)
      | c = constr_eval -> ConstrMayEval c
      | IDENT "fresh"; l = LIST0 fresh_id -> TacFreshId l
      | IDENT "type_term"; c=uconstr -> TacPretype c
      | IDENT "numgoals" -> TacNumgoals ] ]
  ;
  fresh_id:
    [ [ s = STRING -> ArgArg s | id = ident -> ArgVar (!@loc,id) ] ]
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
    [ [ id = METAIDENT -> MetaIdArg (!@loc,true,id)
      | n = integer -> TacGeneric (genarg_of_int n)
      | r = reference -> TacCall (!@loc,r,[])
      | "()" -> TacGeneric (genarg_of_unit ()) ] ]
  ;
  match_key:
    [ [ "match" -> Once
      | "lazymatch" -> Select
      | "multimatch" -> General ] ]
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
        let mode = not (!Flags.tactic_context_compat) in
        Subterm (mode, oid, pc)
      | IDENT "appcontext";  oid = OPT Constr.ident;
          "["; pc = Constr.lconstr_pattern; "]" ->
        msg_warning (strbrk "appcontext is deprecated");
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
	      | CCast (loc, t, (CastConv ty | CastVM ty | CastNative ty)) -> Term t, Some (Term ty)
	      | _ -> mpv, None)
	    | _ -> mpv, None
	  in Def (na, t, Option.default (Term (CHole (Loc.ghost, None, IntroAnonymous, None))) ty)
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
    [ [ id = identref -> MsgIdent id
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
  END
