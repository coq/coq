(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Util
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
let genarg_of_uconstr c = in_gen (rawwit Constrarg.wit_uconstr) c

let reference_to_id = function
  | Libnames.Ident (loc, id) -> (loc, id)
  | Libnames.Qualid (loc,_) ->
      Errors.user_err_loc (loc, "",
        str "This expression should be a simple identifier.")

let tactic_mode = Gram.entry_create "vernac:tactic_command"

let new_entry name =
  let e = Gram.entry_create name in
  let entry = Entry.create name in
  let () = Pcoq.set_grammar entry e in
  e

let selector = new_entry "vernac:selector"

(* Registers the Classic Proof Mode (which uses [tactic_mode] as a parser for
    proof editing and changes nothing else). Then sets it as the default proof mode. *)
let _ =
  let mode = {
    Proof_global.name = "Classic";
    set = (fun () -> set_command_entry tactic_mode);
    reset = (fun () -> set_command_entry Pcoq.Vernac_.noedit_mode);
  } in
  Proof_global.register_proof_mode mode

(* Hack to parse "[ id" without dropping [ *)
let test_bracket_ident =
  Gram.Entry.of_parser "test_bracket_ident"
    (fun strm ->
      match get_tok (stream_nth 0 strm) with
        | KEYWORD "[" ->
            (match get_tok (stream_nth 1 strm) with
              | IDENT _ -> ()
	      | _ -> raise Stream.Failure)
	| _ -> raise Stream.Failure)

(* Tactics grammar rules *)

GEXTEND Gram
  GLOBAL: tactic tacdef_body tactic_expr binder_tactic tactic_arg
          tactic_mode constr_may_eval constr_eval selector;

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
      | a = tactic_arg -> TacArg(!@loc,a)
      | r = reference; la = LIST0 tactic_arg_compat ->
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
  (* Tactic arguments to the right of an application *)
  tactic_arg_compat:
    [ [ a = tactic_arg -> a
      | r = reference -> Reference r
      | c = Constr.constr -> ConstrMayEval (ConstrTerm c)
      (* Unambigous entries: tolerated w/o "ltac:" modifier *)
      | "()" -> TacGeneric (genarg_of_unit ()) ] ]
  ;
  (* Can be used as argument and at toplevel in tactic expressions. *)
  tactic_arg:
    [ [ c = constr_eval -> ConstrMayEval c
      | IDENT "fresh"; l = LIST0 fresh_id -> TacFreshId l
      | IDENT "type_term"; c=uconstr -> TacPretype c
      | IDENT "numgoals" -> TacNumgoals ] ]
  ;
  (* If a qualid is given, use its short name. TODO: have the shortest
     non ambiguous name where dots are replaced by "_"? Probably too
     verbose most of the time. *)
  fresh_id:
    [ [ s = STRING -> ArgArg s (*| id = ident -> ArgVar (!@loc,id)*)
	| qid = qualid -> let (_pth,id) = Libnames.repr_qualid (snd qid) in ArgVar (!@loc,id) ] ]
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
    [ [ n = integer -> TacGeneric (genarg_of_int n)
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
          if redef then Vernacexpr.TacticRedefinition (name, TacFun (it, body))
          else
            let id = reference_to_id name in
            Vernacexpr.TacticDefinition (id, TacFun (it, body))
      | name = Constr.global; redef = ltac_def_kind; body = tactic_expr ->
          if redef then Vernacexpr.TacticRedefinition (name, body)
          else
            let id = reference_to_id name in
            Vernacexpr.TacticDefinition (id, body)
    ] ]
  ;
  tactic:
    [ [ tac = tactic_expr -> tac ] ]
  ;
  selector:
    [ [ n=natural; ":" -> Vernacexpr.SelectNth n
      | test_bracket_ident; "["; id = ident; "]"; ":" -> Vernacexpr.SelectId id
      | IDENT "all" ; ":" -> Vernacexpr.SelectAll ] ]
  ;
  tactic_mode:
    [ [ g = OPT selector; tac = G_vernac.subgoal_command -> tac g ] ]
  ;
  END

open Stdarg
open Constrarg
open Vernacexpr
open Vernac_classifier

let print_info_trace = ref None

let _ = let open Goptions in declare_int_option {
  optsync = true;
  optdepr = false;
  optname = "print info trace";
  optkey = ["Info" ; "Level"];
  optread = (fun () -> !print_info_trace);
  optwrite = fun n -> print_info_trace := n;
}

let vernac_solve n info tcom b =
  let status = Proof_global.with_current_proof (fun etac p ->
    let with_end_tac = if b then Some etac else None in
    let global = match n with SelectAll -> true | _ -> false in
    let info = Option.append info !print_info_trace in
    let (p,status) =
      Pfedit.solve n info (Tacinterp.hide_interp global tcom None) ?with_end_tac p
    in
    (* in case a strict subtree was completed,
       go back to the top of the prooftree *)
    let p = Proof.maximal_unfocus Vernacentries.command_focus p in
    p,status) in
    if not status then Pp.feedback Feedback.AddedAxiom

let pr_ltac_selector = function
| SelectNth i -> int i ++ str ":"
| SelectId id -> str "[" ++ Nameops.pr_id id ++ str "]" ++ str ":"
| SelectAll -> str "all" ++ str ":"

VERNAC ARGUMENT EXTEND ltac_selector PRINTED BY pr_ltac_selector
| [ selector(s) ] -> [ s ]
END

let pr_ltac_info n = str "Info" ++ spc () ++ int n

VERNAC ARGUMENT EXTEND ltac_info PRINTED BY pr_ltac_info
| [ "Info" natural(n) ] -> [ n ]
END

let pr_ltac_use_default b = if b then str ".." else mt ()

VERNAC ARGUMENT EXTEND ltac_use_default PRINTED BY pr_ltac_use_default
| [ "." ] -> [ false ]
| [ "..." ] -> [ true ]
END

VERNAC tactic_mode EXTEND VernacSolve
| [ - ltac_selector_opt(g) ltac_info_opt(n) tactic(t) ltac_use_default(def) ] =>
    [ classify_as_proofstep ] -> [
    let g = Option.default (Proof_global.get_default_goal_selector ()) g in
    vernac_solve g n t def
  ]
| [ - "par" ":" ltac_info_opt(n) tactic(t) ltac_use_default(def) ] =>
    [ VtProofStep true, VtLater ] -> [
    vernac_solve SelectAll n t def
  ]
END
