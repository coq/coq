(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

DECLARE PLUGIN "ltac_plugin"

open Util
open Pp
open Glob_term
open Constrexpr
open Tacexpr
open Namegen
open Genarg
open Genredexpr
open Tok (* necessary for camlp5 *)
open Names

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pvernac.Vernac_
open Pltac

let fail_default_value = Locus.ArgArg 0

let arg_of_expr = function
    TacArg (loc,a) -> a
  | e -> Tacexp (e:raw_tactic_expr)

let genarg_of_unit () = in_gen (rawwit Stdarg.wit_unit) ()
let genarg_of_int n = in_gen (rawwit Stdarg.wit_int) n
let genarg_of_ipattern pat = in_gen (rawwit Tacarg.wit_intro_pattern) pat
let genarg_of_uconstr c = in_gen (rawwit Stdarg.wit_uconstr) c
let in_tac tac = in_gen (rawwit Tacarg.wit_ltac) tac

let reference_to_id qid =
  if Libnames.qualid_is_ident qid then
    CAst.make ?loc:qid.CAst.loc @@ Libnames.qualid_basename qid
  else
    CErrors.user_err ?loc:qid.CAst.loc
      (str "This expression should be a simple identifier.")

let tactic_mode = Entry.create "vernac:tactic_command"

let new_entry name =
  let e = Entry.create name in
  e

let toplevel_selector = new_entry "vernac:toplevel_selector"
let tacdef_body = new_entry "tactic:tacdef_body"

(* Registers the Classic Proof Mode (which uses [tactic_mode] as a parser for
    proof editing and changes nothing else). Then sets it as the default proof mode. *)
let _ =
  let mode = {
    Proof_global.name = "Classic";
    set = (fun () -> Pvernac.set_command_entry tactic_mode);
    reset = (fun () -> Pvernac.(set_command_entry noedit_mode));
  } in
  Proof_global.register_proof_mode mode

(* Hack to parse "[ id" without dropping [ *)
let test_bracket_ident =
  Gram.Entry.of_parser "test_bracket_ident"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "[" ->
            (match stream_nth 1 strm with
              | IDENT _ -> ()
	      | _ -> raise Stream.Failure)
	| _ -> raise Stream.Failure)

(* Tactics grammar rules *)

let hint = G_proofs.hint

GEXTEND Gram
  GLOBAL: tactic tacdef_body tactic_expr binder_tactic tactic_arg command hint
          tactic_mode constr_may_eval constr_eval toplevel_selector
          operconstr;

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
          TacAbstract (tc,Some s)
      | sel = selector; ta = tactic_expr -> TacSelect (sel, ta) ]
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
      | a = tactic_arg -> TacArg(Loc.tag ~loc:!@loc a)
      | r = reference; la = LIST0 tactic_arg_compat ->
          TacArg(Loc.tag ~loc:!@loc @@ TacCall (Loc.tag ~loc:!@loc (r,la))) ]
    | "0"
      [ "("; a = tactic_expr; ")" -> a
      | "["; ">"; (tf,tail) = tactic_then_gen; "]" ->
          begin match tail with
          | Some (t,tl) -> TacExtendTac(Array.of_list tf,t,tl)
          | None -> TacDispatch tf
          end
      | a = tactic_atom -> TacArg (Loc.tag ~loc:!@loc a) ] ]
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
      | c = Constr.constr -> (match c with { CAst.v = CRef (r,None) } -> Reference r | c -> ConstrMayEval (ConstrTerm c))
      (* Unambiguous entries: tolerated w/o "ltac:" modifier *)
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
    [ [ s = STRING -> Locus.ArgArg s (*| id = ident -> Locus.ArgVar (!@loc,id)*)
        | qid = qualid -> Locus.ArgVar (CAst.make ~loc:!@loc @@ Libnames.qualid_basename qid) ] ]
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
      | r = reference -> TacCall (Loc.tag ~loc:!@loc (r,[]))
      | "()" -> TacGeneric (genarg_of_unit ()) ] ]
  ;
  match_key:
    [ [ "match" -> Once
      | "lazymatch" -> Select
      | "multimatch" -> General ] ]
  ;
  input_fun:
    [ [ "_" -> Name.Anonymous
      | l = ident -> Name.Name l ] ]
  ;
  let_clause:
    [ [ idr = identref; ":="; te = tactic_expr ->
         (CAst.map (fun id -> Name id) idr, arg_of_expr te)
      | na = ["_" -> CAst.make ~loc:!@loc Anonymous]; ":="; te = tactic_expr ->
         (na, arg_of_expr te)
      | idr = identref; args = LIST1 input_fun; ":="; te = tactic_expr ->
         (CAst.map (fun id -> Name id) idr, arg_of_expr (TacFun(args,te))) ] ]
  ;
  match_pattern:
    [ [ IDENT "context";  oid = OPT Constr.ident;
          "["; pc = Constr.lconstr_pattern; "]" ->
        Subterm (oid, pc)
      | pc = Constr.lconstr_pattern -> Term pc ] ]
  ;
  match_hyps:
    [ [ na = name; ":"; mp =  match_pattern -> Hyp (na, mp)
      | na = name; ":="; "["; mpv = match_pattern; "]"; ":"; mpt = match_pattern -> Def (na, mpv, mpt)
      | na = name; ":="; mpv = match_pattern ->
	  let t, ty =
	    match mpv with
	    | Term t -> (match t with
	      | { CAst.v = CCast (t, (CastConv ty | CastVM ty | CastNative ty)) } -> Term t, Some (Term ty)
	      | _ -> mpv, None)
	    | _ -> mpv, None
	  in Def (na, t, Option.default (Term (CAst.make @@ CHole (None, IntroAnonymous, None))) ty)
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
    [ [ name = Constr.global; it=LIST1 input_fun;
        redef = ltac_def_kind; body = tactic_expr ->
          if redef then Tacexpr.TacticRedefinition (name, TacFun (it, body))
          else
            let id = reference_to_id name in
            Tacexpr.TacticDefinition (id, TacFun (it, body))
      | name = Constr.global; redef = ltac_def_kind;
        body = tactic_expr ->
          if redef then Tacexpr.TacticRedefinition (name, body)
          else
            let id = reference_to_id name in
            Tacexpr.TacticDefinition (id, body)
    ] ]
  ;
  tactic:
    [ [ tac = tactic_expr -> tac ] ]
  ;

  range_selector:
    [ [ n = natural ; "-" ; m = natural -> (n, m)
      | n = natural -> (n, n) ] ]
  ;
  (* We unfold a range selectors list once so that we can make a special case
   * for a unique SelectNth selector. *)
  range_selector_or_nth:
    [ [ n = natural ; "-" ; m = natural;
        l = OPT [","; l = LIST1 range_selector SEP "," -> l] ->
          Goal_select.SelectList ((n, m) :: Option.default [] l)
      | n = natural;
        l = OPT [","; l = LIST1 range_selector SEP "," -> l] ->
          let open Goal_select in
          Option.cata (fun l -> SelectList ((n, n) :: l)) (SelectNth n) l ] ]
  ;
  selector_body:
  [ [ l = range_selector_or_nth -> l
    | test_bracket_ident; "["; id = ident; "]" -> Goal_select.SelectId id ] ]
  ;
  selector:
    [ [ IDENT "only"; sel = selector_body; ":" -> sel ] ]
  ;
  toplevel_selector:
    [ [ sel = selector_body; ":" -> sel
    |   "!"; ":" -> Goal_select.SelectAlreadyFocused
    |   IDENT "all"; ":" -> Goal_select.SelectAll ] ]
  ;
  tactic_mode:
    [ [ g = OPT toplevel_selector; tac = G_vernac.query_command -> tac g
      | g = OPT toplevel_selector; "{" -> Vernacexpr.VernacSubproof g ] ]
  ;
  command:
    [ [ IDENT "Proof"; "with"; ta = Pltac.tactic; 
        l = OPT [ "using"; l = G_vernac.section_subset_expr -> l ] ->
          Vernacexpr.VernacProof (Some (in_tac ta), l)
      | IDENT "Proof"; "using"; l = G_vernac.section_subset_expr;
        ta = OPT [ "with"; ta = Pltac.tactic -> in_tac ta ] ->
          Vernacexpr.VernacProof (ta,Some l) ] ]
  ;
  hint:
    [ [ IDENT "Extern"; n = natural; c = OPT Constr.constr_pattern ; "=>";
        tac = Pltac.tactic ->
          Hints.HintsExtern (n,c, in_tac tac) ] ]
  ;
  operconstr: LEVEL "0"
    [ [ IDENT "ltac"; ":"; "("; tac = Pltac.tactic_expr; ")" ->
          let arg = Genarg.in_gen (Genarg.rawwit Tacarg.wit_tactic) tac in
          CAst.make ~loc:!@loc @@ CHole (None, IntroAnonymous, Some arg) ] ]
  ;
  END

open Stdarg
open Tacarg
open Vernacexpr
open Vernac_classifier
open Goptions
open Libnames

let print_info_trace = ref None

let _ = declare_int_option {
  optdepr = false;
  optname = "print info trace";
  optkey = ["Info" ; "Level"];
  optread = (fun () -> !print_info_trace);
  optwrite = fun n -> print_info_trace := n;
}

let vernac_solve n info tcom b =
  let open Goal_select in
  let status = Proof_global.with_current_proof (fun etac p ->
    let with_end_tac = if b then Some etac else None in
    let global = match n with SelectAll | SelectList _ -> true | _ -> false in
    let info = Option.append info !print_info_trace in
    let (p,status) =
      Pfedit.solve n info (Tacinterp.hide_interp global tcom None) ?with_end_tac p
    in
    (* in case a strict subtree was completed,
       go back to the top of the prooftree *)
    let p = Proof.maximal_unfocus Vernacentries.command_focus p in
    p,status) in
    if not status then Feedback.feedback Feedback.AddedAxiom

let pr_ltac_selector s = Pptactic.pr_goal_selector ~toplevel:true s

VERNAC ARGUMENT EXTEND ltac_selector PRINTED BY pr_ltac_selector
| [ toplevel_selector(s) ] -> [ s ]
END

let pr_ltac_info n = str "Info" ++ spc () ++ int n

VERNAC ARGUMENT EXTEND ltac_info PRINTED BY pr_ltac_info
| [ "Info" natural(n) ] -> [ n ]
END

let pr_ltac_use_default b =
  if b then (* Bug: a space is inserted before "..." *) str ".." else mt ()

VERNAC ARGUMENT EXTEND ltac_use_default PRINTED BY pr_ltac_use_default
| [ "." ] -> [ false ]
| [ "..." ] -> [ true ]
END

let is_anonymous_abstract = function
  | TacAbstract (_,None) -> true
  | TacSolve [TacAbstract (_,None)] -> true
  | _ -> false
let rm_abstract = function
  | TacAbstract (t,_) -> t
  | TacSolve [TacAbstract (t,_)] -> TacSolve [t]
  | x -> x
let is_explicit_terminator = function TacSolve _ -> true | _ -> false

VERNAC tactic_mode EXTEND VernacSolve
| [ - ltac_selector_opt(g) ltac_info_opt(n) tactic(t) ltac_use_default(def) ] =>
    [ classify_as_proofstep ] -> [
    let g = Option.default (Goal_select.get_default_goal_selector ()) g in
    vernac_solve g n t def
  ]
| [ - "par" ":" ltac_info_opt(n) tactic(t) ltac_use_default(def) ] =>
    [
      let anon_abstracting_tac = is_anonymous_abstract t in
      let solving_tac = is_explicit_terminator t in
      let parallel = `Yes (solving_tac,anon_abstracting_tac) in
      let pbr = if solving_tac then Some "par" else None in
      VtProofStep{ parallel = parallel; proof_block_detection = pbr },
      VtLater
    ] -> [
      let t = rm_abstract t in
      vernac_solve Goal_select.SelectAll n t def
    ]
END

let pr_ltac_tactic_level n = str "(at level " ++ int n ++ str ")"

VERNAC ARGUMENT EXTEND ltac_tactic_level PRINTED BY pr_ltac_tactic_level
| [ "(" "at" "level" natural(n) ")" ] -> [ n ]
END

VERNAC ARGUMENT EXTEND ltac_production_sep
| [ "," string(sep) ] -> [ sep ]
END

let pr_ltac_production_item = function
| Tacentries.TacTerm s -> quote (str s)
| Tacentries.TacNonTerm (_, ((arg, None), None)) -> str arg
| Tacentries.TacNonTerm (_, ((arg, Some _), None)) -> assert false
| Tacentries.TacNonTerm (_, ((arg, sep), Some id)) ->
  let sep = match sep with
  | None -> mt ()
  | Some sep -> str "," ++ spc () ++ quote (str sep)
  in
  str arg ++ str "(" ++ Id.print id ++ sep ++ str ")"

VERNAC ARGUMENT EXTEND ltac_production_item PRINTED BY pr_ltac_production_item
| [ string(s) ] -> [ Tacentries.TacTerm s ]
| [ ident(nt) "(" ident(p) ltac_production_sep_opt(sep) ")" ] ->
  [ Tacentries.TacNonTerm (Loc.tag ~loc ((Id.to_string nt, sep), Some p)) ]
| [ ident(nt) ] ->
  [ Tacentries.TacNonTerm (Loc.tag ~loc ((Id.to_string nt, None), None)) ]
END

VERNAC COMMAND FUNCTIONAL EXTEND VernacTacticNotation
| [ "Tactic" "Notation" ltac_tactic_level_opt(n) ne_ltac_production_item_list(r) ":=" tactic(e) ] =>
  [ VtSideff [], VtNow ] ->
  [ fun ~atts ~st -> let open Vernacinterp in
      let n = Option.default 0 n in
      let deprecation = atts.deprecated in
      Tacentries.add_tactic_notation (Locality.make_module_locality atts.locality) n ?deprecation r e;
      st
  ]
END

VERNAC COMMAND EXTEND VernacPrintLtac CLASSIFIED AS QUERY
| [ "Print" "Ltac" reference(r) ] ->
  [ Feedback.msg_notice (Tacintern.print_ltac r) ]
END

VERNAC COMMAND EXTEND VernacLocateLtac CLASSIFIED AS QUERY
| [ "Locate" "Ltac" reference(r) ] ->
  [ Tacentries.print_located_tactic r ]
END

let pr_ltac_ref = Libnames.pr_qualid

let pr_tacdef_body tacdef_body =
  let id, redef, body =
    match tacdef_body with
    | TacticDefinition ({CAst.v=id}, body) -> Id.print id, false, body
    | TacticRedefinition (id, body) -> pr_ltac_ref id, true, body
  in
  let idl, body =
    match body with
      | Tacexpr.TacFun (idl,b) -> idl,b
      | _ -> [], body in
  id ++
    prlist (function Name.Anonymous -> str " _"
      | Name.Name id -> spc () ++ Id.print id) idl
  ++ (if redef then str" ::=" else str" :=") ++ brk(1,1)
  ++ Pptactic.pr_raw_tactic body

VERNAC ARGUMENT EXTEND ltac_tacdef_body
PRINTED BY pr_tacdef_body
| [ tacdef_body(t) ] -> [ t ]
END

VERNAC COMMAND FUNCTIONAL EXTEND VernacDeclareTacticDefinition
| [ "Ltac" ne_ltac_tacdef_body_list_sep(l, "with") ] => [
    VtSideff (List.map (function
      | TacticDefinition ({CAst.v=r},_) -> r
      | TacticRedefinition (qid,_) -> qualid_basename qid) l), VtLater
  ] -> [ fun ~atts ~st -> let open Vernacinterp in
           let deprecation = atts.deprecated in
           Tacentries.register_ltac (Locality.make_module_locality atts.locality) ?deprecation l;
           st
  ]
END

VERNAC COMMAND EXTEND VernacPrintLtacs CLASSIFIED AS QUERY
| [ "Print" "Ltac" "Signatures" ] -> [ Tacentries.print_ltacs () ]
END
