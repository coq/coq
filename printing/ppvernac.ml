(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Names

open CErrors
open Util
open Extend
open Vernacexpr
open Pputils
open Libnames
open Constrexpr
open Constrexpr_ops
open Decl_kinds

  open Ppconstr

  let do_not_tag _ x = x
  let tag_keyword = do_not_tag ()
  let tag_vernac  = do_not_tag

  let keyword s = tag_keyword (str s)

  let pr_constr = pr_constr_expr
  let pr_lconstr = pr_lconstr_expr
  let pr_spc_lconstr = pr_sep_com spc pr_lconstr_expr

  let pr_lident (loc,id) =
    match loc with
    | None     -> pr_id id
    | Some loc -> let (b,_) = Loc.unloc loc in
                  pr_located pr_id @@ Loc.tag ~loc:(Loc.make_loc (b,b + String.length (Id.to_string id))) id

  let pr_plident (lid, l) =
    pr_lident lid ++
    (match l with
     | Some l -> prlist_with_sep spc pr_lident l
     | None -> mt())
    
  let string_of_fqid fqid =
    String.concat "." (List.map Id.to_string fqid)

  let pr_fqid fqid = str (string_of_fqid fqid)

  let pr_lfqid (loc,fqid) =
    match loc with
    | None     -> pr_fqid fqid
    | Some loc -> let (b,_) = Loc.unloc loc in
                  pr_located pr_fqid @@ Loc.tag ~loc:(Loc.make_loc (b,b + String.length (string_of_fqid fqid))) fqid

  let pr_lname = function
    | (loc,Name id) -> pr_lident (loc,id)
    | lna -> pr_located pr_name lna

  let pr_smart_global = Pputils.pr_or_by_notation pr_reference

  let pr_ltac_ref = Libnames.pr_reference

  let pr_module = Libnames.pr_reference

  let pr_import_module = Libnames.pr_reference

  let sep_end = function
    | VernacBullet _
    | VernacSubproof None
    | VernacEndSubproof -> str""
    | _ -> str"."

  let pr_gen t = Pputils.pr_raw_generic (Global.env ()) t

  let sep = fun _ -> spc()
  let sep_v2 = fun _ -> str"," ++ spc()

  let pr_set_entry_type = function
    | ETName -> str"ident"
    | ETReference -> str"global"
    | ETPattern -> str"pattern"
    | ETConstr _ -> str"constr"
    | ETOther (_,e) -> str e
    | ETBigint -> str "bigint"
    | ETBinder true -> str "binder"
    | ETBinder false -> str "closed binder"
    | ETBinderList _ | ETConstrList _ -> failwith "Internal entry type"

  let pr_comment pr_c = function
    | CommentConstr c -> pr_c c
    | CommentString s -> qs s
    | CommentInt n -> int n

  let pr_in_out_modules = function
    | SearchInside l -> spc() ++ keyword "inside" ++ spc() ++ prlist_with_sep sep pr_module l
    | SearchOutside [] -> mt()
    | SearchOutside l -> spc() ++ keyword "outside" ++ spc() ++ prlist_with_sep sep pr_module l

  let pr_search_about (b,c) =
    (if b then str "-" else mt()) ++
      match c with
        | SearchSubPattern p -> pr_constr_pattern_expr p
        | SearchString (s,sc) -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc

  let pr_search a gopt b pr_p =
    pr_opt (fun g -> Proof_global.pr_goal_selector g ++ str ":"++ spc()) gopt
    ++
      match a with
      | SearchHead c -> keyword "SearchHead" ++ spc() ++ pr_p c ++ pr_in_out_modules b
      | SearchPattern c -> keyword "SearchPattern" ++ spc() ++ pr_p c ++ pr_in_out_modules b
      | SearchRewrite c -> keyword "SearchRewrite" ++ spc() ++ pr_p c ++ pr_in_out_modules b
      | SearchAbout sl ->
	 keyword "Search" ++ spc() ++ prlist_with_sep spc pr_search_about sl ++ pr_in_out_modules b

  let pr_locality local = if local then keyword "Local" else keyword "Global"

  let pr_explanation (e,b,f) =
    let a = match e with
      | ExplByPos (n,_) -> anomaly (Pp.str "No more supported")
      | ExplByName id -> pr_id id in
    let a = if f then str"!" ++ a else a in
    if b then str "[" ++ a ++ str "]" else a

  let pr_option_ref_value = function
    | QualidRefValue id -> pr_reference id
    | StringRefValue s -> qs s

  let pr_printoption table b =
    prlist_with_sep spc str table ++
      pr_opt (prlist_with_sep sep pr_option_ref_value) b

  let pr_set_option a b =
    let pr_opt_value = function
      | IntValue None -> assert false
    (* This should not happen because of the grammar *)
      | IntValue (Some n) -> spc() ++ int n
      | StringValue s -> spc() ++ str s
      | StringOptValue None -> mt()
      | StringOptValue (Some s) -> spc() ++ str s
      | BoolValue b -> mt()
    in pr_printoption a None ++ pr_opt_value b

  let pr_topcmd _ = str"(* <Warning> : No printer for toplevel commands *)"

  let pr_opt_hintbases l = match l with
    | [] -> mt()
    | _ as z -> str":" ++ spc() ++ prlist_with_sep sep str z

  let pr_reference_or_constr pr_c = function
    | HintsReference r -> pr_reference r
    | HintsConstr c -> pr_c c

  let pr_hint_mode = function
    | ModeInput -> str"+"
    | ModeNoHeadEvar -> str"!"
    | ModeOutput -> str"-"

  let pr_hint_info pr_pat { hint_priority = pri; hint_pattern = pat } =
    pr_opt (fun x -> str"|" ++ int x) pri ++
    pr_opt (fun y -> (if Option.is_empty pri then str"| " else mt()) ++ pr_pat y) pat

  let pr_hints db h pr_c pr_pat =
    let opth = pr_opt_hintbases db  in
    let pph =
      match h with
        | HintsResolve l ->
          keyword "Resolve " ++ prlist_with_sep sep
            (fun (info, _, c) -> pr_reference_or_constr pr_c c ++ pr_hint_info pr_pat info)
            l
        | HintsImmediate l ->
          keyword "Immediate" ++ spc() ++
            prlist_with_sep sep (fun c -> pr_reference_or_constr pr_c c) l
        | HintsUnfold l ->
          keyword "Unfold" ++ spc () ++ prlist_with_sep sep pr_reference l
        | HintsTransparency (l, b) ->
          keyword (if b then "Transparent" else "Opaque")
          ++ spc ()
          ++ prlist_with_sep sep pr_reference l
        | HintsMode (m, l) ->
          keyword "Mode"
          ++ spc ()
          ++ pr_reference m ++ spc() ++
            prlist_with_sep spc pr_hint_mode l
        | HintsConstructors c ->
          keyword "Constructors"
          ++ spc() ++ prlist_with_sep spc pr_reference c
        | HintsExtern (n,c,tac) ->
          let pat = match c with None -> mt () | Some pat -> pr_pat pat in
          keyword "Extern" ++ spc() ++ int n ++ spc() ++ pat ++ str" =>" ++
            spc() ++ Pputils.pr_raw_generic (Global.env ()) tac
    in
    hov 2 (keyword "Hint "++ pph ++ opth)

  let pr_with_declaration pr_c = function
    | CWith_Definition (id,c) ->
      let p = pr_c c in
      keyword "Definition" ++ spc() ++ pr_lfqid id ++ str" := " ++ p
    | CWith_Module (id,qid) ->
      keyword "Module" ++ spc() ++ pr_lfqid id ++ str" := " ++
        pr_located pr_qualid qid

  let rec pr_module_ast leading_space pr_c = let open CAst in function
    | { loc ; v = CMident qid } ->
      if leading_space then
        spc () ++ pr_located pr_qualid (loc, qid)
      else
        pr_located pr_qualid (loc,qid)
    | { v = CMwith (mty,decl) } ->
      let m = pr_module_ast leading_space pr_c mty in
      let p = pr_with_declaration pr_c decl in
      m ++ spc() ++ keyword "with" ++ spc() ++ p
    | { v = CMapply (me1, ( { v = CMident _ } as me2 ) ) } ->
      pr_module_ast leading_space pr_c me1 ++ spc() ++ pr_module_ast false pr_c me2
    | { v = CMapply (me1,me2) } ->
      pr_module_ast leading_space pr_c me1 ++ spc() ++
        hov 1 (str"(" ++ pr_module_ast false pr_c me2 ++ str")")

  let pr_inline = function
    | DefaultInline -> mt ()
    | NoInline -> str "[no inline]"
    | InlineAt i -> str "[inline at level " ++ int i ++ str "]"

  let pr_assumption_inline = function
    | DefaultInline -> str "Inline"
    | NoInline -> mt ()
    | InlineAt i -> str "Inline(" ++ int i ++ str ")"

  let pr_module_ast_inl leading_space pr_c (mast,inl) =
    pr_module_ast leading_space pr_c mast ++ pr_inline inl

  let pr_of_module_type prc = function
    | Enforce mty -> str ":" ++ pr_module_ast_inl true prc mty
    | Check mtys ->
      prlist_strict (fun m -> str "<:" ++ pr_module_ast_inl true prc m) mtys

  let pr_require_token = function
    | Some true ->
      keyword "Export" ++ spc ()
    | Some false ->
      keyword "Import" ++ spc ()
    | None -> mt()

  let pr_module_vardecls pr_c (export,idl,(mty,inl)) =
    let m = pr_module_ast true pr_c mty in
    spc() ++
      hov 1 (str"(" ++ pr_require_token export ++
               prlist_with_sep spc pr_lident idl ++ str":" ++ m ++ str")")

  let pr_module_binders l pr_c =
    prlist_strict (pr_module_vardecls pr_c) l

  let pr_type_option pr_c = function
    | { CAst.v = CHole (k, Misctypes.IntroAnonymous, _) } -> mt()
    | _ as c -> brk(0,2) ++ str" :" ++ pr_c c

  let pr_decl_notation prc ((loc,ntn),c,scopt) =
    fnl () ++ keyword "where " ++ qs ntn ++ str " := "
    ++ Flags.without_option Flags.beautify prc c ++
      pr_opt (fun sc -> str ": " ++ str sc) scopt

  let pr_binders_arg =
    pr_non_empty_arg pr_binders

  let pr_and_type_binders_arg bl =
    pr_binders_arg bl

  let pr_onescheme (idop,schem) =
    match schem with
      | InductionScheme (dep,ind,s) ->
        (match idop with
          | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
          | None -> spc ()
        ) ++
          hov 0 ((if dep then keyword "Induction for" else keyword "Minimality for")
                 ++ spc() ++ pr_smart_global ind) ++ spc() ++
          hov 0 (keyword "Sort" ++ spc() ++ pr_glob_sort s)
      | CaseScheme (dep,ind,s) ->
        (match idop with
          | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
          | None -> spc ()
        ) ++
          hov 0 ((if dep then keyword "Elimination for" else keyword "Case for")
                 ++ spc() ++ pr_smart_global ind) ++ spc() ++
          hov 0 (keyword "Sort" ++ spc() ++ pr_glob_sort s)
      | EqualityScheme ind ->
        (match idop with
          | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
          | None -> spc()
        ) ++
          hov 0 (keyword "Equality for")
        ++ spc() ++ pr_smart_global ind

  let begin_of_inductive = function
    | [] -> 0
    | (_,((loc,_),_))::_ -> Option.cata (fun loc -> fst (Loc.unloc loc)) 0 loc

  let pr_class_rawexpr = function
    | FunClass -> keyword "Funclass"
    | SortClass -> keyword "Sortclass"
    | RefClass qid -> pr_smart_global qid

  let pr_assumption_token many (l,a) =
    let l = match l with Some x -> x | None -> Decl_kinds.Global in
    match l, a with
      | (Discharge,Logical) ->
        keyword (if many then "Hypotheses" else "Hypothesis")
      | (Discharge,Definitional) ->
        keyword (if many then "Variables" else "Variable")
      | (Global,Logical) ->
        keyword (if many then "Axioms" else "Axiom")
      | (Global,Definitional) ->
        keyword (if many then "Parameters" else "Parameter")
      | (Local, Logical) ->
        keyword (if many then "Local Axioms" else "Local Axiom")
      | (Local,Definitional) ->
        keyword (if many then "Local Parameters" else "Local Parameter")
      | (Global,Conjectural) -> str"Conjecture"
      | ((Discharge | Local),Conjectural) ->
        anomaly (Pp.str "Don't know how to beautify a local conjecture")

  let pr_params pr_c (xl,(c,t)) =
    hov 2 (prlist_with_sep sep pr_lident xl ++ spc() ++
             (if c then str":>" else str":" ++
                 spc() ++ pr_c t))

  let rec factorize = function
    | [] -> []
    | (c,(idl,t))::l ->
      match factorize l with
        | (xl,((c', t') as r))::l'
            when (c : bool) == c' && Pervasives.(=) t t' ->
          (** FIXME: we need equality on constr_expr *)
          (idl@xl,r)::l'
        | l' -> (idl,(c,t))::l'

  let pr_ne_params_list pr_c l =
    match factorize l with
      | [p] -> pr_params pr_c p
      | l ->
        prlist_with_sep spc
          (fun p -> hov 1 (str "(" ++ pr_params pr_c p ++ str ")")) l

(*
  prlist_with_sep pr_semicolon (pr_params pr_c)
*)

  let pr_thm_token k = keyword (Kindops.string_of_theorem_kind k)

  let pr_syntax_modifier = function
    | SetItemLevel (l,NextLevel) ->
      prlist_with_sep sep_v2 str l ++
        spc() ++ keyword "at next level"
    | SetItemLevel (l,NumLevel n) ->
      prlist_with_sep sep_v2 str l ++
        spc() ++ keyword "at level" ++ spc() ++ int n
    | SetLevel n -> keyword "at level" ++ spc() ++ int n
    | SetAssoc LeftA -> keyword "left associativity"
    | SetAssoc RightA -> keyword "right associativity"
    | SetAssoc NonA -> keyword "no associativity"
    | SetEntryType (x,typ) -> str x ++ spc() ++ pr_set_entry_type typ
    | SetOnlyPrinting -> keyword "only printing"
    | SetOnlyParsing -> keyword "only parsing"
    | SetCompatVersion v -> keyword("compat \"" ^ Flags.pr_version v ^ "\"")
    | SetFormat("text",s) -> keyword "format " ++ pr_located qs s
    | SetFormat(k,s) -> keyword "format " ++ qs k ++ spc() ++ pr_located qs s

  let pr_syntax_modifiers = function
    | [] -> mt()
    | l -> spc() ++
      hov 1 (str"(" ++ prlist_with_sep sep_v2 pr_syntax_modifier l ++ str")")

  let pr_univs pl =
    match pl with
    | None -> mt ()
    | Some pl -> str"@{" ++ prlist_with_sep spc pr_lident pl ++ str"}"

  let pr_rec_definition ((((loc,id),pl),ro,bl,type_,def),ntn) =
    let pr_pure_lconstr c = Flags.without_option Flags.beautify pr_lconstr c in
    let annot = pr_guard_annot pr_lconstr_expr bl ro in
    pr_id id ++ pr_univs pl ++ pr_binders_arg bl ++ annot
    ++ pr_type_option (fun c -> spc() ++ pr_lconstr_expr c) type_
    ++ pr_opt (fun def -> str":=" ++ brk(1,2) ++ pr_pure_lconstr def) def
    ++ prlist (pr_decl_notation pr_constr) ntn

  let pr_statement head (idpl,(bl,c)) =
    assert (not (Option.is_empty idpl));
    let id, pl = Option.get idpl in
    hov 2
      (head ++ spc() ++ pr_lident id ++ pr_univs pl ++ spc() ++
         (match bl with [] -> mt() | _ -> pr_binders bl ++ spc()) ++
         str":" ++ pr_spc_lconstr c)

(**************************************)
(* Pretty printer for vernac commands *)
(**************************************)

  let pr_constrarg c = spc () ++ pr_constr c
  let pr_lconstrarg c = spc () ++ pr_lconstr c
  let pr_intarg n = spc () ++ int n

  let pr_oc = function
    | None -> str" :"
    | Some true -> str" :>"
    | Some false -> str" :>>"

  let pr_record_field ((x, pri), ntn) =
    let prx = match x with
      | (oc,AssumExpr (id,t)) ->
        hov 1 (pr_lname id ++
                 pr_oc oc ++ spc() ++
                 pr_lconstr_expr t)
      | (oc,DefExpr(id,b,opt)) -> (match opt with
          | Some t ->
            hov 1 (pr_lname id ++
                     pr_oc oc ++ spc() ++
                     pr_lconstr_expr t ++ str" :=" ++ pr_lconstr b)
          | None ->
            hov 1 (pr_lname id ++ str" :=" ++ spc() ++
                     pr_lconstr b)) in
    let prpri = match pri with None -> mt() | Some i -> str "| " ++ int i in
    prx ++ prpri ++ prlist (pr_decl_notation pr_constr) ntn

  let pr_record_decl b c fs =
    pr_opt pr_lident c ++ (if c = None then str"{" else str" {") ++
      hv 0 (prlist_with_sep pr_semicolon pr_record_field fs ++ str"}")

  let pr_printable = function
    | PrintFullContext ->
      keyword "Print All"
    | PrintSectionContext s ->
      keyword "Print Section" ++ spc() ++ Libnames.pr_reference s
    | PrintGrammar ent ->
      keyword "Print Grammar" ++ spc() ++ str ent
    | PrintLoadPath dir ->
      keyword "Print LoadPath" ++ pr_opt pr_dirpath dir
    | PrintModules ->
      keyword "Print Modules"
    | PrintMLLoadPath ->
      keyword "Print ML Path"
    | PrintMLModules ->
      keyword "Print ML Modules"
    | PrintDebugGC ->
      keyword "Print ML GC"
    | PrintGraph ->
      keyword "Print Graph"
    | PrintClasses ->
      keyword "Print Classes"
    | PrintTypeClasses ->
      keyword "Print TypeClasses"
    | PrintInstances qid ->
      keyword "Print Instances" ++ spc () ++ pr_smart_global qid
    | PrintCoercions ->
      keyword "Print Coercions"
    | PrintCoercionPaths (s,t) ->
      keyword "Print Coercion Paths" ++ spc()
      ++ pr_class_rawexpr s ++ spc()
      ++ pr_class_rawexpr t
    | PrintCanonicalConversions ->
      keyword "Print Canonical Structures"
    | PrintTables ->
      keyword "Print Tables"
    | PrintHintGoal ->
      keyword "Print Hint"
    | PrintHint qid ->
      keyword "Print Hint" ++ spc () ++ pr_smart_global qid
    | PrintHintDb ->
      keyword "Print Hint *"
    | PrintHintDbName s ->
      keyword "Print HintDb" ++ spc () ++ str s
    | PrintUniverses (b, fopt) ->
      let cmd =
        if b then "Print Sorted Universes"
        else "Print Universes"
      in
      keyword cmd ++ pr_opt str fopt
    | PrintName qid ->
      keyword "Print" ++ spc()  ++ pr_smart_global qid
    | PrintModuleType qid ->
      keyword "Print Module Type" ++ spc() ++ pr_reference qid
    | PrintModule qid ->
      keyword "Print Module" ++ spc() ++ pr_reference qid
    | PrintInspect n ->
      keyword "Inspect" ++ spc() ++ int n
    | PrintScopes ->
      keyword "Print Scopes"
    | PrintScope s ->
      keyword "Print Scope" ++ spc() ++ str s
    | PrintVisibility s ->
      keyword "Print Visibility" ++ pr_opt str s
    | PrintAbout (qid,gopt) ->
       pr_opt (fun g -> Proof_global.pr_goal_selector g ++ str ":"++ spc()) gopt
       ++ keyword "About" ++ spc()  ++ pr_smart_global qid
    | PrintImplicit qid ->
      keyword "Print Implicit" ++ spc()  ++ pr_smart_global qid
    (* spiwack: command printing all the axioms and section variables used in a
       term *)
    | PrintAssumptions (b, t, qid) ->
      let cmd = match b, t with
        | true, true -> "Print All Dependencies"
        | true, false -> "Print Opaque Dependencies"
        | false, true -> "Print Transparent Dependencies"
        | false, false -> "Print Assumptions"
      in
      keyword cmd ++ spc() ++ pr_smart_global qid
    | PrintNamespace dp ->
      keyword "Print Namespace" ++ pr_dirpath dp
    | PrintStrategy None ->
      keyword "Print Strategies"
    | PrintStrategy (Some qid) ->
      keyword "Print Strategy" ++ pr_smart_global qid

  let pr_using e = str (Proof_using.to_string e)

  let rec pr_vernac_body v =
    let return = tag_vernac v in
    match v with
      | VernacPolymorphic (poly, v) ->
        let s = if poly then keyword "Polymorphic" else keyword "Monomorphic" in
        return (s ++ spc () ++ pr_vernac_body v)
      | VernacProgram v ->
        return (keyword "Program" ++ spc() ++ pr_vernac_body v)
      | VernacLocal (local, v) ->
        return (pr_locality local ++ spc() ++ pr_vernac_body v)

      (* Stm *)
      | VernacStm JoinDocument ->
        return (keyword "Stm JoinDocument")
      | VernacStm Wait ->
        return (keyword "Stm Wait")

      (* Proof management *)
      | VernacAbortAll ->
        return (keyword "Abort All")
      | VernacRestart ->
        return (keyword "Restart")
      | VernacUnfocus ->
        return (keyword "Unfocus")
      | VernacUnfocused ->
        return (keyword "Unfocused")
      | VernacGoal c ->
        return (keyword "Goal" ++ pr_lconstrarg c)
      | VernacAbort id ->
        return (keyword "Abort" ++ pr_opt pr_lident id)
      | VernacUndo i ->
        return (
          if Int.equal i 1 then keyword "Undo" else keyword "Undo" ++ pr_intarg i
        )
      | VernacUndoTo i ->
        return (keyword "Undo" ++ spc() ++ keyword "To" ++ pr_intarg i)
      | VernacBacktrack (i,j,k) ->
        return (keyword "Backtrack" ++  spc() ++ prlist_with_sep sep int [i;j;k])
      | VernacFocus i ->
        return (keyword "Focus" ++ pr_opt int i)
      | VernacShow s ->
        let pr_goal_reference = function
          | OpenSubgoals -> mt ()
          | NthGoal n -> spc () ++ int n
          | GoalId id -> spc () ++ pr_id id
          | GoalUid n -> spc () ++ str n in
        let pr_showable = function
          | ShowGoal n -> keyword "Show" ++ pr_goal_reference n
          | ShowGoalImplicitly n -> keyword "Show Implicit Arguments" ++ pr_opt int n
          | ShowProof -> keyword "Show Proof"
          | ShowNode -> keyword "Show Node"
          | ShowScript -> keyword "Show Script"
          | ShowExistentials -> keyword "Show Existentials"
          | ShowUniverses -> keyword "Show Universes"
          | ShowTree -> keyword "Show Tree"
          | ShowProofNames -> keyword "Show Conjectures"
          | ShowIntros b -> keyword "Show " ++ (if b then keyword "Intros" else keyword "Intro")
          | ShowMatch id -> keyword "Show Match " ++ pr_reference id
          | ShowThesis -> keyword "Show Thesis"
        in
        return (pr_showable s)
      | VernacCheckGuard ->
        return (keyword "Guarded")

    (* Resetting *)
      | VernacResetName id ->
        return (keyword "Reset" ++ spc() ++ pr_lident id)
      | VernacResetInitial ->
        return (keyword "Reset Initial")
      | VernacBack i ->
        return (
          if Int.equal i 1 then keyword "Back" else keyword "Back" ++ pr_intarg i
        )
      | VernacBackTo i ->
        return (keyword "BackTo" ++ pr_intarg i)

    (* State management *)
      | VernacWriteState s ->
        return (keyword "Write State" ++ spc () ++ qs s)
      | VernacRestoreState s ->
        return  (keyword "Restore State" ++ spc() ++ qs s)

    (* Control *)
      | VernacLoad (f,s) ->
        return (
          keyword "Load"
          ++ if f then
              (spc() ++ keyword "Verbose" ++ spc())
            else
              spc() ++ qs s
        )
      | VernacTime (_,v) ->
        return (keyword "Time" ++ spc() ++ pr_vernac_body v)
      | VernacRedirect (s, (_,v)) ->
        return (keyword "Redirect" ++ spc() ++ qs s ++ spc() ++ pr_vernac_body v)
      | VernacTimeout(n,v) ->
        return (keyword "Timeout " ++ int n ++ spc() ++ pr_vernac_body v)
      | VernacFail v ->
        return (keyword "Fail" ++ spc() ++ pr_vernac_body v)

    (* Syntax *)
      | VernacOpenCloseScope (_,(opening,sc)) ->
        return (
          keyword (if opening then "Open " else "Close ") ++
            keyword "Scope" ++ spc() ++ str sc
        )
      | VernacDelimiters (sc,Some key) ->
        return (
          keyword "Delimit Scope" ++ spc () ++ str sc ++
            spc() ++ keyword "with" ++ spc () ++ str key
        )
      | VernacDelimiters (sc, None) ->
        return (
          keyword "Undelimit Scope" ++ spc () ++ str sc
        )
      | VernacBindScope (sc,cll) ->
        return (
          keyword "Bind Scope" ++ spc () ++ str sc ++
            spc() ++ keyword "with" ++ spc () ++ prlist_with_sep spc pr_class_rawexpr cll
        )
      | VernacArgumentsScope (q,scl) ->
        let pr_opt_scope = function
          | None -> str"_"
          | Some sc -> str sc
        in
        return (
          keyword "Arguments Scope"
          ++ spc() ++ pr_smart_global q
          ++ spc() ++ str"[" ++ prlist_with_sep sep pr_opt_scope scl ++ str"]"
        )
      | VernacInfix (_,((_,s),mv),q,sn) -> (* A Verifier *)
        return (
          hov 0 (hov 0 (keyword "Infix "
                        ++ qs s ++ str " :=" ++ pr_constrarg q) ++
                   pr_syntax_modifiers mv ++
                   (match sn with
                     | None -> mt()
                     | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
        )
      | VernacNotation (_,c,((_,s),l),opt) ->
        return (
          hov 2 (keyword "Notation" ++ spc() ++ qs s ++
                   str " :=" ++ Flags.without_option Flags.beautify pr_constrarg c ++ pr_syntax_modifiers l ++
                   (match opt with
                     | None -> mt()
                     | Some sc -> str" :" ++ spc() ++ str sc))
        )
      | VernacSyntaxExtension (_,(s,l)) ->
        return (
          keyword "Reserved Notation" ++ spc() ++ pr_located qs s ++
            pr_syntax_modifiers l
        )
      | VernacNotationAddFormat(s,k,v) ->
        return (
          keyword "Format Notation " ++ qs s ++ spc () ++ qs k ++ spc() ++ qs v
        )

      (* Gallina *)
      | VernacDefinition (d,id,b) -> (* A verifier... *)
        let pr_def_token (l,dk) =
          let l = match l with Some x -> x | None -> Decl_kinds.Global in
          keyword (Kindops.string_of_definition_kind (l,false,dk))
        in
        let pr_reduce = function
          | None -> mt()
          | Some r ->
            keyword "Eval" ++ spc() ++
              pr_red_expr (pr_constr, pr_lconstr, pr_smart_global, pr_constr) keyword r ++
              keyword " in" ++ spc()
        in
        let pr_def_body = function
          | DefineBody (bl,red,body,d) ->
            let ty = match d with
              | None -> mt()
              | Some ty -> spc() ++ str":" ++ pr_spc_lconstr ty
            in
            (pr_binders_arg bl,ty,Some (pr_reduce red ++ pr_lconstr body))
          | ProveBody (bl,t) ->
            (pr_binders_arg bl, str" :" ++ pr_spc_lconstr t, None) in
        let (binds,typ,c) = pr_def_body b in
        return (
          hov 2 (
            pr_def_token d ++ spc()
            ++ pr_plident id ++ binds ++ typ
            ++ (match c with
              | None -> mt()
              | Some cc -> str" :=" ++ spc() ++ cc))
        )

      | VernacStartTheoremProof (ki,l,_) ->
        return (
          hov 1 (pr_statement (pr_thm_token ki) (List.hd l) ++
                   prlist (pr_statement (spc () ++ keyword "with")) (List.tl l))
        )

      | VernacEndProof Admitted ->
        return (keyword "Admitted")

      | VernacEndProof (Proved (opac,o)) -> return (
        match o with
          | None -> (match opac with
              | Transparent -> keyword "Defined"
              | Opaque None -> keyword "Qed"
              | Opaque (Some l) ->
                  keyword "Qed" ++ spc() ++ str"export" ++
                    prlist_with_sep (fun () -> str", ") pr_lident l)
          | Some id -> (if opac <> Transparent then keyword "Save" else keyword "Defined") ++ spc() ++ pr_lident id
      )
      | VernacExactProof c ->
        return (hov 2 (keyword "Proof" ++ pr_lconstrarg c))
      | VernacAssumption (stre,t,l) ->
        let n = List.length (List.flatten (List.map fst (List.map snd l))) in
        let pr_params (c, (xl, t)) =
          hov 2 (prlist_with_sep sep pr_plident xl ++ spc() ++
            (if c then str":>" else str":" ++ spc() ++ pr_lconstr_expr t)) in
        let assumptions = prlist_with_sep spc (fun p -> hov 1 (str "(" ++ pr_params p ++ str ")")) l in
        return (hov 2 (pr_assumption_token (n > 1) stre ++
                       pr_non_empty_arg pr_assumption_inline t ++ spc() ++ assumptions))
      | VernacInductive (p,f,l) ->
        let pr_constructor (coe,(id,c)) =
          hov 2 (pr_lident id ++ str" " ++
                   (if coe then str":>" else str":") ++
                   Flags.without_option Flags.beautify pr_spc_lconstr c)
        in
        let pr_constructor_list b l = match l with
          | Constructors [] -> mt()
          | Constructors l ->
            let fst_sep = match l with [_] -> "   " | _ -> " | " in
            pr_com_at (begin_of_inductive l) ++
              fnl() ++ str fst_sep ++
              prlist_with_sep (fun _ -> fnl() ++ str" | ") pr_constructor l
          | RecordDecl (c,fs) ->
            pr_record_decl b c fs
        in
        let pr_oneind key (((coe,(id,pl)),indpar,s,k,lc),ntn) =
          hov 0 (
            str key ++ spc() ++
              (if coe then str"> " else str"") ++ pr_lident id ++ pr_univs pl ++
              pr_and_type_binders_arg indpar ++
              pr_opt (fun s -> str":" ++ spc() ++ pr_lconstr_expr s) s ++
              str" :=") ++ pr_constructor_list k lc ++
            prlist (pr_decl_notation pr_constr) ntn
        in
        let key =
          let (_,_,_,k,_),_ = List.hd l in
          match k with Record -> "Record" | Structure -> "Structure"
            | Inductive_kw -> "Inductive" | CoInductive -> "CoInductive"
            | Class _ -> "Class" | Variant -> "Variant"
        in
        return (
          hov 1 (pr_oneind key (List.hd l)) ++
            (prlist (fun ind -> fnl() ++ hov 1 (pr_oneind "with" ind)) (List.tl l))
        )

      | VernacFixpoint (local, recs) ->
        let local = match local with
          | Some Discharge -> "Let "
          | Some Local -> "Local "
          | None | Some Global -> ""
        in
        return (
          hov 0 (str local ++ keyword "Fixpoint" ++ spc () ++
                   prlist_with_sep (fun _ -> fnl () ++ keyword "with"
                     ++ spc ()) pr_rec_definition recs)
        )

      | VernacCoFixpoint (local, corecs) ->
        let local = match local with
          | Some Discharge -> keyword "Let" ++ spc ()
          | Some Local -> keyword "Local" ++ spc ()
          | None | Some Global -> str ""
        in
        let pr_onecorec ((((loc,id),pl),bl,c,def),ntn) =
          pr_id id ++ pr_univs pl ++ spc() ++ pr_binders bl ++ spc() ++ str":" ++
            spc() ++ pr_lconstr_expr c ++
            pr_opt (fun def -> str":=" ++ brk(1,2) ++ pr_lconstr def) def ++
            prlist (pr_decl_notation pr_constr) ntn
        in
        return (
          hov 0 (local ++ keyword "CoFixpoint" ++ spc() ++
                   prlist_with_sep (fun _ -> fnl() ++ keyword "with" ++ spc ()) pr_onecorec corecs)
        )
      | VernacScheme l ->
        return (
          hov 2 (keyword "Scheme" ++ spc() ++
                   prlist_with_sep (fun _ -> fnl() ++ keyword "with" ++ spc ()) pr_onescheme l)
        )
      | VernacCombinedScheme (id, l) ->
        return (
          hov 2 (keyword "Combined Scheme" ++ spc() ++
                   pr_lident id ++ spc() ++ keyword "from" ++ spc() ++
                   prlist_with_sep (fun _ -> fnl() ++ str", ") pr_lident l)
        )
      | VernacUniverse v ->
        return (
          hov 2 (keyword "Universe" ++ spc () ++
                   prlist_with_sep (fun _ -> str",") pr_lident v)
        )
      | VernacConstraint v ->
        let pr_uconstraint (l, d, r) =
          pr_glob_level l ++ spc () ++ Univ.pr_constraint_type d ++ spc () ++
            pr_glob_level r
        in
        return (
          hov 2 (keyword "Constraint" ++ spc () ++
                   prlist_with_sep (fun _ -> str",") pr_uconstraint v)
        )

      (* Gallina extensions *)
      | VernacBeginSection id ->
        return (hov 2 (keyword "Section" ++ spc () ++ pr_lident id))
      | VernacEndSegment id ->
        return (hov 2 (keyword "End" ++ spc() ++ pr_lident id))
      | VernacNameSectionHypSet (id,set) ->
        return (hov 2 (keyword "Package" ++ spc() ++ pr_lident id ++ spc()++
        str ":="++spc()++pr_using set))
      | VernacRequire (from, exp, l) ->
        let from = match from with
        | None -> mt ()
        | Some r -> keyword "From" ++ spc () ++ pr_module r ++ spc ()
        in
        return (
          hov 2
            (from ++ keyword "Require" ++ spc() ++ pr_require_token exp ++
               prlist_with_sep sep pr_module l)
        )
      | VernacImport (f,l) ->
        return (
          (if f then keyword "Export" else keyword "Import") ++ spc() ++
            prlist_with_sep sep pr_import_module l
        )
      | VernacCanonical q ->
        return (
          keyword "Canonical Structure" ++ spc() ++ pr_smart_global q
        )
      | VernacCoercion (_,id,c1,c2) ->
        return (
          hov 1 (
            keyword "Coercion" ++ spc() ++
              pr_smart_global id ++ spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++
              spc() ++ str">->" ++ spc() ++ pr_class_rawexpr c2)
        )
      | VernacIdentityCoercion (_,id,c1,c2) ->
        return (
          hov 1 (
            keyword "Identity Coercion" ++ spc() ++ pr_lident id ++
              spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++ spc() ++ str">->" ++
              spc() ++ pr_class_rawexpr c2)
        )

      | VernacInstance (abst, sup, (instid, bk, cl), props, info) ->
        return (
          hov 1 (
            (if abst then keyword "Declare" ++ spc () else mt ()) ++
              keyword "Instance" ++
              (match instid with
      	 | (loc, Name id), l -> spc () ++ pr_plident ((loc, id),l) ++ spc () 
               | (_, Anonymous), _ -> mt ()) ++
              pr_and_type_binders_arg sup ++
              str":" ++ spc () ++
              (match bk with Implicit -> str "! " | Explicit -> mt ()) ++
              pr_constr cl ++ pr_hint_info pr_constr_pattern_expr info ++
              (match props with
                | Some (true, { CAst.v = CRecord l}) -> spc () ++ str":=" ++ spc () ++ str"{" ++ pr_record_body l ++ str "}"
                | Some (true,_) -> assert false
                | Some (false,p) -> spc () ++ str":=" ++ spc () ++ pr_constr p
                | None -> mt()))
        )

      | VernacContext l ->
        return (
          hov 1 (
            keyword "Context" ++ pr_and_type_binders_arg l)
        )

      | VernacDeclareInstances insts ->
         let pr_inst (id, info) =
           pr_reference id ++ pr_hint_info pr_constr_pattern_expr info
         in
         return (
          hov 1 (keyword "Existing" ++ spc () ++
                   keyword(String.plural (List.length insts) "Instance") ++
                 spc () ++ prlist_with_sep (fun () -> str", ") pr_inst insts)
        )

      | VernacDeclareClass id ->
        return (
          hov 1 (keyword "Existing" ++ spc () ++ keyword "Class" ++ spc () ++ pr_reference id)
        )

      (* Modules and Module Types *)
      | VernacDefineModule (export,m,bl,tys,bd) ->
        let b = pr_module_binders bl pr_lconstr in
        return (
          hov 2 (keyword "Module" ++ spc() ++ pr_require_token export ++
                   pr_lident m ++ b ++
                   pr_of_module_type pr_lconstr tys ++
                   (if List.is_empty bd then mt () else str ":= ") ++
                   prlist_with_sep (fun () -> str " <+")
                   (pr_module_ast_inl true pr_lconstr) bd)
        )
      | VernacDeclareModule (export,id,bl,m1) ->
        let b = pr_module_binders bl pr_lconstr in
        return (
          hov 2 (keyword "Declare Module" ++ spc() ++ pr_require_token export ++
                   pr_lident id ++ b ++ str " :" ++
                   pr_module_ast_inl true pr_lconstr m1)
        )
      | VernacDeclareModuleType (id,bl,tyl,m) ->
        let b = pr_module_binders bl pr_lconstr in
        let pr_mt = pr_module_ast_inl true pr_lconstr in
        return (
          hov 2 (keyword "Module Type " ++ pr_lident id ++ b ++
                   prlist_strict (fun m -> str " <:" ++ pr_mt m) tyl ++
                   (if List.is_empty m then mt () else str ":= ") ++
                   prlist_with_sep (fun () -> str " <+ ") pr_mt m)
        )
      | VernacInclude (mexprs) ->
        let pr_m = pr_module_ast_inl false pr_lconstr in
        return (
          hov 2 (keyword "Include" ++ spc() ++
                   prlist_with_sep (fun () -> str " <+ ") pr_m mexprs)
        )
      (* Solving *)
      | VernacSolveExistential (i,c) ->
        return (keyword "Existential" ++ spc () ++ int i ++ pr_lconstrarg c)

      (* Auxiliary file and library management *)
      | VernacAddLoadPath (fl,s,d) ->
        return (
          hov 2
            (keyword "Add" ++
               (if fl then spc () ++ keyword "Rec" ++ spc () else spc()) ++
               keyword "LoadPath" ++ spc() ++ qs s ++
               (match d with
                 | None -> mt()
                 | Some dir -> spc() ++ keyword "as" ++ spc() ++ pr_dirpath dir))
        )
      | VernacRemoveLoadPath s ->
        return (keyword "Remove LoadPath" ++ qs s)
      | VernacAddMLPath (fl,s) ->
        return (
          keyword "Add"
          ++ (if fl then spc () ++ keyword "Rec" ++ spc () else spc())
          ++ keyword "ML Path"
          ++ qs s
        )
      | VernacDeclareMLModule (l) ->
        return (
          hov 2 (keyword "Declare ML Module" ++ spc() ++ prlist_with_sep sep qs l)
        )
      | VernacChdir s ->
        return (keyword "Cd" ++ pr_opt qs s)

      (* Commands *)
      | VernacCreateHintDb (dbname,b) ->
        return (
          hov 1 (keyword "Create HintDb" ++ spc () ++
                   str dbname ++ (if b then str" discriminated" else mt ()))
        )
      | VernacRemoveHints (dbnames, ids) ->
        return (
          hov 1 (keyword "Remove Hints" ++ spc () ++
                   prlist_with_sep spc (fun r -> pr_id (coerce_reference_to_id r)) ids ++
                   pr_opt_hintbases dbnames)
        )
      | VernacHints (_, dbnames,h) ->
        return (pr_hints dbnames h pr_constr pr_constr_pattern_expr)
      | VernacSyntacticDefinition (id,(ids,c),_,compat) ->
        return (
          hov 2
            (keyword "Notation" ++ spc () ++ pr_lident id ++ spc () ++
               prlist_with_sep spc pr_id ids ++ str":=" ++ pr_constrarg c ++
               pr_syntax_modifiers
               (match compat with
                | None -> []
                | Some Flags.Current -> [SetOnlyParsing]
                | Some v -> [SetCompatVersion v]))
        )
      | VernacDeclareImplicits (q,[]) ->
        return (
          hov 2 (keyword "Implicit Arguments" ++ spc() ++ pr_smart_global q)
        )
      | VernacDeclareImplicits (q,impls) ->
        return (
          hov 1 (keyword "Implicit Arguments" ++ spc () ++
                   spc() ++ pr_smart_global q ++ spc() ++
                   prlist_with_sep spc (fun imps ->
                     str"[" ++ prlist_with_sep sep pr_explanation imps ++ str"]")
                   impls)
        )
      | VernacArguments (q, args, more_implicits, nargs, mods) ->
        return (
          hov 2 (
            keyword "Arguments" ++ spc() ++
              pr_smart_global q ++
              let pr_s = function None -> str"" | Some (_,s) -> str "%" ++ str s in
              let pr_if b x = if b then x else str "" in
              let pr_br imp x = match imp with
                | Vernacexpr.Implicit -> str "[" ++ x ++ str "]"
                | Vernacexpr.MaximallyImplicit -> str "{" ++ x ++ str "}"
                | Vernacexpr.NotImplicit -> x in
              let rec print_arguments n l =
                match n, l with
                  | Some 0, l -> spc () ++ str"/" ++ print_arguments None l
                  | _, [] -> mt()
                  | n, { name = id; recarg_like = k;
                         notation_scope = s;
                         implicit_status = imp } :: tl ->
                    spc() ++ pr_br imp (pr_if k (str"!") ++ pr_name id ++ pr_s s) ++
                      print_arguments (Option.map pred n) tl
              in
              let rec print_implicits = function
                | [] -> mt ()
                | (name, impl) :: rest ->
                   spc() ++ pr_br impl (pr_name name) ++ print_implicits rest
              in
              print_arguments nargs args ++
                if not (List.is_empty more_implicits) then
                  prlist (fun l -> str"," ++ print_implicits l) more_implicits
                else (mt ()) ++
                (if not (List.is_empty mods) then str" : " else str"") ++
                  prlist_with_sep (fun () -> str", " ++ spc()) (function
                    | `ReductionDontExposeCase -> keyword "simpl nomatch"
                    | `ReductionNeverUnfold -> keyword "simpl never"
                    | `DefaultImplicits -> keyword "default implicits"
                    | `Rename -> keyword "rename"
                    | `Assert -> keyword "assert"
                    | `ExtraScopes -> keyword "extra scopes"
                    | `ClearImplicits -> keyword "clear implicits"
                    | `ClearScopes -> keyword "clear scopes")
                  mods)
        )
      | VernacReserve bl ->
        let n = List.length (List.flatten (List.map fst bl)) in
        return (
          hov 2 (tag_keyword (str"Implicit Type" ++ str (if n > 1 then "s " else " "))
                 ++ pr_ne_params_list pr_lconstr_expr (List.map (fun sb -> false,sb) bl))
        )
      | VernacGeneralizable g ->
        return (
          hov 1 (tag_keyword (
            str"Generalizable Variable" ++
              match g with
                | None -> str "s none"
                | Some [] -> str "s all"
                | Some idl ->
                  str (if List.length idl > 1 then "s " else " ") ++
                    prlist_with_sep spc pr_lident idl)
          ))
      | VernacSetOpacity(k,l) when Conv_oracle.is_transparent k ->
        return (
          hov 1 (keyword "Transparent" ++
                   spc() ++ prlist_with_sep sep pr_smart_global l)
        )
      | VernacSetOpacity(Conv_oracle.Opaque,l) ->
        return (
          hov 1 (keyword "Opaque" ++
                   spc() ++ prlist_with_sep sep pr_smart_global l)
        )
      | VernacSetOpacity _ ->
        return (
          CErrors.anomaly (keyword "VernacSetOpacity used to set something else")
        )
      | VernacSetStrategy l ->
        let pr_lev = function
          | Conv_oracle.Opaque -> keyword "opaque"
          | Conv_oracle.Expand -> keyword "expand"
          | l when Conv_oracle.is_transparent l -> keyword "transparent"
          | Conv_oracle.Level n -> int n
        in
        let pr_line (l,q) =
          hov 2 (pr_lev l ++ spc() ++
                   str"[" ++ prlist_with_sep sep pr_smart_global q ++ str"]")
        in
        return (
          hov 1 (keyword "Strategy" ++ spc() ++
                   hv 0 (prlist_with_sep sep pr_line l))
        )
      | VernacUnsetOption (na) ->
        return (
          hov 1 (keyword "Unset" ++ spc() ++ pr_printoption na None)
        )
      | VernacSetOption (na,v) ->
        return (
          hov 2 (keyword "Set" ++ spc() ++ pr_set_option na v)
        )
      | VernacSetAppendOption (na,v) ->
        return (
          hov 2 (keyword "Set" ++ spc() ++ pr_printoption na None ++
                   spc() ++ keyword "Append" ++ spc() ++ qs v)
        )
      | VernacAddOption (na,l) ->
        return (
          hov 2 (keyword "Add" ++ spc() ++ pr_printoption na (Some l))
        )
      | VernacRemoveOption (na,l) ->
        return (
          hov 2 (keyword "Remove" ++ spc() ++ pr_printoption na (Some l))
        )
      | VernacMemOption (na,l) ->
        return (
          hov 2 (keyword "Test" ++ spc() ++ pr_printoption na (Some l))
        )
      | VernacPrintOption na ->
        return (
          hov 2 (keyword "Test" ++ spc() ++ pr_printoption na None)
        )
      | VernacCheckMayEval (r,io,c) ->
        let pr_mayeval r c = match r with
          | Some r0 ->
            hov 2 (keyword "Eval" ++ spc() ++
                     pr_red_expr (pr_constr,pr_lconstr,pr_smart_global, pr_constr) keyword r0 ++
                     spc() ++ keyword "in" ++ spc () ++ pr_lconstr c)
          | None -> hov 2 (keyword "Check" ++ spc() ++ pr_lconstr c)
        in
        let pr_i = match io with None -> mt ()
                               | Some i -> Proof_global.pr_goal_selector i ++ str ": " in
        return (pr_i ++ pr_mayeval r c)
      | VernacGlobalCheck c ->
        return (hov 2 (keyword "Type" ++ pr_constrarg c))
      | VernacDeclareReduction (s,r) ->
        return (
          keyword "Declare Reduction" ++ spc () ++ str s ++ str " := " ++
            pr_red_expr (pr_constr,pr_lconstr,pr_smart_global, pr_constr) keyword r
        )
      | VernacPrint p ->
        return (pr_printable p)
      | VernacSearch (sea,g,sea_r) ->
        return (pr_search sea g sea_r pr_constr_pattern_expr)
      | VernacLocate loc ->
        let pr_locate =function
          | LocateAny qid -> pr_smart_global qid
          | LocateTerm qid -> keyword "Term" ++ spc() ++ pr_smart_global qid
          | LocateFile f -> keyword "File" ++ spc() ++ qs f
          | LocateLibrary qid -> keyword "Library" ++ spc () ++ pr_module qid
          | LocateModule qid -> keyword "Module" ++ spc () ++ pr_module qid
          | LocateTactic qid -> keyword "Ltac" ++ spc () ++ pr_ltac_ref qid
        in
        return (keyword "Locate" ++ spc() ++ pr_locate loc)
      | VernacRegister (id, RegisterInline) ->
        return (
          hov 2
            (keyword "Register Inline" ++ spc() ++ pr_lident id)
        )
      | VernacComments l ->
        return (
          hov 2
            (keyword "Comments" ++ spc()
             ++ prlist_with_sep sep (pr_comment pr_constr) l)
        )

      (* Toplevel control *)
      | VernacToplevelControl exn ->
        return (pr_topcmd exn)

      (* For extension *)
      | VernacExtend (s,c) ->
        return (pr_extend s c)
      | VernacProof (None, None) ->
        return (keyword "Proof")
      | VernacProof (None, Some e) ->
        return (keyword "Proof " ++ spc () ++
            keyword "using" ++ spc() ++ pr_using e)
      | VernacProof (Some te, None) ->
        return (keyword "Proof with" ++ spc() ++ Pputils.pr_raw_generic (Global.env ()) te)
      | VernacProof (Some te, Some e) ->
        return (
          keyword "Proof" ++ spc () ++
            keyword "using" ++ spc() ++ pr_using e ++ spc() ++
            keyword "with" ++ spc() ++ Pputils.pr_raw_generic (Global.env ()) te
        )
      | VernacProofMode s ->
        return (keyword "Proof Mode" ++ str s)
      | VernacBullet b ->
        return (begin match b with
          | Dash n -> str (String.make n '-')
          | Star n -> str (String.make n '*')
          | Plus n -> str (String.make n '+')
        end)
      | VernacSubproof None ->
        return (str "{")
      | VernacSubproof (Some i) ->
        return (keyword "BeginSubproof" ++ spc () ++ int i)
      | VernacEndSubproof ->
        return (str "}")

  and pr_extend s cl =
    let pr_arg a =
      try pr_gen a
      with Failure _ -> str "<error in " ++ str (fst s) ++ str ">" in
    try
      let rl = Egramml.get_extend_vernac_rule s in
      let rec aux rl cl =
        match rl, cl with
        | Egramml.GramNonTerminal _ :: rl, arg :: cl -> pr_arg arg :: aux rl cl
        | Egramml.GramTerminal s :: rl, cl -> str s :: aux rl cl
        | [], [] -> []
        | _ -> assert false in
      hov 1 (pr_sequence identity (aux rl cl))
    with Not_found ->
      hov 1 (str "TODO(" ++ str (fst s) ++ spc () ++ prlist_with_sep sep pr_arg cl ++ str ")")

  let pr_vernac v =
    try pr_vernac_body v ++ sep_end v
    with e -> CErrors.print e
