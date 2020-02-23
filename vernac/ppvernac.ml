(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Names

open CErrors
open Util
open CAst

open Extend
open Constrexpr
open Constrexpr_ops
open Vernacexpr
open Declaremods
open Pputils

  open Ppconstr

  let do_not_tag _ x = x
  let tag_keyword = do_not_tag ()
  let tag_vernac  = do_not_tag

  let keyword s = tag_keyword (str s)

  let pr_constr = pr_constr_expr
  let pr_lconstr = pr_lconstr_expr
  let pr_spc_lconstr =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    pr_sep_com spc @@ pr_lconstr_expr env sigma

  let pr_uconstraint (l, d, r) =
    pr_glob_sort_name l ++ spc () ++ Univ.pr_constraint_type d ++ spc () ++
      pr_glob_sort_name r

  let pr_univ_name_list = function
    | None -> mt ()
    | Some l ->
      str "@{" ++ prlist_with_sep spc pr_lname l ++ str"}"

  let pr_univdecl_instance l extensible =
    prlist_with_sep spc pr_lident l ++
    (if extensible then str"+" else mt ())

  let pr_univdecl_constraints l extensible =
    if List.is_empty l && extensible then mt ()
    else str"|" ++ spc () ++ prlist_with_sep (fun () -> str",") pr_uconstraint l ++
           (if extensible then str"+" else mt())

  let pr_universe_decl l =
    let open UState in
    match l with
    | None -> mt ()
    | Some l ->
      str"@{" ++ pr_univdecl_instance l.univdecl_instance l.univdecl_extensible_instance ++
        pr_univdecl_constraints l.univdecl_constraints l.univdecl_extensible_constraints ++ str "}"

  let pr_ident_decl (lid, l) =
    pr_lident lid ++ pr_universe_decl l

  let string_of_fqid fqid =
    String.concat "." (List.map Id.to_string fqid)

  let pr_fqid fqid = str (string_of_fqid fqid)

  let pr_lfqid {CAst.loc;v=fqid} =
    match loc with
    | None     -> pr_fqid fqid
    | Some loc -> let (b,_) = Loc.unloc loc in
                  pr_located pr_fqid @@ Loc.tag ~loc:(Loc.make_loc (b,b + String.length (string_of_fqid fqid))) fqid

  let pr_lname_decl (n, u) =
    pr_lname n ++ pr_universe_decl u

  let pr_smart_global = Pputils.pr_or_by_notation pr_qualid

  let pr_ltac_ref = Libnames.pr_qualid

  let pr_module = Libnames.pr_qualid

  let pr_import_module = Libnames.pr_qualid

  let sep_end = function
    | VernacBullet _
    | VernacSubproof _
    | VernacEndSubproof -> str""
    | _ -> str"."

  let pr_gen t =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Pputils.pr_raw_generic env sigma t

  let sep = fun _ -> spc()
  let sep_v2 = fun _ -> str"," ++ spc()

  let pr_notation_entry = function
    | InConstrEntry -> keyword "constr"
    | InCustomEntry s -> keyword "custom" ++ spc () ++ str s

  let pr_at_level = function
    | NumLevel n -> spc () ++ keyword "at" ++ spc () ++ keyword "level" ++ spc () ++ int n
    | NextLevel -> spc () ++ keyword "at" ++ spc () ++ keyword "next" ++ spc () ++ keyword "level"
    | DefaultLevel -> mt ()

  let level_of_pattern_level = function None -> DefaultLevel | Some n -> NumLevel n

  let pr_constr_as_binder_kind = let open Notation_term in function
    | AsIdent -> spc () ++ keyword "as ident"
    | AsIdentOrPattern -> spc () ++ keyword "as pattern"
    | AsStrictPattern -> spc () ++ keyword "as strict pattern"

  let pr_strict b = if b then str "strict " else mt ()

  let pr_set_entry_type pr = function
    | ETIdent -> str"ident"
    | ETGlobal -> str"global"
    | ETPattern (b,n) -> pr_strict b ++ str"pattern" ++ pr_at_level (level_of_pattern_level n)
    | ETConstr (s,bko,lev) -> pr_notation_entry s ++ pr lev ++ pr_opt pr_constr_as_binder_kind bko
    | ETBigint -> str "bigint"
    | ETString -> str "string"
    | ETBinder true -> str "binder"
    | ETBinder false -> str "closed binder"

  let pr_set_simple_entry_type =
    pr_set_entry_type pr_at_level

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
        | SearchSubPattern p ->
          let env = Global.env () in
          let sigma = Evd.from_env env in
          pr_constr_pattern_expr env sigma p
        | SearchString (s,sc) -> qs s ++ pr_opt (fun sc -> str "%" ++ str sc) sc

  let pr_search a gopt b pr_p =
    pr_opt (fun g -> Goal_select.pr_goal_selector g ++ str ":"++ spc()) gopt
    ++
      match a with
      | SearchHead c -> keyword "SearchHead" ++ spc() ++ pr_p c ++ pr_in_out_modules b
      | SearchPattern c -> keyword "SearchPattern" ++ spc() ++ pr_p c ++ pr_in_out_modules b
      | SearchRewrite c -> keyword "SearchRewrite" ++ spc() ++ pr_p c ++ pr_in_out_modules b
      | SearchAbout sl ->
         keyword "SearchAbout" ++ spc() ++ prlist_with_sep spc pr_search_about sl ++ pr_in_out_modules b
      | Search sl ->
         keyword "Search" ++ spc() ++ prlist_with_sep spc pr_search_about sl ++ pr_in_out_modules b

  let pr_option_ref_value = function
    | QualidRefValue id -> pr_qualid id
    | StringRefValue s -> qs s

  let pr_printoption table b =
    prlist_with_sep spc str table ++
      pr_opt (prlist_with_sep sep pr_option_ref_value) b

  let pr_set_option a b =
    pr_printoption a None ++ (match b with
        | OptionUnset | OptionSetTrue -> mt()
        | OptionSetInt n -> spc() ++ int n
        | OptionSetString s -> spc() ++ quote (str s))

  let pr_opt_hintbases l = match l with
    | [] -> mt()
    | _ as z -> str":" ++ spc() ++ prlist_with_sep sep str z

  let pr_reference_or_constr pr_c = let open Hints in function
    | HintsReference r -> pr_qualid r
    | HintsConstr c -> pr_c c

  let pr_hint_mode = let open Hints in function
    | ModeInput -> str"+"
    | ModeNoHeadEvar -> str"!"
    | ModeOutput -> str"-"

  let pr_hint_info pr_pat { Typeclasses.hint_priority = pri; hint_pattern = pat } =
    pr_opt (fun x -> str"|" ++ int x) pri ++
    pr_opt (fun y -> (if Option.is_empty pri then str"| " else mt()) ++ pr_pat y) pat

  let pr_hints db h pr_c pr_pat =
    let opth = pr_opt_hintbases db  in
    let pph =
      let open Hints in
      match h with
        | HintsResolve l ->
          keyword "Resolve " ++ prlist_with_sep sep
            (fun (info, _, c) -> pr_reference_or_constr pr_c c ++ pr_hint_info pr_pat info)
            l
        | HintsResolveIFF (l2r, l, n) ->
          keyword "Resolve " ++ str (if l2r then "->" else "<-")
          ++ prlist_with_sep sep pr_qualid l
        | HintsImmediate l ->
          keyword "Immediate" ++ spc() ++
            prlist_with_sep sep (fun c -> pr_reference_or_constr pr_c c) l
        | HintsUnfold l ->
          keyword "Unfold" ++ spc () ++ prlist_with_sep sep pr_qualid l
        | HintsTransparency (l, b) ->
          keyword (if b then "Transparent" else "Opaque")
          ++ spc ()
          ++ (match l with
              | HintsVariables -> keyword "Variables"
              | HintsConstants -> keyword "Constants"
              | HintsReferences l -> prlist_with_sep sep pr_qualid l)
        | HintsMode (m, l) ->
          keyword "Mode"
          ++ spc ()
          ++ pr_qualid m ++ spc() ++
            prlist_with_sep spc pr_hint_mode l
        | HintsConstructors c ->
          keyword "Constructors"
          ++ spc() ++ prlist_with_sep spc pr_qualid c
        | HintsExtern (n,c,tac) ->
          let pat = match c with None -> mt () | Some pat -> pr_pat pat in
          let env = Global.env () in
          let sigma = Evd.from_env env in
          keyword "Extern" ++ spc() ++ int n ++ spc() ++ pat ++ str" =>" ++
            spc() ++ Pputils.pr_raw_generic env sigma tac
    in
    hov 2 (keyword "Hint "++ pph ++ opth)

  let pr_with_declaration pr_c = function
    | CWith_Definition (id,udecl,c) ->
      let p = pr_c c in
      keyword "Definition" ++ spc() ++ pr_lfqid id ++ pr_universe_decl udecl ++ str" := " ++ p
    | CWith_Module (id,qid) ->
      keyword "Module" ++ spc() ++ pr_lfqid id ++ str" := " ++
        pr_qualid qid

  let rec pr_module_ast leading_space pr_c = function
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
    | { v = CHole (k, Namegen.IntroAnonymous, _) } -> mt()
    | _ as c -> brk(0,2) ++ str" :" ++ pr_c c

  let pr_decl_notation prc ({loc; v=ntn},c,scopt) =
    fnl () ++ keyword "where " ++ qs ntn ++ str " := "
    ++ Flags.without_option Flags.beautify prc c ++
      pr_opt (fun sc -> str ": " ++ str sc) scopt

  let pr_binders_arg =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    pr_non_empty_arg @@ pr_binders env sigma

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
          hov 0 (keyword "Sort" ++ spc() ++ Sorts.pr_sort_family s)
      | CaseScheme (dep,ind,s) ->
        (match idop with
          | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
          | None -> spc ()
        ) ++
          hov 0 ((if dep then keyword "Elimination for" else keyword "Case for")
                 ++ spc() ++ pr_smart_global ind) ++ spc() ++
          hov 0 (keyword "Sort" ++ spc() ++ Sorts.pr_sort_family s)
      | EqualityScheme ind ->
        (match idop with
          | Some id -> hov 0 (pr_lident id ++ str" :=") ++ spc()
          | None -> spc()
        ) ++
          hov 0 (keyword "Equality for")
        ++ spc() ++ pr_smart_global ind

  let begin_of_inductive = function
    | [] -> 0
    | (_,({loc},_))::_ -> Option.cata (fun loc -> fst (Loc.unloc loc)) 0 loc

  let pr_class_rawexpr = function
    | FunClass -> keyword "Funclass"
    | SortClass -> keyword "Sortclass"
    | RefClass qid -> pr_smart_global qid

  let pr_assumption_token many discharge kind =
    match discharge, kind with
      | (NoDischarge,Decls.Logical) ->
        keyword (if many then "Axioms" else "Axiom")
      | (NoDischarge,Decls.Definitional) ->
        keyword (if many then "Parameters" else "Parameter")
      | (NoDischarge,Decls.Conjectural) -> str"Conjecture"
      | (DoDischarge,Decls.Logical) ->
        keyword (if many then "Hypotheses" else "Hypothesis")
      | (DoDischarge,Decls.Definitional) ->
        keyword (if many then "Variables" else "Variable")
      | (DoDischarge,Decls.Conjectural) ->
        anomaly (Pp.str "Don't know how to beautify a local conjecture.")
      | (_,Decls.Context) ->
        anomaly (Pp.str "Context is used only internally.")

  let pr_params pr_c (xl,(c,t)) =
    hov 2 (prlist_with_sep sep pr_lident xl ++ spc() ++
             (if c then str":>" else str":" ++
                 spc() ++ pr_c t))

  let rec factorize = function
    | [] -> []
    | (c,(idl,t))::l ->
      match factorize l with
        | (xl,((c', t') as r))::l'
            when (c : bool) == c' && (=) t t' ->
          (* FIXME: we need equality on constr_expr *)
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

let string_of_theorem_kind = let open Decls in function
  | Theorem -> "Theorem"
  | Lemma -> "Lemma"
  | Fact -> "Fact"
  | Remark -> "Remark"
  | Property -> "Property"
  | Proposition -> "Proposition"
  | Corollary -> "Corollary"

  let pr_thm_token k = keyword (string_of_theorem_kind k)

  let pr_syntax_modifier = let open Gramlib.Gramext in function
    | SetItemLevel (l,bko,n) ->
      prlist_with_sep sep_v2 str l ++ spc () ++ pr_at_level n ++
      pr_opt pr_constr_as_binder_kind bko
    | SetLevel n -> pr_at_level (NumLevel n)
    | SetCustomEntry (s,n) -> keyword "in" ++ spc() ++ keyword "custom" ++ spc() ++ str s ++ (match n with None -> mt () | Some n -> pr_at_level (NumLevel n))
    | SetAssoc LeftA -> keyword "left associativity"
    | SetAssoc RightA -> keyword "right associativity"
    | SetAssoc NonA -> keyword "no associativity"
    | SetEntryType (x,typ) -> str x ++ spc() ++ pr_set_simple_entry_type typ
    | SetOnlyPrinting -> keyword "only printing"
    | SetOnlyParsing -> keyword "only parsing"
    | SetFormat("text",s) -> keyword "format " ++ pr_ast qs s
    | SetFormat(k,s) -> keyword "format " ++ qs k ++ spc() ++ pr_ast qs s

  let pr_syntax_modifiers = function
    | [] -> mt()
    | l -> spc() ++
      hov 1 (str"(" ++ prlist_with_sep sep_v2 pr_syntax_modifier l ++ str")")

  let pr_rec_definition { fname; univs; rec_order; binders; rtype; body_def; notations } =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let pr_pure_lconstr c = Flags.without_option Flags.beautify pr_lconstr c in
    let annot = pr_guard_annot (pr_lconstr_expr env sigma) binders rec_order in
    pr_ident_decl (fname,univs) ++ pr_binders_arg binders ++ annot
    ++ pr_type_option (fun c -> spc() ++ pr_lconstr_expr env sigma c) rtype
    ++ pr_opt (fun def -> str":=" ++ brk(1,2) ++ pr_pure_lconstr env sigma def) body_def
    ++ prlist (pr_decl_notation @@ pr_constr env sigma) notations

  let pr_statement head (idpl,(bl,c)) =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    hov 2
      (head ++ spc() ++ pr_ident_decl idpl ++ spc() ++
         (match bl with [] -> mt() | _ -> pr_binders env sigma bl ++ spc()) ++
         str":" ++ pr_spc_lconstr c)

(**************************************)
(* Pretty printer for vernac commands *)
(**************************************)

  let pr_constrarg c =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    spc () ++ pr_constr env sigma c
  let pr_lconstrarg c =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    spc () ++ pr_lconstr env sigma c
  let pr_intarg n = spc () ++ int n

  let pr_oc = function
    | None -> str" :"
    | Some true -> str" :>"
    | Some false -> str" :>>"

  let pr_record_field (x, { rf_subclass = oc ; rf_priority = pri ; rf_notation = ntn }) =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    let prx = match x with
      | AssumExpr (id,t) ->
        hov 1 (pr_lname id ++
                 pr_oc oc ++ spc() ++
                 pr_lconstr_expr env sigma t)
      | DefExpr(id,b,opt) -> (match opt with
          | Some t ->
            hov 1 (pr_lname id ++
                     pr_oc oc ++ spc() ++
                     pr_lconstr_expr env sigma t ++ str" :=" ++ pr_lconstr env sigma b)
          | None ->
            hov 1 (pr_lname id ++ str" :=" ++ spc() ++
                     pr_lconstr env sigma b)) in
    let prpri = match pri with None -> mt() | Some i -> str "| " ++ int i in
    prx ++ prpri ++ prlist (pr_decl_notation @@ pr_constr env sigma) ntn

  let pr_record_decl c fs =
    pr_opt pr_lident c ++ (if c = None then str"{" else str" {") ++
      hv 0 (prlist_with_sep pr_semicolon pr_record_field fs ++ str"}")

  let pr_printable = function
    | PrintFullContext ->
      keyword "Print All"
    | PrintSectionContext s ->
      keyword "Print Section" ++ spc() ++ Libnames.pr_qualid s
    | PrintGrammar ent ->
      keyword "Print Grammar" ++ spc() ++ str ent
    | PrintCustomGrammar ent ->
      keyword "Print Custom Grammar" ++ spc() ++ str ent
    | PrintLoadPath dir ->
      keyword "Print LoadPath" ++ pr_opt DirPath.print dir
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
    | PrintCanonicalConversions qids ->
      keyword "Print Canonical Structures" ++ prlist pr_smart_global qids
    | PrintTypingFlags ->
      keyword "Print Typing Flags"
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
    | PrintUniverses (b, g, fopt) ->
      let cmd =
        if b then "Print Sorted Universes"
        else "Print Universes"
      in
      let pr_subgraph = prlist_with_sep spc pr_qualid in
      keyword cmd ++ pr_opt pr_subgraph g ++ pr_opt str fopt
    | PrintName (qid,udecl) ->
      keyword "Print" ++ spc()  ++ pr_smart_global qid ++ pr_univ_name_list udecl
    | PrintModuleType qid ->
      keyword "Print Module Type" ++ spc() ++ pr_qualid qid
    | PrintModule qid ->
      keyword "Print Module" ++ spc() ++ pr_qualid qid
    | PrintInspect n ->
      keyword "Inspect" ++ spc() ++ int n
    | PrintScopes ->
      keyword "Print Scopes"
    | PrintScope s ->
      keyword "Print Scope" ++ spc() ++ str s
    | PrintVisibility s ->
      keyword "Print Visibility" ++ pr_opt str s
    | PrintAbout (qid,l,gopt) ->
       pr_opt (fun g -> Goal_select.pr_goal_selector g ++ str ":"++ spc()) gopt
       ++ keyword "About" ++ spc()  ++ pr_smart_global qid ++ pr_univ_name_list l
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
      keyword "Print Namespace" ++ DirPath.print dp
    | PrintStrategy None ->
      keyword "Print Strategies"
    | PrintStrategy (Some qid) ->
      keyword "Print Strategy" ++ pr_smart_global qid
    | PrintRegistered ->
      keyword "Print Registered"

  let pr_using e =
    let rec aux = function
      | SsEmpty -> "()"
      | SsType -> "(Type)"
      | SsSingl { v=id } -> "("^Id.to_string id^")"
      | SsCompl e -> "-" ^ aux e^""
      | SsUnion(e1,e2) -> "("^aux e1 ^" + "^ aux e2^")"
      | SsSubstr(e1,e2) -> "("^aux e1 ^" - "^ aux e2^")"
      | SsFwdClose e -> "("^aux e^")*"
    in Pp.str (aux e)

  let pr_extend s cl =
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


let string_of_definition_object_kind = let open Decls in function
  | Definition -> "Definition"
  | Example -> "Example"
  | Coercion -> "Coercion"
  | SubClass -> "SubClass"
  | CanonicalStructure -> "Canonical Structure"
  | Instance -> "Instance"
  | Let -> "Let"
  | (StructureComponent|Scheme|CoFixpoint|Fixpoint|IdentityCoercion|Method) ->
    CErrors.anomaly (Pp.str "Internal definition kind.")

  let pr_vernac_expr v =
    let return = tag_vernac v in
    let env = Global.env () in
    let sigma = Evd.from_env env in
    match v with
      | VernacLoad (f,s) ->
        return (
          keyword "Load"
          ++ if f then
              (spc() ++ keyword "Verbose" ++ spc())
            else
              spc() ++ qs s
        )

      (* Proof management *)
      | VernacAbortAll ->
        return (keyword "Abort All")
      | VernacRestart ->
        return (keyword "Restart")
      | VernacUnfocus ->
        return (keyword "Unfocus")
      | VernacUnfocused ->
        return (keyword "Unfocused")
      | VernacAbort id ->
        return (keyword "Abort" ++ pr_opt pr_lident id)
      | VernacUndo i ->
        return (
          if Int.equal i 1 then keyword "Undo" else keyword "Undo" ++ pr_intarg i
        )
      | VernacUndoTo i ->
        return (keyword "Undo" ++ spc() ++ keyword "To" ++ pr_intarg i)
      | VernacFocus i ->
        return (keyword "Focus" ++ pr_opt int i)
      | VernacShow s ->
        let pr_goal_reference = function
          | OpenSubgoals -> mt ()
          | NthGoal n -> spc () ++ int n
          | GoalId id -> spc () ++ pr_id id
        in
        let pr_showable = function
          | ShowGoal n -> keyword "Show" ++ pr_goal_reference n
          | ShowProof -> keyword "Show Proof"
          | ShowExistentials -> keyword "Show Existentials"
          | ShowUniverses -> keyword "Show Universes"
          | ShowProofNames -> keyword "Show Conjectures"
          | ShowIntros b -> keyword "Show " ++ (if b then keyword "Intros" else keyword "Intro")
          | ShowMatch id -> keyword "Show Match " ++ pr_qualid id
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

    (* State management *)
      | VernacWriteState s ->
        return (keyword "Write State" ++ spc () ++ qs s)
      | VernacRestoreState s ->
        return  (keyword "Restore State" ++ spc() ++ qs s)

    (* Syntax *)
      | VernacOpenCloseScope (opening,sc) ->
        return (
          keyword (if opening then "Open " else "Close ") ++
            keyword "Scope" ++ spc() ++ str sc
        )
      | VernacDeclareScope sc ->
        return (
          keyword "Declare Scope" ++ spc () ++ str sc
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
      | VernacInfix (({v=s},mv),q,sn) -> (* A Verifier *)
        return (
          hov 0 (hov 0 (keyword "Infix "
                        ++ qs s ++ str " :=" ++ pr_constrarg q) ++
                   pr_syntax_modifiers mv ++
                   (match sn with
                     | None -> mt()
                     | Some sc -> spc() ++ str":" ++ spc() ++ str sc))
        )
      | VernacNotation (c,({v=s},l),opt) ->
        return (
          hov 2 (keyword "Notation" ++ spc() ++ qs s ++
                   str " :=" ++ Flags.without_option Flags.beautify pr_constrarg c ++ pr_syntax_modifiers l ++
                   (match opt with
                     | None -> mt()
                     | Some sc -> str" :" ++ spc() ++ str sc))
        )
      | VernacSyntaxExtension (_, (s, l)) ->
        return (
          keyword "Reserved Notation" ++ spc() ++ pr_ast qs s ++
            pr_syntax_modifiers l
        )
      | VernacNotationAddFormat(s,k,v) ->
        return (
          keyword "Format Notation " ++ qs s ++ spc () ++ qs k ++ spc() ++ qs v
        )
      | VernacDeclareCustomEntry s ->
        return (
          keyword "Declare Custom Entry " ++ str s
        )

      (* Gallina *)
      | VernacDefinition ((discharge,kind),id,b) -> (* A verifier... *)
        let pr_def_token dk =
          keyword (
            if Name.is_anonymous (fst id).v
            then "Goal"
            else string_of_definition_object_kind dk)
        in
        let pr_reduce = function
          | None -> mt()
          | Some r ->
            keyword "Eval" ++ spc() ++
              Ppred.pr_red_expr_env env sigma (pr_constr, pr_lconstr, pr_smart_global, pr_constr) keyword r ++
              keyword " in" ++ spc()
        in
        let pr_def_body = function
          | DefineBody (bl,red,body,d) ->
            let ty = match d with
              | None -> mt()
              | Some ty -> spc() ++ str":" ++ pr_spc_lconstr ty
            in
            (pr_binders_arg bl,ty,Some (pr_reduce red ++ pr_lconstr env sigma body))
          | ProveBody (bl,t) ->
            let typ u = if (fst id).v = Anonymous then (assert (bl = []); u) else (str" :" ++ u) in
            (pr_binders_arg bl, typ (pr_spc_lconstr t), None) in
        let (binds,typ,c) = pr_def_body b in
        return (
          hov 2 (
            pr_def_token kind ++ spc()
            ++ pr_lname_decl id ++ binds ++ typ
            ++ (match c with
              | None -> mt()
              | Some cc -> str" :=" ++ spc() ++ cc))
        )

      | VernacStartTheoremProof (ki,l) ->
        return (
          hov 1 (pr_statement (pr_thm_token ki) (List.hd l) ++
                   prlist (pr_statement (spc () ++ keyword "with")) (List.tl l))
        )

      | VernacEndProof Admitted ->
        return (keyword "Admitted")

      | VernacEndProof (Proved (opac,o)) -> return (
        let open Proof_global in
        match o with
          | None -> (match opac with
              | Transparent -> keyword "Defined"
              | Opaque      -> keyword "Qed")
          | Some id -> (if opac <> Transparent then keyword "Save" else keyword "Defined") ++ spc() ++ pr_lident id
      )
      | VernacExactProof c ->
        return (hov 2 (keyword "Proof" ++ pr_lconstrarg c))
      | VernacAssumption ((discharge,kind),t,l) ->
        let n = List.length (List.flatten (List.map fst (List.map snd l))) in
        let pr_params (c, (xl, t)) =
          hov 2 (prlist_with_sep sep pr_ident_decl xl ++ spc() ++
            (if c then str":>" else str":" ++ spc() ++ pr_lconstr_expr env sigma t)) in
        let assumptions = prlist_with_sep spc (fun p -> hov 1 (str "(" ++ pr_params p ++ str ")")) l in
        return (hov 2 (pr_assumption_token (n > 1) discharge kind ++
                       pr_non_empty_arg pr_assumption_inline t ++ spc() ++ assumptions))
      | VernacInductive (cum, p,f,l) ->
        let pr_constructor (coe,(id,c)) =
          hov 2 (pr_lident id ++ str" " ++
                   (if coe then str":>" else str":") ++
                   Flags.without_option Flags.beautify pr_spc_lconstr c)
        in
        let pr_constructor_list l = match l with
          | Constructors [] -> mt()
          | Constructors l ->
            let fst_sep = match l with [_] -> "   " | _ -> " | " in
            pr_com_at (begin_of_inductive l) ++
              fnl() ++ str fst_sep ++
              prlist_with_sep (fun _ -> fnl() ++ str" | ") pr_constructor l
          | RecordDecl (c,fs) ->
            pr_record_decl c fs
        in
        let pr_oneind key (((coe,iddecl),(indupar,indpar),s,lc),ntn) =
          hov 0 (
            str key ++ spc() ++
              (if coe then str"> " else str"") ++ pr_ident_decl iddecl ++
              pr_and_type_binders_arg indupar ++
              pr_opt (fun p -> str "|" ++ spc() ++ pr_and_type_binders_arg p) indpar ++
              pr_opt (fun s -> str":" ++ spc() ++ pr_lconstr_expr env sigma s) s ++
              str" :=") ++ pr_constructor_list lc ++
            prlist (pr_decl_notation @@ pr_constr env sigma) ntn
        in
        let key =
          let kind =
            match f with Record -> "Record" | Structure -> "Structure"
                       | Inductive_kw -> "Inductive" | CoInductive -> "CoInductive"
                       | Class _ -> "Class" | Variant -> "Variant"
          in
          if p then
            let cm =
              match cum with
              | Some VernacCumulative -> "Cumulative"
              | Some VernacNonCumulative -> "NonCumulative"
              | None -> ""
            in
            cm ^ " " ^ kind
          else kind
        in
        return (
          hov 1 (pr_oneind key (List.hd l)) ++
          (prlist (fun ind -> fnl() ++ hov 1 (pr_oneind "with" ind)) (List.tl l))
        )

      | VernacFixpoint (local, recs) ->
        let local = match local with
          | DoDischarge -> "Let "
          | NoDischarge -> ""
        in
        return (
          hov 0 (str local ++ keyword "Fixpoint" ++ spc () ++
                   prlist_with_sep (fun _ -> fnl () ++ keyword "with"
                     ++ spc ()) pr_rec_definition recs)
        )

      | VernacCoFixpoint (local, corecs) ->
        let local = match local with
          | DoDischarge -> keyword "Let" ++ spc ()
          | NoDischarge -> str ""
        in
        let pr_onecorec {fname; univs; binders; rtype; body_def; notations } =
          pr_ident_decl (fname,univs) ++ spc() ++ pr_binders env sigma binders ++ spc() ++ str":" ++
            spc() ++ pr_lconstr_expr env sigma rtype ++
            pr_opt (fun def -> str":=" ++ brk(1,2) ++ pr_lconstr env sigma def) body_def ++
            prlist (pr_decl_notation @@ pr_constr env sigma) notations
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
      | VernacCoercion (id,c1,c2) ->
        return (
          hov 1 (
            keyword "Coercion" ++ spc() ++
              pr_smart_global id ++ spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++
              spc() ++ str">->" ++ spc() ++ pr_class_rawexpr c2)
        )
      | VernacIdentityCoercion (id,c1,c2) ->
        return (
          hov 1 (
            keyword "Identity Coercion" ++ spc() ++ pr_lident id ++
              spc() ++ str":" ++ spc() ++ pr_class_rawexpr c1 ++ spc() ++ str">->" ++
              spc() ++ pr_class_rawexpr c2)
        )

      | VernacInstance (instid, sup, cl, props, info) ->
        return (
          hov 1 (
            keyword "Instance" ++
            (match instid with
             | {loc; v = Name id}, l -> spc () ++ pr_ident_decl (CAst.(make ?loc id),l) ++ spc ()
             | { v = Anonymous }, _ -> mt ()) ++
            pr_and_type_binders_arg sup ++
              str":" ++ spc () ++
              pr_constr env sigma cl ++ pr_hint_info (pr_constr_pattern_expr env sigma) info ++
              (match props with
                | Some (true, { v = CRecord l}) -> spc () ++ str":=" ++ spc () ++ str"{" ++ pr_record_body l ++ str "}"
                | Some (true,_) -> assert false
                | Some (false,p) -> spc () ++ str":=" ++ spc () ++ pr_constr env sigma p
                | None -> mt()))
        )

      | VernacDeclareInstance (instid, sup, cl, info) ->
        return (
          hov 1 (
            keyword "Declare Instance" ++ spc () ++ pr_ident_decl instid ++ spc () ++
            pr_and_type_binders_arg sup ++
              str":" ++ spc () ++
              pr_constr env sigma cl ++ pr_hint_info (pr_constr_pattern_expr env sigma) info)
        )

      | VernacContext l ->
        return (
          hov 1 (
            keyword "Context" ++ pr_and_type_binders_arg l)
        )

      | VernacExistingInstance insts ->
        let pr_inst (id, info) =
           pr_qualid id ++ pr_hint_info (pr_constr_pattern_expr env sigma) info
         in
         return (
          hov 1 (keyword "Existing" ++ spc () ++
                   keyword(String.plural (List.length insts) "Instance") ++
                 spc () ++ prlist_with_sep (fun () -> str", ") pr_inst insts)
        )

      | VernacExistingClass id ->
        return (
          hov 1 (keyword "Existing" ++ spc () ++ keyword "Class" ++ spc () ++ pr_qualid id)
        )

      (* Modules and Module Types *)
      | VernacDefineModule (export,m,bl,tys,bd) ->
        let b = pr_module_binders bl (pr_lconstr env sigma) in
        return (
          hov 2 (keyword "Module" ++ spc() ++ pr_require_token export ++
                   pr_lident m ++ b ++
                   pr_of_module_type (pr_lconstr env sigma) tys ++
                   (if List.is_empty bd then mt () else str ":= ") ++
                   prlist_with_sep (fun () -> str " <+")
                   (pr_module_ast_inl true (pr_lconstr env sigma)) bd)
        )
      | VernacDeclareModule (export,id,bl,m1) ->
        let b = pr_module_binders bl (pr_lconstr env sigma) in
        return (
          hov 2 (keyword "Declare Module" ++ spc() ++ pr_require_token export ++
                   pr_lident id ++ b ++ str " :" ++
                   pr_module_ast_inl true (pr_lconstr env sigma) m1)
        )
      | VernacDeclareModuleType (id,bl,tyl,m) ->
        let b = pr_module_binders bl (pr_lconstr env sigma) in
        let pr_mt = pr_module_ast_inl true (pr_lconstr env sigma) in
        return (
          hov 2 (keyword "Module Type " ++ pr_lident id ++ b ++
                   prlist_strict (fun m -> str " <:" ++ pr_mt m) tyl ++
                   (if List.is_empty m then mt () else str ":= ") ++
                   prlist_with_sep (fun () -> str " <+ ") pr_mt m)
        )
      | VernacInclude (mexprs) ->
        let pr_m = pr_module_ast_inl false (pr_lconstr env sigma) in
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
                 | Some dir -> spc() ++ keyword "as" ++ spc() ++ DirPath.print dir))
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
      | VernacHints (dbnames,h) ->
        return (pr_hints dbnames h (pr_constr env sigma) (pr_constr_pattern_expr env sigma))
      | VernacSyntacticDefinition (id,(ids,c),{onlyparsing}) ->
        return (
          hov 2
            (keyword "Notation" ++ spc () ++ pr_lident id ++ spc () ++
               prlist_with_sep spc pr_id ids ++ str":=" ++ pr_constrarg c ++
               pr_syntax_modifiers (if onlyparsing then [SetOnlyParsing] else []))
        )
      | VernacArguments (q, args, more_implicits, mods) ->
        return (
          hov 2 (
            keyword "Arguments" ++ spc() ++
              pr_smart_global q ++
              let pr_s = function None -> str"" | Some {v=s} -> str "%" ++ str s in
              let pr_if b x = if b then x else str "" in
              let pr_one_arg (x,k) = pr_if k (str"!") ++ Name.print x in
              let pr_br imp force x =
                let left,right =
                match imp with
                | Glob_term.NonMaxImplicit -> str "[", str "]"
                | Glob_term.MaxImplicit -> str "{", str "}"
                | Glob_term.Explicit -> if force then str"(",str")" else mt(),mt()
                in
                left ++ x ++ right
              in
              let get_arguments_like s imp tl =
                if s = None && imp = Glob_term.Explicit then [], tl
                else
                  let rec fold extra = function
                    | RealArg arg :: tl when
                        Option.equal (fun a b -> String.equal a.CAst.v b.CAst.v) arg.notation_scope s
                        && arg.implicit_status = imp ->
                      fold ((arg.name,arg.recarg_like) :: extra) tl
                    | args -> List.rev extra, args
                  in
                  fold [] tl
              in
              let rec print_arguments = function
                  | [] -> mt()
                  | VolatileArg :: l -> spc () ++ str"/" ++ print_arguments l
                  | BidiArg :: l -> spc () ++ str"&" ++ print_arguments l
                  | RealArg { name = id; recarg_like = k;
                         notation_scope = s;
                         implicit_status = imp } :: tl ->
                    let extra, tl = get_arguments_like s imp tl in
                    spc() ++ pr_br imp (extra<>[]) (prlist_with_sep spc pr_one_arg ((id,k)::extra)) ++
                    pr_s s ++ print_arguments tl
              in
              let rec print_implicits = function
                | [] -> mt ()
                | (name, impl) :: rest ->
                   spc() ++ pr_br impl false (Name.print name) ++ print_implicits rest
              in
              print_arguments args ++
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
                    | `ClearScopes -> keyword "clear scopes"
                    | `ClearBidiHint -> keyword "clear bidirectionality hint")
                  mods)
        )
      | VernacReserve bl ->
        let n = List.length (List.flatten (List.map fst bl)) in
        return (
          hov 2 (tag_keyword (str"Implicit Type" ++ str (if n > 1 then "s " else " "))
                 ++ pr_ne_params_list (pr_lconstr_expr env sigma) (List.map (fun sb -> false,sb) bl))
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
          CErrors.anomaly (keyword "VernacSetOpacity used to set something else.")
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
      | VernacSetOption (export, na,v) ->
        let export = if export then keyword "Export" ++ spc () else mt () in
        let set = if v == OptionUnset then "Unset" else "Set" in
        return (
          hov 2 (export ++ keyword set ++ spc() ++ pr_set_option na v)
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
                     Ppred.pr_red_expr_env env sigma (pr_constr,pr_lconstr,pr_smart_global, pr_constr) keyword r0 ++
                     spc() ++ keyword "in" ++ spc () ++ pr_lconstr env sigma c)
          | None -> hov 2 (keyword "Check" ++ spc() ++ pr_lconstr env sigma c)
        in
        let pr_i = match io with None -> mt ()
                               | Some i -> Goal_select.pr_goal_selector i ++ str ": " in
        return (pr_i ++ pr_mayeval r c)
      | VernacGlobalCheck c ->
        return (hov 2 (keyword "Type" ++ pr_constrarg c))
      | VernacDeclareReduction (s,r) ->
        return (
          keyword "Declare Reduction" ++ spc () ++ str s ++ str " := " ++
            Ppred.pr_red_expr_env env sigma (pr_constr,pr_lconstr,pr_smart_global, pr_constr) keyword r
        )
      | VernacPrint p ->
        return (pr_printable p)
      | VernacSearch (sea,g,sea_r) ->
        return (pr_search sea g sea_r @@ pr_constr_pattern_expr env sigma)
      | VernacLocate loc ->
        let pr_locate =function
          | LocateAny qid -> pr_smart_global qid
          | LocateTerm qid -> keyword "Term" ++ spc() ++ pr_smart_global qid
          | LocateFile f -> keyword "File" ++ spc() ++ qs f
          | LocateLibrary qid -> keyword "Library" ++ spc () ++ pr_module qid
          | LocateModule qid -> keyword "Module" ++ spc () ++ pr_module qid
          | LocateOther (s, qid) -> keyword s ++ spc () ++ pr_ltac_ref qid
        in
        return (keyword "Locate" ++ spc() ++ pr_locate loc)
      | VernacRegister (qid, RegisterCoqlib name) ->
        return (
          hov 2
            (keyword "Register" ++ spc() ++ pr_qualid qid ++ spc () ++ str "as"
             ++ spc () ++ pr_qualid name)
        )
      | VernacRegister (qid, RegisterInline) ->
        return (
          hov 2
            (keyword "Register Inline" ++ spc() ++ pr_qualid qid)
        )
      | VernacPrimitive(id,r,typopt) ->
         hov 2
             (keyword "Primitive" ++ spc() ++ pr_lident id ++
                (Option.cata (fun ty -> spc() ++ str":" ++ pr_spc_lconstr ty) (mt()) typopt) ++ spc() ++
                str ":=" ++ spc() ++
                str (CPrimitives.op_or_type_to_string r))
      | VernacComments l ->
        return (
          hov 2
            (keyword "Comments" ++ spc()
             ++ prlist_with_sep sep (pr_comment (pr_constr env sigma)) l)
        )

      (* For extension *)
      | VernacExtend (s,c) ->
        return (pr_extend s c)
      | VernacProof (None, None) ->
        return (keyword "Proof")
      | VernacProof (None, Some e) ->
        return (keyword "Proof " ++ spc () ++
            keyword "using" ++ spc() ++ pr_using e)
      | VernacProof (Some te, None) ->
        return (keyword "Proof with" ++ spc() ++ Pputils.pr_raw_generic env sigma te)
      | VernacProof (Some te, Some e) ->
        return (
          keyword "Proof" ++ spc () ++
            keyword "using" ++ spc() ++ pr_using e ++ spc() ++
            keyword "with" ++ spc() ++ Pputils.pr_raw_generic env sigma te
        )
      | VernacProofMode s ->
        return (keyword "Proof Mode" ++ str s)
      | VernacBullet b ->
        (* XXX: Redundant with Proof_bullet.print *)
        return (let open Proof_bullet in begin match b with
          | Dash n -> str (String.make n '-')
          | Star n -> str (String.make n '*')
          | Plus n -> str (String.make n '+')
        end)
      | VernacSubproof None ->
        return (str "{")
      | VernacSubproof (Some i) ->
        return (Goal_select.pr_goal_selector i ++ str ":" ++ spc () ++ str "{")
      | VernacEndSubproof ->
        return (str "}")

let pr_control_flag (p : control_flag) =
  let w = match p with
    | ControlTime _ -> keyword "Time"
    | ControlRedirect s -> keyword "Redirect" ++ spc() ++ qs s
    | ControlTimeout n -> keyword "Timeout " ++ int n
    | ControlFail -> keyword "Fail" in
  w ++ spc ()

let pr_vernac_control flags = Pp.prlist pr_control_flag flags

let rec pr_vernac_flag (k, v) =
  let k = keyword k in
  let open Attributes in
  match v with
  | VernacFlagEmpty -> k
  | VernacFlagLeaf v -> k ++ str " = " ++ qs v
  | VernacFlagList m -> k ++ str "( " ++ pr_vernac_flags m ++ str " )"
and pr_vernac_flags m =
  prlist_with_sep (fun () -> str ", ") pr_vernac_flag m

let pr_vernac_attributes =
  function
  | [] -> mt ()
  | flags ->  str "#[" ++ pr_vernac_flags flags ++ str "]" ++ cut ()

let pr_vernac ({v = {control; attrs; expr}} as v) =
  try
    tag_vernac v
      (pr_vernac_control control ++
       pr_vernac_attributes attrs ++
       pr_vernac_expr expr ++
       sep_end expr)
  with e -> CErrors.print e
