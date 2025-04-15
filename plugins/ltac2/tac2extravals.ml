(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open Names
open Genarg
open Tac2ffi
open Tac2env
open Tac2expr
open Tac2entries.Pltac
open Proofview.Notations

open Tac2quote.Refs

let return x = Proofview.tclUNIT x

(** ML types *)

(** Embed all Ltac2 data into Values *)
let to_lvar ist =
  let open Glob_ops in
  let lfun = Tac2interp.set_env ist Id.Map.empty in
  { empty_lvar with Ltac_pretype.ltac_genargs = lfun }

let gtypref kn = GTypRef (Other kn, [])

let of_glob_constr (c:Glob_term.glob_constr) =
  match DAst.get c with
  | GGenarg (GenArg (Glbwit tag, v)) ->
    begin match genarg_type_eq tag wit_ltac2_var_quotation with
    | Some Refl ->
      begin match (fst v) with
      | ConstrVar -> GlbTacexpr (GTacVar (snd v))
      | _ -> GlbVal c
      end
    | None -> GlbVal c
    end
  | _ -> GlbVal c

let intern_constr ist c =
  let {Genintern.ltacvars=lfun; genv=env; extra; intern_sign; strict_check} = ist in
  let scope = Pretyping.WithoutTypeConstraint in
  let ltacvars = {
    Constrintern.ltac_vars = lfun;
    ltac_bound = Id.Set.empty;
    ltac_extra = extra;
  } in
  let c' = Constrintern.intern_core scope ~strict_check ~ltacvars env (Evd.from_env env) intern_sign c in
  c'

let intern_constr_tacexpr ist c =
  let c = intern_constr ist c in
  let v = of_glob_constr c in
  (v, gtypref t_constr)

let interp_constr flags ist c =
  let open Pretyping in
  let ist = to_lvar ist in
  Tac2core.pf_apply ~catch_exceptions:true begin fun env sigma ->
    let (sigma, c) = understand_ltac flags env sigma ist WithoutTypeConstraint c in
    let c = Tac2ffi.of_constr c in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT c
  end

let () =
  let intern = intern_constr_tacexpr in
  let interp ist c = interp_constr Tac2core.constr_flags ist c in
  let print env sigma c = str "constr:(" ++ Printer.pr_lglob_constr_env env sigma c ++ str ")" in
  let raw_print env sigma c = str "constr:(" ++ Ppconstr.pr_constr_expr env sigma c ++ str ")" in
  let subst subst c = Detyping.subst_glob_constr (Global.env()) subst c in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_constr obj

let () =
  let intern = intern_constr_tacexpr in
  let interp ist c = interp_constr Tac2core.open_constr_no_classes_flags ist c in
  let print env sigma c = str "open_constr:(" ++ Printer.pr_lglob_constr_env env sigma c ++ str ")" in
  let raw_print env sigma c = str "open_constr:(" ++ Ppconstr.pr_constr_expr env sigma c ++ str ")" in
  let subst subst c = Detyping.subst_glob_constr (Global.env()) subst c in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_open_constr obj

let () =
  let interp _ id = return (Tac2ffi.of_ident id) in
  let print _ _ id = str "ident:(" ++ Id.print id ++ str ")" in
  let obj = {
    ml_intern = (fun _ id -> GlbVal id, gtypref t_ident);
    ml_interp = interp;
    ml_subst = (fun _ id -> id);
    ml_print = print;
    ml_raw_print = print;
  } in
  define_ml_object Tac2quote.wit_ident obj

let () =
  let intern {Genintern.ltacvars=lfun; genv=env; extra; intern_sign=_; strict_check} c =
    let sigma = Evd.from_env env in
    let ltacvars = {
      Constrintern.ltac_vars = lfun;
      ltac_bound = Id.Set.empty;
      ltac_extra = extra;
    }
    in
    let _, pat = Constrintern.intern_uninstantiated_constr_pattern env sigma ~strict_check ~as_type:false ~ltacvars c in
    GlbVal pat, gtypref t_pattern
  in
  let subst subst c =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Patternops.subst_pattern env sigma subst c
  in
  let print env sigma pat = str "pat:(" ++ Printer.pr_lconstr_pattern_env env sigma pat ++ str ")" in
  let raw_print env sigma pat = str "pat:(" ++ Ppconstr.pr_constr_pattern_expr env sigma pat ++ str ")" in
  let interp env c =
    let ist = to_lvar env in
    Tac2core.pf_apply ~catch_exceptions:true begin fun env sigma ->
      let c = Patternops.interp_pattern env sigma ist c in
      return (Tac2ffi.of_pattern c)
    end
  in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = subst;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_pattern obj

let () =
  let intern ist c =
    let c = intern_constr ist c in
    (GlbVal (Id.Set.empty,c), gtypref t_preterm)
  in
  let interp env (ids,c) =
    let open Ltac_pretype in
    let get_preterm id = match Id.Map.find_opt id env.env_ist with
      | Some v -> to_preterm v
      | None -> assert false
    in
    let closure = {
      idents = Id.Map.empty;
      typed = Id.Map.empty;
      untyped = Id.Map.bind get_preterm ids;
      genargs = Tac2interp.set_env env Id.Map.empty;
    } in
    let c = { closure; term = c } in
    return (Tac2ffi.of_preterm c)
  in
  let subst subst (ids,c) = ids, Detyping.subst_glob_constr (Global.env()) subst c in
  let print env sigma (ids,c) =
    let ppids = if Id.Set.is_empty ids then mt()
      else prlist_with_sep spc Id.print (Id.Set.elements ids) ++ spc() ++ str "|-" ++ spc()
    in
    hov 2 (str "preterm:(" ++ ppids ++ Printer.pr_lglob_constr_env env sigma c ++ str ")")
  in
  let raw_print env sigma c = str "preterm:(" ++ Ppconstr.pr_constr_expr env sigma c ++ str ")" in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = subst;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_preterm obj

let () =
  let intern ist ref = match ref.CAst.v with
  | Tac2qexpr.QHypothesis id ->
    GlbVal (GlobRef.VarRef id), gtypref t_reference
  | Tac2qexpr.QReference qid ->
    let gr =
      try Smartlocate.locate_global_with_alias qid
      with Not_found as exn ->
        let _, info = Exninfo.capture exn in
        Nametab.error_global_not_found ~info qid
    in
    GlbVal gr, gtypref t_reference
  in
  let subst s c = Globnames.subst_global_reference s c in
  let interp _ gr = return (Tac2ffi.of_reference gr) in
  let print _ _ = function
  | GlobRef.VarRef id -> str "reference:(" ++ str "&" ++ Id.print id ++ str ")"
  | r -> str "reference:(" ++ Printer.pr_global r ++ str ")"
  in
  let raw_print _ _ r = match r.CAst.v with
    | Tac2qexpr.QReference qid -> str "reference:(" ++ Libnames.pr_qualid qid ++ str ")"
    | Tac2qexpr.QHypothesis id -> str "reference:(&" ++ Id.print id ++ str ")"
  in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_reference obj

(** Ltac2 in terms *)

let () =
  let interp ?loc ~poly env sigma tycon (ids, tac) =
    (* Syntax prevents bound notation variables in constr quotations *)
    let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
    let () = assert (Id.Set.subset ids (Id.Map.domain ist.env_ist)) in
    let tac = Proofview.tclIGNORE (Tac2interp.interp ist tac) in
    let name, poly = Id.of_string "ltac2", poly in
    let sigma, concl = match tycon with
    | Some ty -> sigma, ty
    | None -> GlobEnv.new_type_evar env sigma ~src:(loc,Evar_kinds.InternalHole)
    in
    let c, sigma = Proof.refine_by_tactic ~name ~poly (GlobEnv.renamed_env env) sigma concl tac in
    let j = { Environ.uj_val = c; Environ.uj_type = concl } in
    (j, sigma)
  in
  GlobEnv.register_constr_interp0 wit_ltac2_constr interp

let interp_constr_var_as_constr ?loc env sigma tycon id =
  let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
  let env = GlobEnv.renamed_env env in
  let c = Id.Map.find id ist.env_ist in
  let c = Tac2ffi.to_constr c in
  let t = Retyping.get_type_of env sigma c in
  let j = { Environ.uj_val = c; uj_type = t } in
  match tycon with
  | None ->
    j, sigma
  | Some ty ->
    let sigma =
      try Evarconv.unify_leq_delay env sigma t ty
      with Evarconv.UnableToUnify (sigma,e) ->
        Pretype_errors.error_actual_type ?loc env sigma j ty e
    in
    {j with Environ.uj_type = ty}, sigma

let interp_preterm_var_as_constr ?loc env sigma tycon id =
  let open Ltac_pretype in
  let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
  let env = GlobEnv.renamed_env env in
  let c = Id.Map.find id ist.env_ist in
  let {closure; term} = Tac2ffi.to_preterm c in
  let vars = {
    ltac_constrs = closure.typed;
    ltac_uconstrs = closure.untyped;
    ltac_idents = closure.idents;
    ltac_genargs = closure.genargs;
  }
  in
  let flags = Tac2core.preterm_flags in
  let tycon = let open Pretyping in match tycon with
    | Some ty -> OfType ty
    | None -> WithoutTypeConstraint
  in
  let sigma, t, ty = Pretyping.understand_ltac_ty flags env sigma vars tycon term in
  Environ.make_judge t ty, sigma

let () =
  let interp ?loc ~poly env sigma tycon (kind,id) =
    let f = match kind with
      | ConstrVar -> interp_constr_var_as_constr
      | PretermVar -> interp_preterm_var_as_constr
      | PatternVar -> assert false
    in
    f ?loc env sigma tycon id
  in
  GlobEnv.register_constr_interp0 wit_ltac2_var_quotation interp

let () =
  let interp _ist tac =
    (* XXX should we be doing something with the ist? *)
    let tac = Tac2interp.(interp empty_environment) tac in
    Proofview.tclBIND tac (fun _ ->
        Ftactic.return (Geninterp.Val.inject (Geninterp.val_tag (topwit Stdarg.wit_unit)) ()))
  in
  Geninterp.register_interp0 wit_ltac2_tac interp

let () =
  let interp env sigma ist (kind,id) =
    let () = match kind with
      | ConstrVar -> assert false (* checked at intern time *)
      | PretermVar -> assert false
      | PatternVar -> ()
    in
    let ist = Tac2interp.get_env ist.Ltac_pretype.ltac_genargs in
    let c = Id.Map.find id ist.env_ist in
    let c = Tac2ffi.to_pattern c in
    c
  in
  Patternops.register_interp_pat wit_ltac2_var_quotation interp

let () =
  let pr_raw (kind,id) = Genprint.PrinterBasic (fun _env _sigma ->
      let ppkind =
      match kind with
        | None -> mt()
        | Some kind -> Id.print kind.CAst.v ++ str ":"
      in
      str "$" ++ ppkind ++ Id.print id.CAst.v)
  in
  let pr_glb (kind,id) = Genprint.PrinterBasic (fun _env _sigma ->
      let ppkind = match kind with
        | ConstrVar -> mt()
        | PretermVar -> str "preterm:"
        | PatternVar -> str "pattern:"
      in
      str "$" ++ ppkind ++ Id.print id) in
  Genprint.register_noval_print0 wit_ltac2_var_quotation pr_raw pr_glb

let () =
  let subs ntnvars globs (ids, tac as orig) =
    if Id.Set.is_empty ids then
      (* closed tactic *)
      orig
    else
      (* Let-bind the notation terms inside the tactic *)
      let fold id (used_ntnvars, accu) =
        let used, c = Genintern.with_used_ntnvars ntnvars (fun () -> globs id) in
        match c with
        | None ->
          CErrors.user_err Pp.(str "Notation variable " ++ Id.print id ++ str " cannot be used in ltac2.")
        | Some c ->
          let c = GTacExt (Tac2quote.wit_preterm, (used, c)) in
          Id.Set.union used_ntnvars used, (Name id, c) :: accu
      in
      let used, bnd = Id.Set.fold fold ids (Id.Set.empty, []) in
      let tac = if List.is_empty bnd then tac else GTacLet (false, bnd, tac) in
      (used, tac)
  in
  Genintern.register_ntn_subst0 wit_ltac2_constr subs

let () =
  let pr_raw e = Genprint.PrinterBasic (fun _env _sigma ->
      let avoid = Id.Set.empty in
      (* FIXME avoid set, same as pr_glb *)
      let e = Tac2intern.debug_globalize_allow_ext avoid e in
      Tac2print.pr_rawexpr_gen ~avoid E5 e) in
  let pr_glb (ids, e) =
    let ids =
      let ids = Id.Set.elements ids in
      if List.is_empty ids then mt ()
      else hov 0 (pr_sequence Id.print ids ++ str " |-") ++ spc()
    in
    (* FIXME avoid set
       eg "Ltac2 bla foo := constr:(ltac2:(foo X.foo))"
       gets incorrectly printed as "fun foo => constr:(ltac2:(foo foo))"
       NB: can't pass through evar map store as the evar map we get is a dummy,
       see Ppconstr.pr_genarg
    *)
    Genprint.PrinterBasic Pp.(fun _env _sigma -> ids ++ Tac2print.pr_glbexpr ~avoid:Id.Set.empty e)
  in
  Genprint.register_noval_print0 wit_ltac2_constr pr_raw pr_glb

let () =
  let pr_raw e = Genprint.PrinterBasic (fun _ _ ->
      let e = Tac2intern.debug_globalize_allow_ext Id.Set.empty e in
      Tac2print.pr_rawexpr_gen ~avoid:Id.Set.empty E5 e)
  in
  let pr_glb e = Genprint.PrinterBasic (fun _ _ -> Tac2print.pr_glbexpr ~avoid:Id.Set.empty e) in
  let pr_top () = assert false in
  Genprint.register_print0 wit_ltac2_tac pr_raw pr_glb pr_top

(** Built-in notation entries *)

let add_syntax_class s f =
  Tac2entries.register_syntax_class (Id.of_string s) f

let rec pr_syntax_class = let open CAst in function
| SexprStr {v=s} -> qstring s
| SexprInt {v=n} -> Pp.int n
| SexprRec (_, {v=na}, args) ->
  let na = match na with
  | None -> str "_"
  | Some id -> Id.print id
  in
  na ++ str "(" ++ prlist_with_sep (fun () -> str ", ") pr_syntax_class args ++ str ")"

let syntax_class_fail s args =
  let args = str "(" ++ prlist_with_sep (fun () -> str ", ") pr_syntax_class args ++ str ")" in
  CErrors.user_err (str "Invalid arguments " ++ args ++ str " in syntactic class " ++ str s)

let q_unit = CAst.make @@ CTacCst (AbsKn (Tuple 0))

let add_expr_syntax_class name entry f =
  add_syntax_class name begin function
  | [] -> Tac2entries.SyntaxRule (Procq.Symbol.nterm entry, f)
  | arg -> syntax_class_fail name arg
  end

let add_generic_syntax_class s entry arg =
  add_expr_syntax_class s entry (fun x -> CAst.make @@ CTacExt (arg, x))

open CAst

let () = add_syntax_class "keyword" begin function
| [SexprStr {loc;v=s}] ->
  let syntax_class = Procq.Symbol.token (Tok.PKEYWORD s) in
  Tac2entries.SyntaxRule (syntax_class, (fun _ -> q_unit))
| arg -> syntax_class_fail "keyword" arg
end

let () = add_syntax_class "terminal" begin function
| [SexprStr {loc;v=s}] ->
  let syntax_class = Procq.Symbol.token (Procq.terminal s) in
  Tac2entries.SyntaxRule (syntax_class, (fun _ -> q_unit))
| arg -> syntax_class_fail "terminal" arg
end

let () = add_syntax_class "list0" begin function
| [tok] ->
  let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.parse_syntax_class tok in
  let syntax_class = Procq.Symbol.list0 syntax_class in
  let act l = Tac2quote.of_list act l in
  Tac2entries.SyntaxRule (syntax_class, act)
| [tok; SexprStr {v=str}] ->
  let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.parse_syntax_class tok in
  let sep = Procq.Symbol.tokens [Procq.TPattern (Procq.terminal str)] in
  let syntax_class = Procq.Symbol.list0sep syntax_class sep false in
  let act l = Tac2quote.of_list act l in
  Tac2entries.SyntaxRule (syntax_class, act)
| arg -> syntax_class_fail "list0" arg
end

let () = add_syntax_class "list1" begin function
| [tok] ->
  let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.parse_syntax_class tok in
  let syntax_class = Procq.Symbol.list1 syntax_class in
  let act l = Tac2quote.of_list act l in
  Tac2entries.SyntaxRule (syntax_class, act)
| [tok; SexprStr {v=str}] ->
  let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.parse_syntax_class tok in
  let sep = Procq.Symbol.tokens [Procq.TPattern (Procq.terminal str)] in
  let syntax_class = Procq.Symbol.list1sep syntax_class sep false in
  let act l = Tac2quote.of_list act l in
  Tac2entries.SyntaxRule (syntax_class, act)
| arg -> syntax_class_fail "list1" arg
end

let () = add_syntax_class "opt" begin function
| [tok] ->
  let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.parse_syntax_class tok in
  let syntax_class = Procq.Symbol.opt syntax_class in
  let act opt = match opt with
  | None ->
    CAst.make @@ CTacCst (AbsKn (Other c_none))
  | Some x ->
    CAst.make @@ CTacApp (CAst.make @@ CTacCst (AbsKn (Other c_some)), [act x])
  in
  Tac2entries.SyntaxRule (syntax_class, act)
| arg -> syntax_class_fail "opt" arg
end

let () = add_syntax_class "self" begin function
| [] ->
  let syntax_class = Procq.Symbol.self in
  let act tac = tac in
  Tac2entries.SyntaxRule (syntax_class, act)
| arg -> syntax_class_fail "self" arg
end

let () = add_syntax_class "next" begin function
| [] ->
  let syntax_class = Procq.Symbol.next in
  let act tac = tac in
  Tac2entries.SyntaxRule (syntax_class, act)
| arg -> syntax_class_fail "next" arg
end

let () = add_syntax_class "tactic" begin function
| [] ->
  (* Default to level 5 parsing *)
  let syntax_class = Procq.Symbol.nterml ltac2_expr "5" in
  let act tac = tac in
  Tac2entries.SyntaxRule (syntax_class, act)
| [SexprInt {loc;v=n}] as arg ->
  let () = if n < 0 || n > 6 then syntax_class_fail "tactic" arg in
  let syntax_class = Procq.Symbol.nterml ltac2_expr (string_of_int n) in
  let act tac = tac in
  Tac2entries.SyntaxRule (syntax_class, act)
| arg -> syntax_class_fail "tactic" arg
end

let () = add_syntax_class "thunk" begin function
| [tok] ->
  let Tac2entries.SyntaxRule (syntax_class, act) = Tac2entries.parse_syntax_class tok in
  let act e = Tac2quote.thunk (act e) in
  Tac2entries.SyntaxRule (syntax_class, act)
| arg -> syntax_class_fail "thunk" arg
end

let () = add_syntax_class "constr" begin function arg ->
  let delimiters = List.map (function
      | SexprRec (_, { v = Some s }, []) -> s
      | _ -> syntax_class_fail "constr" arg)
      arg
  in
  let act e = Tac2quote.of_constr ~delimiters e in
  Tac2entries.SyntaxRule (Procq.Symbol.nterm Procq.Constr.constr, act)
end

  let () = add_syntax_class "lconstr" begin function arg ->
    let delimiters = List.map (function
        | SexprRec (_, { v = Some s }, []) -> s
        | _ -> syntax_class_fail "lconstr" arg)
        arg
    in
    let act e = Tac2quote.of_constr ~delimiters e in
    Tac2entries.SyntaxRule (Procq.Symbol.nterm Procq.Constr.lconstr, act)
  end

let () = add_syntax_class "open_constr" begin function arg ->
  let delimiters = List.map (function
      | SexprRec (_, { v = Some s }, []) -> s
      | _ -> syntax_class_fail "open_constr" arg)
      arg
  in
  let act e = Tac2quote.of_open_constr ~delimiters e in
  Tac2entries.SyntaxRule (Procq.Symbol.nterm Procq.Constr.constr, act)
end

let () = add_syntax_class "open_lconstr" begin function arg ->
  let delimiters = List.map (function
      | SexprRec (_, { v = Some s }, []) -> s
      | _ -> syntax_class_fail "open_lconstr" arg)
      arg
  in
  let act e = Tac2quote.of_open_constr ~delimiters e in
  Tac2entries.SyntaxRule (Procq.Symbol.nterm Procq.Constr.lconstr, act)
end


let () = add_syntax_class "preterm" begin function arg ->
  let delimiters = List.map (function
      | SexprRec (_, { v = Some s }, []) -> s
      | _ -> syntax_class_fail "preterm" arg)
      arg
  in
  let act e = Tac2quote.of_preterm ~delimiters e in
  Tac2entries.SyntaxRule (Procq.Symbol.nterm Procq.Constr.constr, act)
end

let () = add_expr_syntax_class "ident" q_ident (fun id -> Tac2quote.of_anti Tac2quote.of_ident id)
let () = add_expr_syntax_class "bindings" q_bindings Tac2quote.of_bindings
let () = add_expr_syntax_class "with_bindings" q_with_bindings Tac2quote.of_bindings
let () = add_expr_syntax_class "intropattern" q_intropattern Tac2quote.of_intro_pattern
let () = add_expr_syntax_class "intropatterns" q_intropatterns Tac2quote.of_intro_patterns
let () = add_expr_syntax_class "destruction_arg" q_destruction_arg Tac2quote.of_destruction_arg
let () = add_expr_syntax_class "induction_clause" q_induction_clause Tac2quote.of_induction_clause
let () = add_expr_syntax_class "conversion" q_conversion Tac2quote.of_conversion
let () = add_expr_syntax_class "orient" q_orient Tac2quote.of_orient
let () = add_expr_syntax_class "rewriting" q_rewriting Tac2quote.of_rewriting
let () = add_expr_syntax_class "clause" q_clause Tac2quote.of_clause
let () = add_expr_syntax_class "hintdb" q_hintdb Tac2quote.of_hintdb
let () = add_expr_syntax_class "occurrences" q_occurrences Tac2quote.of_occurrences
let () = add_expr_syntax_class "dispatch" q_dispatch Tac2quote.of_dispatch
let () = add_expr_syntax_class "strategy" q_strategy_flag Tac2quote.of_strategy_flag
let () = add_expr_syntax_class "reference" q_reference Tac2quote.of_reference
let () = add_expr_syntax_class "move_location" q_move_location Tac2quote.of_move_location
let () = add_expr_syntax_class "pose" q_pose Tac2quote.of_pose
let () = add_expr_syntax_class "assert" q_assert Tac2quote.of_assertion
let () = add_expr_syntax_class "constr_matching" q_constr_matching Tac2quote.of_constr_matching
let () = add_expr_syntax_class "goal_matching" q_goal_matching Tac2quote.of_goal_matching
let () = add_expr_syntax_class "format" Procq.Prim.lstring Tac2quote.of_format

let () = add_generic_syntax_class "pattern" Procq.Constr.constr Tac2quote.wit_pattern

(** seq syntax_class, a bit hairy *)

open Procq

type _ converter =
| CvNil : (Loc.t -> raw_tacexpr) converter
| CvCns : 'act converter * ('a -> raw_tacexpr) option -> ('a -> 'act) converter

let rec apply : type a. a converter -> raw_tacexpr list -> a = function
| CvNil -> fun accu loc -> Tac2quote.of_tuple ~loc accu
| CvCns (c, None) -> fun accu x -> apply c accu
| CvCns (c, Some f) -> fun accu x -> apply c (f x :: accu)

type seqrule =
| Seqrule : (Tac2expr.raw_tacexpr, Gramlib.Grammar.norec, 'act, Loc.t -> raw_tacexpr) Rule.t * 'act converter -> seqrule

let rec make_seq_rule = function
| [] ->
  Seqrule (Procq.Rule.stop, CvNil)
| tok :: rem ->
  let Tac2entries.SyntaxRule (syntax_class, f) = Tac2entries.parse_syntax_class tok in
  let syntax_class =
    match Procq.generalize_symbol syntax_class with
    | None ->
      CErrors.user_err (str "Recursive symbols (self / next) are not allowed in local rules")
    | Some syntax_class -> syntax_class
  in
  let Seqrule (r, c) = make_seq_rule rem in
  let r = Procq.Rule.next_norec r syntax_class in
  let f = match tok with
  | SexprStr _ -> None (* Leave out mere strings *)
  | _ -> Some f
  in
  Seqrule (r, CvCns (c, f))

let () = add_syntax_class "seq" begin fun toks ->
  let syntax_class =
    let Seqrule (r, c) = make_seq_rule (List.rev toks) in
    Procq.(Symbol.rules [Rules.make r (apply c [])])
  in
  Tac2entries.SyntaxRule (syntax_class, (fun e -> e))
end
