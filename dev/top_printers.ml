(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Printers for the ocaml toplevel. *)

open Sorts
open Util
open Pp
open Names
open Libnames
open Univ
open UVars
open Environ
open Printer
open Constr
open Context
open Genarg
open Clenv

let () = Flags.in_debugger := true
let () = Goptions.set_bool_option_value ["Printing";"Existential";"Instances"] true
let () = Detyping.print_universes := true
let () = Goptions.set_bool_option_value ["Printing";"Matching"] false
let () = Goptions.set_bool_option_value ["Printing";"Sort";"Qualities"] true

let with_env_evm f x =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  f env sigma x

(* std_ppcmds *)
let pp   x = Pp.pp_with !Topfmt.std_ft x

(** Future printer *)

let ppfuture kx = pp (Future.print (fun _ -> str "_") kx)

(* name printers *)
let ppid id = pp (Id.print id)
let pplab l = pp (Label.print l)
let ppmbid mbid = pp (str (MBId.debug_to_string mbid))
let ppdir dir = pp (DirPath.print dir)
let ppmp mp = pp(str (ModPath.debug_to_string mp))
let ppcon con = pp(Constant.debug_print con)
let ppprojrepr con = pp(Constant.debug_print (Projection.Repr.constant con))
let ppproj p = pp(Projection.debug_print p)
let ppkn kn = pp(str (KerName.to_string kn))
let ppmind kn = pp(MutInd.debug_print kn)
let ppind (kn,i) = pp(MutInd.debug_print kn ++ str"," ++int i)
let ppsp sp = pp(pr_path sp)
let ppqualid qid = pp(pr_qualid qid)
let ppscheme k = pp (Ind_tables.pr_scheme_kind k)

let pprecarg = Declareops.pr_recarg
let ppwf_paths x = pp (Declareops.pr_wf_paths x)

let get_current_context () =
  try Vernacstate.Declare.get_current_context ()
  with Vernacstate.Declare.NoCurrentProof ->
    let env = Global.env() in
    Evd.from_env env, env
  [@@ocaml.warning "-3"]

(* term printers *)
let envpp pp = let sigma,env = get_current_context () in pp env sigma
let rawdebug = ref false
let ppevar evk = pp (Evar.print evk)
let pr_constr t =
  let sigma, env = get_current_context () in
  Printer.pr_constr_env env sigma t
let pr_econstr t =
  let sigma, env = get_current_context () in
  Printer.pr_econstr_env env sigma t
let ppconstr x = pp (pr_constr x)
let ppeconstr x = pp (pr_econstr x)
let ppconstr_expr x = let sigma,env = get_current_context () in pp (Ppconstr.pr_constr_expr env sigma x)
let ppconstr_univ x = Constrextern.with_universes ppconstr x
let ppglob_constr = (fun x -> pp(with_env_evm pr_lglob_constr_env x))
let pppattern = (fun x -> pp(envpp pr_constr_pattern_env x))
let pptype = (fun x -> try pp(envpp (fun env evm t -> pr_ltype_env env evm t) x) with e -> pp (str (Printexc.to_string e)))
let ppfconstr c = ppconstr (CClosure.term_of_fconstr c)

let ppuint63 i = pp (str (Uint63.to_string i))

let pp_parray pr a =
  let a, def = Parray.to_array a in
  let a = Array.to_list a in
  pp (str "[|" ++ prlist_with_sep (fun () -> str ";" ++ spc()) pr a ++ spc() ++ str "|" ++ spc() ++ pr def ++ str "|]")

let pp_constr_parray = pp_parray pr_constr
let pp_fconstr_parray = pp_parray (fun f -> pr_constr (CClosure.term_of_fconstr f))

let ppfsubst s =
  let (s, k) = Esubst.Internal.repr s in
  let sep () = str ";" ++ spc () in
  let pr = function
  | Esubst.Internal.REL n -> str "<#" ++ int n ++ str ">"
  | Esubst.Internal.VAL (k, x) -> pr_constr (Vars.lift k (CClosure.term_of_fconstr x))
  in
  pp @@ str "[" ++ prlist_with_sep sep pr s ++ str "| " ++ int k ++ str "]"

let ppnumtokunsigned n = pp (NumTok.Unsigned.print n)
let ppnumtokunsignednat n = pp (NumTok.UnsignedNat.print n)

let prset pr l = str "[" ++ hov 0 (prlist_with_sep spc pr l) ++ str "]"
let ppintset l = pp (prset int (Int.Set.elements l))
let ppidset l = pp (prset Id.print (Id.Set.elements l))

let prset' pr l = str "[" ++ hov 0 (prlist_with_sep pr_comma pr l) ++ str "]"

let pridmap pr l =
  let pr (id,b) = Id.print id ++ str "=>" ++ pr id b in
  prset' pr (Id.Map.fold (fun a b l -> (a,b)::l) l [])
let ppidmap pr l = pp (pridmap pr l)

let prmapgen pr dom =
  if dom = [] then str "[]" else
  str "[domain= " ++ hov 0 (prlist_with_sep spc pr dom) ++ str "]"
let pridmapgen l = prmapgen Id.print (Id.Set.elements (Id.Map.domain l))
let ppidmapgen l = pp (pridmapgen l)
let printmapgen l = prmapgen int (Int.Set.elements (Int.Map.domain l))
let ppintmapgen l = pp (printmapgen l)
let prmodidmapgen l = prmapgen Id.print (ModIdset.elements (ModIdmap.domain l))
let ppmodidmapgen l = pp (prmodidmapgen l)

let ppmpmapgen l =
  pp (prmapgen
        (fun mp -> str (ModPath.debug_to_string mp))
        (MPset.elements (MPmap.domain l)))

let ppdpmapgen l =
  pp (prmapgen
        (fun mp -> str (DirPath.to_string mp))
        (DPset.elements (DPmap.domain l)))

let ppconmapenvgen l =
  pp (prmapgen
        (fun mp -> str (Constant.debug_to_string mp))
        (Cset_env.elements (Cmap_env.domain l)))

let ppmindmapenvgen l =
  pp (prmapgen
        (fun mp -> str (MutInd.debug_to_string mp))
        (Mindmap_env.Set.elements (Mindmap_env.domain l)))

let ppevarsubst = ppidmap (fun id0 -> prset (fun (c,copt,id) ->
  hov 0
  (pr_constr c ++
   (match copt with None -> mt () | Some c -> spc () ++ str "<expanded: " ++
    pr_constr c ++ str">") ++
   (if id = id0 then mt ()
    else spc () ++ str "<canonical: " ++ Id.print id ++ str ">"))))

let prididmap = pridmap (fun _ -> Id.print)
let ppididmap = ppidmap (fun _ -> Id.print)

let prconstrunderbindersidmap = pridmap (fun _ (l,c) ->
  hov 1 (str"[" ++  prlist_with_sep spc Id.print l ++ str"]")
  ++ str "," ++ spc () ++ pr_econstr c)

let ppconstrunderbindersidmap l = pp (prconstrunderbindersidmap l)

let ppunbound_ltac_var_map l = ppidmap (fun _ arg ->
  str"<genarg:" ++ pr_argument_type(genarg_tag arg) ++ str">") l

open Ltac_pretype
let rec pr_closure {idents=idents;typed=typed;untyped=untyped} =
  hov 1 (str"{idents=" ++ prididmap idents ++ str";" ++ spc() ++
         str"typed=" ++ prconstrunderbindersidmap typed ++ str";" ++ spc() ++
         str"untyped=" ++ pr_closed_glob_constr_idmap untyped ++ str"}")
and pr_closed_glob_constr_idmap x =
  pridmap (fun _ -> pr_closed_glob_constr) x
and pr_closed_glob_constr {closure=closure;term=term} =
  pr_closure closure ++ with_env_evm pr_lglob_constr_env term

let ppclosure x = pp (pr_closure x)
let ppclosedglobconstr x = pp (pr_closed_glob_constr x)
let ppclosedglobconstridmap x = pp (pr_closed_glob_constr_idmap x)

let pP s = pp (hov 0 s)

let safe_pr_global = let open GlobRef in function
  | ConstRef kn -> pp (str "CONSTREF(" ++ Constant.debug_print kn ++ str ")")
  | IndRef (kn,i) -> pp (str "INDREF(" ++ MutInd.debug_print kn ++ str "," ++
                          int i ++ str ")")
  | ConstructRef ((kn,i),j) -> pp (str "CONSTRUCTREF(" ++ MutInd.debug_print kn ++ str "," ++
                                      int i ++ str "," ++ int j ++ str ")")
  | VarRef id -> pp (str "VARREF(" ++ Id.print id ++ str ")")

let ppglobal x = try pp(pr_global x) with _ -> safe_pr_global x

let ppconst (sp,j) =
    pp (str"#" ++ KerName.print sp ++ str"=" ++ envpp pr_lconstr_env j.uj_val)

let ppvar ((id,a)) =
    pp (str"#" ++ Id.print id ++ str":" ++ envpp pr_lconstr_env a)

let genppj f j = let (c,t) = f j in (c ++ str " : " ++ t)

let ppj j = pp (genppj (envpp pr_ljudge_env) j)

let ppsubst s = pp (Mod_subst.debug_pr_subst s)
let ppdelta s = pp (Mod_subst.debug_pr_delta s)

let pp_idpred s = pp (pr_idpred s)
let pp_cpred s = pp (pr_cpred s)
let pp_transparent_state s = pp (pr_transparent_state s)
let pp_estack_t n = pp (Reductionops.Stack.pr pr_econstr n)
let pp_state_t n = pp (Reductionops.pr_state Global.(env()) Evd.empty n)

(* proof printers *)
let pr_evar ev = Pp.int (Evar.repr ev)
let ppmetas metas = pp(Termops.pr_metaset metas)
let ppevm evd = pp(Termops.pr_evar_map ~with_univs:!Detyping.print_universes (Some 2) (Global.env ()) evd)
let ppevmall evd = pp(Termops.pr_evar_map ~with_univs:!Detyping.print_universes None (Global.env ()) evd)
let pr_existentialset evars =
  prlist_with_sep spc pr_evar (Evar.Set.elements evars)
let ppexistentialset evars =
  pp (pr_existentialset evars)
let ppexistentialfilter filter = match Evd.Filter.repr filter with
| None -> pp (Pp.str "ø")
| Some f -> pp (prlist_with_sep spc bool f)
let pr_goal e = Pp.(str "GOAL:" ++ int (Evar.repr e))
let ppclenv clenv = pp(pr_clenv clenv)
let ppgoal g = pp(Printer.Debug.pr_goal g)
let pphintdb db = pp(envpp Hints.pr_hint_db_env db)
let ppproofview p =
  let gls,sigma = Proofview.proofview p in
  pp(pr_enum pr_goal gls ++ fnl () ++ Termops.pr_evar_map (Some 1) (Global.env ()) sigma)

let ppopenconstr (x : Evd.open_constr) =
  let (evd,c) = x in pp (Termops.pr_evar_map (Some 2) (Global.env ()) evd ++ envpp pr_econstr_env c)
(* spiwack: deactivated until a replacement is found
let pppftreestate p = pp(print_pftreestate p)
*)

(* let ppgoal g = pp(db_pr_goal g) *)
(* let pr_gls gls = *)
(*   hov 0 (pr_evar_defs (sig_sig gls) ++ fnl () ++ db_pr_goal (sig_it gls)) *)

(* let pr_glls glls = *)
(*   hov 0 (pr_evar_defs (sig_sig glls) ++ fnl () ++ *)
(*          prlist_with_sep fnl db_pr_goal (sig_it glls)) *)

(* let ppsigmagoal g = pp(pr_goal (sig_it g)) *)
(* let prgls gls = pp(pr_gls gls) *)
(* let prglls glls = pp(pr_glls glls) *)

let pproof p = pp(Proof.pr_proof p)

let ppuni u = pp(Universe.raw_pr u)
let ppuni_level u = pp (Level.raw_pr u)
let ppqvar q = pp (QVar.raw_pr q)
let ppesorts s = pp (Sorts.debug_print (Evd.MiniEConstr.ESorts.unsafe_to_sorts s))

let prlev l = UnivNames.pr_level_with_global_universes l
let prqvar q = Sorts.QVar.raw_pr q
let ppqvarset l = pp (hov 1 (str "{" ++ prlist_with_sep spc QVar.raw_pr (QVar.Set.elements l) ++ str "}"))
let ppuniverse_set l = pp (Level.Set.pr prlev l)
let ppuniverse_instance l = pp (Instance.pr prqvar prlev l)
let ppuniverse_context l = pp (pr_universe_context prqvar prlev l)
let ppuniverse_context_set l = pp (pr_universe_context_set prlev l)
let ppuniverse_subst l = pp (UnivSubst.pr_universe_subst Level.raw_pr l)
let ppuniverse_opt_subst l = pp (UnivFlex.pr Level.raw_pr l)
let ppqvar_subst l = pp (UVars.pr_quality_level_subst QVar.raw_pr l)
let ppuniverse_level_subst l = pp (Univ.pr_universe_level_subst Level.raw_pr l)
let ppevar_universe_context l = pp (Termops.pr_evar_universe_context l)
let ppconstraints c = pp (Constraints.pr Level.raw_pr c)
let ppuniverseconstraints c = pp (UnivProblem.Set.pr c)
let ppuniverse_context_future c =
  let ctx = Future.force c in
    ppuniverse_context ctx
let ppuniverses u = pp (UGraph.pr_universes Level.raw_pr (UGraph.repr u))
let ppnamedcontextval e =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  pp (pr_named_context env sigma (named_context_of_val e))

let ppaucontext auctx =
  let qnas, unas = AbstractContext.names auctx in
  let prgen pr var_index nas l = match var_index l with
    | Some n -> (match nas.(n) with
        | Anonymous -> pr l
        | Name id -> Id.print id)
    | None -> pr l
  in
  let prqvar l = prgen prqvar Sorts.QVar.var_index qnas l in
  let prlev l = prgen prlev Level.var_index unas l in
  pp (pr_universe_context prqvar prlev (AbstractContext.repr auctx))


let ppenv e = pp
  (str "[" ++ pr_named_context_of e Evd.empty ++ str "]" ++ spc() ++
   str "[" ++ pr_rel_context e Evd.empty (rel_context e) ++ str "]")

let ppglobenv e = ppenv (GlobEnv.env e)

let ppenvwithcst e = pp
  (str "[" ++ pr_named_context_of e Evd.empty ++ str "]" ++ spc() ++
   str "[" ++ pr_rel_context e Evd.empty (rel_context e) ++ str "]" ++ spc() ++
   str "{" ++ Environ.fold_constants (fun a _ s -> Constant.print a ++ spc () ++ s) e (mt ()) ++ str "}")

let pptac = (fun x -> pp(Ltac_plugin.Pptactic.pr_glob_tactic (Global.env()) x))

let ppobj obj =
  let Libobject.Dyn.Dyn (tag, _) = obj in
  Format.print_string (Libobject.Dyn.repr tag)

let cnt = ref 0

let cast_kind_display k =
  match k with
  | VMcast -> "VMcast"
  | DEFAULTcast -> "DEFAULTcast"
  | NATIVEcast -> "NATIVEcast"

let constr_display csr =
  let rec term_display c = match kind c with
  | Rel n -> "Rel("^(string_of_int n)^")"
  | Meta n -> "Meta("^(string_of_int n)^")"
  | Var id -> "Var("^(Id.to_string id)^")"
  | Sort s -> "Sort("^(sort_display s)^")"
  | Cast (c,k, t) ->
      "Cast("^(term_display c)^","^(cast_kind_display k)^","^(term_display t)^")"
  | Prod (na,t,c) ->
      "Prod("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | Lambda (na,t,c) ->
      "Lambda("^(name_display na)^","^(term_display t)^","^(term_display c)^")\n"
  | LetIn (na,b,t,c) ->
      "LetIn("^(name_display na)^","^(term_display b)^","
      ^(term_display t)^","^(term_display c)^")"
  | App (c,l) -> "App("^(term_display c)^","^(array_display l)^")\n"
  | Evar (e,l) ->
    let l = SList.to_list l in
    let map = function None -> "?" | Some t -> term_display t in
    let l = List.map map l in
    "Evar("^(Pp.string_of_ppcmds (Evar.print e))^", [|"^(String.concat "; " l)^"|])"
  | Const (c,u) -> "Const("^(Constant.to_string c)^","^(universes_display u)^")"
  | Ind ((sp,i),u) ->
      "MutInd("^(MutInd.to_string sp)^","^(string_of_int i)^","^(universes_display u)^")"
  | Construct (((sp,i),j),u) ->
      "MutConstruct(("^(MutInd.to_string sp)^","^(string_of_int i)^"),"
      ^","^(universes_display u)^(string_of_int j)^")"
  | Proj (p, r, c) -> "Proj("^(Projection.to_string p)^","^term_display c ^")"
  | Case (ci,u,pms,((_,p),_),iv,c,bl) ->
      "MutCase(<abs>,"^(term_display p)^","^(term_display c)^","
      ^(array_display (Array.map snd bl))^")"
  | Fix ((t,i),(lna,tl,bl)) ->
      "Fix(([|"^(Array.fold_right (fun x i -> (string_of_int x)^(if not(i="")
        then (";"^i) else "")) t "")^"|],"^(string_of_int i)^"),"
      ^(array_display tl)^",[|"
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^"|],"
      ^(array_display bl)^")"
  | CoFix(i,(lna,tl,bl)) ->
      "CoFix("^(string_of_int i)^"),"
      ^(array_display tl)^","
      ^(Array.fold_right (fun x i -> (name_display x)^(if not(i="")
        then (";"^i) else "")) lna "")^","
      ^(array_display bl)^")"
  | Int i ->
      "Int("^(Uint63.to_string i)^")"
  | Float f ->
      "Float("^(Float64.to_string f)^")"
  | Array (u,t,def,ty) -> "Array("^(array_display t)^","^(term_display def)^","^(term_display ty)^")@{" ^universes_display u^"\n"

  and array_display v =
    "[|"^
    (Array.fold_right
       (fun x i -> (term_display x)^(if not(i="") then (";"^i) else ""))
       v "")^"|]"

  and univ_display u =
    incr cnt; pp (str "with " ++ int !cnt ++ str" " ++ Universe.raw_pr u ++ fnl ())

  and quality_display q =
    incr cnt; pp (str "with " ++ int !cnt ++ str" " ++ Sorts.Quality.raw_pr q ++ fnl ())

  and level_display u =
    incr cnt; pp (str "with " ++ int !cnt ++ str" " ++ Level.raw_pr u ++ fnl ())

  and sort_display = function
    | SProp -> "SProp"
    | Set -> "Set"
    | Prop -> "Prop"
    | Type u -> univ_display u;
        "Type("^(string_of_int !cnt)^")"
    | QSort (q, u) -> univ_display u; Printf.sprintf "QSort(%s, %i)" (Sorts.QVar.to_string q) !cnt

  and universes_display l =
    let qs, us = Instance.to_array l in
    let qs = Array.fold_right (fun x i ->
        quality_display x;
        (string_of_int !cnt)^
        (if not(i="") then (" "^i) else ""))
        qs ""
    in
    Array.fold_right (fun x i -> level_display x; (string_of_int !cnt)^(if not(i="")
        then (" "^i) else "")) us (if qs = "" then "" else (qs^" | "))

  and name_display x = match x.binder_name with
    | Name id -> "Name("^(Id.to_string id)^")"
    | Anonymous -> "Anonymous"

  in
  pp (str (term_display csr) ++fnl ())

let econstr_display c = constr_display EConstr.Unsafe.(to_constr c) ;;

open Format;;

let print_pure_constr csr =
  let rec term_display c = match Constr.kind c with
  | Rel n -> print_string "#"; print_int n
  | Meta n -> print_string "Meta("; print_int n; print_string ")"
  | Var id -> print_string (Id.to_string id)
  | Sort s -> sort_display s
  | Cast (c,_, t) -> open_hovbox 1;
      print_string "("; (term_display c); print_cut();
      print_string "::"; (term_display t); print_string ")"; close_box()
  | Prod ({binder_name=Name(id)},t,c) ->
      open_hovbox 1;
      print_string"("; print_string (Id.to_string id);
      print_string ":"; box_display t;
      print_string ")"; print_cut();
      box_display c; close_box()
  | Prod ({binder_name=Anonymous},t,c) ->
      print_string"("; box_display t; print_cut(); print_string "->";
      box_display c; print_string ")";
  | Lambda (na,t,c) ->
      print_string "["; name_display na;
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | LetIn (na,b,t,c) ->
      print_string "["; name_display na; print_string "=";
      box_display b; print_cut();
      print_string ":"; box_display t; print_string "]";
      print_cut(); box_display c;
  | App (c,l) ->
      print_string "(";
      box_display c;
      Array.iter (fun x -> print_space (); box_display x) l;
      print_string ")"
  | Evar (e,l) -> print_string "Evar#"; print_int (Evar.repr e); print_string "{";
      let iter = function None -> print_space (); print_string "?" | Some t -> print_space (); box_display t in
      List.iter iter (SList.to_list l);
      print_string"}"
  | Const (c,u) -> print_string "Cons(";
      sp_con_display c;
      print_string ","; universes_display u;
      print_string ")"
  | Proj (p,_,c') -> print_string "Proj(";
      sp_prj_display p;
      print_string ",";
      box_display c';
      print_string ")"
  | Ind ((sp,i),u) ->
      print_string "Ind(";
      sp_display sp;
      print_string ","; print_int i;
      print_string ","; universes_display u;
      print_string ")"
  | Construct (((sp,i),j),u) ->
      print_string "Constr(";
      sp_display sp;
      print_string ",";
      print_int i; print_string ","; print_int j;
      print_string ","; universes_display u;
      print_string ")"
  | Case (ci,u,pms,(p,_),iv,c,bl) ->
      let pr_ctx (nas, c) =
        Array.iter (fun na -> print_cut (); name_display na) nas;
        print_string " |- ";
        box_display c
      in
      open_vbox 0;
      print_cut(); print_string "Case";
      print_space(); box_display c; print_space ();
      print_cut(); print_string "in";
      print_cut(); print_string "Ind(";
      sp_display (fst ci.ci_ind);
      print_string ","; print_int (snd ci.ci_ind); print_string ")";
      print_string "@{"; universes_display u; print_string "}";
      Array.iter (fun x -> print_space (); box_display x) pms;
      print_cut(); print_string "return <"; pr_ctx p; print_string ">";
      print_cut(); print_string "with";
      open_vbox 0;
      Array.iter (fun x ->  print_cut();  pr_ctx x) bl;
      close_box();
      print_cut();
      print_string "end";
      close_box()
  | Fix ((t,i),(lna,tl,bl)) ->
      print_string "Fix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let print_fix () =
        for k = 0 to (Array.length tl) - 1 do
          open_vbox 0;
          name_display lna.(k); print_string "/";
          print_int t.(k); print_cut(); print_string ":";
          box_display tl.(k) ; print_cut(); print_string ":=";
          box_display bl.(k); close_box ();
          print_cut()
        done
      in print_string"{"; print_fix(); print_string"}"
  | CoFix(i,(lna,tl,bl)) ->
      print_string "CoFix("; print_int i; print_string ")";
      print_cut();
      open_vbox 0;
      let print_fix () =
        for k = 0 to (Array.length tl) - 1 do
          open_vbox 1;
          name_display lna.(k);  print_cut(); print_string ":";
          box_display tl.(k) ; print_cut(); print_string ":=";
          box_display bl.(k); close_box ();
          print_cut();
        done
      in print_string"{"; print_fix (); print_string"}"
  | Int i ->
     print_string ("Int("^(Uint63.to_string i)^")")
  | Float f ->
      print_string ("Float("^(Float64.to_string f)^")")
  | Array (u,t,def,ty) ->
      print_string "Array(";
      Array.iter (fun x -> box_display x; print_space()) t;
      print_string "|";
      box_display def;
      print_string ":";
      box_display ty;
      print_string ")@{";
      universes_display u;
      print_string "}"

  and box_display c = open_hovbox 1; term_display c; close_box()

  and universes_display u =
    let qs, us = Instance.to_array u in
    Array.iter (fun u -> print_space (); pp (Sorts.Quality.raw_pr u)) qs;
    Array.iter (fun u -> print_space (); pp (Level.raw_pr u)) us

  and sort_display = function
    | SProp -> print_string "SProp"
    | Set -> print_string "Set"
    | Prop -> print_string "Prop"
    | Type u -> open_hbox();
        print_string "Type("; pp (Universe.raw_pr u); print_string ")"; close_box()
    | QSort (q, u) -> open_hbox();
        print_string "QSort("; pp (QVar.raw_pr q); print_string ", "; pp (Universe.raw_pr u); print_string ")"; close_box()

  and name_display x = match x.binder_name with
    | Name id -> print_string (Id.to_string id)
    | Anonymous -> print_string "_"
(* Remove the top names for library and Scratch to avoid long names *)
  and sp_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
        | ("Coq"::_::l) -> l
        | l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (MutInd.debug_to_string sp)
  and sp_con_display sp =
(*    let dir,l = decode_kn sp in
    let ls =
      match List.rev_map Id.to_string (DirPath.repr dir) with
          ("Top"::l)-> l
        | ("Coq"::_::l) -> l
        | l             -> l
    in  List.iter (fun x -> print_string x; print_string ".") ls;*)
      print_string (Constant.debug_to_string sp)
  and sp_prj_display sp =
      print_string (Projection.debug_to_string sp)
  in
    try
     box_display csr; print_flush()
    with e ->
        print_string (Printexc.to_string e);print_flush ();
        raise e

let print_pure_econstr c = print_pure_constr EConstr.Unsafe.(to_constr c) ;;

let pploc x = let (l,r) = Loc.unloc x in
  print_string"(";print_int l;print_string",";print_int r;print_string")"

let pp_argument_type t = pp (pr_argument_type t)

let pp_generic_argument arg =
  pp(str"<genarg:"++pr_argument_type(genarg_tag arg)++str">")

let prgenarginfo arg =
  let Geninterp.Val.Dyn (tag, _) = arg in
  let tpe = Geninterp.Val.pr tag in
  (* FIXME *)
(*   try *)
(*     let data = Pptactic.pr_top_generic (Global.env ()) arg in *)
(*     str "<genarg:" ++ tpe ++ str " := [ " ++ data ++ str " ] >" *)
(*   with _any -> *)
    str "<genarg:" ++ tpe ++ str ">"

let ppgenarginfo arg = pp (prgenarginfo arg)

let ppgenargargt arg = pp (str (Genarg.ArgT.repr arg))

let ppist ist =
  let pr id arg = prgenarginfo arg in
  pp (pridmap pr ist.Geninterp.lfun)

(**********************************************************************)
(* Vernac-level debugging commands                                    *)

let in_current_context f c =
  let (evmap,sign) = get_current_context () in
  f (fst (Constrintern.interp_constr sign evmap c))(*FIXME*)

(* We expand the result of preprocessing to be independent of camlp5

VERNAC COMMAND EXTEND PrintPureConstr
| [ "PrintPureConstr" constr(c) ] -> [ in_current_context print_pure_constr c ]
END
VERNAC COMMAND EXTEND PrintConstr
  [ "PrintConstr" constr(c) ] -> [ in_current_context constr_display c ]
END
*)

let () =
  let open Vernacextend in
  let open Vernactypes in
  let ty_constr = Extend.TUentry (get_arg_tag Stdarg.wit_constr) in
  let cmd_sig = TyTerminal("PrintConstr", TyNonTerminal(ty_constr, TyNil)) in
  let cmd_fn c ?loc:_ ~atts () = vtdefault (fun () -> in_current_context econstr_display c) in
  let cmd_class _ = VtQuery in
  let cmd : ty_ml = TyML (false, cmd_sig, cmd_fn, Some cmd_class) in
  static_vernac_extend ~plugin:None ~command:"PrintConstr" [cmd]

let () =
  let open Vernacextend in
  let open Vernactypes in
  let ty_constr = Extend.TUentry (get_arg_tag Stdarg.wit_constr) in
  let cmd_sig = TyTerminal("PrintPureConstr", TyNonTerminal(ty_constr, TyNil)) in
  let cmd_fn c ?loc:_ ~atts () = vtdefault (fun () -> in_current_context print_pure_econstr c) in
  let cmd_class _ = VtQuery in
  let cmd : ty_ml = TyML (false, cmd_sig, cmd_fn, Some cmd_class) in
  static_vernac_extend ~plugin:None ~command:"PrintPureConstr" [cmd]

(* Setting printer of unbound global reference *)
open Names
open Libnames

let encode_path ?loc prefix mpdir suffix id =
  let dir = match mpdir with
    | None -> []
    | Some mp -> DirPath.repr (dirpath_of_string (ModPath.to_string mp))
  in
  make_qualid ?loc
    (DirPath.make (List.rev (Id.of_string prefix::dir@suffix))) id

let raw_string_of_ref ?loc _ = let open GlobRef in function
  | ConstRef cst ->
      let (mp,id) = KerName.repr (Constant.user cst) in
      encode_path ?loc "CST" (Some mp) [] (Label.to_id id)
  | IndRef (kn,i) ->
      let (mp,id) = KerName.repr (MutInd.user kn) in
      encode_path ?loc "IND" (Some mp) [Label.to_id id]
        (Id.of_string ("_"^string_of_int i))
  | ConstructRef ((kn,i),j) ->
      let (mp,id) = KerName.repr (MutInd.user kn) in
      encode_path ?loc "CSTR" (Some mp)
        [Label.to_id id;Id.of_string ("_"^string_of_int i)]
        (Id.of_string ("_"^string_of_int j))
  | VarRef id ->
      encode_path ?loc "SECVAR" None [] id

let short_string_of_ref ?loc _ = let open GlobRef in function
  | VarRef id -> qualid_of_ident ?loc id
  | ConstRef cst -> qualid_of_ident ?loc (Label.to_id (Constant.label cst))
  | IndRef (kn,0) -> qualid_of_ident ?loc (Label.to_id (MutInd.label kn))
  | IndRef (kn,i) ->
      encode_path ?loc "IND" None [Label.to_id (MutInd.label kn)]
        (Id.of_string ("_"^string_of_int i))
  | ConstructRef ((kn,i),j) ->
      encode_path ?loc "CSTR" None
        [Label.to_id (MutInd.label kn);Id.of_string ("_"^string_of_int i)]
        (Id.of_string ("_"^string_of_int j))

(* Anticipate that printers can be used from ocamldebug and that
   pretty-printer should not make calls to the global env since ocamldebug
   runs in a different process and does not have the proper env at hand *)
let () = Constrextern.set_extern_reference
  (if !rawdebug then raw_string_of_ref else short_string_of_ref)
