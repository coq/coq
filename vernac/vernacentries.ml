(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Concrete syntax of the mathematical vernacular MV V2.6 *)

open Pp
open CErrors
open CAst
open Util
open Names
open Printer
open Goptions
open Libnames
open Vernacexpr
open Locality
open Attributes

module NamedDecl = Context.Named.Declaration

(** TODO: make this function independent of Ltac *)
let (f_interp_redexp, interp_redexp_hook) = Hook.make ()

(* Utility functions, at some point they should all disappear and
   instead enviroment/state selection should be done at the Vernac DSL
   level. *)

let get_current_or_global_context ~pstate =
  match pstate with
  | None -> let env = Global.env () in Evd.(from_env env, env)
  | Some p -> Declare.Proof.get_current_context p

let get_goal_or_global_context ~pstate glnum =
  match pstate with
  | None -> let env = Global.env () in Evd.(from_env env, env)
  | Some p -> Declare.Proof.get_goal_context p glnum

let cl_of_qualid = function
  | FunClass -> Coercionops.CL_FUN
  | SortClass -> Coercionops.CL_SORT
  | RefClass r -> ComCoercion.class_of_global (Smartlocate.smart_global ~head:true r)

let scope_class_of_qualid qid =
  Notation.scope_class_of_class (cl_of_qualid qid)

(** Standard attributes for definition-like commands. *)
module DefAttributes = struct
  type t = {
    locality : bool option;
    polymorphic : bool;
    program : bool;
    deprecated : Deprecation.t option;
    canonical_instance : bool;
  }

  let parse f =
    let open Attributes in
    let (((locality, deprecated), polymorphic), program), canonical_instance =
      parse Notations.(locality ++ deprecation ++ polymorphic ++ program ++ canonical_instance) f
    in
    { polymorphic; program; locality; deprecated; canonical_instance }
end

let module_locality = Attributes.Notations.(locality >>= fun l -> return (make_module_locality l))

let with_locality ~atts f =
  let local = Attributes.(parse locality atts) in
  f ~local

let with_section_locality ~atts f =
  let local = Attributes.(parse locality atts) in
  let section_local = make_section_locality local in
  f ~section_local

let with_module_locality ~atts f =
  let module_local = Attributes.(parse module_locality atts) in
  f ~module_local

let with_def_attributes ~atts f =
  let atts = DefAttributes.parse atts in
  if atts.DefAttributes.program then Declare.Obls.check_program_libraries ();
  f ~atts

(*******************)
(* "Show" commands *)

let show_proof ~pstate =
  (* spiwack: this would probably be cooler with a bit of polishing. *)
  try
    let pstate = Option.get pstate in
    let p = Declare.Proof.get pstate in
    let sigma, _ = Declare.Proof.get_current_context pstate in
    let pprf = Proof.partial_proof p in
    (* In the absence of an environment explicitly attached to the
       proof and on top of which side effects of the proof would be pushed, ,
       we take the global environment which in practise should be a
       superset of the initial environment in which the proof was
       started *)
    let env = Global.env() in
    Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf
  (* We print nothing if there are no goals left *)
  with
  | Proof.NoSuchGoal _
  | Option.IsNone ->
    user_err (str "No goals to show.")

let show_top_evars ~proof =
  (* spiwack: new as of Feb. 2010: shows goal evars in addition to non-goal evars. *)
  let Proof.{goals;shelf;given_up;sigma} = Proof.data proof in
  pr_evars_int sigma ~shelf ~given_up 1 (Evd.undefined_map sigma)

let show_universes ~proof =
  let Proof.{goals;sigma} = Proof.data proof in
  let ctx = Evd.universe_context_set (Evd.minimize_universes sigma) in
  Termops.pr_evar_universe_context (Evd.evar_universe_context sigma) ++ fnl () ++
  str "Normalized constraints: " ++ Univ.pr_universe_context_set (Termops.pr_evd_level sigma) ctx

(* Simulate the Intro(s) tactic *)
let show_intro ~proof all =
  let open EConstr in
  let Proof.{goals;sigma} = Proof.data proof in
  if not (List.is_empty goals) then begin
    let gl = {Evd.it=List.hd goals ; sigma = sigma; } in
    let l,_= decompose_prod_assum sigma (Termops.strip_outer_cast sigma (Tacmach.pf_concl gl)) in
    if all then
      let lid = Tactics.find_intro_names l gl in
      hov 0 (prlist_with_sep  spc Id.print lid)
    else if not (List.is_empty l) then
      let n = List.last l in
      Id.print (List.hd (Tactics.find_intro_names [n] gl))
    else mt ()
  end else mt ()

(** Textual display of a generic "match" template *)

let show_match id =
  let patterns =
    try ComInductive.make_cases (Nametab.global_inductive id)
    with Not_found -> user_err Pp.(str "Unknown inductive type.")
  in
  let pr_branch l =
    str "| " ++ hov 1 (prlist_with_sep spc str l) ++ str " =>"
  in
  v 1 (str "match # with" ++ fnl () ++
       prlist_with_sep fnl pr_branch patterns ++ fnl () ++ str "end" ++ fnl ())

(* "Print" commands *)

let print_loadpath dir =
  let l = Loadpath.get_load_paths () in
  let l = match dir with
  | None -> l
  | Some dir ->
    let filter p = is_dirpath_prefix_of dir (Loadpath.logical p) in
    List.filter filter l
  in
  str "Logical Path / Physical path:" ++ fnl () ++
    prlist_with_sep fnl Loadpath.pp l

let print_modules () =
  let loaded = Library.loaded_libraries () in
  str"Loaded library files: " ++
  pr_vertical_list DirPath.print loaded


let print_module qid =
  try
    let open Nametab.GlobDirRef in
    let globdir = Nametab.locate_dir qid in
      match globdir with
          DirModule Nametab.{ obj_dir; obj_mp; _ } ->
          Printmod.print_module (Printmod.printable_body obj_dir) obj_mp
        | _ -> raise Not_found
  with
    Not_found -> user_err (str"Unknown Module " ++ pr_qualid qid)

let print_modtype qid =
  try
    let kn = Nametab.locate_modtype qid in
    Printmod.print_modtype kn
  with Not_found ->
    (* Is there a module of this name ? If yes we display its type *)
    try
      let mp = Nametab.locate_module qid in
      Printmod.print_module false mp
    with Not_found ->
      user_err (str"Unknown Module Type or Module " ++ pr_qualid qid)

let print_namespace ~pstate ns =
  let ns = List.rev (Names.DirPath.repr ns) in
  (* [match_dirpath], [match_modulpath] are helpers for [matches]
     which checks whether a constant is in the namespace [ns]. *)
  let rec match_dirpath ns = function
    | [] -> Some ns
    | id::dir ->
        begin match match_dirpath ns dir with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  let rec match_modulepath ns = function
    | MPbound _ -> None (* Not a proper namespace. *)
    | MPfile dir -> match_dirpath ns (Names.DirPath.repr dir)
    | MPdot (mp,lbl) ->
        let id = Names.Label.to_id lbl in
        begin match match_modulepath ns mp with
        | Some [] as y -> y
        | Some (a::ns') ->
            if Names.Id.equal a id then Some ns'
            else None
        | None -> None
        end
  in
  (* [qualified_minus n mp] returns a list of qualifiers representing
     [mp] except the [n] first (in the concrete syntax order).  The
     idea is that if [mp] matches [ns], then [qualified_minus mp
     (length ns)] will be the correct representation of [mp] assuming
     [ns] is imported. *)
  (* precondition: [mp] matches some namespace of length [n] *)
  let qualified_minus n mp =
    let rec list_of_modulepath = function
      | MPbound _ -> assert false (* MPbound never matches *)
      | MPfile dir -> Names.DirPath.repr dir
      | MPdot (mp,lbl) -> (Names.Label.to_id lbl)::(list_of_modulepath mp)
    in
    snd (Util.List.chop n (List.rev (list_of_modulepath mp)))
  in
  let print_list pr l = prlist_with_sep (fun () -> str".") pr l in
  let print_kn kn =
    let (mp,lbl) = Names.KerName.repr kn in
    let qn = (qualified_minus (List.length ns) mp)@[Names.Label.to_id lbl] in
    print_list Id.print qn
  in
  let print_constant ~pstate k body =
    (* FIXME: universes *)
    let t = body.Declarations.const_type in
    let sigma, env = get_current_or_global_context ~pstate in
    print_kn k ++ str":" ++ spc() ++ Printer.pr_type_env env sigma t
  in
  let matches mp = match match_modulepath ns mp with
  | Some [] -> true
  | _ -> false in
  let constants_in_namespace =
    Environ.fold_constants (fun c body acc ->
        let kn = Constant.user c in
        if matches (KerName.modpath kn)
        then acc++fnl()++hov 2 (print_constant ~pstate kn body)
        else acc)
      (Global.env ()) (str"")
  in
  (print_list Id.print ns)++str":"++fnl()++constants_in_namespace

let print_strategy r =
  let open Conv_oracle in
  let pr_level = function
  | Expand -> str "expand"
  | Level 0 -> str "transparent"
  | Level n -> str "level" ++ spc() ++ int n
  | Opaque -> str "opaque"
  in
  let pr_strategy (ref, lvl) = pr_global ref ++ str " : " ++ pr_level lvl in
  let oracle = Environ.oracle (Global.env ()) in
  match r with
  | None ->
    let fold key lvl (vacc, cacc) = match key with
    | VarKey id -> ((GlobRef.VarRef id, lvl) :: vacc, cacc)
    | ConstKey cst -> (vacc, (GlobRef.ConstRef cst, lvl) :: cacc)
    | RelKey _ -> (vacc, cacc)
    in
    let var_lvl, cst_lvl = fold_strategy fold oracle ([], []) in
    let var_msg =
      if List.is_empty var_lvl then mt ()
      else str "Variable strategies" ++ fnl () ++
        hov 0 (prlist_with_sep fnl pr_strategy var_lvl) ++ fnl ()
    in
    let cst_msg =
      if List.is_empty cst_lvl then mt ()
      else str "Constant strategies" ++ fnl () ++
        hov 0 (prlist_with_sep fnl pr_strategy cst_lvl)
    in
    var_msg ++ cst_msg
  | Some r ->
    let r = Smartlocate.smart_global r in
    let key = let open GlobRef in match r with
    | VarRef id -> VarKey id
    | ConstRef cst -> ConstKey cst
    | IndRef _ | ConstructRef _ -> user_err Pp.(str "The reference is not unfoldable")
    in
    let lvl = get_strategy oracle key in
    pr_strategy (r, lvl)

let print_registered () =
  let pr_lib_ref (s,r) =
    pr_global r ++ str " registered as " ++ str s
  in
  hov 0 (prlist_with_sep fnl pr_lib_ref @@ Coqlib.get_lib_refs ())


let dump_universes_gen prl g s =
  let output = open_out s in
  let output_constraint, close =
    if Filename.check_suffix s ".dot" || Filename.check_suffix s ".gv" then begin
      (* the lazy unit is to handle errors while printing the first line *)
      let init = lazy (Printf.fprintf output "digraph universes {\n") in
      begin fun kind left right ->
        let () = Lazy.force init in
        match kind with
          | Univ.Lt ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=bold];\n" right left
          | Univ.Le ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=solid];\n" right left
          | Univ.Eq ->
            Printf.fprintf output "  \"%s\" -> \"%s\" [style=dashed];\n" left right
      end, begin fun () ->
        if Lazy.is_val init then Printf.fprintf output "}\n";
        close_out output
      end
    end else begin
      begin fun kind left right ->
        let kind = match kind with
          | Univ.Lt -> "<"
          | Univ.Le -> "<="
          | Univ.Eq -> "="
        in
        Printf.fprintf output "%s %s %s ;\n" left kind right
      end, (fun () -> close_out output)
    end
  in
  let output_constraint k l r = output_constraint k (prl l) (prl r) in
  try
    UGraph.dump_universes output_constraint g;
    close ();
    str "Universes written to file \"" ++ str s ++ str "\"."
  with reraise ->
    let reraise = Exninfo.capture reraise in
    close ();
    Exninfo.iraise reraise

let universe_subgraph ?loc g univ =
  let open Univ in
  let sigma = Evd.from_env (Global.env()) in
  let univs_of q =
    let q =  Glob_term.(GType q) in
    (* this function has a nice error message for not found univs *)
    LSet.singleton (Pretyping.interp_known_glob_level ?loc sigma q)
  in
  let univs = List.fold_left (fun univs q -> LSet.union univs (univs_of q)) LSet.empty g in
  let csts = UGraph.constraints_for ~kept:(LSet.add Level.prop (LSet.add Level.set univs)) univ in
  let univ = LSet.fold UGraph.add_universe_unconstrained univs UGraph.initial_universes in
  UGraph.merge_constraints csts univ

let print_universes ?loc ~sort ~subgraph dst =
  let univ = Global.universes () in
  let univ = match subgraph with
    | None -> univ
    | Some g -> universe_subgraph ?loc g univ
  in
  let univ = if sort then UGraph.sort_universes univ else univ in
  let pr_remaining =
    if Global.is_joined_environment () then mt ()
    else str"There may remain asynchronous universe constraints"
  in
  let prl = UnivNames.pr_with_global_universes in
  begin match dst with
    | None -> UGraph.pr_universes prl univ ++ pr_remaining
    | Some s -> dump_universes_gen (fun u -> Pp.string_of_ppcmds (prl u)) univ s
  end

(*********************)
(* "Locate" commands *)

let locate_file f =
  let file = Flags.silently Loadpath.locate_file f in
  str file

let msg_found_library = function
  | Loadpath.LibLoaded, fulldir, file ->
    hov 0 (DirPath.print fulldir ++ strbrk " has been loaded from file " ++ str file)
  | Loadpath.LibInPath, fulldir, file ->
    hov 0 (DirPath.print fulldir ++ strbrk " is bound to file " ++ str file)

let err_unmapped_library ?from qid =
  let dir = fst (repr_qualid qid) in
  let prefix = match from with
  | None -> str "."
  | Some from ->
    str " and prefix " ++ DirPath.print from ++ str "."
  in
  user_err ?loc:qid.CAst.loc
    ~hdr:"locate_library"
    (strbrk "Cannot find a physical path bound to logical path matching suffix " ++
       DirPath.print dir ++ prefix)

let err_notfound_library ?from qid =
  let prefix = match from with
  | None -> str "."
  | Some from ->
    str " with prefix " ++ DirPath.print from ++ str "."
  in
  let bonus =
    if !Flags.load_vos_libraries then " (While searching for a .vos file.)" else "" in
  user_err ?loc:qid.CAst.loc ~hdr:"locate_library"
     (strbrk "Unable to locate library " ++ pr_qualid qid ++ prefix ++ str bonus)

let print_located_library qid =
  let open Loadpath in
  match locate_qualified_library ~warn:false qid with
  | Ok lib -> msg_found_library lib
  | Error LibUnmappedDir -> err_unmapped_library qid
  | Error LibNotFound -> err_notfound_library qid

let smart_global r =
  let gr = Smartlocate.smart_global r in
  Dumpglob.add_glob ?loc:r.loc gr;
  gr

let dump_global r =
  try
    let gr = Smartlocate.smart_global r in
    Dumpglob.add_glob ?loc:r.loc gr
  with e when CErrors.noncritical e -> ()
(**********)
(* Syntax *)

let vernac_syntax_extension ~module_local infix l =
  if infix then Metasyntax.check_infix_modifiers (snd l);
  Metasyntax.add_syntax_extension ~local:module_local l

let vernac_declare_scope ~module_local sc =
  Metasyntax.declare_scope module_local sc

let vernac_delimiters ~module_local sc action =
  match action with
  | Some lr -> Metasyntax.add_delimiters module_local sc lr
  | None -> Metasyntax.remove_delimiters module_local sc

let vernac_bind_scope ~module_local sc cll =
  Metasyntax.add_class_scope module_local sc (List.map scope_class_of_qualid cll)

let vernac_open_close_scope ~section_local (b,s) =
  Notation.open_close_scope (section_local,b,s)

let vernac_infix ~atts =
  let module_local, deprecation = Attributes.(parse Notations.(module_locality ++ deprecation) atts) in
  Metasyntax.add_infix ~local:module_local deprecation (Global.env())

let vernac_notation ~atts =
  let module_local, deprecation = Attributes.(parse Notations.(module_locality ++ deprecation) atts) in
  Metasyntax.add_notation ~local:module_local deprecation (Global.env())

let vernac_custom_entry ~module_local s =
  Metasyntax.declare_custom_entry module_local s

(***********)
(* Gallina *)

let check_name_freshness locality {CAst.loc;v=id} : unit =
  (* We check existence here: it's a bit late at Qed time *)
  if Nametab.exists_cci (Lib.make_path id) || Termops.is_section_variable id ||
     locality <> Locality.Discharge && Nametab.exists_cci (Lib.make_path_except_section id)
  then
    user_err ?loc  (Id.print id ++ str " already exists.")

let program_inference_hook env sigma ev =
  let tac = !Declare.Obls.default_tactic in
  let evi = Evd.find sigma ev in
  let evi = Evarutil.nf_evar_info sigma evi in
  let env = Evd.evar_filtered_env env evi in
  try
    let concl = evi.Evd.evar_concl in
    if not (Evarutil.is_ground_env sigma env &&
            Evarutil.is_ground_term sigma concl)
    then None
    else
      let c, _, _, _, ctx =
        Declare.build_by_tactic ~poly:false env ~uctx:(Evd.evar_universe_context sigma) ~typ:concl tac
      in
      Some (Evd.set_universe_context sigma ctx, EConstr.of_constr c)
  with
  | Logic_monad.TacticFailure e when noncritical e ->
    user_err Pp.(str "The statement obligations could not be resolved \
                      automatically, write a statement definition first.")

(* XXX: Interpretation of lemma command, duplication with ComFixpoint
   / ComDefinition ? *)
let interp_lemma ~program_mode ~flags ~scope env0 evd thms =
  let inference_hook = if program_mode then Some program_inference_hook else None in
  List.fold_left_map (fun evd ((id, _), (bl, t)) ->
      let evd, (impls, ((env, ctx), imps)) =
        Constrintern.interp_context_evars ~program_mode env0 evd bl
      in
      let evd, (t', imps') = Constrintern.interp_type_evars_impls ~flags ~impls env evd t in
      let flags = Pretyping.{ all_and_fail_flags with program_mode } in
      let evd = Pretyping.solve_remaining_evars ?hook:inference_hook flags env evd in
      let ids = List.map Context.Rel.Declaration.get_name ctx in
      check_name_freshness scope id;
      let thm = Declare.CInfo.make ~name:id.CAst.v ~typ:(EConstr.it_mkProd_or_LetIn t' ctx)
          ~args:ids ~impargs:(imps @ imps') () in
      evd, thm)
    evd thms

(* Checks done in start_lemma_com *)
let post_check_evd ~udecl ~poly evd =
  let () =
    if not UState.(udecl.univdecl_extensible_instance &&
                   udecl.univdecl_extensible_constraints) then
      ignore (Evd.check_univ_decl ~poly evd udecl)
  in
  if poly then evd
  else (* We fix the variables to ensure they won't be lowered to Set *)
    Evd.fix_undefined_variables evd

let start_lemma_com ~program_mode ~poly ~scope ~kind ?hook thms =
  let env0 = Global.env () in
  let flags = Pretyping.{ all_no_fail_flags with program_mode } in
  let decl = fst (List.hd thms) in
  let evd, udecl = Constrexpr_ops.interp_univ_decl_opt env0 (snd decl) in
  let evd, thms = interp_lemma ~program_mode ~flags ~scope env0 evd thms in
  let mut_analysis = RecLemmas.look_for_possibly_mutual_statements evd thms in
  let evd = Evd.minimize_universes evd in
  match mut_analysis with
  | RecLemmas.NonMutual thm ->
    let thm = Declare.CInfo.to_constr evd thm in
    let evd = post_check_evd ~udecl ~poly evd in
    let info = Declare.Info.make ?hook ~poly ~scope ~kind ~udecl () in
    Declare.Proof.start_with_initialization ~info ~cinfo:thm evd
  | RecLemmas.Mutual { mutual_info; cinfo ; possible_guards } ->
    let cinfo = List.map (Declare.CInfo.to_constr evd) cinfo in
    let evd = post_check_evd ~udecl ~poly evd in
    let info = Declare.Info.make ?hook ~poly ~scope ~kind ~udecl () in
    Declare.Proof.start_mutual_with_initialization ~info ~cinfo evd ~mutual_info (Some possible_guards)

let vernac_definition_hook ~canonical_instance ~local ~poly = let open Decls in function
| Coercion ->
  Some (ComCoercion.add_coercion_hook ~poly)
| CanonicalStructure ->
  Some (Declare.Hook.(make (fun { S.dref } -> Canonical.declare_canonical_structure ?local dref)))
| SubClass ->
  Some (ComCoercion.add_subclass_hook ~poly)
| Definition when canonical_instance ->
  Some (Declare.Hook.(make (fun { S.dref } -> Canonical.declare_canonical_structure ?local dref)))
| Let when canonical_instance ->
  Some (Declare.Hook.(make (fun { S.dref } -> Canonical.declare_canonical_structure dref)))
| _ -> None

let default_thm_id = Id.of_string "Unnamed_thm"

let fresh_name_for_anonymous_theorem () =
  Namegen.next_global_ident_away default_thm_id Id.Set.empty

let vernac_definition_name lid local =
  let lid =
    match lid with
    | { v = Name.Anonymous; loc } ->
         CAst.make ?loc (fresh_name_for_anonymous_theorem ())
    | { v = Name.Name n; loc } -> CAst.make ?loc n in
  let () =
    match local with
    | Discharge -> Dumpglob.dump_definition lid true "var"
    | Global _ -> Dumpglob.dump_definition lid false "def"
  in
  lid

let vernac_definition_interactive ~atts (discharge, kind) (lid, pl) bl t =
  let open DefAttributes in
  let local = enforce_locality_exp atts.locality discharge in
  let hook = vernac_definition_hook ~canonical_instance:atts.canonical_instance ~local:atts.locality ~poly:atts.polymorphic kind in
  let program_mode = atts.program in
  let poly = atts.polymorphic in
  let name = vernac_definition_name lid local in
  start_lemma_com ~program_mode ~poly ~scope:local ~kind:(Decls.IsDefinition kind) ?hook [(name, pl), (bl, t)]

let vernac_definition ~atts (discharge, kind) (lid, pl) bl red_option c typ_opt =
  let open DefAttributes in
  let scope = enforce_locality_exp atts.locality discharge in
  let hook = vernac_definition_hook ~canonical_instance:atts.canonical_instance ~local:atts.locality ~poly:atts.polymorphic kind in
  let program_mode = atts.program in
  let name = vernac_definition_name lid scope in
  let red_option = match red_option with
    | None -> None
    | Some r ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Some (snd (Hook.get f_interp_redexp env sigma r)) in
  if program_mode then
    let kind = Decls.IsDefinition kind in
    ComDefinition.do_definition_program ~name:name.v
      ~poly:atts.polymorphic ~scope ~kind pl bl red_option c typ_opt ?hook
  else
    let () =
      ComDefinition.do_definition ~name:name.v
        ~poly:atts.polymorphic ~scope ~kind pl bl red_option c typ_opt ?hook in
    ()

(* NB: pstate argument to use combinators easily *)
let vernac_start_proof ~atts kind l =
  let open DefAttributes in
  let scope = enforce_locality_exp atts.locality NoDischarge in
  if Dumpglob.dump () then
    List.iter (fun ((id, _), _) -> Dumpglob.dump_definition id false "prf") l;
  start_lemma_com ~program_mode:atts.program ~poly:atts.polymorphic ~scope ~kind:(Decls.IsProof kind) l

let vernac_end_proof ~lemma = let open Vernacexpr in function
  | Admitted ->
    Declare.Proof.save_admitted ~proof:lemma
  | Proved (opaque,idopt) ->
    let _ : Names.GlobRef.t list = Declare.Proof.save ~proof:lemma ~opaque ~idopt
    in ()

let vernac_exact_proof ~lemma c =
  (* spiwack: for simplicity I do not enforce that "Proof proof_term" is
     called only at the beginning of a proof. *)
  let lemma, status = Declare.Proof.by (Tactics.exact_proof c) lemma in
  let _ : _ list = Declare.Proof.save ~proof:lemma ~opaque:Opaque ~idopt:None in
  if not status then Feedback.feedback Feedback.AddedAxiom

let vernac_assumption ~atts discharge kind l nl =
  let open DefAttributes in
  let scope = enforce_locality_exp atts.locality discharge in
  List.iter (fun (is_coe,(idl,c)) ->
    if Dumpglob.dump () then
      List.iter (fun (lid, _) ->
          match scope with
            | Global _ -> Dumpglob.dump_definition lid false "ax"
            | Discharge -> Dumpglob.dump_definition lid true "var") idl) l;
  ComAssumption.do_assumptions ~poly:atts.polymorphic ~program_mode:atts.program ~scope ~kind nl l

let is_polymorphic_inductive_cumulativity =
  declare_bool_option_and_ref ~depr:false ~value:false
    ~key:["Polymorphic";"Inductive";"Cumulativity"]

let polymorphic_cumulative =
  let error_poly_context () =
    user_err
      Pp.(str "The cumulative and noncumulative attributes can only be used in a polymorphic context.");
  in
  let open Attributes in
  let open Notations in
  qualify_attribute "universes"
    (bool_attribute ~name:"Polymorphism" ~on:"polymorphic" ~off:"monomorphic"
     ++ bool_attribute ~name:"Cumulativity" ~on:"cumulative" ~off:"noncumulative")
  >>= function
  | Some poly, Some cum ->
     (* Case of Polymorphic|Monomorphic Cumulative|NonCumulative Inductive
        and #[ universes(polymorphic|monomorphic,cumulative|noncumulative) ] Inductive *)
     if poly then return (true, cum)
     else error_poly_context ()
  | Some poly, None ->
     (* Case of Polymorphic|Monomorphic Inductive
        and #[ universes(polymorphic|monomorphic) ] Inductive *)
     if poly then return (true, is_polymorphic_inductive_cumulativity ())
     else return (false, false)
  | None, Some cum ->
     (* Case of Cumulative|NonCumulative Inductive *)
     if is_universe_polymorphism () then return (true, cum)
     else error_poly_context ()
  | None, None ->
     (* Case of Inductive *)
     if is_universe_polymorphism () then
       return (true, is_polymorphic_inductive_cumulativity ())
     else
       return (false, false)

let get_uniform_inductive_parameters =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Uniform"; "Inductive"; "Parameters"]
    ~value:false

let should_treat_as_uniform () =
  if get_uniform_inductive_parameters ()
  then ComInductive.UniformParameters
  else ComInductive.NonUniformParameters

let vernac_record ~template udecl ~cumulative k ~poly finite records =
  let map ((coe, id), binders, sort, nameopt, cfs) =
    let const = match nameopt with
    | None -> Nameops.add_prefix "Build_" id.v
    | Some lid ->
      let () = Dumpglob.dump_definition lid false "constr" in
      lid.v
    in
    let () =
      if Dumpglob.dump () then
        let () = Dumpglob.dump_definition id false "rec" in
        let iter (x, _) = match x with
        | Vernacexpr.AssumExpr ({loc;v=Name id}, _) ->
          Dumpglob.dump_definition (make ?loc id) false "proj"
        | _ -> ()
        in
        List.iter iter cfs
    in
    coe, id, binders, cfs, const, sort
  in
  let records = List.map map records in
  ignore(Record.definition_structure ~template udecl k ~cumulative ~poly finite records)

let extract_inductive_udecl (indl:(inductive_expr * decl_notation list) list) =
  match indl with
  | [] -> assert false
  | (((coe,(id,udecl)),b,c,d),e) :: rest ->
    let rest = List.map (fun (((coe,(id,udecl)),b,c,d),e) ->
        if Option.has_some udecl
        then user_err ~hdr:"inductive udecl" Pp.(strbrk "Universe binders must be on the first inductive of the block.")
        else (((coe,id),b,c,d),e))
        rest
    in
    udecl, (((coe,id),b,c,d),e) :: rest

let finite_of_kind = let open Declarations in function
  | Inductive_kw -> Finite
  | CoInductive -> CoFinite
  | Variant | Record | Structure | Class _ -> BiFinite

let private_ind =
  let open Attributes in
  let open Notations in
  attribute_of_list
    [ "matching"
    , single_key_parser ~name:"Private (matching) inductive type" ~key:"matching" ()
    ]
  |> qualify_attribute "private"
  >>= function
  | Some () -> return true
  | None -> return false

let vernac_inductive ~atts kind indl =
  let (template, (poly, cumulative)), private_ind = Attributes.(
      parse Notations.(template ++ polymorphic_cumulative ++ private_ind) atts) in
  let open Pp in
  let udecl, indl = extract_inductive_udecl indl in
  if Dumpglob.dump () then
    List.iter (fun (((coe,lid), _, _, cstrs), _) ->
      match cstrs with
        | Constructors cstrs ->
            Dumpglob.dump_definition lid false "ind";
            List.iter (fun (_, (lid, _)) ->
                         Dumpglob.dump_definition lid false "constr") cstrs
        | _ -> () (* dumping is done by vernac_record (called below) *) )
      indl;

  let finite = finite_of_kind kind in
  let is_record = function
  | ((_ , _ , _ , RecordDecl _), _) -> true
  | _ -> false
  in
  let is_constructor = function
  | ((_ , _ , _ , Constructors _), _) -> true
  | _ -> false
  in
  let is_defclass = match kind, indl with
  | Class _, [ ( id , bl , c , Constructors [l]), [] ] -> Some (id, bl, c, l)
  | _ -> None
  in
  if Option.has_some is_defclass then
    (* Definitional class case *)
    let (id, bl, c, l) = Option.get is_defclass in
    let bl = match bl with
      | bl, None -> bl
      | _ -> CErrors.user_err Pp.(str "Definitional classes do not support the \"|\" syntax.")
    in
    let (coe, (lid, ce)) = l in
    let coe' = if coe then Some true else None in
    let f = AssumExpr ((make ?loc:lid.loc @@ Name lid.v), ce),
            { rf_subclass = coe' ; rf_priority = None ; rf_notation = [] ; rf_canonical = true } in
    vernac_record ~template udecl ~cumulative (Class true) ~poly finite [id, bl, c, None, [f]]
  else if List.for_all is_record indl then
    (* Mutual record case *)
    let () = match kind with
      | Variant ->
        user_err (str "The Variant keyword does not support syntax { ... }.")
      | Record | Structure | Class _ | Inductive_kw | CoInductive -> ()
    in
    let check_where ((_, _, _, _), wh) = match wh with
    | [] -> ()
    | _ :: _ ->
      user_err (str "where clause not supported for records")
    in
    let () = List.iter check_where indl in
    let unpack ((id, bl, c, decl), _) = match decl with
    | RecordDecl (oc, fs) ->
      let bl = match bl with
        | bl, None -> bl
        | _ -> CErrors.user_err Pp.(str "Records do not support the \"|\" syntax.")
      in
      (id, bl, c, oc, fs)
    | Constructors _ -> assert false (* ruled out above *)
    in
    let kind = match kind with Class _ -> Class false | _ -> kind in
    let recordl = List.map unpack indl in
    vernac_record ~template udecl ~cumulative kind ~poly finite recordl
  else if List.for_all is_constructor indl then
    (* Mutual inductive case *)
    let () = match kind with
    | (Record | Structure) ->
      user_err (str "The Record keyword is for types defined using the syntax { ... }.")
    | Class _ ->
      user_err (str "Inductive classes not supported")
    | Variant | Inductive_kw | CoInductive -> ()
    in
    let check_name ((na, _, _, _), _) = match na with
    | (true, _) ->
      user_err (str "Variant types do not handle the \"> Name\" \
        syntax, which is reserved for records. Use the \":>\" \
        syntax on constructors instead.")
    | _ -> ()
    in
    let () = List.iter check_name indl in
    let unpack (((_, id) , bl, c, decl), ntn) = match decl with
    | Constructors l -> (id, bl, c, l), ntn
    | RecordDecl _ -> assert false (* ruled out above *)
    in
    let indl = List.map unpack indl in
    let uniform = should_treat_as_uniform () in
    ComInductive.do_mutual_inductive ~template udecl indl ~cumulative ~poly ~private_ind ~uniform finite
  else
    user_err (str "Mixed record-inductive definitions are not allowed")

let vernac_fixpoint_common ~atts discharge l =
  if Dumpglob.dump () then
    List.iter (fun { fname } -> Dumpglob.dump_definition fname false "def") l;
  enforce_locality_exp atts.DefAttributes.locality discharge

let vernac_fixpoint_interactive ~atts discharge l =
  let open DefAttributes in
  let scope = vernac_fixpoint_common ~atts discharge l in
  if atts.program then
    CErrors.user_err Pp.(str"Program Fixpoint requires a body");
  ComFixpoint.do_fixpoint_interactive ~scope ~poly:atts.polymorphic l

let vernac_fixpoint ~atts discharge l =
  let open DefAttributes in
  let scope = vernac_fixpoint_common ~atts discharge l in
  if atts.program then
    (* XXX: Switch to the attribute system and match on ~atts *)
    ComProgramFixpoint.do_fixpoint ~scope ~poly:atts.polymorphic l
  else
    ComFixpoint.do_fixpoint ~scope ~poly:atts.polymorphic l

let vernac_cofixpoint_common ~atts discharge l =
  if Dumpglob.dump () then
    List.iter (fun { fname } -> Dumpglob.dump_definition fname false "def") l;
  enforce_locality_exp atts.DefAttributes.locality discharge

let vernac_cofixpoint_interactive ~atts discharge l =
  let open DefAttributes in
  let scope = vernac_cofixpoint_common ~atts discharge l in
  if atts.program then
    CErrors.user_err Pp.(str"Program CoFixpoint requires a body");
  ComFixpoint.do_cofixpoint_interactive ~scope ~poly:atts.polymorphic l

let vernac_cofixpoint ~atts discharge l =
  let open DefAttributes in
  let scope = vernac_cofixpoint_common ~atts discharge l in
  if atts.program then
    ComProgramFixpoint.do_cofixpoint ~scope ~poly:atts.polymorphic l
  else
    ComFixpoint.do_cofixpoint ~scope ~poly:atts.polymorphic l

let vernac_scheme l =
  if Dumpglob.dump () then
    List.iter (fun (lid, s) ->
               Option.iter (fun lid -> Dumpglob.dump_definition lid false "def") lid;
               match s with
               | InductionScheme (_, r, _)
               | CaseScheme (_, r, _)
               | EqualityScheme r -> dump_global r) l;
  Indschemes.do_scheme l

let vernac_combined_scheme lid l =
  if Dumpglob.dump () then
    (Dumpglob.dump_definition lid false "def";
     List.iter (fun {loc;v=id} -> dump_global (make ?loc @@ Constrexpr.AN (qualid_of_ident ?loc id))) l);
 Indschemes.do_combined_scheme lid l

let vernac_universe ~poly l =
  if poly && not (Global.sections_are_opened ()) then
    user_err ~hdr:"vernac_universe"
                 (str"Polymorphic universes can only be declared inside sections, " ++
                  str "use Monomorphic Universe instead");
  DeclareUniv.do_universe ~poly l

let vernac_constraint ~poly l =
  if poly && not (Global.sections_are_opened ()) then
    user_err ~hdr:"vernac_constraint"
                 (str"Polymorphic universe constraints can only be declared"
                  ++ str " inside sections, use Monomorphic Constraint instead");
  DeclareUniv.do_constraint ~poly l

(**********************)
(* Modules            *)

let add_subnames_of ns full_n n =
  let open GlobRef in
  let module NSet = Globnames.ExtRefSet in
  let add1 r ns = NSet.add (Globnames.TrueGlobal r) ns in
  match n with
  | Globnames.SynDef _ | Globnames.TrueGlobal (ConstRef _ | ConstructRef _ | VarRef _) ->
    CErrors.user_err Pp.(str "Only inductive types can be used with Import (...).")
  | Globnames.TrueGlobal (IndRef (mind,i)) ->
    let open Declarations in
    let dp = Libnames.dirpath full_n in
    let mib = Global.lookup_mind mind in
    let mip = mib.mind_packets.(i) in
    let ns = add1 (IndRef (mind,i)) ns in
    let ns = Array.fold_left_i (fun j ns _ -> add1 (ConstructRef ((mind,i),j+1)) ns)
        ns mip.mind_consnames
    in
    List.fold_left (fun ns f ->
        let s = Indrec.elimination_suffix f in
        let n_elim = Id.of_string (Id.to_string mip.mind_typename ^ s) in
        match Nametab.extended_global_of_path (Libnames.make_path dp n_elim) with
        | exception Not_found -> ns
        | n_elim -> NSet.add n_elim ns)
      ns Sorts.all_families

let interp_filter_in m = function
  | ImportAll ->  Libobject.Unfiltered
  | ImportNames ns ->
    let module NSet = Globnames.ExtRefSet in
    let dp_m = Nametab.dirpath_of_module m in
    let ns =
      List.fold_left (fun ns (n,etc) ->
          let full_n =
            let dp_n,n = repr_qualid n in
            make_path (append_dirpath dp_m dp_n) n
          in
          let n = try Nametab.extended_global_of_path full_n
            with Not_found ->
              CErrors.user_err
                Pp.(str "Cannot find name " ++ pr_qualid n ++ spc() ++
                    str "in module " ++ pr_qualid (Nametab.shortest_qualid_of_module m))
          in
          let ns = NSet.add n ns in
          if etc then add_subnames_of ns full_n n else ns)
        NSet.empty ns
    in
    Libobject.Names ns

let vernac_import export refl =
  let import_mod (qid,f) =
    let m = try Nametab.locate_module qid
      with Not_found ->
        CErrors.user_err Pp.(str "Cannot find module " ++ pr_qualid qid)
    in
    let f = interp_filter_in m f in
    Declaremods.import_module f ~export m
  in
  List.iter import_mod refl

let vernac_declare_module export {loc;v=id} binders_ast mty_ast =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Global.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if not (Option.is_empty export) then
      user_err Pp.(str "Arguments of a functor declaration cannot be exported. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
     else (idl,ty)) binders_ast in
  let mp = Declaremods.declare_module id binders_ast (Declaremods.Enforce mty_ast) [] in
  Dumpglob.dump_moddef ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is declared");
  Option.iter (fun export -> vernac_import export [qualid_of_ident id, ImportAll]) export

let vernac_define_module export {loc;v=id} (binders_ast : module_binder list) mty_ast_o mexpr_ast_l =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Global.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  match mexpr_ast_l with
    | [] ->
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp = Declaremods.start_module export id binders_ast mty_ast_o in
       Dumpglob.dump_moddef ?loc mp "mod";
       Flags.if_verbose Feedback.msg_info
         (str "Interactive Module " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [qualid_of_ident id, ImportAll]) export
         ) argsexport
    | _::_ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if not (Option.is_empty export) then
           user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
       let mp =
         Declaremods.declare_module
           id binders_ast mty_ast_o mexpr_ast_l
       in
       Dumpglob.dump_moddef ?loc mp "mod";
       Flags.if_verbose Feedback.msg_info
         (str "Module " ++ Id.print id ++ str " is defined");
       Option.iter (fun export -> vernac_import export [qualid_of_ident id, ImportAll])
         export

let vernac_end_module export {loc;v=id} =
  let mp = Declaremods.end_module () in
  Dumpglob.dump_modref ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is defined");
  Option.iter (fun export -> vernac_import export [qualid_of_ident ?loc id, ImportAll]) export

let vernac_declare_module_type {loc;v=id} binders_ast mty_sign mty_ast_l =
  if Global.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");

  match mty_ast_l with
    | [] ->
       let binders_ast,argsexport =
         List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> export,i)idl)@argsexport) binders_ast
             ([],[]) in

       let mp = Declaremods.start_modtype id binders_ast mty_sign in
       Dumpglob.dump_moddef ?loc mp "modtype";
       Flags.if_verbose Feedback.msg_info
         (str "Interactive Module Type " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [qualid_of_ident ?loc id, ImportAll]) export
         ) argsexport

    | _ :: _ ->
        let binders_ast = List.map
          (fun (export,idl,ty) ->
            if not (Option.is_empty export) then
              user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
            else (idl,ty)) binders_ast in
        let mp = Declaremods.declare_modtype id binders_ast mty_sign mty_ast_l in
        Dumpglob.dump_moddef ?loc mp "modtype";
        Flags.if_verbose Feedback.msg_info
          (str "Module Type " ++ Id.print id ++ str " is defined")

let vernac_end_modtype {loc;v=id} =
  let mp = Declaremods.end_modtype () in
  Dumpglob.dump_modref ?loc mp "modtype";
  Flags.if_verbose Feedback.msg_info (str "Module Type " ++ Id.print id ++ str " is defined")

let vernac_include l = Declaremods.declare_include l

(**********************)
(* Gallina extensions *)

(* Sections *)

let vernac_begin_section ~poly ({v=id} as lid) =
  Dumpglob.dump_definition lid true "sec";
  Lib.open_section id;
  (* If there was no polymorphism attribute this just sets the option
     to its current value ie noop. *)
  set_bool_option_value_gen ~locality:OptLocal ["Universe"; "Polymorphism"] poly

let vernac_end_section {CAst.loc; v} =
  Dumpglob.dump_reference ?loc
    (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
  Lib.close_section ()

let vernac_name_sec_hyp {v=id} set = Proof_using.name_set id set

(* Dispatcher of the "End" command *)
let msg_of_subsection ss id =
  let kind =
    match ss with
    | Lib.OpenedModule (false,_,_,_) -> "module"
    | Lib.OpenedModule (true,_,_,_) -> "module type"
    | Lib.OpenedSection _ -> "section"
    | _ -> "unknown"
  in
  Pp.str kind ++ spc () ++ Id.print id

let vernac_end_segment ({v=id} as lid) =
  let ss = Lib.find_opening_node id in
  let what_for = msg_of_subsection ss lid.v in
  Declare.Obls.check_solved_obligations ~what_for;
  match ss with
  | Lib.OpenedModule (false,export,_,_) -> vernac_end_module export lid
  | Lib.OpenedModule (true,_,_,_) -> vernac_end_modtype lid
  | Lib.OpenedSection _ -> vernac_end_section lid
  | _ -> assert false

(* Libraries *)

let warn_require_in_section =
  CWarnings.create ~name:"require-in-section" ~category:"fragile"
    (fun () -> strbrk "Use of “Require” inside a section is fragile." ++ spc() ++
               strbrk "It is not recommended to use this functionality in finished proof scripts.")

let vernac_require from import qidl =
  if Global.sections_are_opened () then warn_require_in_section ();
  let root = match from with
  | None -> None
  | Some from ->
    let (hd, tl) = Libnames.repr_qualid from in
    Some (Libnames.add_dirpath_suffix hd tl)
  in
  let locate qid =
    let open Loadpath in
    let warn = not !Flags.quiet in
    match locate_qualified_library ?root ~warn qid with
    | Ok (_,dir,f) -> dir, f
    | Error LibUnmappedDir -> err_unmapped_library ?from:root qid
    | Error LibNotFound -> err_notfound_library ?from:root qid
  in
  let modrefl = List.map locate qidl in
  if Dumpglob.dump () then
    List.iter2 (fun {CAst.loc} dp -> Dumpglob.dump_libref ?loc dp "lib") qidl (List.map fst modrefl);
  let lib_resolver = Loadpath.try_locate_absolute_library in
  Library.require_library_from_dirpath ~lib_resolver modrefl import

(* Coercions and canonical structures *)

let vernac_canonical ~local r =
  Canonical.declare_canonical_structure ?local (smart_global r)

let vernac_coercion ~atts ref qids qidt =
  let local, poly = Attributes.(parse Notations.(locality ++ polymorphic) atts) in
  let local = enforce_locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = smart_global ref in
  ComCoercion.try_add_new_coercion_with_target ref' ~local ~poly ~source ~target;
  Flags.if_verbose Feedback.msg_info (pr_global ref' ++ str " is now a coercion")

let vernac_identity_coercion ~atts id qids qidt =
  let local, poly = Attributes.(parse Notations.(locality ++ polymorphic) atts) in
  let local = enforce_locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  ComCoercion.try_add_new_identity_coercion id ~local ~poly ~source ~target

(* Type classes *)

let vernac_instance_program ~atts name bl t props info =
  Dumpglob.dump_constraint (fst name) false "inst";
  let locality, poly =
    Attributes.(parse (Notations.(locality ++ polymorphic))) atts
  in
  let global = not (make_section_locality locality) in
  let _id : Id.t = Classes.new_instance_program ~global ~poly name bl t props info in
  ()

let vernac_instance_interactive ~atts name bl t info props =
  Dumpglob.dump_constraint (fst name) false "inst";
  let locality, poly =
    Attributes.(parse (Notations.(locality ++ polymorphic))) atts
  in
  let global = not (make_section_locality locality) in
  let _id, pstate =
    Classes.new_instance_interactive ~global ~poly name bl t info props in
  pstate

let vernac_instance ~atts name bl t props info =
  Dumpglob.dump_constraint (fst name) false "inst";
  let locality, poly =
    Attributes.(parse (Notations.(locality ++ polymorphic))) atts
  in
  let global = not (make_section_locality locality) in
  let _id : Id.t =
    Classes.new_instance ~global ~poly name bl t props info in
  ()

let vernac_declare_instance ~atts id bl inst pri =
  Dumpglob.dump_definition (fst id) false "inst";
  let (program, locality), poly =
    Attributes.(parse (Notations.(program ++ locality ++ polymorphic))) atts
  in
  let global = not (make_section_locality locality) in
  Classes.declare_new_instance ~program_mode:program ~global ~poly id bl inst pri

let vernac_existing_instance ~section_local insts =
  let glob = not section_local in
  List.iter (fun (id, info) -> Classes.existing_instance glob id (Some info)) insts

let vernac_existing_class id =
  Record.declare_existing_class (Nametab.global id)

(***********)
(* Solving *)

let command_focus = Proof.new_focus_kind ()
let focus_command_cond = Proof.no_cond command_focus

  (* A command which should be a tactic. It has been
     added by Christine to patch an error in the design of the proof
     machine, and enables to instantiate existential variables when
     there are no more goals to solve. It cannot be a tactic since
     all tactics fail if there are no further goals to prove. *)

let vernac_solve_existential ~pstate n com =
  Declare.Proof.map ~f:(fun p ->
      let intern env sigma = Constrintern.intern_constr env sigma com in
      Proof.V82.instantiate_evar (Global.env ()) n intern p) pstate

let vernac_set_end_tac ~pstate tac =
  let env = Genintern.empty_glob_sign (Global.env ()) in
  let _, tac = Genintern.generic_intern env tac in
  (* TO DO verifier s'il faut pas mettre exist s | TacId s ici*)
  Declare.Proof.set_endline_tactic tac pstate

let vernac_set_used_variables ~pstate e : Declare.Proof.t =
  let env = Global.env () in
  let initial_goals pf = Proofview.initial_goals Proof.(data pf).Proof.entry in
  let tys = List.map snd (initial_goals (Declare.Proof.get pstate)) in
  let tys = List.map EConstr.Unsafe.to_constr tys in
  let l = Proof_using.process_expr env e tys in
  let vars = Environ.named_context env in
  List.iter (fun id ->
    if not (List.exists (NamedDecl.get_id %> Id.equal id) vars) then
      user_err ~hdr:"vernac_set_used_variables"
        (str "Unknown variable: " ++ Id.print id))
    l;
  let _, pstate = Declare.Proof.set_used_variables pstate l in
  pstate

(*****************************)
(* Auxiliary file management *)

let expand filename =
  Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) filename

let vernac_add_loadpath ~implicit pdir coq_path =
  let open Loadpath in
  let pdir = expand pdir in
  add_vo_path { unix_path = pdir; coq_path; has_ml = true; implicit; recursive = true }

let vernac_remove_loadpath path =
  Loadpath.remove_load_path (expand path)
  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path path =
  Mltop.add_ml_dir (expand path)

let vernac_declare_ml_module ~local l =
  let local = Option.default false local in
  Mltop.declare_ml_modules local (List.map expand l)

let vernac_chdir = function
  | None -> Feedback.msg_notice (str (Sys.getcwd()))
  | Some path ->
      begin
        try Sys.chdir (expand path)
        with Sys_error err ->
          (* Cd is typically used to control the output directory of
          extraction. A failed Cd could lead to overwriting .ml files
          so we make it an error. *)
          user_err Pp.(str ("Cd failed: " ^ err))
      end;
      Flags.if_verbose Feedback.msg_info (str (Sys.getcwd()))

(********************)
(* State management *)

let vernac_write_state file =
  let file = CUnix.make_suffix file ".coq" in
  Vernacstate.System.dump file

let vernac_restore_state file =
  let file = Loadpath.locate_file (CUnix.make_suffix file ".coq") in
  Vernacstate.System.load file

(************)
(* Commands *)

let vernac_create_hintdb ~module_local id b =
  Hints.create_hint_db module_local id TransparentState.full b

let warn_implicit_core_hint_db =
  CWarnings.create ~name:"implicit-core-hint-db" ~category:"deprecated"
         (fun () -> strbrk "Adding and removing hints in the core database implicitly is deprecated. "
             ++ strbrk"Please specify a hint database.")

let vernac_remove_hints ~module_local dbnames ids =
  let dbnames =
    if List.is_empty dbnames then
      (warn_implicit_core_hint_db (); ["core"])
    else dbnames
  in
  Hints.remove_hints module_local dbnames (List.map Smartlocate.global_with_alias ids)

let vernac_hints ~atts dbnames h =
  let dbnames =
    if List.is_empty dbnames then
      (warn_implicit_core_hint_db (); ["core"])
    else dbnames
  in
  let locality, poly = Attributes.(parse Notations.(option_locality ++ polymorphic) atts) in
  let () = match locality with
  | OptGlobal ->
    if Global.sections_are_opened () then
    CErrors.user_err Pp.(str
      "This command does not support the global attribute in sections.");
  | OptExport ->
    if Global.sections_are_opened () then
    CErrors.user_err Pp.(str
      "This command does not support the export attribute in sections.");
  | OptDefault | OptLocal -> ()
  in
  Hints.add_hints ~locality dbnames (ComHints.interp_hints ~poly h)

let vernac_syntactic_definition ~atts lid x only_parsing =
  let module_local, deprecation = Attributes.(parse Notations.(module_locality ++ deprecation) atts) in
  Dumpglob.dump_definition lid false "syndef";
  Metasyntax.add_syntactic_definition ~local:module_local deprecation (Global.env()) lid.v x only_parsing

let default_env () = {
  Notation_term.ninterp_var_type = Id.Map.empty;
  ninterp_rec_vars = Id.Map.empty;
}

let vernac_reserve bl =
  let sb_decl = (fun (idl,c) ->
    let env = Global.env() in
    let sigma = Evd.from_env env in
    let t,ctx = Constrintern.interp_type env sigma c in
    let t = Detyping.detype Detyping.Now false Id.Set.empty env (Evd.from_ctx ctx) t in
    let t,_ = Notation_ops.notation_constr_of_glob_constr (default_env ()) t in
    Reserve.declare_reserved_type idl t)
  in List.iter sb_decl bl

let vernac_generalizable ~local =
  let local = Option.default true local in
  Implicit_quantifiers.declare_generalizable ~local

let allow_sprop_opt_name = ["Allow";"StrictProp"]
let cumul_sprop_opt_name = ["Cumulative";"StrictProp"]

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = allow_sprop_opt_name;
      optread  = (fun () -> Global.sprop_allowed());
      optwrite = Global.set_allow_sprop }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = cumul_sprop_opt_name;
      optread  = Global.is_cumulative_sprop;
      optwrite = Global.set_cumulative_sprop }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Silent"];
      optread  = (fun () -> !Flags.quiet);
      optwrite = ((:=) Flags.quiet) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Implicit";"Arguments"];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Parentheses"];
      optread  = (fun () -> !Constrextern.print_parentheses);
      optwrite = (fun b ->  Constrextern.print_parentheses := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !Detyping.print_evar_arguments);
      optwrite = (:=) Detyping.print_evar_arguments }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let () =
  declare_int_option
    { optdepr  = false;
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
                   let lev = Option.default Flags.default_inline_level o in
                   Flags.set_inline_level lev) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Kernel"; "Term"; "Sharing"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.share_reduction);
      optwrite = Global.set_share_reduction }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Compact";"Contexts"];
      optread  = (fun () -> Printer.get_compact_context());
      optwrite = (fun b -> Printer.set_compact_context b) }

let () =
  declare_int_option
    { optdepr  = false;
      optkey   = ["Printing";"Depth"];
      optread  = Topfmt.get_depth_boxes;
      optwrite = Topfmt.set_depth_boxes }

let () =
  declare_int_option
    { optdepr  = false;
      optkey   = ["Printing";"Width"];
      optread  = Topfmt.get_margin;
      optwrite = Topfmt.set_margin }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Dump";"Bytecode"];
      optread  = (fun () -> !Cbytegen.dump_bytecode);
      optwrite = (:=) Cbytegen.dump_bytecode }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Dump";"Lambda"];
      optread  = (fun () -> !Clambda.dump_lambda);
      optwrite = (:=) Clambda.dump_lambda }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let () =
  declare_string_option ~preprocess:CWarnings.normalize_flags_string
    { optdepr  = false;
      optkey   = ["Warnings"];
      optread  = CWarnings.get_flags;
      optwrite = CWarnings.set_flags }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Guard"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_guarded);
      optwrite = (fun b -> Global.set_check_guarded b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Positivity"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_positive);
      optwrite = (fun b -> Global.set_check_positive b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optkey   = ["Universe"; "Checking"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.check_universes);
      optwrite = (fun b -> Global.set_check_universes b) }

let vernac_set_strategy ~local l =
  let local = Option.default false local in
  let glob_ref r =
    match smart_global r with
      | GlobRef.ConstRef sp -> EvalConstRef sp
      | GlobRef.VarRef id -> EvalVarRef id
      | _ -> user_err Pp.(str
          "cannot set an inductive type or a constructor as transparent") in
  let l = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) l in
  Redexpr.set_strategy local l

let vernac_set_opacity ~local (v,l) =
  let local = Option.default true local in
  let glob_ref r =
    match smart_global r with
      | GlobRef.ConstRef sp -> EvalConstRef sp
      | GlobRef.VarRef id -> EvalVarRef id
      | _ -> user_err Pp.(str
          "cannot set an inductive type or a constructor as transparent") in
  let l = List.map glob_ref l in
  Redexpr.set_strategy local [v,l]

let vernac_set_option0 ~locality key opt =
  match opt with
  | OptionUnset -> unset_option_value_gen ~locality key
  | OptionSetString s -> set_string_option_value_gen ~locality key s
  | OptionSetInt n -> set_int_option_value_gen ~locality key (Some n)
  | OptionSetTrue -> set_bool_option_value_gen ~locality key true

let vernac_set_append_option ~locality key s =
  set_string_option_append_value_gen ~locality key s

let vernac_set_option ~locality table v = match v with
| OptionSetString s ->
  (* We make a special case for warnings because appending is their
  natural semantics *)
  if CString.List.equal table ["Warnings"] then
    vernac_set_append_option ~locality table s
  else
    let (last, prefix) = List.sep_last table in
    if String.equal last "Append" && not (List.is_empty prefix) then
      vernac_set_append_option ~locality prefix s
    else
      vernac_set_option0 ~locality table v
| _ -> vernac_set_option0 ~locality table v

let vernac_add_option = iter_table { aux = fun table -> table.add }

let vernac_remove_option = iter_table { aux = fun table -> table.remove }

let vernac_mem_option = iter_table { aux = fun table -> table.mem }

let vernac_print_option key =
  try (get_ref_table key).print ()
  with Not_found ->
  try (get_string_table key).print ()
  with Not_found ->
  try print_option_value key
  with Not_found -> error_undeclared_key key

let get_current_context_of_args ~pstate =
  match pstate with
  | None -> fun _ ->
    let env = Global.env () in Evd.(from_env env, env)
  | Some lemma ->
    function
    | Some n -> Declare.Proof.get_goal_context lemma n
    | None -> Declare.Proof.get_current_context lemma

let query_command_selector ?loc = function
  | None -> None
  | Some (Goal_select.SelectNth n) -> Some n
  | _ -> user_err ?loc ~hdr:"query_command_selector"
      (str "Query commands only support the single numbered goal selector.")

let vernac_check_may_eval ~pstate ~atts redexp glopt rc =
  let glopt = query_command_selector glopt in
  let sigma, env = get_current_context_of_args ~pstate glopt in
  let sigma, c = Constrintern.interp_open_constr ~expected_type:Pretyping.UnknownIfTermOrType env sigma rc in
  let sigma = Evarconv.solve_unif_constraints_with_heuristics env sigma in
  Evarconv.check_problems_are_solved env sigma;
  let sigma = Evd.minimize_universes sigma in
  let uctx = Evd.universe_context_set sigma in
  let env = Environ.push_context_set uctx (Evarutil.nf_env_evar sigma env) in
  let j =
    if Evarutil.has_undefined_evars sigma c then
      Evarutil.j_nf_evar sigma (Retyping.get_judgment_of env sigma c)
    else
      let c = EConstr.to_constr sigma c in
      (* OK to call kernel which does not support evars *)
      Environ.on_judgment EConstr.of_constr (Arguments_renaming.rename_typing env c)
  in
  let pp = match redexp with
    | None ->
        let evars_of_term c = Evarutil.undefined_evars_of_term sigma c in
        let l = Evar.Set.union (evars_of_term j.Environ.uj_val) (evars_of_term j.Environ.uj_type) in
        let j = { j with Environ.uj_type = Reductionops.nf_betaiota env sigma j.Environ.uj_type } in
        Prettyp.print_judgment env sigma j ++
        pr_ne_evar_set (fnl () ++ str "where" ++ fnl ()) (mt ()) sigma l
    | Some r ->
        let (sigma,r_interp) = Hook.get f_interp_redexp env sigma r in
        let redfun env evm c =
          let (redfun, _) = Redexpr.reduction_of_red_expr env r_interp in
          let (_, c) = redfun env evm c in
          c
        in
        Prettyp.print_eval redfun env sigma rc j
  in
  pp ++ Printer.pr_universe_ctx_set sigma uctx

let vernac_declare_reduction ~local s r =
  let local = Option.default false local in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Redexpr.declare_red_expr local s (snd (Hook.get f_interp_redexp env sigma r))

  (* The same but avoiding the current goal context if any *)
let vernac_global_check c =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let c,uctx = Constrintern.interp_constr env sigma c in
  let senv = Global.safe_env() in
  let uctx = UState.context_set uctx in
  let senv = Safe_typing.push_context_set ~strict:false uctx senv in
  let c = EConstr.to_constr sigma c in
  let j = Safe_typing.typing senv c in
  let env = Safe_typing.env_of_safe_env senv in
  Prettyp.print_safe_judgment env sigma j ++
  pr_universe_ctx_set sigma uctx


let get_nth_goal ~pstate n =
  let pf = Declare.Proof.get pstate in
  let Proof.{goals;sigma} = Proof.data pf in
  let gl = {Evd.it=List.nth goals (n-1) ; sigma = sigma; } in
  gl

(* Printing "About" information of a hypothesis of the current goal.
   We only print the type and a small statement to this comes from the
   goal. Precondition: there must be at least one current goal. *)
let print_about_hyp_globs ~pstate ?loc ref_or_by_not udecl glopt =
  let exception NoHyp in
  let open Context.Named.Declaration in
  try
    (* Fallback early to globals *)
    let pstate = match pstate with
      | None -> raise Not_found
      | Some pstate -> pstate
    in
    (* FIXME error on non None udecl if we find the hyp. *)
    let glnumopt = query_command_selector ?loc glopt in
    let gl,id =
      let open Constrexpr in
      match glnumopt, ref_or_by_not.v with
      | None,AN qid when qualid_is_ident qid -> (* goal number not given, catch any failure *)
         (try get_nth_goal ~pstate 1, qualid_basename qid with _ -> raise NoHyp)
      | Some n,AN qid when qualid_is_ident qid ->  (* goal number given, catch if wong *)
         (try get_nth_goal ~pstate n, qualid_basename qid
          with
            Failure _ -> user_err ?loc ~hdr:"print_about_hyp_globs"
                          (str "No such goal: " ++ int n ++ str "."))
      | _ , _ -> raise NoHyp in
    let hyps = Tacmach.pf_hyps gl in
    let decl = Context.Named.lookup id hyps in
    let natureofid = match decl with
                     | LocalAssum _ -> "Hypothesis"
                     | LocalDef (_,bdy,_) ->"Constant (let in)" in
    let sigma, env = Declare.Proof.get_current_context pstate in
    v 0 (Id.print id ++ str":" ++ pr_econstr_env env sigma (NamedDecl.get_type decl) ++ fnl() ++ fnl()
         ++ str natureofid ++ str " of the goal context.")
  with (* fallback to globals *)
    | NoHyp | Not_found ->
    let sigma, env = get_current_or_global_context ~pstate in
    Prettyp.print_about env sigma ref_or_by_not udecl

let vernac_print ~pstate ~atts =
  let sigma, env = get_current_or_global_context ~pstate in
  function
  | PrintTypingFlags -> pr_typing_flags (Environ.typing_flags (Global.env ()))
  | PrintTables -> print_tables ()
  | PrintFullContext-> Prettyp.print_full_context_typ env sigma
  | PrintSectionContext qid -> Prettyp.print_sec_context_typ env sigma qid
  | PrintInspect n -> Prettyp.inspect env sigma n
  | PrintGrammar ent -> Metasyntax.pr_grammar ent
  | PrintCustomGrammar ent -> Metasyntax.pr_custom_grammar ent
  | PrintLoadPath dir -> (* For compatibility ? *) print_loadpath dir
  | PrintModules -> print_modules ()
  | PrintModule qid -> print_module qid
  | PrintModuleType qid -> print_modtype qid
  | PrintNamespace ns -> print_namespace ~pstate ns
  | PrintMLLoadPath -> Mltop.print_ml_path ()
  | PrintMLModules -> Mltop.print_ml_modules ()
  | PrintDebugGC -> Mltop.print_gc ()
  | PrintName (qid,udecl) ->
    dump_global qid;
    Prettyp.print_name env sigma qid udecl
  | PrintGraph -> Prettyp.print_graph ()
  | PrintClasses -> Prettyp.print_classes()
  | PrintTypeClasses -> Prettyp.print_typeclasses()
  | PrintInstances c -> Prettyp.print_instances (smart_global c)
  | PrintCoercions -> Prettyp.print_coercions ()
  | PrintCoercionPaths (cls,clt) ->
    Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt)
  | PrintCanonicalConversions qids ->
    let grefs = List.map Smartlocate.smart_global qids in
    Prettyp.print_canonical_projections env sigma grefs
  | PrintUniverses (sort, subgraph, dst) -> print_universes ~sort ~subgraph dst
  | PrintHint r -> Hints.pr_hint_ref env sigma (smart_global r)
  | PrintHintGoal ->
     begin match pstate with
     | Some pstate ->
       let pf = Declare.Proof.get pstate in
       Hints.pr_applicable_hint pf
     | None ->
       str "No proof in progress"
     end
  | PrintHintDbName s -> Hints.pr_hint_db_by_name env sigma s
  | PrintHintDb -> Hints.pr_searchtable env sigma
  | PrintScopes ->
    Notation.pr_scopes (Constrextern.without_symbols (pr_lglob_constr_env env))
  | PrintScope s ->
    Notation.pr_scope (Constrextern.without_symbols (pr_lglob_constr_env env)) s
  | PrintVisibility s ->
    Notation.pr_visibility (Constrextern.without_symbols (pr_lglob_constr_env env)) s
  | PrintAbout (ref_or_by_not,udecl,glnumopt) ->
    print_about_hyp_globs ~pstate ref_or_by_not udecl glnumopt
  | PrintImplicit qid ->
    dump_global qid;
    Prettyp.print_impargs qid
  | PrintAssumptions (o,t,r) ->
      (* Prints all the axioms and section variables used by a term *)
      let gr = smart_global r in
      let cstr = Globnames.printable_constr_of_global gr in
      let st = Conv_oracle.get_transp_state (Environ.oracle (Global.env())) in
      let nassums =
        Assumptions.assumptions st ~add_opaque:o ~add_transparent:t gr cstr in
      Printer.pr_assumptionset env sigma nassums
  | PrintStrategy r -> print_strategy r
  | PrintRegistered -> print_registered ()

let vernac_search ~pstate ~atts s gopt r =
  let open ComSearch in
  let gopt = query_command_selector gopt in
  let sigma, env =
    match gopt with | None ->
      (* 1st goal by default if it exists, otherwise no goal at all *)
      (try get_goal_or_global_context ~pstate 1
       with _ -> let env = Global.env () in (Evd.from_env env, env))
    (* if goal selector is given and wrong, then let exceptions be raised. *)
    | Some g -> get_goal_or_global_context ~pstate g in
  interp_search env sigma s r

let vernac_locate ~pstate = let open Constrexpr in function
  | LocateAny {v=AN qid}  -> Prettyp.print_located_qualid qid
  | LocateTerm {v=AN qid} -> Prettyp.print_located_term qid
  | LocateAny {v=ByNotation (ntn, sc)} (* TODO : handle Ltac notations *)
  | LocateTerm {v=ByNotation (ntn, sc)} ->
    let _, env = get_current_or_global_context ~pstate in
    Notation.locate_notation
      (Constrextern.without_symbols (pr_lglob_constr_env env)) ntn sc
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> Prettyp.print_located_module qid
  | LocateOther (s, qid) -> Prettyp.print_located_other s qid
  | LocateFile f -> locate_file f

let vernac_register qid r =
  let gr = Smartlocate.global_with_alias qid in
  match r with
  | RegisterInline ->
    begin match gr with
    | GlobRef.ConstRef c -> Global.register_inline c
    | _ -> CErrors.user_err (Pp.str "Register Inline: expecting a constant")
    end
  | RegisterCoqlib n ->
    let ns, id = Libnames.repr_qualid n in
    if DirPath.equal (dirpath_of_string "kernel") ns then begin
      if Global.sections_are_opened () then
        user_err Pp.(str "Registering a kernel type is not allowed in sections");
      let CPrimitives.PIE pind = match Id.to_string id with
        | "ind_bool" -> CPrimitives.(PIE PIT_bool)
        | "ind_carry" -> CPrimitives.(PIE PIT_carry)
        | "ind_pair" -> CPrimitives.(PIE PIT_pair)
        | "ind_cmp" -> CPrimitives.(PIE PIT_cmp)
        | "ind_f_cmp" -> CPrimitives.(PIE PIT_f_cmp)
        | "ind_f_class" -> CPrimitives.(PIE PIT_f_class)
        | k -> CErrors.user_err Pp.(str "Register: unknown identifier “" ++ str k ++ str "” in the “kernel” namespace")
      in
      match gr with
      | GlobRef.IndRef ind -> Global.register_inductive ind pind
      | _ -> CErrors.user_err (Pp.str "Register in kernel: expecting an inductive type")
    end
    else Coqlib.register_ref (Libnames.string_of_qualid n) gr

(********************)
(* Proof management *)

let vernac_focus ~pstate gln =
  Declare.Proof.map ~f:(fun p ->
    match gln with
      | None -> Proof.focus focus_command_cond () 1 p
      | Some 0 ->
         user_err Pp.(str "Invalid goal number: 0. Goal numbering starts with 1.")
      | Some n ->
         Proof.focus focus_command_cond () n p)
    pstate

  (* Unfocuses one step in the focus stack. *)
let vernac_unfocus ~pstate =
  Declare.Proof.map
    ~f:(fun p -> Proof.unfocus command_focus p ())
    pstate

(* Checks that a proof is fully unfocused. Raises an error if not. *)
let vernac_unfocused ~pstate =
  let p = Declare.Proof.get pstate in
  if Proof.unfocused p then
    str"The proof is indeed fully unfocused."
  else
    user_err Pp.(str "The proof is not fully unfocused.")

(* "{" focuses on the first goal, "n: {" focuses on the n-th goal
    "}" unfocuses, provided that the proof of the goal has been completed.
*)
let subproof_kind = Proof.new_focus_kind ()
let subproof_cond = Proof.done_cond subproof_kind

let vernac_subproof gln ~pstate =
  Declare.Proof.map ~f:(fun p ->
    match gln with
    | None -> Proof.focus subproof_cond () 1 p
    | Some (Goal_select.SelectNth n) -> Proof.focus subproof_cond () n p
    | Some (Goal_select.SelectId id) -> Proof.focus_id subproof_cond () id p
    | _ -> user_err ~hdr:"bracket_selector"
             (str "Brackets do not support multi-goal selectors."))
    pstate

let vernac_end_subproof ~pstate =
  Declare.Proof.map ~f:(fun p ->
      Proof.unfocus subproof_kind p ())
    pstate

let vernac_bullet (bullet : Proof_bullet.t) ~pstate =
  Declare.Proof.map ~f:(fun p ->
    Proof_bullet.put p bullet) pstate

(* Stack is needed due to show proof names, should deprecate / remove
   and take pstate *)
let vernac_show ~pstate =
  match pstate with
  (* Show functions that don't require a proof state *)
  | None ->
    begin function
      | ShowProof -> show_proof ~pstate:None
      | ShowMatch id -> show_match id
      | _ ->
        user_err (str "This command requires an open proof.")
    end
  (* Show functions that require a proof state *)
  | Some pstate ->
    let proof = Declare.Proof.get pstate in
    begin function
    | ShowGoal goalref ->
      begin match goalref with
        | OpenSubgoals -> pr_open_subgoals ~proof
        | NthGoal n -> pr_nth_open_subgoal ~proof n
        | GoalId id -> pr_goal_by_id ~proof id
      end
    | ShowExistentials -> show_top_evars ~proof
    | ShowUniverses -> show_universes ~proof
    (* Deprecate *)
    | ShowProofNames ->
      Id.print (Declare.Proof.get_name pstate)
    | ShowIntros all -> show_intro ~proof all
    | ShowProof -> show_proof ~pstate:(Some pstate)
    | ShowMatch id -> show_match id
    end

let vernac_check_guard ~pstate =
  let pts = Declare.Proof.get pstate in
  let pfterm = List.hd (Proof.partial_proof pts) in
  let message =
    try
      let { Evd.it=gl ; sigma=sigma } = Proof.V82.top_goal pts in
      Inductiveops.control_only_guard (Goal.V82.env sigma gl) sigma pfterm;
      (str "The condition holds up to here")
    with UserError(_,s) ->
      (str ("Condition violated: ") ++s)
  in message

(* We interpret vernacular commands to a DSL that specifies their
   allowed actions on proof states *)
let translate_vernac ~atts v = let open Vernacextend in match v with
  | VernacAbortAll
  | VernacRestart
  | VernacUndo _
  | VernacUndoTo _
  | VernacResetName _
  | VernacResetInitial
  | VernacBack _
  | VernacAbort _ ->
    anomaly (str "type_vernac")
  | VernacLoad _ ->
    anomaly (str "Load is not supported recursively")

  (* Syntax *)
  | VernacSyntaxExtension (infix, sl) ->
    VtDefault(fun () -> with_module_locality ~atts vernac_syntax_extension infix sl)
  | VernacDeclareScope sc ->
    VtDefault(fun () -> with_module_locality ~atts vernac_declare_scope sc)
  | VernacDelimiters (sc,lr) ->
    VtDefault(fun () -> with_module_locality ~atts vernac_delimiters sc lr)
  | VernacBindScope (sc,rl) ->
    VtDefault(fun () -> with_module_locality ~atts vernac_bind_scope sc rl)
  | VernacOpenCloseScope (b, s) ->
    VtDefault(fun () -> with_section_locality ~atts vernac_open_close_scope (b,s))
  | VernacInfix (mv,qid,sc) ->
    VtDefault(fun () -> vernac_infix ~atts mv qid sc)
  | VernacNotation (c,infpl,sc) ->
    VtDefault(fun () -> vernac_notation ~atts c infpl sc)
  | VernacNotationAddFormat(n,k,v) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        Metasyntax.add_notation_extra_printing_rule n k v)
  | VernacDeclareCustomEntry s ->
    VtDefault(fun () -> with_module_locality ~atts vernac_custom_entry s)

  (* Gallina *)

  | VernacDefinition (discharge,lid,DefineBody (bl,red_option,c,typ)) ->
    VtDefault (fun () ->
      with_def_attributes ~atts
       vernac_definition discharge lid bl red_option c typ)
  | VernacDefinition (discharge,lid,ProveBody(bl,typ)) ->
    VtOpenProof(fun () ->
      with_def_attributes ~atts
       vernac_definition_interactive discharge lid bl typ)

  | VernacStartTheoremProof (k,l) ->
    VtOpenProof(fun () -> with_def_attributes ~atts vernac_start_proof k l)
  | VernacExactProof c ->
    VtCloseProof (fun ~lemma ->
        unsupported_attributes atts;
        vernac_exact_proof ~lemma c)

  | VernacDefineModule (export,lid,bl,mtys,mexprl) ->
    let i () =
      unsupported_attributes atts;
      vernac_define_module export lid bl mtys mexprl in
    (* XXX: We should investigate if eventually this should be made
       VtNoProof in all cases. *)
    if List.is_empty mexprl then VtNoProof i else VtDefault i

  | VernacDeclareModuleType (lid,bl,mtys,mtyo) ->
    VtNoProof(fun () ->
        unsupported_attributes atts;
        vernac_declare_module_type lid bl mtys mtyo)
  | VernacAssumption ((discharge,kind),nl,l) ->
    VtDefault(fun () -> with_def_attributes ~atts vernac_assumption discharge kind l nl)
  | VernacInductive (finite, l) ->
    VtDefault(fun () -> vernac_inductive ~atts finite l)
  | VernacFixpoint (discharge, l) ->
    let opens = List.exists (fun { body_def } -> Option.is_empty body_def) l in
    if opens then
      VtOpenProof (fun () ->
        with_def_attributes ~atts vernac_fixpoint_interactive discharge l)
    else
      VtDefault (fun () ->
        with_def_attributes ~atts vernac_fixpoint discharge l)
  | VernacCoFixpoint (discharge, l) ->
    let opens = List.exists (fun { body_def } -> Option.is_empty body_def) l in
    if opens then
      VtOpenProof(fun () -> with_def_attributes ~atts vernac_cofixpoint_interactive discharge l)
    else
      VtDefault(fun () -> with_def_attributes ~atts vernac_cofixpoint discharge l)

  | VernacScheme l ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_scheme l)
  | VernacCombinedScheme (id, l) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_combined_scheme id l)
  | VernacUniverse l ->
    VtDefault(fun () -> vernac_universe ~poly:(only_polymorphism atts) l)
  | VernacConstraint l ->
    VtDefault(fun () -> vernac_constraint ~poly:(only_polymorphism atts) l)

  (* Modules *)
  | VernacDeclareModule (export,lid,bl,mtyo) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_declare_module export lid bl mtyo)
  | VernacInclude in_asts ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_include in_asts)
  (* Gallina extensions *)
  | VernacBeginSection lid ->
    VtNoProof(fun () ->
        vernac_begin_section ~poly:(only_polymorphism atts) lid)
  | VernacEndSegment lid ->
    VtNoProof(fun () ->
        unsupported_attributes atts;
        vernac_end_segment lid)
  | VernacNameSectionHypSet (lid, set) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_name_sec_hyp lid set)
  | VernacRequire (from, export, qidl) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_require from export qidl)
  | VernacImport (export,qidl) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_import export qidl)
  | VernacCanonical qid ->
    VtDefault(fun () ->
        vernac_canonical ~local:(only_locality atts) qid)
  | VernacCoercion (r,s,t) ->
    VtDefault(fun () -> vernac_coercion ~atts r s t)
  | VernacIdentityCoercion ({v=id},s,t) ->
    VtDefault(fun () -> vernac_identity_coercion ~atts id s t)

  (* Type classes *)
  | VernacInstance (name, bl, t, props, info) ->
    let atts, program = Attributes.(parse_with_extra program) atts in
    if program then
      VtDefault (fun () -> vernac_instance_program ~atts name bl t props info)
    else begin match props with
    | None ->
       VtOpenProof (fun () ->
        vernac_instance_interactive ~atts name bl t info None)
    | Some props ->
      let atts, refine = Attributes.parse_with_extra Classes.refine_att atts in
      if refine then
        VtOpenProof (fun () ->
          vernac_instance_interactive ~atts name bl t info (Some props))
      else
        VtDefault (fun () ->
          vernac_instance ~atts name bl t props info)
    end

  | VernacDeclareInstance (id, bl, inst, info) ->
    VtDefault(fun () -> vernac_declare_instance ~atts id bl inst info)
  | VernacContext sup ->
    VtDefault(fun () -> ComAssumption.context ~poly:(only_polymorphism atts) sup)
  | VernacExistingInstance insts ->
    VtDefault(fun () -> with_section_locality ~atts vernac_existing_instance insts)
  | VernacExistingClass id ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_existing_class id)

  (* Solving *)
  | VernacSolveExistential (n,c) ->
    VtModifyProof(fun ~pstate ->
        unsupported_attributes atts;
        vernac_solve_existential ~pstate n c)
  (* Auxiliary file and library management *)
  | VernacAddLoadPath { implicit; physical_path; logical_path } ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_add_loadpath ~implicit physical_path logical_path)
  | VernacRemoveLoadPath s ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_remove_loadpath s)
  | VernacAddMLPath (s) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_add_ml_path s)
  | VernacDeclareMLModule l ->
    VtDefault(fun () -> with_locality ~atts vernac_declare_ml_module l)
  | VernacChdir s ->
    VtDefault(fun () -> unsupported_attributes atts; vernac_chdir s)

  (* State management *)
  | VernacWriteState s ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_write_state s)
  | VernacRestoreState s ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_restore_state s)

  (* Commands *)
  | VernacCreateHintDb (dbname,b) ->
    VtDefault(fun () ->
        with_module_locality ~atts vernac_create_hintdb dbname b)
  | VernacRemoveHints (dbnames,ids) ->
    VtDefault(fun () ->
        with_module_locality ~atts vernac_remove_hints dbnames ids)
  | VernacHints (dbnames,hints) ->
    VtDefault(fun () ->
        vernac_hints ~atts dbnames hints)
  | VernacSyntacticDefinition (id,c,b) ->
     VtDefault(fun () -> vernac_syntactic_definition ~atts id c b)
  | VernacArguments (qid, args, more_implicits, flags) ->
    VtDefault(fun () ->
        with_section_locality ~atts
          (ComArguments.vernac_arguments qid args more_implicits flags))
  | VernacReserve bl ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_reserve bl)
  | VernacGeneralizable gen ->
    VtDefault(fun () -> with_locality ~atts vernac_generalizable gen)
  | VernacSetOpacity qidl ->
    VtDefault(fun () -> with_locality ~atts vernac_set_opacity qidl)
  | VernacSetStrategy l ->
    VtDefault(fun () -> with_locality ~atts vernac_set_strategy l)
  | VernacSetOption (export,key,v) ->
    let atts = if export then ("export", VernacFlagEmpty) :: atts else atts in
    VtDefault(fun () ->
        vernac_set_option ~locality:(parse option_locality atts) key v)
  | VernacRemoveOption (key,v) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_remove_option key v)
  | VernacAddOption (key,v) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_add_option key v)
  | VernacMemOption (key,v) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_mem_option key v)
  | VernacPrintOption key ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_print_option key)
  | VernacCheckMayEval (r,g,c) ->
    VtReadProofOpt(fun ~pstate ->
        Feedback.msg_notice @@
        vernac_check_may_eval ~pstate ~atts r g c)
  | VernacDeclareReduction (s,r) ->
    VtDefault(fun () ->
        with_locality ~atts vernac_declare_reduction s r)
  | VernacGlobalCheck c ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        Feedback.msg_notice @@ vernac_global_check c)
  | VernacPrint p ->
    VtReadProofOpt(fun ~pstate ->
        Feedback.msg_notice @@ vernac_print ~pstate ~atts p)
  | VernacSearch (s,g,r) ->
    VtReadProofOpt(
        unsupported_attributes atts;
        vernac_search ~atts s g r)
  | VernacLocate l -> unsupported_attributes atts;
    VtReadProofOpt(fun ~pstate ->
        Feedback.msg_notice @@ vernac_locate ~pstate l)
  | VernacRegister (qid, r) ->
    VtNoProof(fun () ->
        unsupported_attributes atts;
        vernac_register qid r)
  | VernacPrimitive (id, prim, typopt) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        ComPrimitive.do_primitive id prim typopt)
  | VernacComments l ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        Flags.if_verbose Feedback.msg_info (str "Comments ok\n"))
  (* Proof management *)
  | VernacFocus n ->
    VtModifyProof(unsupported_attributes atts;vernac_focus n)
  | VernacUnfocus ->
    VtModifyProof(unsupported_attributes atts;vernac_unfocus)
  | VernacUnfocused ->
    VtReadProof(fun ~pstate ->
      unsupported_attributes atts;
      Feedback.msg_notice @@ vernac_unfocused ~pstate)
  | VernacBullet b ->
    VtModifyProof(
      unsupported_attributes atts;
      vernac_bullet b)
  | VernacSubproof n ->
    VtModifyProof(
      unsupported_attributes atts;
      vernac_subproof n)
  | VernacEndSubproof ->
    VtModifyProof(
      unsupported_attributes atts;
      vernac_end_subproof)
  | VernacShow s ->
    VtReadProofOpt(fun ~pstate ->
      unsupported_attributes atts;
      Feedback.msg_notice @@ vernac_show ~pstate s)
  | VernacCheckGuard ->
    VtReadProof(fun ~pstate ->
        unsupported_attributes atts;
        Feedback.msg_notice @@ vernac_check_guard ~pstate)
  | VernacProof (tac, using) ->
    VtModifyProof(fun ~pstate ->
    unsupported_attributes atts;
    let using = Option.append using (Proof_using.get_default_proof_using ()) in
    let tacs = if Option.is_empty tac then "tac:no" else "tac:yes" in
    let usings = if Option.is_empty using then "using:no" else "using:yes" in
    Aux_file.record_in_aux_at "VernacProof" (tacs^" "^usings);
    let pstate = Option.cata (vernac_set_end_tac ~pstate) pstate tac in
    Option.cata (vernac_set_used_variables ~pstate) pstate using)
  | VernacProofMode mn ->
    VtDefault(fun () -> unsupported_attributes atts)

  | VernacEndProof pe ->
    VtCloseProof (vernac_end_proof pe)

  (* Extensions *)
  | VernacExtend (opn,args) ->
    Vernacextend.type_vernac ~atts opn args
