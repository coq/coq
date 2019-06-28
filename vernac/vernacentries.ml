(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Nameops
open Tacmach
open Constrintern
open Prettyp
open Printer
open Goptions
open Libnames
open Globnames
open Vernacexpr
open Decl_kinds
open Constrexpr
open Redexpr
open Lemmas
open Locality
open Attributes

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

(** TODO: make this function independent of Ltac *)
let (f_interp_redexp, interp_redexp_hook) = Hook.make ()

let debug = false

(* XXX Should move to a common library *)
let vernac_pperr_endline pp =
  if debug then Format.eprintf "@[%a@]@\n%!" Pp.pp_with (pp ()) else ()

(* Utility functions, at some point they should all disappear and
   instead enviroment/state selection should be done at the Vernac DSL
   level. *)

let get_current_or_global_context ~pstate =
  match pstate with
  | None -> let env = Global.env () in Evd.(from_env env, env)
  | Some p -> Pfedit.get_current_context p

let get_goal_or_global_context ~pstate glnum =
  match pstate with
  | None -> let env = Global.env () in Evd.(from_env env, env)
  | Some p -> Pfedit.get_goal_context p glnum

let cl_of_qualid = function
  | FunClass -> Classops.CL_FUN
  | SortClass -> Classops.CL_SORT
  | RefClass r -> Class.class_of_global (Smartlocate.smart_global ~head:true r)

let scope_class_of_qualid qid =
  Notation.scope_class_of_class (cl_of_qualid qid)

(** Standard attributes for definition-like commands. *)
module DefAttributes = struct
  type t = {
    locality : bool option;
    polymorphic : bool;
    program : bool;
    deprecated : Deprecation.t option;
  }

  let parse f =
    let open Attributes in
    let ((locality, deprecated), polymorphic), program =
      parse Notations.(locality ++ deprecation ++ polymorphic ++ program) f
    in
    { polymorphic; program; locality; deprecated }
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
  if atts.DefAttributes.program then Obligations.check_program_libraries ();
  f ~atts

(*******************)
(* "Show" commands *)

let show_proof ~pstate =
  (* spiwack: this would probably be cooler with a bit of polishing. *)
  try
    let pstate = Option.get pstate in
    let p = Proof_global.get_proof pstate in
    let sigma, env = Pfedit.get_current_context pstate in
    let pprf = Proof.partial_proof p in
    Pp.prlist_with_sep Pp.fnl (Printer.pr_econstr_env env sigma) pprf
  (* We print nothing if there are no goals left *)
  with
  | Pfedit.NoSuchGoal
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
    let l,_= decompose_prod_assum sigma (Termops.strip_outer_cast sigma (pf_concl gl)) in
    if all then
      let lid = Tactics.find_intro_names l gl in
      hov 0 (prlist_with_sep  spc Id.print lid)
    else if not (List.is_empty l) then
      let n = List.last l in
      Id.print (List.hd (Tactics.find_intro_names [n] gl))
    else mt ()
  end else mt ()

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

(*

  HH notes in PR #679:

  The Show Match could also be made more robust, for instance in the
  presence of let in the branch of a constructor. A
  decompose_prod_assum would probably suffice for that, but then, it
  is a Context.Rel.Declaration.t which needs to be matched and not
  just a pair (name,type).

  Otherwise, this is OK. After all, the API on inductive types is not
  so canonical in general, and in this simple case, working at the
  low-level of mind_nf_lc seems reasonable (compared to working at the
  higher-level of Inductiveops).

*)
    
let make_cases_aux glob_ref =
  let open Declarations in
  match glob_ref with
    | Globnames.IndRef ind ->
      let mib, mip = Global.lookup_inductive ind in
	Util.Array.fold_right_i
          (fun i (ctx, _) l ->
             let al = Util.List.skipn (List.length mib.mind_params_ctxt) (List.rev ctx) in
	     let rec rename avoid = function
	       | [] -> []
               | RelDecl.LocalDef _ :: l -> "_" :: rename avoid l
               | RelDecl.LocalAssum (n, _)::l ->
                   let n' = Namegen.next_name_away_with_default (Id.to_string Namegen.default_dependent_ident) n.Context.binder_name avoid in
                   Id.to_string n' :: rename (Id.Set.add n' avoid) l in
	     let al' = rename Id.Set.empty al in
	     let consref = ConstructRef (ith_constructor_of_inductive ind (i + 1)) in
	     (Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty consref) :: al') :: l)
          mip.mind_nf_lc []
    | _ -> raise Not_found

let make_cases s =
  let qualified_name = Libnames.qualid_of_string s in
  let glob_ref = Nametab.locate qualified_name in
  make_cases_aux glob_ref

(** Textual display of a generic "match" template *)

let show_match id =
  let patterns =
    try make_cases_aux (Nametab.global id)
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
  let opened = Library.opened_libraries ()
  and loaded = Library.loaded_libraries () in
  (* we intersect over opened to preserve the order of opened since *)
  (* non-commutative operations (e.g. visibility) are done at import time *)
  let loaded_opened = List.intersect DirPath.equal opened loaded
  and only_loaded = List.subtract DirPath.equal loaded opened in
  str"Loaded and imported library files: " ++
  pr_vertical_list DirPath.print loaded_opened ++ fnl () ++
  str"Loaded and not imported library files: " ++
  pr_vertical_list DirPath.print only_loaded


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
    | VarKey id -> ((VarRef id, lvl) :: vacc, cacc)
    | ConstKey cst -> (vacc, (ConstRef cst, lvl) :: cacc)
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
    let key = match r with
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
    let reraise = CErrors.push reraise in
    close ();
    iraise reraise

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
  user_err ?loc:qid.CAst.loc ~hdr:"locate_library"
     (strbrk "Unable to locate library " ++ pr_qualid qid ++ prefix)

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

let vernac_arguments_scope ~section_local r scl =
  Notation.declare_arguments_scope section_local (smart_global r) scl

let vernac_infix ~atts =
  let module_local, deprecation = Attributes.(parse Notations.(module_locality ++ deprecation) atts) in
  Metasyntax.add_infix ~local:module_local deprecation (Global.env())

let vernac_notation ~atts =
  let module_local, deprecation = Attributes.(parse Notations.(module_locality ++ deprecation) atts) in
  Metasyntax.add_notation ~local:module_local deprecation (Global.env())

let vernac_custom_entry ~module_local s =
  Metasyntax.declare_custom_entry module_local s

(* Default proof mode, to be set at the beginning of proofs for
   programs that cannot be statically classified. *)
let default_proof_mode = ref (Pvernac.register_proof_mode "Noedit" Pvernac.Vernac_.noedit_mode)
let get_default_proof_mode () = !default_proof_mode

let get_default_proof_mode_opt () = Pvernac.proof_mode_to_string !default_proof_mode
let set_default_proof_mode_opt name =
  default_proof_mode :=
    match Pvernac.lookup_proof_mode name with
    | Some pm -> pm
    | None -> CErrors.user_err Pp.(str (Format.sprintf "No proof mode named \"%s\"." name))

let proof_mode_opt_name = ["Default";"Proof";"Mode"]
let () =
  Goptions.declare_string_option Goptions.{
    optdepr = false;
    optname = "default proof mode" ;
    optkey = proof_mode_opt_name;
    optread = get_default_proof_mode_opt;
    optwrite = set_default_proof_mode_opt;
  }

(***********)
(* Gallina *)

let start_proof_and_print ~program_mode ~poly ?hook ~scope ~kind l =
  let inference_hook =
    if program_mode then
      let hook env sigma ev =
        let tac = !Obligations.default_tactic in
        let evi = Evd.find sigma ev in
        let evi = Evarutil.nf_evar_info sigma evi in
        let env = Evd.evar_filtered_env evi in
        try
          let concl = evi.Evd.evar_concl in
          if not (Evarutil.is_ground_env sigma env &&
                  Evarutil.is_ground_term sigma concl)
          then raise Exit;
          let c, _, ctx =
            Pfedit.build_by_tactic ~poly:false env (Evd.evar_universe_context sigma) concl tac
          in Evd.set_universe_context sigma ctx, EConstr.of_constr c
        with Logic_monad.TacticFailure e when Logic.catchable_exception e ->
          user_err Pp.(str "The statement obligations could not be resolved \
                 automatically, write a statement definition first.")
      in Some hook
    else None
  in
  start_lemma_com ~program_mode ?inference_hook ?hook ~poly ~scope ~kind l

let vernac_definition_hook ~poly = function
| Coercion ->
  Some (Class.add_coercion_hook ~poly)
| CanonicalStructure ->
  Some (DeclareDef.Hook.(make (fun { S.dref } -> Canonical.declare_canonical_structure dref)))
| SubClass ->
  Some (Class.add_subclass_hook ~poly)
| _ -> None

let fresh_name_for_anonymous_theorem () =
  Namegen.next_global_ident_away Lemmas.default_thm_id Id.Set.empty

let vernac_definition_name lid local =
  let lid =
    match lid with
    | { v = Name.Anonymous; loc } ->
         CAst.make ?loc (fresh_name_for_anonymous_theorem ())
    | { v = Name.Name n; loc } -> CAst.make ?loc n in
  let () =
    let open DeclareDef in
    match local with
    | Discharge -> Dumpglob.dump_definition lid true "var"
    | Global _ -> Dumpglob.dump_definition lid false "def"
  in
  lid

let vernac_definition_interactive ~atts (discharge, kind) (lid, pl) bl t =
  let open DefAttributes in
  let local = enforce_locality_exp atts.locality discharge in
  let hook = vernac_definition_hook ~poly:atts.polymorphic kind in
  let program_mode = atts.program in
  let poly = atts.polymorphic in
  let name = vernac_definition_name lid local in
  start_proof_and_print ~program_mode ~poly ~scope:local ~kind:(DefinitionBody kind) ?hook [(name, pl), (bl, t)]

let vernac_definition ~atts (discharge, kind) (lid, pl) bl red_option c typ_opt =
  let open DefAttributes in
  let scope = enforce_locality_exp atts.locality discharge in
  let hook = vernac_definition_hook ~poly:atts.polymorphic kind in
  let program_mode = atts.program in
  let name = vernac_definition_name lid scope in
  let red_option = match red_option with
    | None -> None
    | Some r ->
      let env = Global.env () in
      let sigma = Evd.from_env env in
      Some (snd (Hook.get f_interp_redexp env sigma r)) in
  ComDefinition.do_definition ~program_mode ~name:name.v
    ~poly:atts.polymorphic ~scope ~kind pl bl red_option c typ_opt ?hook

(* NB: pstate argument to use combinators easily *)
let vernac_start_proof ~atts kind l =
  let open DefAttributes in
  let scope = enforce_locality_exp atts.locality NoDischarge in
  if Dumpglob.dump () then
    List.iter (fun ((id, _), _) -> Dumpglob.dump_definition id false "prf") l;
  start_proof_and_print ~program_mode:atts.program ~poly:atts.polymorphic ~scope ~kind:(Proof kind) l

let vernac_end_proof ~lemma = let open Vernacexpr in function
  | Admitted ->
    save_lemma_admitted ~lemma
  | Proved (opaque,idopt) ->
    save_lemma_proved ~lemma ~opaque ~idopt

let vernac_exact_proof ~lemma c =
  (* spiwack: for simplicity I do not enforce that "Proof proof_term" is
     called only at the beginning of a proof. *)
  let lemma, status = Lemmas.by (Tactics.exact_proof c) lemma in
  let () = save_lemma_proved ~lemma ~opaque:Proof_global.Opaque ~idopt:None in
  if not status then Feedback.feedback Feedback.AddedAxiom

let vernac_assumption ~atts discharge kind l nl =
  let open DefAttributes in
  let scope = enforce_locality_exp atts.locality discharge in
  List.iter (fun (is_coe,(idl,c)) ->
    if Dumpglob.dump () then
      List.iter (fun (lid, _) ->
          match scope with
            | DeclareDef.Global _ -> Dumpglob.dump_definition lid false "ax"
            | DeclareDef.Discharge -> Dumpglob.dump_definition lid true "var") idl) l;
  let status = ComAssumption.do_assumptions ~poly:atts.polymorphic ~program_mode:atts.program ~scope ~kind nl l in
  if not status then Feedback.feedback Feedback.AddedAxiom

let is_polymorphic_inductive_cumulativity =
  declare_bool_option_and_ref ~depr:false ~value:false
    ~name:"Polymorphic inductive cumulativity"
    ~key:["Polymorphic"; "Inductive"; "Cumulativity"]

let should_treat_as_cumulative cum poly =
  match cum with
  | Some VernacCumulative ->
    if poly then true
    else user_err Pp.(str "The Cumulative prefix can only be used in a polymorphic context.")
  | Some VernacNonCumulative ->
    if poly then false
    else user_err Pp.(str "The NonCumulative prefix can only be used in a polymorphic context.")
  | None -> poly && is_polymorphic_inductive_cumulativity ()

let get_uniform_inductive_parameters =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~name:"Uniform inductive parameters"
    ~key:["Uniform"; "Inductive"; "Parameters"]
    ~value:false

let should_treat_as_uniform () =
  if get_uniform_inductive_parameters ()
  then ComInductive.UniformParameters
  else ComInductive.NonUniformParameters

let vernac_record ~template udecl cum k poly finite records =
  let is_cumulative = should_treat_as_cumulative cum poly in
  let map ((coe, id), binders, sort, nameopt, cfs) =
    let const = match nameopt with
    | None -> add_prefix "Build_" id.v
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
  ignore(Record.definition_structure ~template udecl k is_cumulative ~poly finite records)

let extract_inductive_udecl (indl:(inductive_expr * decl_notation list) list) =
  match indl with
  | [] -> assert false
  | (((coe,(id,udecl)),b,c,k,d),e) :: rest ->
    let rest = List.map (fun (((coe,(id,udecl)),b,c,k,d),e) ->
        if Option.has_some udecl
        then user_err ~hdr:"inductive udecl" Pp.(strbrk "Universe binders must be on the first inductive of the block.")
        else (((coe,id),b,c,k,d),e))
        rest
    in
    udecl, (((coe,id),b,c,k,d),e) :: rest

(** When [poly] is true the type is declared polymorphic. When [lo] is true,
    then the type is declared private (as per the [Private] keyword). [finite]
    indicates whether the type is inductive, co-inductive or
    neither. *)
let vernac_inductive ~atts cum lo finite indl =
  let template, poly = Attributes.(parse Notations.(template ++ polymorphic) atts) in
  let open Pp in
  let udecl, indl = extract_inductive_udecl indl in
  if Dumpglob.dump () then
    List.iter (fun (((coe,lid), _, _, _, cstrs), _) ->
      match cstrs with
	| Constructors cstrs ->
	    Dumpglob.dump_definition lid false "ind";
	    List.iter (fun (_, (lid, _)) ->
			 Dumpglob.dump_definition lid false "constr") cstrs
	| _ -> () (* dumping is done by vernac_record (called below) *) )
      indl;

  let is_record = function
  | ((_ , _ , _ , _, RecordDecl _), _) -> true
  | _ -> false
  in
  let is_constructor = function
  | ((_ , _ , _ , _, Constructors _), _) -> true
  | _ -> false
  in
  let is_defclass = match indl with
  | [ ( id , bl , c , Class _, Constructors [l]), [] ] -> Some (id, bl, c, l)
  | _ -> None
  in
  if Option.has_some is_defclass then
    (* Definitional class case *)
    let (id, bl, c, l) = Option.get is_defclass in
    let (coe, (lid, ce)) = l in
    let coe' = if coe then Some true else None in
    let f = AssumExpr ((make ?loc:lid.loc @@ Name lid.v), ce),
            { rf_subclass = coe' ; rf_priority = None ; rf_notation = [] ; rf_canonical = true } in
    vernac_record ~template udecl cum (Class true) poly finite [id, bl, c, None, [f]]
  else if List.for_all is_record indl then
    (* Mutual record case *)
    let check_kind ((_, _, _, kind, _), _) = match kind with
    | Variant ->
      user_err (str "The Variant keyword does not support syntax { ... }.")
    | Record | Structure | Class _ | Inductive_kw | CoInductive -> ()
    in
    let () = List.iter check_kind indl in
    let check_where ((_, _, _, _, _), wh) = match wh with
    | [] -> ()
    | _ :: _ ->
      user_err (str "where clause not supported for records")
    in
    let () = List.iter check_where indl in
    let unpack ((id, bl, c, _, decl), _) = match decl with
    | RecordDecl (oc, fs) ->
      (id, bl, c, oc, fs)
    | Constructors _ -> assert false (* ruled out above *)
    in
    let ((_, _, _, kind, _), _) = List.hd indl in
    let kind = match kind with Class _ -> Class false | _ -> kind in
    let recordl = List.map unpack indl in
    vernac_record ~template udecl cum kind poly finite recordl
  else if List.for_all is_constructor indl then
    (* Mutual inductive case *)
    let check_kind ((_, _, _, kind, _), _) = match kind with
    | (Record | Structure) ->
      user_err (str "The Record keyword is for types defined using the syntax { ... }.")
    | Class _ ->
      user_err (str "Inductive classes not supported")
    | Variant | Inductive_kw | CoInductive -> ()
    in
    let () = List.iter check_kind indl in
    let check_name ((na, _, _, _, _), _) = match na with
    | (true, _) ->
      user_err (str "Variant types do not handle the \"> Name\" \
        syntax, which is reserved for records. Use the \":>\" \
        syntax on constructors instead.")
    | _ -> ()
    in
    let () = List.iter check_name indl in
    let unpack (((_, id) , bl, c, _, decl), ntn) = match decl with
    | Constructors l -> (id, bl, c, l), ntn
    | RecordDecl _ -> assert false (* ruled out above *)
    in
    let indl = List.map unpack indl in
    let is_cumulative = should_treat_as_cumulative cum poly in
    let uniform = should_treat_as_uniform () in
    ComInductive.do_mutual_inductive ~template udecl indl is_cumulative ~poly lo ~uniform finite
  else
    user_err (str "Mixed record-inductive definitions are not allowed")
(*

  match indl with
  | [ ( id , bl , c , Class _, Constructors [l]), [] ] ->
      let f =
        let (coe, ({loc;v=id}, ce)) = l in
	let coe' = if coe then Some true else None in
          (((coe', AssumExpr ((make ?loc @@ Name id), ce)), None), [])
      in vernac_record cum (Class true) atts.polymorphic finite [id, bl, c, None, [f]]
    *)

let vernac_fixpoint_common ~atts discharge l =
  if Dumpglob.dump () then
    List.iter (fun (((lid,_), _, _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
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
    List.iter (fun (((lid,_), _, _, _), _) -> Dumpglob.dump_definition lid false "def") l;
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
     List.iter (fun {loc;v=id} -> dump_global (make ?loc @@ AN (qualid_of_ident ?loc id))) l);
 Indschemes.do_combined_scheme lid l

let vernac_universe ~poly l =
  if poly && not (Lib.sections_are_opened ()) then
    user_err ~hdr:"vernac_universe"
		 (str"Polymorphic universes can only be declared inside sections, " ++
		  str "use Monomorphic Universe instead");
  Declare.do_universe ~poly l

let vernac_constraint ~poly l =
  if poly && not (Lib.sections_are_opened ()) then
    user_err ~hdr:"vernac_constraint"
		 (str"Polymorphic universe constraints can only be declared"
		  ++ str " inside sections, use Monomorphic Constraint instead");
  Declare.do_constraint ~poly l

(**********************)
(* Modules            *)

let vernac_import export refl =
  Library.import_module export refl

let vernac_declare_module export {loc;v=id} binders_ast mty_ast =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  let binders_ast = List.map
   (fun (export,idl,ty) ->
     if not (Option.is_empty export) then
      user_err Pp.(str "Arguments of a functor declaration cannot be exported. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
     else (idl,ty)) binders_ast in
  let mp =
    Declaremods.declare_module Modintern.interp_module_ast
      id binders_ast (Declaremods.Enforce mty_ast) []
  in
  Dumpglob.dump_moddef ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is declared");
  Option.iter (fun export -> vernac_import export [qualid_of_ident id]) export

let vernac_define_module export {loc;v=id} (binders_ast : module_binder list) mty_ast_o mexpr_ast_l =
  (* We check the state of the system (in section, in module type)
     and what module information is supplied *)
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");
  match mexpr_ast_l with
    | [] ->
       let binders_ast,argsexport =
        List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> export,i)idl)@argsexport) binders_ast
             ([],[]) in
       let mp =
         Declaremods.start_module Modintern.interp_module_ast
           export id binders_ast mty_ast_o
       in
       Dumpglob.dump_moddef ?loc mp "mod";
       Flags.if_verbose Feedback.msg_info
         (str "Interactive Module " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [qualid_of_ident id]) export
         ) argsexport
    | _::_ ->
       let binders_ast = List.map
        (fun (export,idl,ty) ->
          if not (Option.is_empty export) then
           user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
          else (idl,ty)) binders_ast in
       let mp =
         Declaremods.declare_module Modintern.interp_module_ast
	   id binders_ast mty_ast_o mexpr_ast_l
       in
       Dumpglob.dump_moddef ?loc mp "mod";
       Flags.if_verbose Feedback.msg_info
	 (str "Module " ++ Id.print id ++ str " is defined");
       Option.iter (fun export -> vernac_import export [qualid_of_ident id])
         export

let vernac_end_module export {loc;v=id} =
  let mp = Declaremods.end_module () in
  Dumpglob.dump_modref ?loc mp "mod";
  Flags.if_verbose Feedback.msg_info (str "Module " ++ Id.print id ++ str " is defined");
  Option.iter (fun export -> vernac_import export [qualid_of_ident ?loc id]) export

let vernac_declare_module_type {loc;v=id} binders_ast mty_sign mty_ast_l =
  if Lib.sections_are_opened () then
    user_err Pp.(str "Modules and Module Types are not allowed inside sections.");

  match mty_ast_l with
    | [] ->
       let binders_ast,argsexport =
	 List.fold_right
         (fun (export,idl,ty) (args,argsexport) ->
           (idl,ty)::args, (List.map (fun {v=i} -> export,i)idl)@argsexport) binders_ast
             ([],[]) in

       let mp =
         Declaremods.start_modtype Modintern.interp_module_ast
           id binders_ast mty_sign
       in
       Dumpglob.dump_moddef ?loc mp "modtype";
       Flags.if_verbose Feedback.msg_info
	 (str "Interactive Module Type " ++ Id.print id ++ str " started");
       List.iter
         (fun (export,id) ->
           Option.iter
             (fun export -> vernac_import export [qualid_of_ident ?loc id]) export
         ) argsexport

    | _ :: _ ->
	let binders_ast = List.map
          (fun (export,idl,ty) ->
            if not (Option.is_empty export) then
              user_err Pp.(str "Arguments of a functor definition can be imported only if the definition is interactive. Remove the \"Export\" and \"Import\" keywords from every functor argument.")
            else (idl,ty)) binders_ast in
	let mp =
          Declaremods.declare_modtype Modintern.interp_module_ast
	    id binders_ast mty_sign mty_ast_l
        in
        Dumpglob.dump_moddef ?loc mp "modtype";
	Flags.if_verbose Feedback.msg_info
	  (str "Module Type " ++ Id.print id ++ str " is defined")

let vernac_end_modtype {loc;v=id} =
  let mp = Declaremods.end_modtype () in
  Dumpglob.dump_modref ?loc mp "modtype";
  Flags.if_verbose Feedback.msg_info (str "Module Type " ++ Id.print id ++ str " is defined")

let vernac_include l =
  Declaremods.declare_include Modintern.interp_module_ast l

(**********************)
(* Gallina extensions *)

(* Sections *)

let vernac_begin_section ({v=id} as lid) =
  Dumpglob.dump_definition lid true "sec";
  Lib.open_section id

let vernac_end_section {CAst.loc} =
  Dumpglob.dump_reference ?loc
    (DirPath.to_string (Lib.current_dirpath true)) "<>" "sec";
  Lib.close_section ()

let vernac_name_sec_hyp {v=id} set = Proof_using.name_set id set

(* Dispatcher of the "End" command *)

let vernac_end_segment ({v=id} as lid) =
  match Lib.find_opening_node id with
  | Lib.OpenedModule (false,export,_,_) -> vernac_end_module export lid
  | Lib.OpenedModule (true,_,_,_) -> vernac_end_modtype lid
  | Lib.OpenedSection _ -> vernac_end_section lid
  | _ -> assert false

(* Libraries *)

let warn_require_in_section =
  let name = "require-in-section" in
  let category = "deprecated" in
  CWarnings.create ~name ~category
    (fun () -> strbrk "Use of “Require” inside a section is deprecated.")

let vernac_require from import qidl =
  if Lib.sections_are_opened () then warn_require_in_section ();
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

let vernac_canonical r =
  Canonical.declare_canonical_structure (smart_global r)

let vernac_coercion ~atts ref qids qidt =
  let local, poly = Attributes.(parse Notations.(locality ++ polymorphic) atts) in
  let local = enforce_locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  let ref' = smart_global ref in
  Class.try_add_new_coercion_with_target ref' ~local ~poly ~source ~target;
  Flags.if_verbose Feedback.msg_info (pr_global ref' ++ str " is now a coercion")

let vernac_identity_coercion ~atts id qids qidt =
  let local, poly = Attributes.(parse Notations.(locality ++ polymorphic) atts) in
  let local = enforce_locality local in
  let target = cl_of_qualid qidt in
  let source = cl_of_qualid qids in
  Class.try_add_new_identity_coercion id ~local ~poly ~source ~target

(* Type classes *)

let vernac_instance_program ~atts name bl t props info =
  Dumpglob.dump_constraint (fst name) false "inst";
  let (program, locality), poly =
    Attributes.(parse (Notations.(program ++ locality ++ polymorphic))) atts
  in
  let global = not (make_section_locality locality) in
  let _id : Id.t = Classes.new_instance_program ~global ~poly name bl t props info in
  ()

let vernac_instance_interactive ~atts name bl t info =
  Dumpglob.dump_constraint (fst name) false "inst";
  let (program, locality), poly =
    Attributes.(parse (Notations.(program ++ locality ++ polymorphic))) atts
  in
  let global = not (make_section_locality locality) in
  let _id, pstate =
    Classes.new_instance_interactive ~global ~poly name bl t info in
  pstate

let vernac_instance ~atts name bl t props info =
  Dumpglob.dump_constraint (fst name) false "inst";
  let (program, locality), poly =
    Attributes.(parse (Notations.(program ++ locality ++ polymorphic))) atts
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

let vernac_context ~poly l =
  if not (ComAssumption.context ~poly l) then Feedback.feedback Feedback.AddedAxiom

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
  Proof_global.map_proof (fun p ->
      let intern env sigma = Constrintern.intern_constr env sigma com in
      Proof.V82.instantiate_evar (Global.env ()) n intern p) pstate

let vernac_set_end_tac ~pstate tac =
  let env = Genintern.empty_glob_sign (Global.env ()) in
  let _, tac = Genintern.generic_intern env tac in
  (* TO DO verifier s'il faut pas mettre exist s | TacId s ici*)
  Proof_global.set_endline_tactic tac pstate

let vernac_set_used_variables ~pstate e : Proof_global.t =
  let env = Global.env () in
  let initial_goals pf = Proofview.initial_goals Proof.(data pf).Proof.entry in
  let tys = List.map snd (initial_goals (Proof_global.get_proof pstate)) in
  let tys = List.map EConstr.Unsafe.to_constr tys in
  let l = Proof_using.process_expr env e tys in
  let vars = Environ.named_context env in
  List.iter (fun id ->
    if not (List.exists (NamedDecl.get_id %> Id.equal id) vars) then
      user_err ~hdr:"vernac_set_used_variables"
        (str "Unknown variable: " ++ Id.print id))
    l;
  let _, pstate = Proof_global.set_used_variables pstate l in
  pstate

(*****************************)
(* Auxiliary file management *)

let expand filename =
  Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) filename

let vernac_add_loadpath implicit pdir ldiropt =
  let open Loadpath in
  let pdir = expand pdir in
  let alias = Option.default Libnames.default_root_prefix ldiropt in
  add_coq_path { recursive = true;
                 path_spec = VoPath { unix_path = pdir; coq_path = alias; has_ml = AddTopML; implicit } }

let vernac_remove_loadpath path =
  Loadpath.remove_load_path (expand path)
  (* Coq syntax for ML or system commands *)

let vernac_add_ml_path isrec path =
  let open Loadpath in
  add_coq_path { recursive = isrec; path_spec = MlPath (expand path) }

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
  States.extern_state file

let vernac_restore_state file =
  let file = Loadpath.locate_file (CUnix.make_suffix file ".coq") in
  States.intern_state file

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
  let local, poly = Attributes.(parse Notations.(locality ++ polymorphic) atts) in
  let local = enforce_module_locality local in
  Hints.add_hints ~local dbnames (Hints.interp_hints ~poly h)

let vernac_syntactic_definition ~atts lid x compat =
  let module_local, deprecation = Attributes.(parse Notations.(module_locality ++ deprecation) atts) in
  Dumpglob.dump_definition lid false "syndef";
  Metasyntax.add_syntactic_definition ~local:module_local deprecation (Global.env()) lid.v x compat

let cache_bidi_hints (_name, (gr, ohint)) =
  match ohint with
  | None -> Pretyping.clear_bidirectionality_hint gr
  | Some nargs -> Pretyping.add_bidirectionality_hint gr nargs

let load_bidi_hints _ r =
  cache_bidi_hints r

let subst_bidi_hints (subst, (gr, ohint as orig)) =
  let gr' = subst_global_reference subst gr in
  if gr == gr' then orig else (gr', ohint)

let discharge_bidi_hints (_name, (gr, ohint)) =
  if isVarRef gr && Lib.is_in_section gr then None
  else
    let vars = Lib.variable_section_segment_of_reference gr in
    let n = List.length vars in
    Some (gr, Option.map ((+) n) ohint)

let inBidiHints =
  let open Libobject in
  declare_object { (default_object "BIDIRECTIONALITY-HINTS" ) with
                   load_function = load_bidi_hints;
                   cache_function = cache_bidi_hints;
                   classify_function = (fun o -> Substitute o);
                   subst_function = subst_bidi_hints;
                   discharge_function = discharge_bidi_hints;
                 }


let warn_arguments_assert =
  CWarnings.create ~name:"arguments-assert" ~category:"vernacular"
         (fun sr ->
          strbrk "This command is just asserting the names of arguments of " ++
            pr_global sr ++ strbrk". If this is what you want add " ++
            strbrk "': assert' to silence the warning. If you want " ++
            strbrk "to clear implicit arguments add ': clear implicits'. " ++
            strbrk "If you want to clear notation scopes add ': clear scopes'")

(* [nargs_for_red] is the number of arguments required to trigger reduction,
   [args] is the main list of arguments statuses,
   [more_implicits] is a list of extra lists of implicit statuses  *)
let vernac_arguments ~section_local reference args more_implicits nargs_for_red nargs_before_bidi flags =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let assert_flag = List.mem `Assert flags in
  let rename_flag = List.mem `Rename flags in
  let clear_scopes_flag = List.mem `ClearScopes flags in
  let extra_scopes_flag = List.mem `ExtraScopes flags in
  let clear_implicits_flag = List.mem `ClearImplicits flags in
  let default_implicits_flag = List.mem `DefaultImplicits flags in
  let never_unfold_flag = List.mem `ReductionNeverUnfold flags in
  let nomatch_flag = List.mem `ReductionDontExposeCase flags in
  let clear_bidi_hint = List.mem `ClearBidiHint flags in

  let err_incompat x y =
    user_err Pp.(str ("Options \""^x^"\" and \""^y^"\" are incompatible.")) in

  if assert_flag && rename_flag then
    err_incompat "assert" "rename";
  if clear_scopes_flag && extra_scopes_flag then
    err_incompat "clear scopes" "extra scopes";
  if clear_implicits_flag && default_implicits_flag then
    err_incompat "clear implicits" "default implicits";

  let sr = smart_global reference in
  let inf_names =
    let ty, _ = Typeops.type_of_global_in_context env sr in
    Impargs.compute_implicits_names env sigma (EConstr.of_constr ty)
  in
  let prev_names =
    try Arguments_renaming.arguments_names sr with Not_found -> inf_names
  in
  let num_args = List.length inf_names in
  assert (Int.equal num_args (List.length prev_names));

  let names_of args = List.map (fun a -> a.name) args in

  (* Checks *)

  let err_extra_args names =
    user_err ~hdr:"vernac_declare_arguments"
                 (strbrk "Extra arguments: " ++
                    prlist_with_sep pr_comma Name.print names ++ str ".")
  in
  let err_missing_args names =
    user_err ~hdr:"vernac_declare_arguments"
                 (strbrk "The following arguments are not declared: " ++
                    prlist_with_sep pr_comma Name.print names ++ str ".")
  in

  let rec check_extra_args extra_args =
    match extra_args with
    | [] -> ()
    | { notation_scope = None } :: _ ->
      user_err Pp.(str"Extra arguments should specify a scope.")
    | { notation_scope = Some _ } :: args -> check_extra_args args
  in

  let args, scopes =
    let scopes = List.map (fun { notation_scope = s } -> s) args in
    if List.length args > num_args then
      let args, extra_args = List.chop num_args args in
      if extra_scopes_flag then
        (check_extra_args extra_args; (args, scopes))
      else err_extra_args (names_of extra_args)
    else args, scopes
  in

  if Option.cata (fun n -> n > num_args) false nargs_for_red then
    user_err Pp.(str "The \"/\" modifier should be put before any extra scope.");

  if Option.cata (fun n -> n > num_args) false nargs_before_bidi then
    user_err Pp.(str "The \"&\" modifier should be put before any extra scope.");

  let scopes_specified = List.exists Option.has_some scopes in
  
  if scopes_specified && clear_scopes_flag then
    user_err Pp.(str "The \"clear scopes\" flag is incompatible with scope annotations.");

  let names = List.map (fun { name } -> name) args in
  let names = names :: List.map (List.map fst) more_implicits in

  let rename_flag_required = ref false in
  let example_renaming = ref None in
  let save_example_renaming renaming =
    rename_flag_required := !rename_flag_required
                            || not (Name.equal (fst renaming) Anonymous);
    if Option.is_empty !example_renaming then
      example_renaming := Some renaming
  in

  let rec names_union names1 names2 =
    match names1, names2 with
    | [], [] -> []
    | _ :: _, [] -> names1
    | [], _ :: _ -> names2
    | (Name _ as name) :: names1, Anonymous :: names2
    | Anonymous :: names1, (Name _ as name) :: names2 ->
       name :: names_union names1 names2
    | name1 :: names1, name2 :: names2 ->
       if Name.equal name1 name2 then
         name1 :: names_union names1 names2
       else user_err Pp.(str "Argument lists should agree on the names they provide.")
  in

  let names = List.fold_left names_union [] names in

  let rec rename prev_names names =
    match prev_names, names with
    | [], [] -> []
    | [], _ :: _ -> err_extra_args names
    | _ :: _, [] when assert_flag ->
       (* Error messages are expressed in terms of original names, not
            renamed ones. *)
       err_missing_args (List.lastn (List.length prev_names) inf_names)
    | _ :: _, [] -> prev_names
    | prev :: prev_names, Anonymous :: names ->
       prev :: rename prev_names names
    | prev :: prev_names, (Name id as name) :: names ->
       if not (Name.equal prev name) then save_example_renaming (prev,name);
       name :: rename prev_names names
  in
  
  let names = rename prev_names names in
  let renaming_specified = Option.has_some !example_renaming in

  if !rename_flag_required && not rename_flag then begin
    let msg =
      match !example_renaming with
      | None ->
        strbrk "To rename arguments the \"rename\" flag must be specified."
      | Some (o,n) ->
        strbrk "Flag \"rename\" expected to rename " ++ Name.print o ++
        strbrk " into " ++ Name.print n ++ str "."
    in user_err ~hdr:"vernac_declare_arguments" msg
  end;

  let duplicate_names =
    List.duplicates Name.equal (List.filter ((!=) Anonymous) names)
  in
  if not (List.is_empty duplicate_names) then begin
    let duplicates = prlist_with_sep pr_comma Name.print duplicate_names in
    user_err (strbrk "Some argument names are duplicated: " ++ duplicates)
  end;

  let implicits =
    List.map (fun { name; implicit_status = i } -> (name,i)) args
  in
  let implicits = implicits :: more_implicits in

  let implicits = List.map (List.map snd) implicits in
  let implicits_specified = match implicits with
    | [l] -> List.exists (function Impargs.NotImplicit -> false | _ -> true) l
    | _ -> true in

  if implicits_specified && clear_implicits_flag then
    user_err Pp.(str "The \"clear implicits\" flag is incompatible with implicit annotations");

  if implicits_specified && default_implicits_flag then
    user_err Pp.(str "The \"default implicits\" flag is incompatible with implicit annotations");

  let rargs =
    Util.List.map_filter (function (n, true) -> Some n | _ -> None)
      (Util.List.map_i (fun i { recarg_like = b } -> i, b) 0 args)
  in

  let red_behavior =
    let open Reductionops.ReductionBehaviour in
    match never_unfold_flag, nomatch_flag, rargs, nargs_for_red with
    | true, false, [], None -> Some NeverUnfold
    | true, true, _, _ -> err_incompat "simpl never" "simpl nomatch"
    | true, _, _::_, _ -> err_incompat "simpl never" "!"
    | true, _, _, Some _ -> err_incompat "simpl never" "/"
    | false, false, [], None  -> None
    | false, false, _, _ -> Some (UnfoldWhen { nargs = nargs_for_red;
                                               recargs = rargs;
                                             })
    | false, true, _, _ -> Some (UnfoldWhenNoMatch { nargs = nargs_for_red;
                                                     recargs = rargs;
                                                   })
  in


  let red_modifiers_specified = Option.has_some red_behavior in

  let bidi_hint_specified = Option.has_some nargs_before_bidi in

  if bidi_hint_specified && clear_bidi_hint then
    err_incompat "clear bidirectionality hint" "&";


  (* Actions *)

  if renaming_specified then begin
    Arguments_renaming.rename_arguments section_local sr names
  end;

  if scopes_specified || clear_scopes_flag then begin
      let scopes = List.map (Option.map (fun {loc;v=k} ->
        try ignore (Notation.find_scope k); k
        with UserError _ ->
          Notation.find_delimiters_scope ?loc k)) scopes
      in
      vernac_arguments_scope ~section_local reference scopes
    end;

  if implicits_specified || clear_implicits_flag then
    Impargs.set_implicits section_local (smart_global reference) implicits;

  if default_implicits_flag then
    Impargs.declare_implicits section_local (smart_global reference);

  if red_modifiers_specified then begin
    match sr with
    | ConstRef _ as c ->
       Reductionops.ReductionBehaviour.set
         ~local:section_local c (Option.get red_behavior)

    | _ -> user_err
             (strbrk "Modifiers of the behavior of the simpl tactic "++
              strbrk "are relevant for constants only.")
  end;

  if bidi_hint_specified then begin
    let n = Option.get nargs_before_bidi in
    if section_local then
      Pretyping.add_bidirectionality_hint sr n
    else
      Lib.add_anonymous_leaf (inBidiHints (sr, Some n))
    end;

  if clear_bidi_hint then begin
    if section_local then
      Pretyping.clear_bidirectionality_hint sr
    else
      Lib.add_anonymous_leaf (inBidiHints (sr, None))
  end;

 if not (renaming_specified ||
         implicits_specified ||
         scopes_specified ||
         red_modifiers_specified ||
         bidi_hint_specified) && (List.is_empty flags) then
    warn_arguments_assert sr

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

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "allow sprop";
      optkey   = ["Allow";"StrictProp"];
      optread  = (fun () -> Global.sprop_allowed());
      optwrite = Global.set_allow_sprop }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "silent";
      optkey   = ["Silent"];
      optread  = (fun () -> !Flags.quiet);
      optwrite = ((:=) Flags.quiet) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit arguments";
      optkey   = ["Implicit";"Arguments"];
      optread  = Impargs.is_implicit_args;
      optwrite = Impargs.make_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "strict implicit arguments";
      optkey   = ["Strict";"Implicit"];
      optread  = Impargs.is_strict_implicit_args;
      optwrite = Impargs.make_strict_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "strong strict implicit arguments";
      optkey   = ["Strongly";"Strict";"Implicit"];
      optread  = Impargs.is_strongly_strict_implicit_args;
      optwrite = Impargs.make_strongly_strict_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "contextual implicit arguments";
      optkey   = ["Contextual";"Implicit"];
      optread  = Impargs.is_contextual_implicit_args;
      optwrite = Impargs.make_contextual_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit status of reversible patterns";
      optkey   = ["Reversible";"Pattern";"Implicit"];
      optread  = Impargs.is_reversible_pattern_implicit_args;
      optwrite = Impargs.make_reversible_pattern_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "maximal insertion of implicit";
      optkey   = ["Maximal";"Implicit";"Insertion"];
      optread  = Impargs.is_maximal_implicit_args;
      optwrite = Impargs.make_maximal_implicit_args }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "coercion printing";
      optkey   = ["Printing";"Coercions"];
      optread  = (fun () -> !Constrextern.print_coercions);
      optwrite = (fun b ->  Constrextern.print_coercions := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "printing of existential variable instances";
      optkey   = ["Printing";"Existential";"Instances"];
      optread  = (fun () -> !Detyping.print_evar_arguments);
      optwrite = (:=) Detyping.print_evar_arguments }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit arguments printing";
      optkey   = ["Printing";"Implicit"];
      optread  = (fun () -> !Constrextern.print_implicits);
      optwrite = (fun b ->  Constrextern.print_implicits := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "implicit arguments defensive printing";
      optkey   = ["Printing";"Implicit";"Defensive"];
      optread  = (fun () -> !Constrextern.print_implicits_defensive);
      optwrite = (fun b ->  Constrextern.print_implicits_defensive := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "projection printing using dot notation";
      optkey   = ["Printing";"Projections"];
      optread  = (fun () -> !Constrextern.print_projections);
      optwrite = (fun b ->  Constrextern.print_projections := b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "notations printing";
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !Constrextern.print_no_symbol);
      optwrite = (fun b ->  Constrextern.print_no_symbol := not b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "raw printing";
      optkey   = ["Printing";"All"];
      optread  = (fun () -> !Flags.raw_print);
      optwrite = (fun b -> Flags.raw_print := b) }

let () =
  declare_int_option
    { optdepr  = false;
      optname  = "the level of inlining during functor application";
      optkey   = ["Inline";"Level"];
      optread  = (fun () -> Some (Flags.get_inline_level ()));
      optwrite = (fun o ->
	           let lev = Option.default Flags.default_inline_level o in
	           Flags.set_inline_level lev) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "kernel term sharing";
      optkey   = ["Kernel"; "Term"; "Sharing"];
      optread  = (fun () -> (Global.typing_flags ()).Declarations.share_reduction);
      optwrite = Global.set_share_reduction }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "display compact goal contexts";
      optkey   = ["Printing";"Compact";"Contexts"];
      optread  = (fun () -> Printer.get_compact_context());
      optwrite = (fun b -> Printer.set_compact_context b) }

let () =
  declare_int_option
    { optdepr  = false;
      optname  = "the printing depth";
      optkey   = ["Printing";"Depth"];
      optread  = Topfmt.get_depth_boxes;
      optwrite = Topfmt.set_depth_boxes }

let () =
  declare_int_option
    { optdepr  = false;
      optname  = "the printing width";
      optkey   = ["Printing";"Width"];
      optread  = Topfmt.get_margin;
      optwrite = Topfmt.set_margin }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "printing of universes";
      optkey   = ["Printing";"Universes"];
      optread  = (fun () -> !Constrextern.print_universes);
      optwrite = (fun b -> Constrextern.print_universes:=b) }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "dumping bytecode after compilation";
      optkey   = ["Dump";"Bytecode"];
      optread  = (fun () -> !Cbytegen.dump_bytecode);
      optwrite = (:=) Cbytegen.dump_bytecode }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "dumping VM lambda code after compilation";
      optkey   = ["Dump";"Lambda"];
      optread  = (fun () -> !Clambda.dump_lambda);
      optwrite = (:=) Clambda.dump_lambda }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "explicitly parsing implicit arguments";
      optkey   = ["Parsing";"Explicit"];
      optread  = (fun () -> !Constrintern.parsing_explicit);
      optwrite = (fun b ->  Constrintern.parsing_explicit := b) }

let () =
  declare_string_option ~preprocess:CWarnings.normalize_flags_string
    { optdepr  = false;
      optname  = "warnings display";
      optkey   = ["Warnings"];
      optread  = CWarnings.get_flags;
      optwrite = CWarnings.set_flags }

let () =
  declare_string_option 
    { optdepr  = false;
      optname  = "native_compute profiler output";
      optkey   = ["NativeCompute"; "Profile"; "Filename"];
      optread  = Nativenorm.get_profile_filename;
      optwrite = Nativenorm.set_profile_filename }

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "enable native compute profiling";
      optkey   = ["NativeCompute"; "Profiling"];
      optread  = Nativenorm.get_profiling_enabled;
      optwrite = Nativenorm.set_profiling_enabled }

let vernac_set_strategy ~local l =
  let local = Option.default false local in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> user_err Pp.(str
          "cannot set an inductive type or a constructor as transparent") in
  let l = List.map (fun (lev,ql) -> (lev,List.map glob_ref ql)) l in
  Redexpr.set_strategy local l

let vernac_set_opacity ~local (v,l) =
  let local = Option.default true local in
  let glob_ref r =
    match smart_global r with
      | ConstRef sp -> EvalConstRef sp
      | VarRef id -> EvalVarRef id
      | _ -> user_err Pp.(str
          "cannot set an inductive type or a constructor as transparent") in
  let l = List.map glob_ref l in
  Redexpr.set_strategy local [v,l]

let get_option_locality export local =
  if export then
    if Option.is_empty local then OptExport
    else user_err Pp.(str "Locality modifiers forbidden with Export")
  else match local with
  | Some true -> OptLocal
  | Some false -> OptGlobal
  | None -> OptDefault

let vernac_set_option0 ~local export key opt =
  let locality = get_option_locality export local in
  match opt with
  | OptionUnset -> unset_option_value_gen ~locality key
  | OptionSetString s -> set_string_option_value_gen ~locality key s
  | OptionSetInt n -> set_int_option_value_gen ~locality key (Some n)
  | OptionSetTrue -> set_bool_option_value_gen ~locality key true

let vernac_set_append_option ~local export key s =
  let locality = get_option_locality export local in
  set_string_option_append_value_gen ~locality key s

let vernac_set_option ~local export table v = match v with
| OptionSetString s ->
  (* We make a special case for warnings because appending is their
  natural semantics *)
  if CString.List.equal table ["Warnings"] then
    vernac_set_append_option ~local export table s
  else
    let (last, prefix) = List.sep_last table in
    if String.equal last "Append" && not (List.is_empty prefix) then
      vernac_set_append_option ~local export prefix s
    else
      vernac_set_option0 ~local export table v
| _ -> vernac_set_option0 ~local export table v

let vernac_add_option key lv =
  let f = function
    | StringRefValue s -> (get_string_table key).add (Global.env()) s
    | QualidRefValue locqid -> (get_ref_table key).add (Global.env()) locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_remove_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key).remove (Global.env()) s
  | QualidRefValue locqid -> (get_ref_table key).remove (Global.env()) locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

let vernac_mem_option key lv =
  let f = function
  | StringRefValue s -> (get_string_table key).mem (Global.env()) s
  | QualidRefValue locqid -> (get_ref_table key).mem (Global.env()) locqid
  in
  try List.iter f lv with Not_found -> error_undeclared_key key

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
    | Some n -> Pfedit.get_goal_context lemma n
    | None -> Pfedit.get_current_context lemma

let query_command_selector ?loc = function
  | None -> None
  | Some (Goal_select.SelectNth n) -> Some n
  | _ -> user_err ?loc ~hdr:"query_command_selector"
      (str "Query commands only support the single numbered goal selector.")

let vernac_check_may_eval ~pstate ~atts redexp glopt rc =
  let glopt = query_command_selector glopt in
  let sigma, env = get_current_context_of_args ~pstate glopt in
  let sigma, c = interp_open_constr env sigma rc in
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
        print_judgment env sigma j ++
        pr_ne_evar_set (fnl () ++ str "where" ++ fnl ()) (mt ()) sigma l
    | Some r ->
        let (sigma,r_interp) = Hook.get f_interp_redexp env sigma r in
	let redfun env evm c =
          let (redfun, _) = reduction_of_red_expr env r_interp in
          let (_, c) = redfun env evm c in
          c
        in
        print_eval redfun env sigma rc j
  in
  pp ++ Printer.pr_universe_ctx_set sigma uctx

let vernac_declare_reduction ~local s r =
  let local = Option.default false local in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  declare_red_expr local s (snd (Hook.get f_interp_redexp env sigma r))

  (* The same but avoiding the current goal context if any *)
let vernac_global_check c =
  let env = Global.env() in
  let sigma = Evd.from_env env in
  let c,uctx = interp_constr env sigma c in
  let senv = Global.safe_env() in
  let uctx = UState.context_set uctx in
  let senv = Safe_typing.push_context_set false uctx senv in
  let c = EConstr.to_constr sigma c in
  let j = Safe_typing.typing senv c in
  let env = Safe_typing.env_of_safe_env senv in
  print_safe_judgment env sigma j ++
  pr_universe_ctx_set sigma uctx


let get_nth_goal ~pstate n =
  let pf = Proof_global.get_proof pstate in
  let Proof.{goals;sigma} = Proof.data pf in
  let gl = {Evd.it=List.nth goals (n-1) ; sigma = sigma; } in
  gl

exception NoHyp

(* Printing "About" information of a hypothesis of the current goal.
   We only print the type and a small statement to this comes from the
   goal. Precondition: there must be at least one current goal. *)
let print_about_hyp_globs ~pstate ?loc ref_or_by_not udecl glopt =
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
      match glnumopt, ref_or_by_not.v with
      | None,AN qid when qualid_is_ident qid -> (* goal number not given, catch any failure *)
         (try get_nth_goal ~pstate 1, qualid_basename qid with _ -> raise NoHyp)
      | Some n,AN qid when qualid_is_ident qid ->  (* goal number given, catch if wong *)
         (try get_nth_goal ~pstate n, qualid_basename qid
	  with
	    Failure _ -> user_err ?loc ~hdr:"print_about_hyp_globs"
                          (str "No such goal: " ++ int n ++ str "."))
      | _ , _ -> raise NoHyp in
    let hyps = pf_hyps gl in
    let decl = Context.Named.lookup id hyps in
    let natureofid = match decl with
                     | LocalAssum _ -> "Hypothesis"
                     | LocalDef (_,bdy,_) ->"Constant (let in)" in
    let sigma, env = Pfedit.get_current_context pstate in
    v 0 (Id.print id ++ str":" ++ pr_econstr_env env sigma (NamedDecl.get_type decl) ++ fnl() ++ fnl()
	 ++ str natureofid ++ str " of the goal context.")
  with (* fallback to globals *)
    | NoHyp | Not_found ->
    let sigma, env = get_current_or_global_context ~pstate in
    print_about env sigma ref_or_by_not udecl

let vernac_print ~pstate ~atts =
  let sigma, env = get_current_or_global_context ~pstate in
  function
  | PrintTables -> print_tables ()
  | PrintFullContext-> print_full_context_typ env sigma
  | PrintSectionContext qid -> print_sec_context_typ env sigma qid
  | PrintInspect n -> inspect env sigma n
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
    print_name env sigma qid udecl
  | PrintGraph -> Prettyp.print_graph ()
  | PrintClasses -> Prettyp.print_classes()
  | PrintTypeClasses -> Prettyp.print_typeclasses()
  | PrintInstances c -> Prettyp.print_instances (smart_global c)
  | PrintCoercions -> Prettyp.print_coercions ()
  | PrintCoercionPaths (cls,clt) ->
    Prettyp.print_path_between (cl_of_qualid cls) (cl_of_qualid clt)
  | PrintCanonicalConversions -> Prettyp.print_canonical_projections env sigma
  | PrintUniverses (sort, subgraph, dst) -> print_universes ~sort ~subgraph dst
  | PrintHint r -> Hints.pr_hint_ref env sigma (smart_global r)
  | PrintHintGoal ->
     begin match pstate with
     | Some pstate ->
       Hints.pr_applicable_hint pstate
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
    print_impargs qid
  | PrintAssumptions (o,t,r) ->
      (* Prints all the axioms and section variables used by a term *)
      let gr = smart_global r in
      let cstr = printable_constr_of_global gr in
      let st = Conv_oracle.get_transp_state (Environ.oracle (Global.env())) in
      let nassums =
	Assumptions.assumptions st ~add_opaque:o ~add_transparent:t gr cstr in
      Printer.pr_assumptionset env sigma nassums
  | PrintStrategy r -> print_strategy r
  | PrintRegistered -> print_registered ()

let global_module qid =
  try Nametab.full_name_module qid
  with Not_found ->
    user_err ?loc:qid.CAst.loc ~hdr:"global_module"
     (str "Module/section " ++ pr_qualid qid ++ str " not found.")

let interp_search_restriction = function
  | SearchOutside l -> (List.map global_module l, true)
  | SearchInside l -> (List.map global_module l, false)

open Search

let interp_search_about_item env sigma =
  function
  | SearchSubPattern pat ->
      let _,pat = intern_constr_pattern env sigma pat in
      GlobSearchSubPattern pat
  | SearchString (s,None) when Id.is_valid s ->
      GlobSearchString s
  | SearchString (s,sc) ->
      try
	let ref =
	  Notation.interp_notation_as_global_reference
	    (fun _ -> true) s sc in
	GlobSearchSubPattern (Pattern.PRef ref)
      with UserError _ ->
	user_err ~hdr:"interp_search_about_item"
          (str "Unable to interp \"" ++ str s ++ str "\" either as a reference or as an identifier component")

(* 05f22a5d6d5b8e3e80f1a37321708ce401834430 introduced the
   `search_output_name_only` option to avoid excessive printing when
   searching.

   The motivation was to make search usable for IDE completion,
   however, it is still too slow due to the non-indexed nature of the
   underlying search mechanism.

   In the future we should deprecate the option and provide a fast,
   indexed name-searching interface.
*)
let search_output_name_only = ref false

let () =
  declare_bool_option
    { optdepr  = false;
      optname  = "output-name-only search";
      optkey   = ["Search";"Output";"Name";"Only"];
      optread  = (fun () -> !search_output_name_only);
      optwrite = (:=) search_output_name_only }

let vernac_search ~pstate ~atts s gopt r =
  let gopt = query_command_selector gopt in
  let r = interp_search_restriction r in
  let env,gopt =
    match gopt with | None ->
      (* 1st goal by default if it exists, otherwise no goal at all *)
      (try snd (get_goal_or_global_context ~pstate 1) , Some 1
       with _ -> Global.env (),None)
    (* if goal selector is given and wrong, then let exceptions be raised. *)
    | Some g -> snd (get_goal_or_global_context ~pstate g) , Some g
  in
  let get_pattern c = snd (intern_constr_pattern env Evd.(from_env env) c) in
  let pr_search ref env c =
    let pr = pr_global ref in
    let pp = if !search_output_name_only
      then pr
      else begin
        let pc = pr_lconstr_env env Evd.(from_env env) c in
        hov 2 (pr ++ str":" ++ spc () ++ pc)
      end
    in Feedback.msg_notice pp
  in
  match s with
  | SearchPattern c ->
      (Search.search_pattern ?pstate gopt (get_pattern c) r |> Search.prioritize_search) pr_search
  | SearchRewrite c ->
      (Search.search_rewrite ?pstate gopt (get_pattern c) r |> Search.prioritize_search) pr_search
  | SearchHead c ->
      (Search.search_by_head ?pstate gopt (get_pattern c) r |> Search.prioritize_search) pr_search
  | SearchAbout sl ->
      (Search.search_about ?pstate gopt (List.map (on_snd (interp_search_about_item env Evd.(from_env env))) sl) r |>
       Search.prioritize_search) pr_search

let vernac_locate ~pstate = function
  | LocateAny {v=AN qid}  -> print_located_qualid qid
  | LocateTerm {v=AN qid} -> print_located_term qid
  | LocateAny {v=ByNotation (ntn, sc)} (* TODO : handle Ltac notations *)
  | LocateTerm {v=ByNotation (ntn, sc)} ->
    let _, env = get_current_or_global_context ~pstate in
    Notation.locate_notation
      (Constrextern.without_symbols (pr_lglob_constr_env env)) ntn sc
  | LocateLibrary qid -> print_located_library qid
  | LocateModule qid -> print_located_module qid
  | LocateOther (s, qid) -> print_located_other s qid
  | LocateFile f -> locate_file f

let vernac_register qid r =
  let gr = Smartlocate.global_with_alias qid in
  match r with
  | RegisterInline ->
    begin match gr with
    | ConstRef c -> Global.register_inline c
    | _ -> CErrors.user_err (Pp.str "Register Inline: expecting a constant")
    end
  | RegisterCoqlib n ->
    let ns, id = Libnames.repr_qualid n in
    if DirPath.equal (dirpath_of_string "kernel") ns then begin
      if Lib.sections_are_opened () then
        user_err Pp.(str "Registering a kernel type is not allowed in sections");
      let pind = match Id.to_string id with
        | "ind_bool" -> CPrimitives.PIT_bool
        | "ind_carry" -> CPrimitives.PIT_carry
        | "ind_pair" -> CPrimitives.PIT_pair
        | "ind_cmp" -> CPrimitives.PIT_cmp
        | k -> CErrors.user_err Pp.(str "Register: unknown identifier “" ++ str k ++ str "” in the “kernel” namespace")
      in
      match gr with
      | IndRef ind -> Global.register_inductive ind pind
      | _ -> CErrors.user_err (Pp.str "Register in kernel: expecting an inductive type")
    end
    else Coqlib.register_ref (Libnames.string_of_qualid n) gr

(********************)
(* Proof management *)

let vernac_focus ~pstate gln =
  Proof_global.map_proof (fun p ->
    match gln with
      | None -> Proof.focus focus_command_cond () 1 p
      | Some 0 ->
         user_err Pp.(str "Invalid goal number: 0. Goal numbering starts with 1.")
      | Some n ->
         Proof.focus focus_command_cond () n p)
    pstate

  (* Unfocuses one step in the focus stack. *)
let vernac_unfocus ~pstate =
  Proof_global.map_proof
    (fun p -> Proof.unfocus command_focus p ())
    pstate

(* Checks that a proof is fully unfocused. Raises an error if not. *)
let vernac_unfocused ~pstate =
  let p = Proof_global.get_proof pstate in
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
  Proof_global.map_proof (fun p ->
    match gln with
    | None -> Proof.focus subproof_cond () 1 p
    | Some (Goal_select.SelectNth n) -> Proof.focus subproof_cond () n p
    | Some (Goal_select.SelectId id) -> Proof.focus_id subproof_cond () id p
    | _ -> user_err ~hdr:"bracket_selector"
             (str "Brackets do not support multi-goal selectors."))
    pstate

let vernac_end_subproof ~pstate =
  Proof_global.map_proof (fun p ->
      Proof.unfocus subproof_kind p ())
    pstate

let vernac_bullet (bullet : Proof_bullet.t) ~pstate =
  Proof_global.map_proof (fun p ->
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
    let proof = Proof_global.get_proof pstate in
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
      Id.print (Proof_global.get_proof_name pstate)
    | ShowIntros all -> show_intro ~proof all
    | ShowProof -> show_proof ~pstate:(Some pstate)
    | ShowMatch id -> show_match id
    end

let vernac_check_guard ~pstate =
  let pts = Proof_global.get_proof pstate in
  let pfterm = List.hd (Proof.partial_proof pts) in
  let message =
    try
      let { Evd.it=gl ; sigma=sigma } = Proof.V82.top_goal pts in
      Inductiveops.control_only_guard (Goal.V82.env sigma gl) sigma pfterm;
      (str "The condition holds up to here")
    with UserError(_,s) ->
      (str ("Condition violated: ") ++s)
  in message

(** A global default timeout, controlled by option "Set Default Timeout n".
    Use "Unset Default Timeout" to deactivate it (or set it to 0). *)

let default_timeout = ref None

(* Timeout *)
let vernac_timeout ?timeout (f : 'a -> 'b) (x : 'a) : 'b =
  match !default_timeout, timeout with
  | _, Some n
  | Some n, None ->
    Control.timeout n f x Timeout
  | None, None ->
    f x

(* Fail *)
let test_mode = ref false

(* Restoring the state is the caller's responsibility *)
let with_fail f : (Pp.t, unit) result =
  try
    let _ = f () in
    Error ()
  with
  (* Fail Timeout is a common pattern so we need to support it. *)
  | e when CErrors.noncritical e || e = Timeout ->
    (* The error has to be printed in the failing state *)
    Ok CErrors.(iprint ExplainErr.(process_vernac_interp_error (push e)))

(* We restore the state always *)
let with_fail ~st f =
  let res = with_fail f in
  Vernacstate.invalidate_cache ();
  Vernacstate.unfreeze_interp_state st;
  match res with
  | Error () ->
    user_err ~hdr:"Fail" (str "The command has not failed!")
  | Ok msg ->
    if not !Flags.quiet || !test_mode
    then Feedback.msg_info (str "The command has indeed failed with message:" ++ fnl () ++ msg)

let locate_if_not_already ?loc (e, info) =
  match Loc.get_loc info with
  | None   -> (e, Option.cata (Loc.add_loc info) info loc)
  | Some l -> (e, info)

exception End_of_input

(* EJGA: We may remove this, only used twice below *)
let vernac_require_open_lemma ~stack f =
  match stack with
  | Some stack -> f stack
  | None -> user_err Pp.(str "Command not supported (No proof-editing in progress)")

let interp_typed_vernac c ~stack =
  let open Vernacextend in
  match c with
  | VtDefault f -> f (); stack
  | VtNoProof f ->
    if Option.has_some stack then
      user_err Pp.(str "Command not supported (Open proofs remain)");
    let () = f () in
    stack
  | VtCloseProof f ->
    vernac_require_open_lemma ~stack (fun stack ->
        let lemma, stack = Vernacstate.LemmaStack.pop stack in
        f ~lemma;
        stack)
  | VtOpenProof f ->
    Some (Vernacstate.LemmaStack.push stack (f ()))
  | VtModifyProof f ->
    Option.map (Vernacstate.LemmaStack.map_top_pstate ~f:(fun pstate -> f ~pstate)) stack
  | VtReadProofOpt f ->
    let pstate = Option.map (Vernacstate.LemmaStack.with_top_pstate ~f:(fun x -> x)) stack in
    f ~pstate;
    stack
  | VtReadProof f ->
    vernac_require_open_lemma ~stack
      (Vernacstate.LemmaStack.with_top_pstate ~f:(fun pstate -> f ~pstate));
    stack

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
  | VernacBackTo _
  | VernacAbort _
  | VernacLoad _ ->
    anomaly (str "type_vernac")
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
  | VernacInductive (cum, priv, finite, l) ->
    VtDefault(fun () -> vernac_inductive ~atts cum priv finite l)
  | VernacFixpoint (discharge, l) ->
    let opens = List.exists (fun ((_,_,_,_,p),_) -> Option.is_empty p) l in
    if opens then
      VtOpenProof (fun () ->
        with_def_attributes ~atts vernac_fixpoint_interactive discharge l)
    else
      VtDefault (fun () ->
        with_def_attributes ~atts vernac_fixpoint discharge l)
  | VernacCoFixpoint (discharge, l) ->
    let opens = List.exists (fun ((_,_,_,p),_) -> Option.is_empty p) l in
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
        unsupported_attributes atts;
        vernac_begin_section lid)
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
        unsupported_attributes atts;
        vernac_canonical qid)
  | VernacCoercion (r,s,t) ->
    VtDefault(fun () -> vernac_coercion ~atts r s t)
  | VernacIdentityCoercion ({v=id},s,t) ->
    VtDefault(fun () -> vernac_identity_coercion ~atts id s t)

  (* Type classes *)
  | VernacInstance (name, bl, t, props, info) ->
    let { DefAttributes.program } = DefAttributes.parse atts in
    if program then
      VtDefault (fun () -> vernac_instance_program ~atts name bl t props info)
    else begin match props with
    | None ->
       VtOpenProof(fun () ->
        vernac_instance_interactive ~atts name bl t info)
    | Some props ->
       VtDefault(fun () ->
        vernac_instance ~atts name bl t props info)
    end

  | VernacDeclareInstance (id, bl, inst, info) ->
    VtDefault(fun () -> vernac_declare_instance ~atts id bl inst info)
  | VernacContext sup ->
    VtDefault(fun () -> vernac_context ~poly:(only_polymorphism atts) sup)
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
  | VernacAddLoadPath (isrec,s,alias) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_add_loadpath isrec s alias)
  | VernacRemoveLoadPath s ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_remove_loadpath s)
  | VernacAddMLPath (isrec,s) ->
    VtDefault(fun () ->
        unsupported_attributes atts;
        vernac_add_ml_path isrec s)
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
  | VernacArguments (qid, args, more_implicits, nargs, bidi, flags) ->
    VtDefault(fun () ->
        with_section_locality ~atts (vernac_arguments qid args more_implicits nargs bidi flags))
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
  | VernacSetOption (export, key,v) ->
    VtDefault(fun () ->
        vernac_set_option ~local:(only_locality atts) export key v)
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
        ComAssumption.do_primitive id prim typopt)
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

(* "locality" is the prefix "Local" attribute, while the "local" component
 * is the outdated/deprecated "Local" attribute of some vernacular commands
 * still parsed as the obsolete_locality grammar entry for retrocompatibility.
 * loc is the Loc.t of the vernacular command being interpreted. *)
let rec interp_expr ?proof ~atts ~st c =
  let stack = st.Vernacstate.lemmas in
  vernac_pperr_endline (fun () -> str "interpreting: " ++ Ppvernac.pr_vernac_expr c);
  match c with

  (* The STM should handle that, but LOAD bypasses the STM... *)
  | VernacAbortAll    -> CErrors.user_err  (str "AbortAll cannot be used through the Load command")
  | VernacRestart     -> CErrors.user_err  (str "Restart cannot be used through the Load command")
  | VernacUndo _      -> CErrors.user_err  (str "Undo cannot be used through the Load command")
  | VernacUndoTo _    -> CErrors.user_err  (str "UndoTo cannot be used through the Load command")

  (* Resetting *)
  | VernacResetName _  -> anomaly (str "VernacResetName not handled by Stm.")
  | VernacResetInitial -> anomaly (str "VernacResetInitial not handled by Stm.")
  | VernacBack _       -> anomaly (str "VernacBack not handled by Stm.")
  | VernacBackTo _     -> anomaly (str "VernacBackTo not handled by Stm.")

  (* This one is possible to handle here *)
  | VernacAbort id    -> CErrors.user_err  (str "Abort cannot be used through the Load command")

  (* Loading a file requires access to the control interpreter so
     [vernac_load] is mutually-recursive with [interp_expr] *)
  | VernacLoad (verbosely,fname) ->
    unsupported_attributes atts;
    vernac_load ~verbosely ~st fname

  | v ->
    let fv = translate_vernac ~atts v in
    interp_typed_vernac ~stack fv

(* XXX: This won't properly set the proof mode, as of today, it is
   controlled by the STM. Thus, we would need access information from
   the classifier. The proper fix is to move it to the STM, however,
   the way the proof mode is set there makes the task non trivial
   without a considerable amount of refactoring.
 *)
and vernac_load ~verbosely ~st fname =
  let there_are_pending_proofs ~stack = not Option.(is_empty stack) in
  let stack = st.Vernacstate.lemmas in
  if there_are_pending_proofs ~stack then
    CErrors.user_err Pp.(str "Load is not supported inside proofs.");
  (* Open the file *)
  let fname =
    Envars.expand_path_macros ~warn:(fun x -> Feedback.msg_warning (str x)) fname in
  let fname = CUnix.make_suffix fname ".v" in
  let input =
    let longfname = Loadpath.locate_file fname in
    let in_chan = open_utf8_file_in longfname in
    Pcoq.Parsable.make ~loc:(Loc.initial (Loc.InFile longfname)) (Stream.of_channel in_chan) in
  (* Parsing loop *)
  let v_mod = if verbosely then Flags.verbosely else Flags.silently in
  let parse_sentence proof_mode = Flags.with_option Flags.we_are_parsing
    (fun po ->
    match Pcoq.Entry.parse (Pvernac.main_entry proof_mode) po with
      | Some x -> x
      | None -> raise End_of_input) in
  let rec load_loop ~stack =
    try
      let proof_mode = Option.map (fun _ -> get_default_proof_mode ()) stack in
      let stack =
        v_mod (interp_control ?proof:None ~st:{ st with Vernacstate.lemmas = stack })
          (parse_sentence proof_mode input) in
      load_loop ~stack
    with
      End_of_input ->
      stack
  in
  let stack = load_loop ~stack in
  (* If Load left a proof open, we fail too. *)
  if there_are_pending_proofs ~stack then
    CErrors.user_err Pp.(str "Files processed by Load cannot leave open proofs.");
  stack

and interp_control ?proof ~st v = match v with
  | { v=VernacExpr (atts, cmd) } ->
    interp_expr ?proof ~atts ~st cmd
  | { v=VernacFail v } ->
    with_fail ~st (fun () -> interp_control ?proof ~st v);
    st.Vernacstate.lemmas
  | { v=VernacTimeout (timeout,v) } ->
    vernac_timeout ~timeout (interp_control ?proof ~st) v
  | { v=VernacRedirect (s, v) } ->
    Topfmt.with_output_to_file s (interp_control ?proof ~st) v
  | { v=VernacTime (batch, cmd) }->
    let header = if batch then Topfmt.pr_cmd_header cmd else Pp.mt () in
    System.with_time ~batch ~header (interp_control ?proof ~st) cmd

let () =
  declare_int_option
    { optdepr  = false;
      optname  = "the default timeout";
      optkey   = ["Default";"Timeout"];
      optread  = (fun () -> !default_timeout);
      optwrite = ((:=) default_timeout) }

(* Be careful with the cache here in case of an exception. *)
let interp ?(verbosely=true) ~st cmd =
  Vernacstate.unfreeze_interp_state st;
  try vernac_timeout (fun st ->
      let v_mod = if verbosely then Flags.verbosely else Flags.silently in
      let ontop = v_mod (interp_control ~st) cmd in
      Vernacstate.Proof_global.set ontop [@ocaml.warning "-3"];
      Vernacstate.freeze_interp_state ~marshallable:false
    ) st
  with exn ->
    let exn = CErrors.push exn in
    let exn = locate_if_not_already ?loc:cmd.CAst.loc exn in
    Vernacstate.invalidate_cache ();
    iraise exn

let interp_qed_delayed_proof ~proof ~info ~st ?loc pe : Vernacstate.t =
  let stack = st.Vernacstate.lemmas in
  let stack = Option.cata (fun stack -> snd @@ Vernacstate.LemmaStack.pop stack) None stack in
  try
    let () = match pe with
      | Admitted ->
        save_lemma_admitted_delayed ~proof ~info
      | Proved (_,idopt) ->
        save_lemma_proved_delayed ~proof ~info ~idopt in
    { st with Vernacstate.lemmas = stack }
  with exn ->
    let exn = CErrors.push exn in
    let exn = locate_if_not_already ?loc exn in
    Vernacstate.invalidate_cache ();
    iraise exn
