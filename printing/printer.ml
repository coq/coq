(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Constr
open Context
open Environ
open Evd
open Constrextern
open Ppconstr
open Declarations

module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration
module CompactedDecl = Ppconstr.CompactedDecl

let () =
  Goptions.declare_bool_option
    { Goptions.optstage = Summary.Stage.Interp;
      Goptions.optdepr  = None;
      Goptions.optkey   = ["Printing";"Fully";"Qualified"];
      Goptions.optread  = Nametab.print_fully_qualified;
      Goptions.optwrite = Nametab.set_print_fully_qualified }

let current_combined = PrintingFlags.current
let current_extern = PrintingFlags.Extern.current

(**********************************************************************)
(** Terms                                                             *)

(* [goal_concl_style] means that all names of goal/section variables
   and all names of rel variables (if any) in the given env and all short
   names of global definitions of the current module must be avoided while
   printing bound variables.
   Otherwise, short names of global definitions are printed qualified
   and only names of goal/section variables and rel names that do
   _not_ occur in the scope of the binder to be printed are avoided. *)

(* When a [Printing Reversible] flag is set, the externalization is
   checked for reparsability and the printing flags are possibly made
   more explicit accordingly, hence rendering uses the flags returned
   by [ReversiblePrinting.checked_extern]. *)
let checked_extern_constr ?inctx ?scope ~flags env sigma t =
  ReversiblePrinting.checked_extern ~flags
    ~extern:(fun ~flags -> extern_constr ?inctx ?scope ~flags env sigma t)
    ~kind:ReversiblePrinting.Term env sigma t

let checked_extern_type ?goal_concl_style ?impargs ~flags env sigma t =
  ReversiblePrinting.checked_extern ~flags
    ~extern:(fun ~flags -> extern_type ?goal_concl_style ~flags env sigma ?impargs t)
    ~kind:ReversiblePrinting.Type env sigma t

let pr_econstr_n_env ?inctx ?scope ?(flags=current_combined()) env sigma n t =
  let flags, c = checked_extern_constr ?inctx ?scope ~flags env sigma t in
  let ppflags = Ppconstr.of_printing_flags flags in
  pr_constr_expr_n ~flags:ppflags env sigma n c
let pr_econstr_env ?inctx ?scope ?(flags=current_combined()) env sigma t =
  let flags, c = checked_extern_constr ?inctx ?scope ~flags env sigma t in
  let ppflags = Ppconstr.of_printing_flags flags in
  pr_constr_expr ~flags:ppflags env sigma c
let pr_leconstr_env ?inctx ?scope ?(flags=current_combined()) env sigma t =
  let flags, c = checked_extern_constr ?inctx ?scope ~flags env sigma t in
  let ppflags = Ppconstr.of_printing_flags flags in
  Ppconstr.pr_lconstr_expr ~flags:ppflags env sigma c

let pr_constr_n_env ?inctx ?scope ?flags env sigma n c =
  pr_econstr_n_env ?inctx ?scope ?flags env sigma n (EConstr.of_constr c)
let pr_constr_env ?inctx ?scope ?flags env sigma c =
  pr_econstr_env ?inctx ?scope ?flags env sigma (EConstr.of_constr c)
let pr_lconstr_env ?inctx ?scope ?flags env sigma c =
  pr_leconstr_env ?inctx ?scope ?flags env sigma (EConstr.of_constr c)

let pr_constr_under_binders_env_gen pr ?flags env sigma (ids,c) =
  (* Warning: clashes can occur with variables of same name in env but *)
  (* we also need to preserve the actual names of the patterns *)
  (* So what to do? *)
  let assums = List.map (fun id -> (make_annot (Name id) Sorts.Relevant,(* dummy *) mkProp)) ids in
  pr ?inctx:None ?scope:None ?flags (Termops.push_rels_assum assums env) sigma c

let pr_constr_under_binders_env = pr_constr_under_binders_env_gen pr_econstr_env
let pr_lconstr_under_binders_env = pr_constr_under_binders_env_gen pr_leconstr_env

let pr_etype_env ?goal_concl_style ?(flags=current_combined()) env sigma t =
  let flags, c = checked_extern_type ?goal_concl_style ~flags env sigma t in
  let ppflags = Ppconstr.of_printing_flags flags in
  pr_constr_expr ~flags:ppflags env sigma c
let pr_letype_env ?goal_concl_style ?(flags=current_combined()) env sigma ?impargs t =
  let flags, c = checked_extern_type ?goal_concl_style ?impargs ~flags env sigma t in
  let ppflags = Ppconstr.of_printing_flags flags in
  pr_lconstr_expr ~flags:ppflags env sigma c

let pr_type_env ?goal_concl_style ?flags env sigma c =
  pr_etype_env ?goal_concl_style ?flags env sigma (EConstr.of_constr c)
let pr_ltype_env ?goal_concl_style ?flags env sigma ?impargs c =
  pr_letype_env ?goal_concl_style ?flags env sigma ?impargs (EConstr.of_constr c)

let pr_ljudge_env ?flags env sigma j =
  (pr_leconstr_env ?flags env sigma j.uj_val, pr_leconstr_env ?flags env sigma j.uj_type)

let pr_lglob_constr_env ?(flags=current_extern()) env sigma c =
  let ppflags = Ppconstr.of_extern_flags flags in
  pr_lconstr_expr ~flags:ppflags env sigma
    (extern_glob_constr (extern_env ~flags env sigma) c)
let pr_glob_constr_env ?(flags=current_extern()) env sigma c =
  let ppflags = Ppconstr.of_extern_flags flags in
  pr_constr_expr ~flags:ppflags env sigma
    (extern_glob_constr (extern_env ~flags env sigma) c)

let pr_closed_glob_n_env ?goal_concl_style ?inctx ?scope ?(flags=current_combined()) env sigma n c =
  let ppflags = Ppconstr.of_printing_flags flags in
  pr_constr_expr_n ~flags:ppflags env sigma n
    (extern_closed_glob ?goal_concl_style ?inctx ?scope ~flags env sigma c)
let pr_closed_glob_env ?goal_concl_style ?inctx ?scope ?(flags=current_combined()) env sigma c =
  let ppflags = Ppconstr.of_printing_flags flags in
  pr_constr_expr ~flags:ppflags env sigma
    (extern_closed_glob ?goal_concl_style ?inctx ?scope ~flags env sigma c)
let pr_closed_lglob_env ?goal_concl_style ?inctx ?scope ?(flags=current_combined()) env sigma c =
  let ppflags = Ppconstr.of_printing_flags flags in
  pr_lconstr_expr ~flags:ppflags env sigma
    (extern_closed_glob ?goal_concl_style ?inctx ?scope ~flags env sigma c)

let pr_lconstr_pattern_env ?(flags=current_extern()) env sigma c =
  let ppflags = Ppconstr.of_extern_flags flags in
  pr_lconstr_pattern_expr ~flags:ppflags env sigma
    (extern_constr_pattern ~flags (Termops.names_of_rel_context env) sigma c)
let pr_constr_pattern_env ?(flags=current_extern()) env sigma c =
  let ppflags = Ppconstr.of_extern_flags flags in
  pr_constr_pattern_expr ~flags:ppflags env sigma
    (extern_constr_pattern ~flags (Termops.names_of_rel_context env) sigma c)
let pr_uninstantiated_lconstr_pattern_env ?(flags=current_extern()) env sigma c =
  let ppflags = Ppconstr.of_extern_flags flags in
  pr_lconstr_pattern_expr ~flags:ppflags env sigma
    (extern_uninstantiated_pattern ~flags (Termops.names_of_rel_context env) sigma c)
let pr_uninstantiated_constr_pattern_env ?(flags=current_extern()) env sigma c =
  let ppflags = Ppconstr.of_extern_flags flags in
  pr_constr_pattern_expr ~flags:ppflags env sigma
    (extern_uninstantiated_pattern ~flags (Termops.names_of_rel_context env) sigma c)

let pr_cases_pattern ?(flags=current_extern()) t =
  let ppflags = Ppconstr.of_extern_flags flags in
  pr_cases_pattern_expr ~flags:ppflags
    (extern_cases_pattern ~flags Names.Id.Set.empty t)

let pr_sort ?universes ?qualities sigma s =
  let flags = PrintingFlags.Detype.current() in
  let universes = Option.default flags.universes universes in
  let qualities = Option.default flags.qualities qualities in
  pr_sort_expr (extern_sort ~universes ~qualities sigma s)

let () = Termops.Internal.set_print_constr
  (fun env sigma t -> pr_leconstr_env ~flags:(current_combined()) env sigma t)

let pr_in_comment x = str "(* " ++ x ++ str " *)"

(** Term printers resilient to [Nametab] errors *)

(** When the nametab isn't up-to-date, the term printers above
    could raise [Not_found] during [Nametab.shortest_qualid_of_global].
    In this case, we build here a fully-qualified name based upon
    the kernel modpath and label of constants, and the idents in
    the [mutual_inductive_body] for the inductives and constructors
    (needs an environment for this). *)

let id_of_global env = let open GlobRef in function
  | ConstRef kn -> Constant.label kn
  | IndRef (kn,0) -> MutInd.label kn
  | IndRef (kn,i) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_typename
  | ConstructRef ((kn,i),j) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_consnames.(j-1)
  | VarRef v -> v

let rec dirpath_of_mp = function
  | MPfile sl -> sl
  | MPbound uid -> DirPath.make [MBId.to_id uid]
  | MPdot (mp,l) ->
    Libnames.add_dirpath_suffix (dirpath_of_mp mp) l

let dirpath_of_global = let open GlobRef in function
  | ConstRef kn -> dirpath_of_mp (Constant.modpath kn)
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
    dirpath_of_mp (MutInd.modpath kn)
  | VarRef _ -> DirPath.empty

let qualid_of_global ?loc env r =
  Libnames.make_qualid ?loc (dirpath_of_global r) (id_of_global env r)

let safe_extern_wrapper f env sigma c =
  let orig_extern_ref = Constrextern.get_extern_reference () in
  let extern_ref ?loc vars r =
    try orig_extern_ref vars r
    with e when CErrors.noncritical e ->
      qualid_of_global ?loc env r
  in
  Constrextern.set_extern_reference extern_ref;
  try
    let p = f env sigma c in
    Constrextern.set_extern_reference orig_extern_ref;
    Some p
  with e when CErrors.noncritical e ->
    Constrextern.set_extern_reference orig_extern_ref;
    None

let safe_gen f env sigma c = match safe_extern_wrapper f env sigma c with
| None -> str "??"
| Some v -> v

let safe_pr_lconstr_env ?flags = safe_gen (pr_lconstr_env ?flags)
let safe_pr_constr_env ?flags = safe_gen (pr_constr_env ?flags)

let q_ident = Id.of_string "α"

let u_ident = Id.of_string "u"

(** Replace the names in [uctx] with either:
    - the exact names in [user_names];
    - the existing names in [uctx], eventually freshened; or
    - fresh names generated from the default id *)
let fill_names ?user_names uctx =
  let open UVars in
  let { quals; univs } = AbstractContext.names uctx in
  let user_qnames, user_unames = match user_names with
  | None -> Array.map (fun _ -> Anonymous) quals, Array.map (fun _ -> Anonymous) univs
  | Some (gref, (qdecl, udecl)) ->
    let quals = Array.map_of_list (fun lname -> lname.CAst.v) qdecl in
    let univs = Array.map_of_list (fun lname -> lname.CAst.v) udecl in
    let user_size = Array.length quals, Array.length univs in
    if not (eq_sizes (AbstractContext.size uctx) user_size) then
      let open UnivGen in
      raise (UniverseLengthMismatch {
          gref;
          actual = AbstractContext.size uctx;
          expect = Array.length quals, Array.length univs;
        })
    else quals, univs
  in
  let add_id bounds = function Anonymous -> bounds | Name id -> Id.Set.add id bounds in
  let boundqs = Array.fold_left add_id Id.Set.empty user_qnames in
  let boundus = Array.fold_left add_id Id.Set.empty user_unames in
  let freshen_name bounds user_name name = match user_name, name with
  | Name id, _ -> bounds, Name id
  | Anonymous, Anonymous -> bounds, Anonymous
  | Anonymous, Name id ->
    let id = Namegen.next_ident_away_from id (fun id -> Id.Set.mem id bounds) in
    Id.Set.add id bounds, Name id
  in
  let boundqs, quals = Array.fold_left2_map freshen_name boundqs user_qnames quals in
  let boundus, univs = Array.fold_left2_map freshen_name boundus user_unames univs in
  let gen_name (uid, bounds as acc) = function
  | Name id -> acc, Name id
  | Anonymous ->
    let uid = Namegen.next_ident_away_from uid (fun id -> Id.Set.mem id bounds) in
    (uid, Id.Set.add uid bounds), Name uid
  in
  let _, quals = Array.fold_left_map gen_name (q_ident, boundqs) quals in
  let _, univs = Array.fold_left_map gen_name (u_ident, boundus) univs in
  AbstractContext.refine_names { quals; univs } uctx

let pr_sort_context_set sigma c =
  if !PrintingFlags.print_universes && not (UnivGen.is_empty_sort_context c) then
    let ctx = UnivGen.pr_sort_context (Evd.sort_printer sigma) c in
    fnl() ++ pr_in_comment (v 0 ctx)
  else
    mt()

let pr_universe_ctx sigma ?variance c =
  if !PrintingFlags.print_universes && not (UVars.UContext.is_empty c) then
    fnl()++
    pr_in_comment
      (v 0
         (UVars.UContext.pr (Evd.sort_printer sigma) ?variance c))
  else
    mt()

let pr_abstract_universe_ctx sigma ?variance ?priv c =
  let priv = Option.default Univ.ContextSet.empty priv in
  let has_priv = not (Univ.ContextSet.is_empty priv) in
  if !PrintingFlags.print_universes && (not (UVars.AbstractContext.is_empty c) || has_priv) then
    let prlev u = Termops.pr_evd_level sigma u in
    let pub = (if has_priv then str "Public universes:" ++ fnl() else mt()) ++ v 0 (UVars.AbstractContext.pr (Evd.sort_printer sigma) ?variance c) in
    let priv = if has_priv then fnl() ++ str "Private universes:" ++ fnl() ++ v 0 (Univ.ContextSet.pr prlev priv) else mt() in
    fnl()++pr_in_comment (pub ++ priv)
  else
    mt()

let pr_universes sigma ?variance ?priv = function
  | Declarations.Monomorphic -> mt ()
  | Declarations.Polymorphic ctx -> pr_abstract_universe_ctx sigma ?variance ?priv ctx

(**********************************************************************)
(* Global references *)

let pr_global_env = Nametab.pr_global_env
let pr_global = pr_global_env Id.Set.empty

let pr_abstract_universe_binder evd auctx =
  let open UVars in
  let printer = Evd.sort_printer evd in
  let uctx = AbstractContext.repr auctx in
  let pp =
    if UContext.is_empty uctx then mt()
    else if PConstraints.is_empty (UContext.constraints uctx) then
      h (Instance.pr printer (UContext.instance uctx))
    else
      h (Instance.pr printer (UContext.instance uctx) ++ str " | ") ++
      h (v 0 (PConstraints.pr printer (UContext.constraints uctx)))
  in
  str"@{" ++ pp ++ str"}"

let pr_universe_instance evd inst =
  str "@{" ++ UVars.Instance.pr (Evd.sort_printer evd) inst ++ str "}"

let pr_puniverses f env sigma (c,u) =
  if !PrintingFlags.print_universes
  then f env c ++ pr_universe_instance sigma u
  else f env c

let pr_existential_key = Termops.pr_existential_key
let pr_existential ?flags env sigma ev = pr_lconstr_env ?flags env sigma (mkEvar ev)

let pr_constant env cst = Termops.pr_global_env env (GlobRef.ConstRef cst)
let pr_inductive env ind = Termops.pr_global_env env (GlobRef.IndRef ind)
let pr_constructor env cstr = Termops.pr_global_env env (GlobRef.ConstructRef cstr)

let pr_pconstant = pr_puniverses pr_constant
let pr_pinductive = pr_puniverses pr_inductive
let pr_pconstructor = pr_puniverses pr_constructor

let pr_evaluable_reference env ref =
  pr_global (Tacred.global_of_evaluable_reference env ref)

(* XXX inline this in only caller in himsg? *)
let pr_notation_interpretation_env env sigma c =
  let flags = { (PrintingFlags.Extern.current()) with notations = false } in
  pr_glob_constr_env ~flags env sigma c

(*let pr_glob_constr t =
  pr_lconstr (Constrextern.extern_glob_constr Id.Set.empty t)*)

(*open Pattern

let pr_pattern t = pr_pattern_env (Global.env()) empty_names_context t*)

(**********************************************************************)
(* Contexts and declarations                                          *)


(* Flag for compact display of goals *)

let { Goptions.get = get_compact_context } =
  Goptions.declare_bool_option_and_ref ~key:["Printing";"Compact";"Contexts"] ~value:false ()

let { Goptions.get = print_var_status } =
  Goptions.declare_bool_option_and_ref ~key:["Printing";"Variables";"Status"] ~value:false ()

let pr_ecompacted_decl ?flags env sigma decl =
  let ids, pbody, typ = match decl with
    | CompactedDecl.LocalAssum (ids, typ) ->
      ids, None, typ
    | CompactedDecl.LocalDef (ids, c, typ) ->
      (* Force evaluation *)
      let pb = pr_leconstr_env ?flags ~inctx:true env sigma c in
      let pb = if EConstr.isCast sigma c then surround pb else pb in
      ids, Some pb, typ in
  let pp_status status =
    if print_var_status() then
      match status with
      | None -> mt()
      | Some SecVar -> spc() ++ pr_in_comment (str "section variable")
      | Some ProofVar -> spc() ++ pr_in_comment (str "hypothesis")
    else mt()
  in
  let pids =
    hov 0 (prlist_with_sep pr_comma (fun (status, id) -> pr_id id.binder_name ++ pp_status status) ids) in
  let pt = pr_letype_env ?flags env sigma typ in
  match pbody with
  | None -> hov 2 (pids ++ str" :" ++ spc () ++ pt)
  | Some pbody ->
    hov 2 (pids ++ str" :=" ++ spc () ++ pbody ++ spc () ++ str": " ++ pt)

let pr_enamed_decl ?flags env sigma status decl =
  decl |> CompactedDecl.of_named_decl status |> pr_ecompacted_decl ?flags env sigma

let pr_named_decl ?flags env sigma status (decl:Constr.named_declaration) =
  pr_enamed_decl ?flags env sigma status (EConstr.of_named_decl decl)

let pr_rel_decl ?flags env sigma decl =
  let na = RelDecl.get_name decl in
  let typ = RelDecl.get_type decl in
  let pbody = match decl with
    | RelDecl.LocalAssum _ -> mt ()
    | RelDecl.LocalDef (_,c,_) ->
        (* Force evaluation *)
        let pb = pr_lconstr_env ?flags ~inctx:true env sigma c in
        let pb = if isCast c then surround pb else pb in
        (str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = pr_ltype_env ?flags env sigma typ in
  match na with
  | Anonymous -> hov 2 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
  | Name id -> hov 2 (pr_id id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)

let pr_erel_decl ?flags env sigma (decl:EConstr.rel_declaration) =
  let Refl = EConstr.Unsafe.eq in
  pr_rel_decl ?flags env sigma decl



(* Prints out an "env" in a nice format.  We print out the
 * signature,then a horizontal bar, then the debruijn environment.
 * It's printed out from outermost to innermost, so it's readable. *)

(* Prints a signature, all declarations on the same line if possible *)

let pr_named_context ?flags env sigma ctx =
  hv 0 (prlist_with_sep (fun () -> ws 2) (fun d -> pr_named_decl ?flags env sigma None d) ctx)

let pr_named_context_of ?flags env sigma =
  let make_decl_list env status d pps = pr_named_decl ?flags env sigma (Some status) d :: pps in
  let psl = List.rev (fold_named_context make_decl_list env ~init:[]) in
  hv 0 (prlist_with_sep (fun _ -> ws 2) (fun x -> x) psl)

let pr_var_list_decl ?flags env sigma decl =
  hov 0 (pr_ecompacted_decl ?flags env sigma decl)

let pr_rel_context ?(flags=current_combined()) env sigma rel_context =
  let ppflags = Ppconstr.of_printing_flags flags in
  let rel_context = EConstr.of_rel_context rel_context in
  pr_binders ~flags:ppflags env sigma (extern_rel_context ~flags env sigma rel_context)

let pr_rel_context_of ?flags env sigma =
  pr_rel_context ?flags env sigma (rel_context env)

(* Prints an env (variables and de Bruijn). Separator: newline *)
let pr_context_unlimited ?flags env sigma =
  let sign_env =
    List.fold_right
      (fun d pps ->
         let pidt =  pr_ecompacted_decl ?flags env sigma d in
         (pps ++ fnl () ++ pidt))
      (compact_named_context sigma (Environ.named_context_val env)) (mt ())
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl ?flags env sigma d in (pps ++ fnl () ++ pnat))
      env ~init:(mt ())
  in
  (sign_env ++ db_env)

let pr_ne_context_of header ?flags env sigma =
  if List.is_empty (Environ.rel_context env) &&
    List.is_empty (Environ.named_context env)  then (mt ())
  else let penv = pr_context_unlimited ?flags env sigma in (header ++ penv ++ fnl ())

(* Heuristic for horizontalizing hypothesis that the user probably
   considers as "variables": An hypothesis H:T where T:S and S<>Prop. *)
let should_compact env sigma typ =
  get_compact_context() &&
    let type_of_typ = Retyping.get_type_of env sigma typ in
    not (Termops.is_Prop sigma type_of_typ)


(* If option Compact Contexts is set, we pack "simple" hypothesis in a
   hov box (with three sapaces as a separator), the global box being a
   v box *)
let rec bld_sign_env ?flags env sigma ctxt pps =
  match ctxt with
  | [] -> pps
  | CompactedDecl.LocalAssum (_,typ)::ctxt' when should_compact env sigma typ ->
    let pps',ctxt' = bld_sign_env_id ?flags env sigma ctxt (mt ()) true in
    (* putting simple hyps in a more horizontal flavor *)
    bld_sign_env ?flags env sigma ctxt' (pps ++ brk (0,0) ++ hov 0 pps')
  | d:: ctxt' ->
    let pidt = pr_var_list_decl ?flags env sigma d in
    let pps' = pps ++ brk (0,0) ++ pidt in
    bld_sign_env ?flags env sigma ctxt' pps'
and bld_sign_env_id ?flags env sigma ctxt pps is_start =
  match ctxt with
  | [] -> pps,ctxt
 | CompactedDecl.LocalAssum(_,typ) as d :: ctxt' when should_compact env sigma typ ->
    let pidt = pr_var_list_decl ?flags env sigma d in
    let pps' = pps ++ (if not is_start then brk (3,0) else (mt ())) ++ pidt in
    bld_sign_env_id ?flags env sigma ctxt' pps' false
  | _ -> pps,ctxt


(* compact printing an env (variables and de Bruijn). Separator: three
   spaces between simple hyps, and newline otherwise *)
let pr_context_limit_compact ?n ?flags env sigma =
  let ctxt = Environ.named_context_val env in
  let ctxt = compact_named_context sigma ctxt in
  let lgth = List.length ctxt in
  let n_capped =
    match n with
    | None -> lgth
    | Some n when n > lgth -> lgth
    | Some n -> n in
  let ctxt_chopped,ctxt_hidden = Util.List.chop n_capped ctxt in
  (* a dot line hinting the number of hidden hyps. *)
  let hidden_dots = String.make (List.length ctxt_hidden) '.' in
  let sign_env = v 0 (str hidden_dots ++ (mt ())
                 ++ bld_sign_env ?flags env sigma (List.rev ctxt_chopped) (mt ())) in
  let db_env =
    fold_rel_context (fun env d pps -> pps ++ fnl () ++ pr_rel_decl ?flags env sigma d)
      env ~init:(mt ()) in
  sign_env ++ db_env

(* The number of printed hypothesis in a goal *)
(* If [None], no limit *)
let { Goptions.get = print_hyps_limit } =
  Goptions.declare_intopt_option_and_ref
    ~key:["Hyps";"Limit"]
    ~value:None
    ()

let pr_context_of ?flags env sigma =
  let n = print_hyps_limit () in
  hv 0 (pr_context_limit_compact ?n ?flags env sigma)

(* display goal parts (Proof mode) *)

let pr_predicate pr_elt (b, elts) =
  let pr_elts = prlist_with_sep spc pr_elt elts in
    if b then
      str"all" ++
        (if List.is_empty elts then mt () else str" except: " ++ pr_elts)
    else
      if List.is_empty elts then str"none" else pr_elts

let pr_cpred p =
  let safe_pr_constant env kn =
    try pr_constant env kn
    with Not_found when !Flags.in_debugger || !Flags.in_ml_toplevel ->
      Names.Constant.print kn in
  pr_predicate (safe_pr_constant (Global.env())) (Cpred.elements p)

let pr_idpred p = pr_predicate Id.print (Id.Pred.elements p)

let pr_prpred p = pr_predicate Projection.Repr.print (PRpred.elements p)

let pr_transparent_state ts =
  hv 0 (str"VARIABLES: " ++ pr_idpred ts.TransparentState.tr_var ++ fnl () ++
        str"CONSTANTS: " ++ pr_cpred ts.TransparentState.tr_cst ++ fnl () ++
        str"PROJECTIONS: " ++ pr_prpred ts.TransparentState.tr_prj ++ fnl ())

(* display evar type: a context and a type *)
let pr_evgl_sign ?(flags=current_combined()) env sigma (evi : undefined evar_info) =
  let env = evar_env env evi in
  let ps = pr_named_context_of ~flags env sigma in
  let _, l = match Filter.repr (evar_filter evi) with
  | None -> [], []
  | Some f -> List.filter2 (fun b c -> not b) f (evar_context evi)
  in
  let ids = List.rev_map NamedDecl.get_id l in
  let warn =
    if List.is_empty ids then mt () else
      (str " (" ++ prlist_with_sep pr_comma pr_id ids ++ str " cannot be used)")
  in
  let concl = Evd.evar_concl evi in
  let pc = pr_leconstr_env ~flags env sigma concl in
  let candidates =
    begin match Evd.evar_candidates evi with
    | None -> mt ()
    | Some l ->
      spc () ++ str "= {" ++
      prlist_with_sep (fun () -> str "|") (pr_leconstr_env ~flags env sigma) l ++ str "}"
    end
  in
  hov 0 (str"[" ++ ps ++ spc () ++ str"|- "  ++ pc ++ str"]" ++
           candidates ++ warn)

(* Print an existential variable *)

let pr_evar ?(flags=current_combined()) sigma (evk, evi) =
  let env = Global.env () in
  let pegl = pr_evgl_sign ~flags env sigma evi in
  hov 2 (pr_existential_key env sigma evk ++ str " :" ++ spc () ++ pegl)

(* Print an enumerated list of existential variables *)
let rec pr_evars_int_hd pr sigma i = function
  | [] -> mt ()
  | (evk,evi)::rest ->
      (hov 0 (pr i evk evi)) ++
      (match rest with [] -> mt () | _ -> fnl () ++ pr_evars_int_hd pr sigma (i+1) rest)

let pr_evars_int ?(flags=current_combined()) sigma ~shelf ~given_up i evs =
  let pr_status i =
    let status =
      if List.mem i shelf then [str "shelved"]
      else if List.mem i given_up then [str "given up"]
      else [] in
    (* Check whether the evar has an unfocusable name *)
    let status =
      if not (Evd.evar_has_unambiguous_name i sigma)  then str "only printing" :: status
      else status
    in
    begin match status with
    | [] -> mt ()
    | s :: [] -> str " (" ++ s ++ str ")"
    | s1 :: s2 :: _ -> str " (" ++ s2 ++ str "; " ++ s1 ++ str ")"
    end in
  pr_evars_int_hd
    (fun i evk evi ->
      str "Existential " ++ int i ++ str " =" ++
      spc () ++ pr_evar ~flags sigma (evk,evi) ++ pr_status evk)
    sigma i (Evar.Map.bindings evs)

let pr_evars ?(flags=current_combined()) sigma evs =
  pr_evars_int_hd (fun i evk evi -> pr_evar ~flags sigma (evk,evi)) sigma 1 (Evar.Map.bindings evs)

(* Display a list of evars given by their name, with a prefix *)
let pr_ne_evar_set ?(flags=current_combined()) hd tl sigma l =
  if l != Evar.Set.empty then
    let l = Evar.Map.bind (fun ev ->
        let evi = Evd.find_undefined sigma ev in
        Evarutil.nf_evar_info sigma evi)
        l
    in
    hd ++ pr_evars ~flags sigma l ++ tl
  else
    mt ()

(* Printer function for sets of Assumptions.assumptions.
   It is used primarily by the Print Assumptions command. *)

let { Goptions.get = print_all_assumptions } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"All";"Assumptions"]
    ~value:false
    ()

type axiom =
  | Constant of Constant.t
  | Positive of MutInd.t
  | Guarded of GlobRef.t
  | TypeInType of GlobRef.t
  | UIP of MutInd.t
  | IndicesNotMattering of MutInd.t

type context_object =
  | Variable of Id.t (* A section variable or a Let definition *)
  | Axiom of axiom * (GlobRef.t * Constr.rel_context * types) list
  | Opaque of Constant.t     (* An opaque constant. *)
  | Transparent of Constant.t

(* Defines a set of [assumption] *)
module OrderedContextObject =
struct
  type t = context_object

  let compare_axiom x y =
    match x,y with
    | Constant k1 , Constant k2 ->
      Constant.UserOrd.compare k1 k2
    | Positive m1 , Positive m2
    | UIP m1, UIP m2
    | IndicesNotMattering m1, IndicesNotMattering m2 ->
      MutInd.UserOrd.compare m1 m2
    | Guarded k1 , Guarded k2
    | TypeInType k1, TypeInType k2 ->
      GlobRef.UserOrd.compare k1 k2
    | Constant _, _ -> -1
    | _, Constant _ -> 1
    | Positive _, _ -> -1
    | _, Positive _ -> 1
    | Guarded _, _ -> -1
    | _, Guarded _ -> 1
    | TypeInType _, _ -> -1
    | _, TypeInType _ -> 1
    | UIP _, _ -> -1
    | _, UIP _ -> 1

  let compare x y =
    match x , y with
    | Variable i1 , Variable i2 -> Id.compare i1 i2
    | Variable _ , _ -> -1
    | _ , Variable _ -> 1
    | Axiom (k1,_) , Axiom (k2, _) -> compare_axiom k1 k2
    | Axiom _ , _ -> -1
    | _ , Axiom _ -> 1
    | Opaque k1 , Opaque k2 -> Constant.UserOrd.compare k1 k2
    | Opaque _ , _ -> -1
    | _ , Opaque _ -> 1
    | Transparent k1 , Transparent k2 -> Constant.UserOrd.compare k1 k2
end

module ContextObjectSet = Set.Make (OrderedContextObject)
module ContextObjectMap = Map.Make (OrderedContextObject)

type theory_assumptions = {
  has_impredicative_set : bool;
  has_rewrite_rules : bool;
  has_type_in_type : bool;
}

let pr_assumptionset ?(flags=current_combined()) env sigma theory_info s =
  let print_all = print_all_assumptions () in
  let dominated_by_env ax =
    match ax with
    | IndicesNotMattering _ -> not print_all && not (indices_matter env)
    | _ -> false
  in
  let s = ContextObjectMap.filter (fun k _v -> match k with
    | Axiom (ax, _) -> not (dominated_by_env ax)
    | _ -> true) s
  in
  let show_theory_impredicative_set = (print_all && theory_info.has_impredicative_set) || is_impredicative_set env in
  let show_theory_rewrite_rules = (print_all && theory_info.has_rewrite_rules) || rewrite_rules_allowed env in
  let show_theory_type_in_type = (print_all && theory_info.has_type_in_type) || type_in_type env in
  if ContextObjectMap.is_empty s &&
       not show_theory_rewrite_rules &&
       not show_theory_impredicative_set then
    str "Closed under the global context"
  else
    let safe_pr_constant env kn =
      try pr_constant env kn
      with Not_found ->
        Names.Constant.print kn
    in
    let safe_pr_global env gr =
      try Termops.pr_global_env env gr
      with Not_found ->
        let open GlobRef in match gr with
        | VarRef id -> Id.print id
        | ConstRef con -> Constant.print con
        | IndRef (mind,_) -> MutInd.print mind
        | ConstructRef _ -> assert false
    in
    let safe_pr_inductive env kn =
      try pr_inductive env (kn,0)
      with Not_found ->
        MutInd.print kn
    in
    let safe_pr_ltype env sigma typ =
      try str " :" ++ spc () ++ pr_ltype_env ~flags env sigma typ
      with e when CErrors.noncritical e -> mt ()
    in
    let safe_pr_ltype_relctx (rctx, typ) =
      let env = Environ.push_rel_context rctx env in
      try str " " ++ pr_ltype_env ~flags env sigma typ
      with e when CErrors.noncritical e -> mt ()
    in
    let pr_axiom env ax typ =
      match ax with
      | Constant kn ->
          hov 2 (safe_pr_constant env kn ++ safe_pr_ltype env sigma typ)
      | Positive m ->
          hov 2 (safe_pr_inductive env m ++ spc () ++ strbrk"is assumed to be positive.")
      | Guarded gr ->
          hov 2 (safe_pr_global env gr ++ spc () ++ strbrk"is assumed to be guarded.")
      | TypeInType gr ->
          hov 2 (safe_pr_global env gr ++ spc () ++ strbrk"relies on an unsafe hierarchy.")
      | UIP mind ->
          hov 2 (safe_pr_inductive env mind ++ spc () ++ strbrk"relies on definitional UIP.")
      | IndicesNotMattering mind ->
          hov 2 (safe_pr_inductive env mind ++ spc () ++ strbrk"relies on indices not mattering.")
    in
    let fold t typ accu =
      let (v, a, o, tr) = accu in
      match t with
      | Variable id ->
        let var = pr_id id ++ spc() ++ str ": " ++ pr_ltype_env ~flags env sigma typ in
        (var :: v, a, o, tr)
      | Axiom (axiom, []) ->
        let ax = pr_axiom env axiom typ in
        (v, ax :: a, o, tr)
      | Axiom (axiom,l) ->
        let ax = pr_axiom env axiom typ ++
          spc() ++
          prlist_with_sep cut (fun (gr, ctx, ty) ->
            let lab = let open GlobRef in match gr with
              | ConstRef kn -> Constant.label kn
              | IndRef (kn,_)
              | ConstructRef ((kn,_),_) -> MutInd.label kn
              | VarRef id -> id
            in
            str "used in " ++ Id.print lab ++
            str " to prove" ++ fnl() ++ safe_pr_ltype_relctx (ctx,ty))
          l in
        (v, ax :: a, o, tr)
      | Opaque kn ->
        let opq = safe_pr_constant env kn ++ safe_pr_ltype env sigma typ in
        (v, a, opq :: o, tr)
      | Transparent kn ->
        let tran = safe_pr_constant env kn ++ safe_pr_ltype env sigma typ in
        (v, a, o, tran :: tr)
    in
    let (vars, axioms, opaque, trans) =
      ContextObjectMap.fold fold s ([], [], [], [])
    in
    let theory =
      if show_theory_impredicative_set then
        [str "Set is impredicative"]
      else []
    in
    let theory =
      if show_theory_rewrite_rules then
        str "Rewrite rules are allowed (subject reduction might be broken)" :: theory
      else theory
    in
    let theory =
      if show_theory_type_in_type then
        str "Type hierarchy is collapsed (logic is inconsistent)" :: theory
      else theory
    in
    let opt_list title = function
    | [] -> None
    | l ->
      let section =
        title ++ fnl () ++
        v 0 (prlist_with_sep fnl (fun s -> s) l) in
      Some section
    in
    let assums = [
      opt_list (str "Transparent constants:") trans;
      opt_list (str "Section Variables:") vars;
      opt_list (str "Axioms:") axioms;
      opt_list (str "Opaque constants:") opaque;
      opt_list (str "Theory:") theory;
    ] in
    prlist_with_sep fnl (fun x -> x) (Option.List.flatten assums)

let pr_typing_flags flags =
  str "check_guarded: " ++ bool flags.check_guarded ++ fnl ()
  ++ str "check_positive: " ++ bool flags.check_positive ++ fnl ()
  ++ str "check_universes: " ++ bool flags.check_universes ++ fnl ()
  ++ str "definitional uip: " ++ bool flags.allow_uip

module Debug =
struct

let goal_repr sigma g =
  let EvarInfo evi = Evd.find sigma g in
  let env = Evd.evar_filtered_env (Global.env ()) evi in
  let concl = match Evd.evar_body evi with
  | Evd.Evar_empty -> Evd.evar_concl evi
  | Evd.Evar_defined b -> Retyping.get_type_of env sigma b
  in
  env, concl

let pr_goal ?(flags=current_combined()) gl =
  let sigma = Proofview.Goal.sigma gl in
  let g = Proofview.Goal.goal gl in
  let env, concl = goal_repr sigma g in
  let goal =
    pr_context_of ~flags env sigma ++ cut () ++
      str "============================" ++ cut ()  ++
      hov 0 (pr_letype_env ~goal_concl_style:true ~flags env sigma concl)
  in
  str "  " ++ v 0 goal

end
