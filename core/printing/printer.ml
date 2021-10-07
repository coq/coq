(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
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
module CompactedDecl = Context.Compacted.Declaration

(* This is set on by proofgeneral proof-tree mode. But may be used for
   other purposes *)
let print_goal_tag_opt_name = ["Printing";"Goal";"Tags"]
let should_tag =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:print_goal_tag_opt_name
    ~value:false

let should_unfoc =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Unfocused"]
    ~value:false

let should_gname =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Goal";"Names"]
    ~value:false

let print_goal_names = should_gname (* for export *)

(**********************************************************************)
(** Terms                                                             *)

(* [goal_concl_style] means that all names of goal/section variables
   and all names of rel variables (if any) in the given env and all short
   names of global definitions of the current module must be avoided while
   printing bound variables.
   Otherwise, short names of global definitions are printed qualified
   and only names of goal/section variables and rel names that do
   _not_ occur in the scope of the binder to be printed are avoided. *)

let pr_econstr_n_env ?lax ?inctx ?scope env sigma n t =
  pr_constr_expr_n env sigma n (extern_constr ?lax ?inctx ?scope env sigma t)
let pr_econstr_env ?lax ?inctx ?scope env sigma t =
  pr_constr_expr env sigma (extern_constr ?lax ?inctx ?scope env sigma t)
let pr_leconstr_env = Proof_diffs.pr_leconstr_env

let pr_constr_n_env ?lax ?inctx ?scope env sigma n c =
  pr_econstr_n_env ?lax ?inctx ?scope env sigma n (EConstr.of_constr c)
let pr_constr_env ?lax ?inctx ?scope env sigma c =
  pr_econstr_env ?lax ?inctx ?scope env sigma (EConstr.of_constr c)
let pr_lconstr_env = Proof_diffs.pr_lconstr_env

let pr_open_lconstr_env ?lax ?inctx ?scope env sigma (_,c) =
  pr_leconstr_env ?lax ?inctx ?scope env sigma c
let pr_open_constr_env ?lax ?inctx ?scope env sigma (_,c) =
  pr_econstr_env ?lax ?inctx ?scope env sigma c

let pr_constr_under_binders_env_gen pr env sigma (ids,c) =
  (* Warning: clashes can occur with variables of same name in env but *)
  (* we also need to preserve the actual names of the patterns *)
  (* So what to do? *)
  let assums = List.map (fun id -> (make_annot (Name id) Sorts.Relevant,(* dummy *) mkProp)) ids in
  pr (Termops.push_rels_assum assums env) sigma c

let pr_constr_under_binders_env = pr_constr_under_binders_env_gen pr_econstr_env
let pr_lconstr_under_binders_env = pr_constr_under_binders_env_gen pr_leconstr_env

let pr_etype_env ?lax ?goal_concl_style env sigma t =
  pr_constr_expr env sigma (extern_type ?lax ?goal_concl_style env sigma t)
let pr_letype_env = Proof_diffs.pr_letype_env

let pr_type_env ?lax ?goal_concl_style env sigma c =
  pr_etype_env ?lax ?goal_concl_style env sigma (EConstr.of_constr c)
let pr_ltype_env ?lax ?goal_concl_style env sigma ?impargs c =
  pr_letype_env ?lax ?goal_concl_style env sigma ?impargs (EConstr.of_constr c)

let pr_ljudge_env env sigma j =
  (pr_leconstr_env env sigma j.uj_val, pr_leconstr_env env sigma j.uj_type)

let pr_lglob_constr_env env sigma c =
  pr_lconstr_expr env sigma (extern_glob_constr (extern_env env sigma) c)
let pr_glob_constr_env env sigma c =
  pr_constr_expr env sigma (extern_glob_constr (extern_env env sigma) c)

let pr_closed_glob_n_env ?lax ?goal_concl_style ?inctx ?scope env sigma n c =
  pr_constr_expr_n env sigma n (extern_closed_glob ?lax ?goal_concl_style ?inctx ?scope env sigma c)
let pr_closed_glob_env ?lax ?goal_concl_style ?inctx ?scope env sigma c =
  pr_constr_expr env sigma (extern_closed_glob ?lax ?goal_concl_style ?inctx ?scope env sigma c)

let pr_lconstr_pattern_env env sigma c =
  pr_lconstr_pattern_expr env sigma (extern_constr_pattern (Termops.names_of_rel_context env) sigma c)
let pr_constr_pattern_env env sigma c =
  pr_constr_pattern_expr env sigma (extern_constr_pattern (Termops.names_of_rel_context env) sigma c)

let pr_cases_pattern t =
  pr_cases_pattern_expr (extern_cases_pattern Names.Id.Set.empty t)

let pr_sort sigma s = pr_sort_expr (extern_sort sigma s)

let () = Termops.Internal.set_print_constr
  (fun env sigma t -> pr_lconstr_expr env sigma (extern_constr ~lax:true env sigma t))

let pr_in_comment x = str "(* " ++ x ++ str " *)"

(** Term printers resilient to [Nametab] errors *)

(** When the nametab isn't up-to-date, the term printers above
    could raise [Not_found] during [Nametab.shortest_qualid_of_global].
    In this case, we build here a fully-qualified name based upon
    the kernel modpath and label of constants, and the idents in
    the [mutual_inductive_body] for the inductives and constructors
    (needs an environment for this). *)

let id_of_global env = let open GlobRef in function
  | ConstRef kn -> Label.to_id (Constant.label kn)
  | IndRef (kn,0) -> Label.to_id (MutInd.label kn)
  | IndRef (kn,i) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_typename
  | ConstructRef ((kn,i),j) ->
    (Environ.lookup_mind kn env).mind_packets.(i).mind_consnames.(j-1)
  | VarRef v -> v

let rec dirpath_of_mp = function
  | MPfile sl -> sl
  | MPbound uid -> DirPath.make [MBId.to_id uid]
  | MPdot (mp,l) ->
    Libnames.add_dirpath_suffix (dirpath_of_mp mp) (Label.to_id l)

let dirpath_of_global = let open GlobRef in function
  | ConstRef kn -> dirpath_of_mp (Constant.modpath kn)
  | IndRef (kn,_) | ConstructRef ((kn,_),_) ->
    dirpath_of_mp (MutInd.modpath kn)
  | VarRef _ -> DirPath.empty

let qualid_of_global ?loc env r =
  Libnames.make_qualid ?loc (dirpath_of_global r) (id_of_global env r)

let safe_gen f env sigma c =
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
    p
  with e when CErrors.noncritical e ->
    Constrextern.set_extern_reference orig_extern_ref;
    str "??"

let safe_pr_lconstr_env = safe_gen pr_lconstr_env
let safe_pr_constr_env = safe_gen pr_constr_env

let u_ident = Id.of_string "u"

let universe_binders_with_opt_names orig names =
  let orig = Univ.AbstractContext.names orig in
  let orig = Array.to_list orig in
  let udecl = match names with
  | None -> orig
  | Some udecl ->
    try
      List.map2 (fun orig {CAst.v = na} ->
          match na with
          | Anonymous -> orig
          | Name id -> Name id) orig udecl
    with Invalid_argument _ ->
      let len = List.length orig in
      CErrors.user_err ~hdr:"universe_binders_with_opt_names"
        Pp.(str "Universe instance should have length " ++ int len)
  in
  let fold_named i ubind = function
    | Name id -> Id.Map.add id (Univ.Level.var i) ubind
    | Anonymous -> ubind
  in
  let ubind = List.fold_left_i fold_named 0 UnivNames.empty_binders udecl in
  let fold_anons i (u_ident, ubind) = function
    | Name _ -> u_ident, ubind
    | Anonymous ->
      let id = Namegen.next_ident_away_from u_ident (fun id -> Id.Map.mem id ubind) in
      (id, Id.Map.add id (Univ.Level.var i) ubind)
  in
  let (_, ubind) = List.fold_left_i fold_anons 0 (u_ident, ubind) udecl in
  ubind

let pr_universe_ctx_set sigma c =
  if !Detyping.print_universes && not (Univ.ContextSet.is_empty c) then
    fnl()++pr_in_comment (v 0 (Univ.pr_universe_context_set (Termops.pr_evd_level sigma) c))
  else
    mt()

let pr_universe_ctx sigma ?variance c =
  if !Detyping.print_universes && not (Univ.UContext.is_empty c) then
    fnl()++pr_in_comment (v 0 (Univ.pr_universe_context (Termops.pr_evd_level sigma) ?variance c))
  else
    mt()

let pr_abstract_universe_ctx sigma ?variance ?priv c =
  let open Univ in
  let priv = Option.default Univ.ContextSet.empty priv in
  let has_priv = not (ContextSet.is_empty priv) in
  if !Detyping.print_universes && (not (Univ.AbstractContext.is_empty c) || has_priv) then
    let prlev u = Termops.pr_evd_level sigma u in
    let pub = (if has_priv then str "Public universes:" ++ fnl() else mt()) ++ v 0 (Univ.pr_abstract_universe_context prlev ?variance c) in
    let priv = if has_priv then fnl() ++ str "Private universes:" ++ fnl() ++ v 0 (Univ.pr_universe_context_set prlev priv) else mt() in
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

let pr_universe_instance_constraints evd inst csts =
  let open Univ in
  let prlev = Termops.pr_evd_level evd in
  let pcsts = if Constraints.is_empty csts then mt()
    else str " |= " ++
         prlist_with_sep (fun () -> str "," ++ spc())
           (fun (u,d,v) -> hov 0 (prlev u ++ pr_constraint_type d ++ prlev v))
           (Constraints.elements csts)
  in
  str"@{" ++ Instance.pr prlev inst ++ pcsts ++ str"}"

let pr_universe_instance evd inst =
  pr_universe_instance_constraints evd inst Univ.Constraints.empty

let pr_puniverses f env sigma (c,u) =
  if !Constrextern.print_universes
  then f env c ++ pr_universe_instance sigma u
  else f env c

let pr_existential_key = Termops.pr_existential_key
let pr_existential env sigma ev = pr_lconstr_env env sigma (mkEvar ev)

let pr_constant env cst = pr_global_env (Termops.vars_of_env env) (GlobRef.ConstRef cst)
let pr_inductive env ind = pr_global_env (Termops.vars_of_env env) (GlobRef.IndRef ind)
let pr_constructor env cstr = pr_global_env (Termops.vars_of_env env) (GlobRef.ConstructRef cstr)

let pr_pconstant = pr_puniverses pr_constant
let pr_pinductive = pr_puniverses pr_inductive
let pr_pconstructor = pr_puniverses pr_constructor

let pr_evaluable_reference ref =
  pr_global (Tacred.global_of_evaluable_reference ref)

(*let pr_glob_constr t =
  pr_lconstr (Constrextern.extern_glob_constr Id.Set.empty t)*)

(*open Pattern

let pr_pattern t = pr_pattern_env (Global.env()) empty_names_context t*)

(**********************************************************************)
(* Contexts and declarations                                          *)


(* Flag for compact display of goals *)

let get_compact_context,set_compact_context =
  let compact_context = ref false in
  (fun () -> !compact_context),(fun b  -> compact_context := b)

let pr_compacted_decl env sigma decl =
  let ids, pbody, typ = match decl with
    | CompactedDecl.LocalAssum (ids, typ) ->
       ids, mt (), typ
    | CompactedDecl.LocalDef (ids,c,typ) ->
       (* Force evaluation *)
       let pb = pr_lconstr_env ~inctx:true env sigma c in
       let pb = if isCast c then surround pb else pb in
       ids, (str" := " ++ pb ++ cut ()), typ
  in
  let pids = prlist_with_sep pr_comma (fun id -> pr_id id.binder_name) ids in
  let pt = pr_ltype_env env sigma typ in
  let ptyp = (str" : " ++ pt) in
  hov 0 (pids ++ pbody ++ ptyp)

let pr_named_decl env sigma decl =
  decl |> CompactedDecl.of_named_decl |> pr_compacted_decl env sigma

let pr_rel_decl env sigma decl =
  let na = RelDecl.get_name decl in
  let typ = RelDecl.get_type decl in
  let pbody = match decl with
    | RelDecl.LocalAssum _ -> mt ()
    | RelDecl.LocalDef (_,c,_) ->
        (* Force evaluation *)
        let pb = pr_lconstr_env ~inctx:true env sigma c in
        let pb = if isCast c then surround pb else pb in
        (str":=" ++ spc () ++ pb ++ spc ()) in
  let ptyp = pr_ltype_env env sigma typ in
  match na with
  | Anonymous -> hov 0 (str"<>" ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)
  | Name id -> hov 0 (pr_id id ++ spc () ++ pbody ++ str":" ++ spc () ++ ptyp)


(* Prints out an "env" in a nice format.  We print out the
 * signature,then a horizontal bar, then the debruijn environment.
 * It's printed out from outermost to innermost, so it's readable. *)

(* Prints a signature, all declarations on the same line if possible *)
let pr_named_context_of env sigma =
  let make_decl_list env d pps = pr_named_decl env sigma d :: pps in
  let psl = List.rev (fold_named_context make_decl_list env ~init:[]) in
  hv 0 (prlist_with_sep (fun _ -> ws 2) (fun x -> x) psl)

let pr_var_list_decl env sigma decl =
  hov 0 (pr_compacted_decl env sigma decl)

let pr_named_context env sigma ne_context =
  hv 0 (Context.Named.fold_outside
          (fun d pps -> pps ++ ws 2 ++ pr_named_decl env sigma d)
          ne_context ~init:(mt ()))

let pr_rel_context env sigma rel_context =
  let rel_context = List.map (fun d -> Termops.map_rel_decl EConstr.of_constr d) rel_context in
  pr_binders env sigma (extern_rel_context None env sigma rel_context)

let pr_rel_context_of env sigma =
  pr_rel_context env sigma (rel_context env)

(* Prints an env (variables and de Bruijn). Separator: newline *)
let pr_context_unlimited env sigma =
  let sign_env =
    Context.Compacted.fold
      (fun d pps ->
         let pidt =  pr_compacted_decl env sigma d in
         (pps ++ fnl () ++ pidt))
      (Termops.compact_named_context (named_context env)) ~init:(mt ())
  in
  let db_env =
    fold_rel_context
      (fun env d pps ->
         let pnat = pr_rel_decl env sigma d in (pps ++ fnl () ++ pnat))
      env ~init:(mt ())
  in
  (sign_env ++ db_env)

let pr_ne_context_of header env sigma =
  if List.is_empty (Environ.rel_context env) &&
    List.is_empty (Environ.named_context env)  then (mt ())
  else let penv = pr_context_unlimited env sigma in (header ++ penv ++ fnl ())

(* Heuristic for horizontalizing hypothesis that the user probably
   considers as "variables": An hypothesis H:T where T:S and S<>Prop. *)
let should_compact env sigma typ =
  get_compact_context() &&
    let type_of_typ = Retyping.get_type_of env sigma (EConstr.of_constr typ) in
    not (is_Prop (EConstr.to_constr sigma type_of_typ))


(* If option Compact Contexts is set, we pack "simple" hypothesis in a
   hov box (with three sapaces as a separator), the global box being a
   v box *)
let rec bld_sign_env env sigma ctxt pps =
  match ctxt with
  | [] -> pps
  | CompactedDecl.LocalAssum (ids,typ)::ctxt' when should_compact env sigma typ ->
    let pps',ctxt' = bld_sign_env_id env sigma ctxt (mt ()) true in
    (* putting simple hyps in a more horizontal flavor *)
    bld_sign_env env sigma ctxt' (pps ++ brk (0,0) ++ hov 0 pps')
  | d:: ctxt' ->
    let pidt = pr_var_list_decl env sigma d in
    let pps' = pps ++ brk (0,0) ++ pidt in
    bld_sign_env env sigma ctxt' pps'
and bld_sign_env_id env sigma ctxt pps is_start =
  match ctxt with
  | [] -> pps,ctxt
 | CompactedDecl.LocalAssum(ids,typ) as d :: ctxt' when should_compact env sigma typ ->
    let pidt = pr_var_list_decl env sigma d in
    let pps' = pps ++ (if not is_start then brk (3,0) else (mt ())) ++ pidt in
    bld_sign_env_id env sigma ctxt' pps' false
  | _ -> pps,ctxt


(* compact printing an env (variables and de Bruijn). Separator: three
   spaces between simple hyps, and newline otherwise *)
let pr_context_limit_compact ?n env sigma =
  let ctxt = Termops.compact_named_context (named_context env) in
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
                 ++ bld_sign_env env sigma (List.rev ctxt_chopped) (mt ())) in
  let db_env =
    fold_rel_context (fun env d pps -> pps ++ fnl () ++ pr_rel_decl env sigma d)
      env ~init:(mt ()) in
  sign_env ++ db_env

(* The number of printed hypothesis in a goal *)
(* If [None], no limit *)
let print_hyps_limit =
  Goptions.declare_intopt_option_and_ref ~depr:false ~key:["Hyps";"Limit"]

let pr_context_of env sigma = match print_hyps_limit () with
  | None -> hv 0 (pr_context_limit_compact env sigma)
  | Some n -> hv 0 (pr_context_limit_compact ~n env sigma)

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
    with Not_found when !Flags.in_debugger || !Flags.in_toplevel ->
      Names.Constant.print kn in
  pr_predicate (safe_pr_constant (Global.env())) (Cpred.elements p)

let pr_idpred p = pr_predicate Id.print (Id.Pred.elements p)

let pr_transparent_state ts =
  hv 0 (str"VARIABLES: " ++ pr_idpred ts.TransparentState.tr_var ++ fnl () ++
        str"CONSTANTS: " ++ pr_cpred ts.TransparentState.tr_cst ++ fnl ())

(* display complete goal
 og_s has goal+sigma on the previous proof step for diffs
 g_s has goal+sigma on the current proof step
 *)
let pr_goal ?(diffs=false) ?og_s g_s =
  let g = sig_it g_s in
  let sigma = Tacmach.project g_s in
  let env = Goal.V82.env sigma g in
  let concl = Goal.V82.concl sigma g in
  let goal =
    if diffs then
      Proof_diffs.diff_goal ?og_s g sigma
    else
      pr_context_of env sigma ++ cut () ++
        str "============================" ++ cut ()  ++
        hov 0 (pr_letype_env ~goal_concl_style:true env sigma concl)
  in
  str "  " ++ v 0 goal

(* display a goal tag *)
let pr_goal_tag g =
  let s = " (ID " ^ Goal.uid g ^ ")" in
  str s

(* display a goal name *)
let pr_goal_name sigma g =
  if should_gname() then str " " ++ Pp.surround (pr_existential_key sigma g)
  else mt ()

let pr_goal_header nme sigma g =
  let (g,sigma) = Goal.V82.nf_evar sigma g in
  str "goal " ++ nme ++ (if should_tag() then pr_goal_tag g else str"")
  ++ (if should_gname() then str " " ++ Pp.surround (pr_existential_key sigma g) else mt ())

(* display the conclusion of a goal *)
let pr_concl n ?(diffs=false) ?og_s sigma g =
  let (g,sigma) = Goal.V82.nf_evar sigma g in
  let env = Goal.V82.env sigma g in
  let pc =
    if diffs then
      Proof_diffs.diff_concl ?og_s sigma g
    else
      pr_letype_env ~goal_concl_style:true env sigma (Goal.V82.concl sigma g)
  in
  let header = pr_goal_header (int n) sigma g in
  header ++ str " is:" ++ cut () ++ str" "  ++ pc

(* display evar type: a context and a type *)
let pr_evgl_sign env sigma evi =
  let env = evar_env env evi in
  let ps = pr_named_context_of env sigma in
  let _, l = match Filter.repr (evar_filter evi) with
  | None -> [], []
  | Some f -> List.filter2 (fun b c -> not b) f (evar_context evi)
  in
  let ids = List.rev_map NamedDecl.get_id l in
  let warn =
    if List.is_empty ids then mt () else
      (str " (" ++ prlist_with_sep pr_comma pr_id ids ++ str " cannot be used)")
  in
  let pc = pr_leconstr_env env sigma evi.evar_concl in
  let candidates =
    match evi.evar_body, evi.evar_candidates with
    | Evar_empty, Some l ->
       spc () ++ str "= {" ++
         prlist_with_sep (fun () -> str "|") (pr_leconstr_env env sigma) l ++ str "}"
    | _ ->
       mt ()
  in
  hov 0 (str"[" ++ ps ++ spc () ++ str"|- "  ++ pc ++ str"]" ++
           candidates ++ warn)

(* Print an existential variable *)

let pr_evar sigma (evk, evi) =
  let env = Global.env () in
  let pegl = pr_evgl_sign env sigma evi in
  hov 0 (pr_existential_key sigma evk ++ str " : " ++ pegl)

(* Print an enumerated list of existential variables *)
let rec pr_evars_int_hd pr sigma i = function
  | [] -> mt ()
  | (evk,evi)::rest ->
      (hov 0 (pr i evk evi)) ++
      (match rest with [] -> mt () | _ -> fnl () ++ pr_evars_int_hd pr sigma (i+1) rest)

let pr_evars_int sigma ~shelf ~given_up i evs =
  let pr_status i =
    if List.mem i shelf then str " (shelved)"
    else if List.mem i given_up then str " (given up)"
    else mt () in
  pr_evars_int_hd
    (fun i evk evi ->
      str "Existential " ++ int i ++ str " =" ++
      spc () ++ pr_evar sigma (evk,evi) ++ pr_status evk)
    sigma i (Evar.Map.bindings evs)

let pr_evars sigma evs =
  pr_evars_int_hd (fun i evk evi -> pr_evar sigma (evk,evi)) sigma 1 (Evar.Map.bindings evs)

(* Display a list of evars given by their name, with a prefix *)
let pr_ne_evar_set hd tl sigma l =
  if l != Evar.Set.empty then
    let l = Evar.Set.fold (fun ev ->
      Evar.Map.add ev (Evarutil.nf_evar_info sigma (Evd.find sigma ev)))
      l Evar.Map.empty in
    hd ++ pr_evars sigma l ++ tl
  else
    mt ()

let pr_selected_subgoal name sigma g =
  let pg = pr_goal { sigma=sigma ; it=g; } in
  let header = pr_goal_header name sigma g in
  v 0 (header ++ str " is:" ++ cut () ++ pg)

let pr_subgoal n sigma =
  let rec prrec p = function
    | [] -> user_err Pp.(str "No such goal.")
    | g::rest ->
        if Int.equal p 1 then
          pr_selected_subgoal (int n) sigma g
        else
          prrec (p-1) rest
  in
  prrec n

let pr_internal_existential_key ev = Evar.print ev

let print_evar_constraints gl sigma =
  let pr_env =
    match gl with
    | None -> fun e' -> pr_context_of e' sigma
    | Some g ->
       let env = Goal.V82.env sigma g in fun e' ->
       begin
         if Context.Named.equal Constr.equal (named_context env) (named_context e') then
           if Context.Rel.equal Constr.equal (rel_context env) (rel_context e') then mt ()
           else pr_rel_context_of e' sigma ++ str " |-" ++ spc ()
         else pr_context_of e' sigma ++ str " |-" ++ spc ()
       end
  in
  let pr_evconstr (pbty,env,t1,t2) =
    let t1 = Evarutil.nf_evar sigma t1
    and t2 = Evarutil.nf_evar sigma t2 in
    let env =
      (* We currently allow evar instances to refer to anonymous de Bruijn
         indices, so we protect the error printing code in this case by giving
         names to every de Bruijn variable in the rel_context of the conversion
         problem. MS: we should rather stop depending on anonymous variables, they
         can be used to indicate independency. Also, this depends on a strategy for
         naming/renaming *)
      Namegen.make_all_name_different env sigma in
    str" " ++
      hov 2 (pr_env env ++ pr_leconstr_env env sigma t1 ++ spc () ++
             str (match pbty with
                  | Reduction.CONV -> "=="
                  | Reduction.CUMUL -> "<=") ++
             spc () ++ pr_leconstr_env env sigma t2)
  in
  let pr_candidate ev evi (candidates,acc) =
    if Option.has_some evi.evar_candidates then
      (succ candidates, acc ++ pr_evar sigma (ev,evi) ++ fnl ())
    else (candidates, acc)
  in
  let constraints =
    let _, cstrs = Evd.extract_all_conv_pbs sigma in
    if List.is_empty cstrs then mt ()
    else fnl () ++ str (String.plural (List.length cstrs) "unification constraint")
         ++ str":" ++ fnl () ++ hov 0 (prlist_with_sep fnl pr_evconstr cstrs)
  in
  let candidates, ppcandidates = Evd.fold_undefined pr_candidate sigma (0,mt ()) in
  constraints ++
    if candidates > 0 then
      fnl () ++ str (String.plural candidates "existential") ++
        str" with candidates:" ++ fnl () ++ hov 0 ppcandidates
    else mt ()

let should_print_dependent_evars =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Dependent";"Evars";"Line"]
    ~value:false

let print_dependent_evars gl sigma seeds =
  if should_print_dependent_evars () then
    let mt_pp = mt () in
    let evars = Evarutil.gather_dependent_evars sigma seeds in
    let evars_pp = Evar.Map.fold (fun e i s ->
        let e' = pr_internal_existential_key e in
        let sep = if s = mt_pp then "" else ", " in
        s ++ str sep ++ e' ++
            (match i with
            | None -> str ":" ++ (Termops.pr_existential_key sigma e)
            | Some i ->
              let using = Evar.Set.fold (fun d s ->
                  s ++ str " " ++ (pr_internal_existential_key d))
                i mt_pp in
              str " using" ++ using))
      evars mt_pp
    in
    let evars_current_pp = match gl with
        | None -> mt_pp
        | Some gl ->
           let evars_current = Evarutil.gather_dependent_evars sigma [ gl ] in
           Evar.Map.fold (fun e _ s ->
               s ++ str " " ++ (pr_internal_existential_key e))
             evars_current mt_pp
    in
    cut () ++ cut () ++
      str "(dependent evars: " ++ evars_pp ++
      str "; in current goal:" ++ evars_current_pp ++ str ")"
  else mt ()

module GoalMap = Evar.Map

(* Print open subgoals. Checks for uninstantiated existential variables *)
(* spiwack: [seeds] is for printing dependent evars in emacs mode. *)
(* spiwack: [pr_first] is true when the first goal must be singled out
   and printed in its entirety. *)
(* [os_map] is derived from the previous proof step, used for diffs *)
let pr_subgoals ?(pr_first=true) ?(diffs=false) ?os_map
                        close_cmd sigma ~seeds ~shelf ~stack ~unfocused ~goals =
  let diff_goal_map =
    match os_map with
    | Some (_, diff_goal_map) -> diff_goal_map
    | None -> GoalMap.empty
  in

  (* Printing functions for the extra informations. *)
  let rec print_stack a = function
    | [] -> Pp.int a
    | b::l -> Pp.int a ++ str"-" ++ print_stack b l
  in
  let print_unfocused_nums l =
    match l with
    | [] -> None
    | a::l -> Some (str"unfocused: " ++ print_stack a l)
  in
  let print_shelf l =
    match l with
    | [] -> None
    | _ -> Some (str"shelved: " ++ Pp.int (List.length l))
  in
  let rec print_comma_separated_list a l =
    match l with
    | [] -> a
    | b::l -> print_comma_separated_list (a++str", "++b) l
  in
  let print_extra_list l =
    match l with
    | [] -> Pp.mt ()
    | a::l -> Pp.spc () ++ str"(" ++ print_comma_separated_list a l ++ str")"
  in
  let extra = Option.List.flatten [ print_unfocused_nums stack ; print_shelf shelf ] in
  let print_extra = print_extra_list extra in
  let focused_if_needed =
    let needed = not (CList.is_empty extra) && pr_first in
    if needed then str" focused "
    else str" " (* non-breakable space *)
  in

  let get_ogs g =
    match os_map with
    | Some (osigma, _) ->
      (* if Not_found, returning None treats the goal as new and it will be diff highlighted;
         returning Some { it = g; sigma = sigma } will compare the new goal
         to itself and it won't be highlighted *)
      (try Some { it = GoalMap.find g diff_goal_map; sigma = osigma }
      with Not_found -> None)
    | None -> None
  in
  let rec pr_rec n = function
    | [] -> (mt ())
    | g::rest ->
       let og_s = get_ogs g in
       let pc = pr_concl n ~diffs ?og_s sigma g in
        let prest = pr_rec (n+1) rest in
        (cut () ++ pc ++ prest)
  in
  let print_multiple_goals g l =
    if pr_first then
      let og_s = get_ogs g in
      pr_goal ~diffs ?og_s { it = g ; sigma = sigma }
      ++ (if l=[] then mt () else cut ())
      ++ pr_rec 2 l
    else
      pr_rec 1 (g::l)
  in
  let pr_evar_info gl sigma seeds =
    let first_goal = if pr_first then gl else None in
    print_evar_constraints gl sigma ++ print_dependent_evars first_goal sigma seeds
  in
  (* Side effect! This has to be made more robust *)
  let () =
    match close_cmd with
    | Some cmd -> Feedback.msg_info cmd
    | None -> ()
  in

  (* Main function *)
  match goals with
  | [] ->
    let exl = Evd.undefined_map sigma in
    if Evar.Map.is_empty exl then
      v 0 (str "No more goals." ++ pr_evar_info None sigma seeds)
    else
      let pei = pr_evars_int sigma ~shelf ~given_up:[] 1 exl in
      v 0 ((str "No more goals,"
          ++ str " but there are non-instantiated existential variables:"
          ++ cut () ++ (hov 0 pei)
          ++ pr_evar_info None sigma seeds
          ++ cut () ++ str "You can use Unshelve."))
  | g1::rest ->
      let goals = print_multiple_goals g1 rest in
      let ngoals = List.length rest+1 in
      v 0 (
        int ngoals ++ focused_if_needed ++ str(String.plural ngoals "goal")
        ++ print_extra
        ++ str (if pr_first && (should_gname()) && ngoals > 1 then ", goal 1" else "")
        ++ (if pr_first && should_tag() then pr_goal_tag g1 else str"")
        ++ (if pr_first then pr_goal_name sigma g1 else mt()) ++ cut () ++ goals
        ++ (if unfocused=[] then str ""
           else (cut() ++ cut() ++ str "*** Unfocused goals:" ++ cut()
                 ++ pr_rec (List.length rest + 2) unfocused))
        ++ pr_evar_info (Some g1) sigma seeds
      )

let pr_open_subgoals_diff ?(quiet=false) ?(diffs=false) ?oproof proof =
  (* spiwack: it shouldn't be the job of the printer to look up stuff
     in the [evar_map], I did stuff that way because it was more
     straightforward, but seriously, [Proof.proof] should return
     [evar_info]-s instead. *)
  let p = proof in
  let Proof.{goals; stack; sigma} = Proof.data p in
  let shelf = Evd.shelf sigma in
  let given_up = Evd.given_up sigma in
  let stack = List.map (fun (l,r) -> List.length l + List.length r) stack in
  let seeds = Proof.V82.top_evars p in
  begin match goals with
  | [] -> let { Evd.it = bgoals ; sigma = bsigma } = Proof.V82.background_subgoals p in
          begin match bgoals,shelf,given_up with
          | [] , [] , g when Evar.Set.is_empty g -> pr_subgoals None sigma ~seeds ~shelf ~stack ~unfocused:[] ~goals
          | [] , [] , _ ->
             Feedback.msg_info (str "No more goals, but there are some goals you gave up:");
             fnl ()
            ++ pr_subgoals ~pr_first:false None bsigma ~seeds ~shelf:[] ~stack:[] ~unfocused:[] ~goals:(Evar.Set.elements given_up)
            ++ fnl () ++ str "You need to go back and solve them."
          | [] , _ , _ ->
            Feedback.msg_info (str "All the remaining goals are on the shelf.");
            fnl ()
            ++ pr_subgoals ~pr_first:false None bsigma ~seeds ~shelf:[] ~stack:[] ~unfocused:[] ~goals:shelf
          | _ , _, _ ->
            let cmd = if quiet then None else
              Some
                (str "This subproof is complete, but there are some unfocused goals." ++
                (let s = Proof_bullet.suggest p in
                 if Pp.ismt s then s else fnl () ++ s) ++
                fnl ())
            in
            pr_subgoals ~pr_first:false cmd bsigma ~seeds ~shelf ~stack:[] ~unfocused:[] ~goals:bgoals
          end
  | _ ->
     let { Evd.it = bgoals ; sigma = bsigma } = Proof.V82.background_subgoals p in
     let bgoals_focused, bgoals_unfocused = List.partition (fun x -> List.mem x goals) bgoals in
     let unfocused_if_needed = if should_unfoc() then bgoals_unfocused else [] in
     let os_map = match oproof with
       | Some op when diffs ->
         (try
           let Proof.{sigma=osigma} = Proof.data op in
           let diff_goal_map = Proof_diffs.make_goal_map oproof proof in
           Some (osigma, diff_goal_map)
         with Pp_diff.Diff_Failure msg ->
           Proof_diffs.notify_proof_diff_failure msg;
           None)
       | _ -> None
     in
     pr_subgoals ~pr_first:true ~diffs ?os_map None bsigma ~seeds ~shelf ~stack:[]
        ~unfocused:unfocused_if_needed ~goals:bgoals_focused
  end

let pr_open_subgoals ~proof =
  pr_open_subgoals_diff proof

let pr_nth_open_subgoal ~proof n =
  let Proof.{goals;sigma} = Proof.data proof in
  pr_subgoal n sigma goals

let pr_goal_by_id ~proof id =
  try
    let { Proof.sigma } = Proof.data proof in
    let g = Evd.evar_key id sigma in
    pr_selected_subgoal (pr_id id) sigma g
  with Not_found -> user_err Pp.(str "No such goal.")

(** print a goal identified by the goal id as it appears in -emacs mode.
    sid should be the Stm state id corresponding to proof.  Used to support
    the Prooftree tool in Proof General. (https://askra.de/software/prooftree/).
*)
let pr_goal_emacs ~proof gid sid =
  match proof with
  | None -> user_err Pp.(str "No proof for that state.")
  | Some proof ->
    let pr gs =
      v 0 ((str "goal ID " ++ (int gid) ++ str " at state " ++ (int sid)) ++ cut ()
          ++ pr_goal gs)
    in
    try
      let { Proof.sigma } = Proof.data proof in
      pr { it = Evar.unsafe_of_int gid ; sigma }
    with Not_found -> user_err Pp.(str "No such goal.")

(* Printer function for sets of Assumptions.assumptions.
   It is used primarily by the Print Assumptions command. *)

type axiom =
  | Constant of Constant.t
  | Positive of MutInd.t
  | Guarded of GlobRef.t
  | TypeInType of GlobRef.t
  | UIP of MutInd.t

type context_object =
  | Variable of Id.t (* A section variable or a Let definition *)
  | Axiom of axiom * (Label.t * Constr.rel_context * types) list
  | Opaque of Constant.t     (* An opaque constant. *)
  | Transparent of Constant.t

(* Defines a set of [assumption] *)
module OrderedContextObject =
struct
  type t = context_object

  let compare_axiom x y =
    match x,y with
    | Constant k1 , Constant k2 ->
      Constant.CanOrd.compare k1 k2
    | Positive m1 , Positive m2
    | UIP m1, UIP m2 ->
      MutInd.CanOrd.compare m1 m2
    | Guarded k1 , Guarded k2
    | TypeInType k1, TypeInType k2 ->
      GlobRef.CanOrd.compare k1 k2
    | Constant _, _ -> -1
    | _, Constant _ -> 1
    | Positive _, _ -> -1
    | _, Positive _ -> 1
    | Guarded _, _ -> -1
    | _, Guarded _ -> 1
    | TypeInType _, _ -> -1
    | _, TypeInType _ -> 1

  let compare x y =
    match x , y with
    | Variable i1 , Variable i2 -> Id.compare i1 i2
    | Variable _ , _ -> -1
    | _ , Variable _ -> 1
    | Axiom (k1,_) , Axiom (k2, _) -> compare_axiom k1 k2
    | Axiom _ , _ -> -1
    | _ , Axiom _ -> 1
    | Opaque k1 , Opaque k2 -> Constant.CanOrd.compare k1 k2
    | Opaque _ , _ -> -1
    | _ , Opaque _ -> 1
    | Transparent k1 , Transparent k2 -> Constant.CanOrd.compare k1 k2
end

module ContextObjectSet = Set.Make (OrderedContextObject)
module ContextObjectMap = Map.Make (OrderedContextObject)

let pr_assumptionset env sigma s =
  if ContextObjectMap.is_empty s &&
       not (is_impredicative_set env) then
    str "Closed under the global context"
  else
    let safe_pr_constant env kn =
      try pr_constant env kn
      with Not_found ->
        Names.Constant.print kn
    in
    let safe_pr_global env gr =
      try pr_global_env (Termops.vars_of_env env) gr
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
      try str " : " ++ pr_ltype_env env sigma typ
      with e when CErrors.noncritical e -> mt ()
    in
    let safe_pr_ltype_relctx (rctx, typ) =
      let env = Environ.push_rel_context rctx env in
      try str " " ++ pr_ltype_env env sigma typ
      with e when CErrors.noncritical e -> mt ()
    in
    let pr_axiom env ax typ =
      match ax with
      | Constant kn ->
          hov 1 (safe_pr_constant env kn ++ cut() ++ safe_pr_ltype env sigma typ)
      | Positive m ->
          hov 2 (safe_pr_inductive env m ++ spc () ++ strbrk"is assumed to be positive.")
      | Guarded gr ->
          hov 2 (safe_pr_global env gr ++ spc () ++ strbrk"is assumed to be guarded.")
      | TypeInType gr ->
          hov 2 (safe_pr_global env gr ++ spc () ++ strbrk"relies on an unsafe hierarchy.")
      | UIP mind ->
          hov 2 (safe_pr_inductive env mind ++ spc () ++ strbrk"relies on definitional UIP.")
    in
    let fold t typ accu =
      let (v, a, o, tr) = accu in
      match t with
      | Variable id ->
        let var = pr_id id ++ spc() ++ str ": " ++ pr_ltype_env env sigma typ in
        (var :: v, a, o, tr)
      | Axiom (axiom, []) ->
        let ax = pr_axiom env axiom typ in
        (v, ax :: a, o, tr)
      | Axiom (axiom,l) ->
        let ax = pr_axiom env axiom typ ++
          spc() ++
          prlist_with_sep cut (fun (lbl, ctx, ty) ->
            str "used in " ++ Label.print lbl ++
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
      if is_impredicative_set env then
        [str "Set is impredicative"]
      else []
    in
    let theory =
      if type_in_type env then
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

(* print the proof step, possibly with diffs highlighted, *)
let print_and_diff oldp newp =
  match newp with
  | None -> ()
  | Some proof ->
    let output =
      if Proof_diffs.show_diffs () then
        try pr_open_subgoals_diff ~diffs:true ?oproof:oldp proof
        with Pp_diff.Diff_Failure msg -> begin
          (* todo: print the unparsable string (if we know it) *)
          Feedback.msg_warning Pp.(str ("Diff failure: " ^ msg) ++ cut()
              ++ str "Showing results without diff highlighting" );
          pr_open_subgoals ~proof
        end
      else
        pr_open_subgoals ~proof
    in
    Feedback.msg_notice output;;

let pr_typing_flags flags =
  str "check_guarded: " ++ bool flags.check_guarded ++ fnl ()
  ++ str "check_positive: " ++ bool flags.check_positive ++ fnl ()
  ++ str "check_universes: " ++ bool flags.check_universes ++ fnl ()
  ++ str "cumulative sprop: " ++ bool flags.cumulative_sprop ++ fnl ()
  ++ str "definitional uip: " ++ bool flags.allow_uip
