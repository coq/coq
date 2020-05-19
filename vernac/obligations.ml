(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Printf
open Names
open Pp
open Util

(* For the records fields, opens should go away one these types are private *)
open Declare.Obls
open Declare.Obls.Obligation
open Declare.Obls.ProgramDecl

let reduce c =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  EConstr.Unsafe.to_constr (Reductionops.clos_norm_flags CClosure.betaiota env sigma (EConstr.of_constr c))

let explain_no_obligations = function
    Some ident -> str "No obligations for program " ++ Id.print ident
  | None -> str "No obligations remaining"

module Error = struct

  let no_obligations n =
    CErrors.user_err (explain_no_obligations n)

  let ambiguous_program id ids =
    CErrors.user_err
      Pp.(str "More than one program with unsolved obligations: " ++ prlist Id.print ids
          ++ str "; use the \"of\" clause to specify, as in \"Obligation 1 of " ++ Id.print id ++ str "\"")

  let unknown_obligation num =
    CErrors.user_err (Pp.str (sprintf "Unknown obligation number %i" (succ num)))

  let already_solved num =
    CErrors.user_err
      ( str "Obligation" ++ spc () ++ int num ++ str "already" ++ spc ()
        ++ str "solved." )

  let depends num rem =
    CErrors.user_err
      ( str "Obligation " ++ int num
        ++ str " depends on obligation(s) "
        ++ pr_sequence (fun x -> int (succ x)) rem)

end

let default_tactic = ref (Proofview.tclUNIT ())

let evar_of_obligation o = Evd.make_evar (Global.named_context_val ()) (EConstr.of_constr o.obl_type)

let subst_deps expand obls deps t =
  let osubst = Declare.Obls.obl_substitution expand obls deps in
    (Vars.replace_vars (List.map (fun (n, (_, b)) -> n, b) osubst) t)

let subst_deps_obl obls obl =
  let t' = subst_deps true obls obl.obl_deps obl.obl_type in
  Obligation.set_type ~typ:t' obl

open Evd

let is_defined obls x = not (Option.is_empty obls.(x).obl_body)

let deps_remaining obls deps =
  Int.Set.fold
    (fun x acc ->
      if is_defined obls x then acc
      else x :: acc)
    deps []

let goal_kind = Decls.(IsDefinition Definition)
let goal_proof_kind = Decls.(IsProof Lemma)

let kind_of_obligation o =
  match o with
  | Evar_kinds.Define false
  | Evar_kinds.Expand -> goal_kind
  | _ -> goal_proof_kind

(* Solve an obligation using tactics, return the corresponding proof term *)
let warn_solve_errored =
  CWarnings.create ~name:"solve_obligation_error" ~category:"tactics"
    (fun err ->
      Pp.seq
        [ str "Solve Obligations tactic returned error: "
        ; err
        ; fnl ()
        ; str "This will become an error in the future" ])

let solve_by_tac ?loc name evi t poly uctx =
  (* the status is dropped. *)
  try
    let env = Global.env () in
    let body, types, _univs, _, uctx =
      Declare.build_by_tactic env ~uctx ~poly ~typ:evi.evar_concl t in
    Inductiveops.control_only_guard env (Evd.from_ctx uctx) (EConstr.of_constr body);
    Some (body, types, uctx)
  with
  | Refiner.FailError (_, s) as exn ->
    let _ = Exninfo.capture exn in
    CErrors.user_err ?loc ~hdr:"solve_obligation" (Lazy.force s)
  (* If the proof is open we absorb the error and leave the obligation open *)
  | Proof.OpenProof _ ->
    None
  | e when CErrors.noncritical e ->
    let err = CErrors.print e in
    warn_solve_errored ?loc err;
    None

let get_unique_prog prg =
  match State.get_unique_open_prog prg with
  | Ok prg -> prg
  | Error [] ->
    Error.no_obligations None
  | Error ((id :: _) as ids) ->
    Error.ambiguous_program id ids

let rec solve_obligation prg num tac =
  let user_num = succ num in
  let { obls; remaining=rem } = prg.prg_obligations in
  let obl = obls.(num) in
  let remaining = deps_remaining obls obl.obl_deps in
  let () =
    if not (Option.is_empty obl.obl_body)
    then Error.already_solved user_num;
    if not (List.is_empty remaining)
    then Error.depends user_num remaining
  in
  let obl = subst_deps_obl obls obl in
  let scope = Declare.(Global Declare.ImportNeedQualified) in
  let kind = kind_of_obligation (snd obl.obl_status) in
  let evd = Evd.from_ctx prg.prg_ctx in
  let evd = Evd.update_sigma_env evd (Global.env ()) in
  let auto n oblset tac = auto_solve_obligations n ~oblset tac in
  let proof_ending =
    Declare.Proof_ending.End_obligation
      {Declare.Obls.name = prg.prg_name; num; auto}
  in
  let info = Lemmas.Info.make ~proof_ending ~scope ~kind () in
  let poly = prg.prg_poly in
  let lemma = Lemmas.start_lemma ~name:obl.obl_name ~poly ~info evd (EConstr.of_constr obl.obl_type) in
  let lemma = fst @@ Lemmas.by !default_tactic lemma in
  let lemma = Option.cata (fun tac -> Lemmas.set_endline_tactic tac lemma) lemma tac in
  lemma

and obligation (user_num, name, typ) tac =
  let num = pred user_num in
  let prg = get_unique_prog name in
  let { obls; remaining } = prg.prg_obligations in
  if num >= 0 && num < Array.length obls then
    let obl = obls.(num) in
    match obl.obl_body with
    | None -> solve_obligation prg num tac
    | Some r -> Error.already_solved num
  else Error.unknown_obligation num

and solve_obligation_by_tac prg obls i tac =
  let obl = obls.(i) in
    match obl.obl_body with
    | Some _ -> None
    | None ->
      if List.is_empty (deps_remaining obls obl.obl_deps) then
        let obl = subst_deps_obl obls obl in
        let tac =
          match tac with
          | Some t -> t
          | None ->
            match obl.obl_tac with
            | Some t -> t
            | None -> !default_tactic
        in
        let evd = Evd.from_ctx prg.prg_ctx in
        let evd = Evd.update_sigma_env evd (Global.env ()) in
        match solve_by_tac ?loc:(fst obl.obl_location) obl.obl_name (evar_of_obligation obl) tac
                prg.prg_poly (Evd.evar_universe_context evd) with
        | None -> None
        | Some (t, ty, uctx) ->
          let prg = ProgramDecl.set_uctx ~uctx prg in
          (* Why is uctx not used above? *)
          let def, obl' = declare_obligation prg obl ~body:t ~types:ty ~uctx in
          obls.(i) <- obl';
          if def && not prg.prg_poly then (
            (* Declare the term constraints with the first obligation only *)
            let uctx_global = UState.from_env (Global.env ()) in
            let uctx = UState.merge_subst uctx_global (UState.subst uctx) in
            Some (ProgramDecl.set_uctx ~uctx prg))
          else Some prg
      else None

and solve_prg_obligations prg ?oblset tac =
  let { obls; remaining } = prg.prg_obligations in
  let rem = ref remaining in
  let obls' = Array.copy obls in
  let set = ref Int.Set.empty in
  let p = match oblset with
    | None -> (fun _ -> true)
    | Some s -> set := s;
      (fun i -> Int.Set.mem i !set)
  in
  let (), prg =
    Array.fold_left_i
      (fun i ((), prg) x ->
        if p i then (
          match solve_obligation_by_tac prg obls' i tac with
          | None -> (), prg
          | Some prg ->
            let deps = dependencies obls i in
            set := Int.Set.union !set deps;
            decr rem;
            (), prg)
        else (), prg)
      ((), prg) obls'
  in
  update_obls prg obls' !rem

and solve_obligations n tac =
  let prg = get_unique_prog n in
    solve_prg_obligations prg tac

and solve_all_obligations tac =
  State.fold ~init:() ~f:(fun k v () ->
      let _ = solve_prg_obligations v tac in ())

and try_solve_obligation n prg tac =
  let prg = get_unique_prog prg in
  let {obls; remaining } = prg.prg_obligations in
  let obls' = Array.copy obls in
  match solve_obligation_by_tac prg obls' n tac with
  | Some prg' ->
    let _r = update_obls prg' obls' (pred remaining) in
    ()
  | None -> ()

and try_solve_obligations n tac =
  let _ = solve_obligations n tac in
  ()

and auto_solve_obligations n ?oblset tac : progress =
  Flags.if_verbose Feedback.msg_info
    (str "Solving obligations automatically...");
  let prg = get_unique_prog n in
  solve_prg_obligations prg ?oblset tac

open Pp

let show_single_obligation i n obls x =
  let x = subst_deps_obl obls x in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let msg =
    str "Obligation" ++ spc ()
    ++ int (succ i)
    ++ spc () ++ str "of" ++ spc () ++ Id.print n ++ str ":" ++ spc ()
    ++ hov 1 (Printer.pr_constr_env env sigma x.obl_type
              ++ str "." ++ fnl ()) in
  Feedback.msg_info msg

let show_obligations_of_prg ?(msg = true) prg =
  let n = prg.prg_name in
  let {obls; remaining} = prg.prg_obligations in
  let showed = ref 5 in
    if msg then Feedback.msg_info (int remaining ++ str " obligation(s) remaining: ");
    Array.iteri
      (fun i x ->
         match x.obl_body with
         | None ->
           if !showed > 0 then begin
             decr showed;
             show_single_obligation i n obls x
           end
         | Some _ -> ())
      obls

let show_obligations ?(msg = true) n =
  let progs =
    match n with
    | None ->
      State.all ()
    | Some n ->
      (match State.find n with
       | Some prg -> [prg]
       | None -> Error.no_obligations (Some n))
  in
  List.iter (fun x -> show_obligations_of_prg ~msg x) progs

let show_term n =
  let prg = get_unique_prog n in
  let n = prg.prg_name in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  Id.print n ++ spc () ++ str ":" ++ spc ()
  ++ Printer.pr_constr_env env sigma prg.prg_type
  ++ spc () ++ str ":=" ++ fnl ()
  ++ Printer.pr_constr_env env sigma prg.prg_body

let msg_generating_obl name obls =
  let len = Array.length obls in
  let info = Id.print name ++ str " has type-checked" in
  Feedback.msg_info
    (if len = 0 then info ++ str "."
     else
       info ++ str ", generating " ++ int len ++
       str (String.plural len " obligation"))

let add_definition ~name ?term t ~uctx ?(udecl = UState.default_univ_decl)
    ?(impargs = []) ~poly
    ?(scope = Declare.Global Declare.ImportDefaultBehavior)
    ?(kind = Decls.Definition) ?tactic ?(reduce = reduce) ?hook
    ?(opaque = false) obls =
  let prg = ProgramDecl.make ~opaque name ~udecl term t ~uctx [] None [] obls ~impargs ~poly ~scope ~kind reduce ?hook in
  let {obls;_} = prg.prg_obligations in
  if Int.equal (Array.length obls) 0 then (
    Flags.if_verbose (msg_generating_obl name) obls;
    let cst = Declare.Obls.declare_definition prg in
    Defined cst)
  else
    let () = Flags.if_verbose (msg_generating_obl name) obls in
    let () = State.add name prg in
    let res = auto_solve_obligations (Some name) tactic in
    match res with
    | Remain rem ->
      Flags.if_verbose (show_obligations ~msg:false) (Some name);
      res
    | _ -> res

let add_mutual_definitions l ~uctx ?(udecl = UState.default_univ_decl)
    ?tactic ~poly ?(scope = Declare.Global Declare.ImportDefaultBehavior)
    ?(kind = Decls.Definition) ?(reduce = reduce) ?hook ?(opaque = false)
    notations fixkind =
  let deps = List.map (fun ({Declare.Recthm.name; _}, _, _) -> name) l in
  let pm =
    List.fold_left
      (fun () ({Declare.Recthm.name; typ; impargs; _}, b, obls) ->
        let prg =
          ProgramDecl.make ~opaque name ~udecl (Some b) typ ~uctx deps
            (Some fixkind) notations obls ~impargs ~poly ~scope ~kind reduce
            ?hook
        in
        State.add name prg)
      () l
  in
  let pm, _defined =
    List.fold_left
      (fun (pm, finished) x ->
        if finished then (pm, finished)
        else
          let res = auto_solve_obligations (Some x) tactic in
          match res with
          | Defined _ ->
            (* If one definition is turned into a constant,
               the whole block is defined. *)
            (pm, true)
          | _ -> (pm, false))
      (pm, false) deps
  in
  pm

let admit_prog prg =
  let {obls; remaining} = prg.prg_obligations in
  let obls = Array.copy obls in
    Array.iteri
      (fun i x ->
        match x.obl_body with
        | None ->
            let x = subst_deps_obl obls x in
            let ctx = UState.univ_entry ~poly:false prg.prg_ctx in
            let kn = Declare.declare_constant ~name:x.obl_name ~local:Declare.ImportNeedQualified
              (Declare.ParameterEntry (None, (x.obl_type, ctx), None)) ~kind:Decls.(IsAssumption Conjectural)
            in
              Declare.assumption_message x.obl_name;
              obls.(i) <- Obligation.set_body ~body:(DefinedObl (kn, Univ.Instance.empty)) x
        | Some _ -> ())
      obls;
  Declare.Obls.update_obls prg obls 0

(* get_any_prog *)
let rec admit_all_obligations () =
  let prg = State.first_pending () in
  match prg with
  | None -> ()
  | Some prg ->
    let _prog = admit_prog prg in
    admit_all_obligations ()

let admit_obligations n =
  match n with
  | None -> admit_all_obligations ()
  | Some _ ->
    let prg = get_unique_prog n in
    let _ = admit_prog prg in
    ()

let next_obligation n tac =
  let prg = match n with
    | None -> State.first_pending () |> Option.get
    | Some _ -> get_unique_prog n
  in
  let {obls; remaining} = prg.prg_obligations in
  let is_open _ x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
  let i = match Array.findi is_open obls with
    | Some i -> i
    | None -> CErrors.anomaly (Pp.str "Could not find a solvable obligation.")
  in
  solve_obligation prg i tac

let check_program_libraries () =
  Coqlib.check_required_library Coqlib.datatypes_module_name;
  Coqlib.check_required_library ["Coq";"Init";"Specif"];
  Coqlib.check_required_library ["Coq";"Program";"Tactics"]
