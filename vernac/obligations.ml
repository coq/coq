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
open CErrors
open Util

(* For the records fields, opens should go away one these types are private *)
open DeclareObl
open DeclareObl.Obligation
open DeclareObl.ProgramDecl

let pperror cmd = CErrors.user_err ~hdr:"Program" cmd
let error s = pperror (str s)

let reduce c =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  EConstr.Unsafe.to_constr (Reductionops.clos_norm_flags CClosure.betaiota env sigma (EConstr.of_constr c))

exception NoObligations of Id.t option

let explain_no_obligations = function
    Some ident -> str "No obligations for program " ++ Id.print ident
  | None -> str "No obligations remaining"

let assumption_message = Declare.assumption_message

let default_tactic = ref (Proofview.tclUNIT ())

let evar_of_obligation o = Evd.make_evar (Global.named_context_val ()) (EConstr.of_constr o.obl_type)

let subst_deps expand obls deps t =
  let osubst = DeclareObl.obl_substitution expand obls deps in
    (Vars.replace_vars (List.map (fun (n, (_, b)) -> n, b) osubst) t)

let subst_deps_obl obls obl =
  let t' = subst_deps true obls obl.obl_deps obl.obl_type in
  Obligation.set_type ~typ:t' obl

open Evd

let map_cardinal m =
  let i = ref 0 in
  ProgMap.iter (fun _ v ->
      if (CEphemeron.get v).prg_obligations.remaining > 0 then incr i) m;
  !i

exception Found of ProgramDecl.t CEphemeron.key

let map_first m =
  try
    ProgMap.iter (fun _ v ->
        if (CEphemeron.get v).prg_obligations.remaining > 0 then
          raise (Found v)) m;
    assert(false)
  with Found x -> x

let get_prog name =
  let prg_infos = get_prg_info_map () in
    match name with
        Some n ->
          (try CEphemeron.get (ProgMap.find n prg_infos)
           with Not_found -> raise (NoObligations (Some n)))
      | None ->
          (let n = map_cardinal prg_infos in
             match n with
                 0 -> raise (NoObligations None)
               | 1 -> CEphemeron.get (map_first prg_infos)
               | _ ->
                let progs = Id.Set.elements (ProgMap.domain prg_infos) in
                let prog = List.hd progs in
                let progs = prlist_with_sep pr_comma Id.print progs in
                user_err
                  (str "More than one program with unsolved obligations: " ++ progs
                  ++ str "; use the \"of\" clause to specify, as in \"Obligation 1 of " ++ Id.print prog ++ str "\""))

let get_any_prog () =
  let prg_infos = get_prg_info_map () in
  let n = map_cardinal prg_infos in
  if n > 0 then CEphemeron.get (map_first prg_infos)
  else raise (NoObligations None)

let get_prog_err n =
  try get_prog n with NoObligations id -> pperror (explain_no_obligations id)

let get_any_prog_err () =
  try get_any_prog () with NoObligations id -> pperror (explain_no_obligations id)

let all_programs () =
  ProgMap.fold (fun k p l -> p :: l) (get_prg_info_map ()) []

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

let rec string_of_list sep f = function
    [] -> ""
  | x :: [] -> f x
  | x :: ((y :: _) as tl) -> f x ^ sep ^ string_of_list sep f tl

(* Solve an obligation using tactics, return the corresponding proof term *)
let warn_solve_errored = CWarnings.create ~name:"solve_obligation_error" ~category:"tactics" (fun err ->
    Pp.seq [str "Solve Obligations tactic returned error: "; err; fnl ();
            str "This will become an error in the future"])

let solve_by_tac ?loc name evi t poly uctx =
  try
    (* the status is dropped. *)
    let env = Global.env () in
    let body, types, _, uctx =
      Pfedit.build_by_tactic env ~uctx ~poly ~typ:evi.evar_concl t in
    Inductiveops.control_only_guard env (Evd.from_ctx uctx) (EConstr.of_constr body);
    Some (body, types, uctx)
  with
  | Refiner.FailError (_, s) as exn ->
    let _ = Exninfo.capture exn in
    user_err ?loc ~hdr:"solve_obligation" (Lazy.force s)
  (* If the proof is open we absorb the error and leave the obligation open *)
  | Proof.OpenProof _ ->
    None
  | e when CErrors.noncritical e ->
    let err = CErrors.print e in
    warn_solve_errored ?loc err;
    None

let rec solve_obligation prg num tac =
  let user_num = succ num in
  let { obls; remaining=rem } = prg.prg_obligations in
  let obl = obls.(num) in
  let remaining = deps_remaining obls obl.obl_deps in
  let () =
    if not (Option.is_empty obl.obl_body) then
      pperror (str "Obligation" ++ spc () ++ int user_num ++ str "already" ++ spc() ++ str "solved.");
    if not (List.is_empty remaining) then
      pperror (str "Obligation " ++ int user_num ++ str " depends on obligation(s) "
        ++ str (string_of_list ", " (fun x -> string_of_int (succ x)) remaining));
  in
  let obl = subst_deps_obl obls obl in
  let scope = DeclareDef.(Global Declare.ImportNeedQualified) in
  let kind = kind_of_obligation (snd obl.obl_status) in
  let evd = Evd.from_ctx prg.prg_ctx in
  let evd = Evd.update_sigma_env evd (Global.env ()) in
  let auto n oblset tac = auto_solve_obligations n ~oblset tac in
  let proof_ending = Lemmas.Proof_ending.End_obligation (DeclareObl.{name = prg.prg_name; num; auto}) in
  let hook = DeclareDef.Hook.make (DeclareObl.obligation_hook prg obl num auto) in
  let info = Lemmas.Info.make ~hook ~proof_ending ~scope ~kind () in
  let poly = prg.prg_poly in
  let lemma = Lemmas.start_lemma ~name:obl.obl_name ~poly ~info evd (EConstr.of_constr obl.obl_type) in
  let lemma = fst @@ Lemmas.by !default_tactic lemma in
  let lemma = Option.cata (fun tac -> Lemmas.set_endline_tactic tac lemma) lemma tac in
  lemma

and obligation (user_num, name, typ) tac =
  let num = pred user_num in
  let prg = get_prog_err name in
  let { obls; remaining } = prg.prg_obligations in
    if num >= 0 && num < Array.length obls then
      let obl = obls.(num) in
        match obl.obl_body with
          | None -> solve_obligation prg num tac
          | Some r -> error "Obligation already solved"
    else error (sprintf "Unknown obligation number %i" (succ num))


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
        | Some (t, ty, ctx) ->
          let prg = ProgramDecl.set_uctx ~uctx:ctx prg in
          (* Why is uctx not used above? *)
          let uctx = UState.univ_entry ~poly:prg.prg_poly ctx in
          let def, obl' = declare_obligation prg obl t ty uctx in
          obls.(i) <- obl';
          if def && not prg.prg_poly then (
            (* Declare the term constraints with the first obligation only *)
            let evd = Evd.from_env (Global.env ()) in
            let evd = Evd.merge_universe_subst evd (Evd.universe_subst (Evd.from_ctx ctx)) in
            let ctx' = Evd.evar_universe_context evd in
            Some (ProgramDecl.set_uctx ~uctx:ctx' prg))
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
  let prg =
    Array.fold_left_i (fun i prg x ->
      if p i then
        match solve_obligation_by_tac prg obls' i tac with
        | None -> prg
        | Some prg ->
          let deps = dependencies obls i in
          set := Int.Set.union !set deps;
          decr rem;
          prg
      else prg)
      prg obls'
  in
  update_obls prg obls' !rem

and solve_obligations n tac =
  let prg = get_prog_err n in
    solve_prg_obligations prg tac

and solve_all_obligations tac =
  ProgMap.iter (fun k v -> ignore(solve_prg_obligations (CEphemeron.get v) tac)) (get_prg_info_map ())

and try_solve_obligation n prg tac =
  let prg = get_prog prg in
  let {obls; remaining } = prg.prg_obligations in
  let obls' = Array.copy obls in
    match solve_obligation_by_tac prg obls' n tac with
    | Some prg' -> ignore(update_obls prg' obls' (pred remaining))
    | None -> ()

and try_solve_obligations n tac =
  try ignore (solve_obligations n tac) with NoObligations _ -> ()

and auto_solve_obligations n ?oblset tac : progress =
  Flags.if_verbose Feedback.msg_info (str "Solving obligations automatically...");
  try solve_prg_obligations (get_prog_err n) ?oblset tac with NoObligations _ -> Dependent

open Pp
let show_obligations_of_prg ?(msg=true) prg =
  let n = prg.prg_name in
  let {obls; remaining} = prg.prg_obligations in
  let showed = ref 5 in
    if msg then Feedback.msg_info (int remaining ++ str " obligation(s) remaining: ");
    Array.iteri (fun i x ->
                   match x.obl_body with
                   | None ->
                       if !showed > 0 then (
                         decr showed;
                         let x = subst_deps_obl obls x in
                         let env = Global.env () in
                         let sigma = Evd.from_env env in
                         Feedback.msg_info (str "Obligation" ++ spc() ++ int (succ i) ++ spc () ++
                                   str "of" ++ spc() ++ Id.print n ++ str ":" ++ spc () ++
                                   hov 1 (Printer.pr_constr_env env sigma x.obl_type ++
                                            str "." ++ fnl ())))
                   | Some _ -> ())
      obls

let show_obligations ?(msg=true) n =
  let progs = match n with
    | None -> all_programs ()
    | Some n ->
        try [ProgMap.find n (get_prg_info_map ())]
        with Not_found -> raise (NoObligations (Some n))
  in List.iter (fun x -> show_obligations_of_prg ~msg (CEphemeron.get x)) progs

let show_term n =
  let prg = get_prog_err n in
  let n = prg.prg_name in
  let env = Global.env () in
  let sigma = Evd.from_env env in
    (Id.print n ++ spc () ++ str":" ++ spc () ++
             Printer.pr_constr_env env sigma prg.prg_type ++ spc () ++ str ":=" ++ fnl ()
            ++ Printer.pr_constr_env env sigma prg.prg_body)

let add_definition ~name ?term t ~uctx ?(udecl=UState.default_univ_decl)
                   ?(impargs=[]) ~poly ?(scope=DeclareDef.Global Declare.ImportDefaultBehavior) ?(kind=Decls.Definition) ?tactic
    ?(reduce=reduce) ?hook ?(opaque = false) obls =
  let info = Id.print name ++ str " has type-checked" in
  let prg = ProgramDecl.make ~opaque name ~udecl term t ~uctx [] None [] obls ~impargs ~poly ~scope ~kind reduce ?hook in
  let {obls;_} = prg.prg_obligations in
  if Int.equal (Array.length obls) 0 then (
    Flags.if_verbose Feedback.msg_info (info ++ str ".");
    let cst = DeclareObl.declare_definition prg in
    Defined cst)
  else (
    let len = Array.length obls in
    let () = Flags.if_verbose Feedback.msg_info (info ++ str ", generating " ++ int len ++ str (String.plural len " obligation")) in
      progmap_add name (CEphemeron.create prg);
      let res = auto_solve_obligations (Some name) tactic in
        match res with
        | Remain rem -> Flags.if_verbose (fun () -> show_obligations ~msg:false (Some name)) (); res
        | _ -> res)

let add_mutual_definitions l ~uctx ?(udecl=UState.default_univ_decl) ?tactic
                           ~poly ?(scope=DeclareDef.Global Declare.ImportDefaultBehavior) ?(kind=Decls.Definition) ?(reduce=reduce)
    ?hook ?(opaque = false) notations fixkind =
  let deps = List.map (fun ({ DeclareDef.Recthm.name; _ }, _, _) -> name) l in
    List.iter
    (fun ({ DeclareDef.Recthm.name; typ; impargs; _ }, b, obls) ->
     let prg = ProgramDecl.make ~opaque name ~udecl (Some b) typ ~uctx deps (Some fixkind)
       notations obls ~impargs ~poly ~scope ~kind reduce ?hook
     in progmap_add name (CEphemeron.create prg)) l;
    let _defined =
      List.fold_left (fun finished x ->
        if finished then finished
        else
          let res = auto_solve_obligations (Some x) tactic in
            match res with
            | Defined _ ->
                (* If one definition is turned into a constant,
                   the whole block is defined. *) true
            | _ -> false)
        false deps
    in ()

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
              (Declare.ParameterEntry (None,(x.obl_type,ctx),None)) ~kind:Decls.(IsAssumption Conjectural)
            in
              assumption_message x.obl_name;
              obls.(i) <- Obligation.set_body ~body:(DefinedObl (kn, Univ.Instance.empty)) x
        | Some _ -> ())
      obls;
    ignore(DeclareObl.update_obls prg obls 0)

let rec admit_all_obligations () =
  let prg = try Some (get_any_prog ()) with NoObligations _ -> None in
  match prg with
  | None -> ()
  | Some prg ->
    admit_prog prg;
    admit_all_obligations ()

let admit_obligations n =
  match n with
  | None -> admit_all_obligations ()
  | Some _ ->
    let prg = get_prog_err n in
    admit_prog prg

let next_obligation n tac =
  let prg = match n with
  | None -> get_any_prog_err ()
  | Some _ -> get_prog_err n
  in
  let {obls; remaining} = prg.prg_obligations in
  let is_open _ x = Option.is_empty x.obl_body && List.is_empty (deps_remaining obls x.obl_deps) in
  let i = match Array.findi is_open obls with
  | Some i -> i
  | None -> anomaly (Pp.str "Could not find a solvable obligation.")
  in
  solve_obligation prg i tac

let check_program_libraries () =
  Coqlib.check_required_library Coqlib.datatypes_module_name;
  Coqlib.check_required_library ["Coq";"Init";"Specif"];
  Coqlib.check_required_library ["Coq";"Program";"Tactics"]
