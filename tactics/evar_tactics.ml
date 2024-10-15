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
open Names
open Constr
open CErrors
open Evd
open Evarsolve
open Locus
open Context.Named.Declaration
open Pp
open Ltac_pretype

module NamedDecl = Context.Named.Declaration

(******************************************)
(* Instantiation of existential variables *)
(******************************************)

let define_and_solve_constraints evk c env evd =
  if Termops.occur_evar evd evk c then
    Pretype_errors.error_occur_check env evd evk c;
  let evd = define evk c evd in
  let (evd,pbs) = extract_changed_conv_pbs_from evd (Some (Evar.Set.singleton evk)) in
  match
    List.fold_left
      (fun p (pbty,env,t1,t2) -> match p with
        | Success evd -> Evarconv.evar_conv_x (Evarconv.default_flags_of TransparentState.full) env evd pbty t1 t2
        | UnifFailure _ as x -> x) (Success evd)
      pbs
  with
    | Success evd -> evd
    | UnifFailure _ -> user_err Pp.(str "Instance does not satisfy the constraints.")

let w_refine evk rawc env sigma =
  let evi =
    try Evd.find_undefined sigma evk
    with Not_found ->
      let () = assert (Evd.mem sigma evk) in
      user_err Pp.(str "Instantiate called on already-defined evar")
  in
  let env = Evd.evar_filtered_env env evi in
  let sigma',typed_c =
    let flags = Pretyping.{
      use_coercions = true;
      use_typeclasses = UseTC;
      solve_unification_constraints = true;
      fail_evar = false;
      expand_evars = true;
      program_mode = false;
      polymorphic = false;
      undeclared_evars_patvars = false;
      patvars_abstract = false;
      unconstrained_sorts = false;
    } in
    let expected_type = Pretyping.OfType (Evd.evar_concl evi) in
    try Pretyping.understand_uconstr ~flags ~expected_type env sigma rawc
    with e when CErrors.noncritical e ->
      let loc = Glob_ops.loc_of_glob_constr rawc.term in
      user_err ?loc
                (str "Instance is not well-typed in the environment of " ++
                 Termops.pr_existential_key env sigma evk ++ str ".")
  in
  define_and_solve_constraints evk typed_c env sigma'

(* The instantiate tactic *)

let instantiate_evar evk rawc =
  let open Proofview.Notations in
  Proofview.tclENV >>= fun env ->
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let sigma' = w_refine evk rawc env sigma in
  Proofview.Unsafe.tclEVARS sigma'
  end

let evar_list sigma c =
  let rec evrec acc c =
    match EConstr.kind sigma c with
    | Evar (evk, _ as ev) -> ev :: acc
    | _ -> EConstr.fold sigma evrec acc c in
  evrec [] c

let instantiate_tac n c ido =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let env = Proofview.Goal.env gl in
  let concl = Proofview.Goal.concl gl in
  let evl =
    match ido with
      | None -> evar_list sigma concl
      | Some (id, hloc) ->
          let decl = Environ.lookup_named id env in
            match hloc with
                InHyp ->
                  (match decl with
                    | LocalAssum (_,typ) -> evar_list sigma (EConstr.of_constr typ)
                    | _ -> user_err Pp.(str "Please be more specific: in type or value?"))
              | InHypTypeOnly ->
                  evar_list sigma (EConstr.of_constr (NamedDecl.get_type decl))
              | InHypValueOnly ->
                  (match decl with
                    | LocalDef (_,body,_) -> evar_list sigma (EConstr.of_constr body)
                    | _ -> user_err Pp.(str "Not a defined hypothesis.")) in
  if List.length evl < n then
    user_err Pp.(str "Not enough uninstantiated existential variables.");
  if n <= 0 then user_err Pp.(str "Incorrect existential variable index.");
  let evk,_ = List.nth evl (n-1) in
  instantiate_evar evk c
  end

let instantiate_tac_by_name id c =
  Proofview.Goal.enter begin fun gl ->
  let sigma = Proofview.Goal.sigma gl in
  let evk =
    try Evd.evar_key id sigma
    with Not_found -> user_err Pp.(str "Unknown existential variable.") in
  instantiate_evar evk c
  end

let let_evar name typ =
  let src = (Loc.tag Evar_kinds.GoalEvar) in
  Proofview.Goal.enter begin fun gl ->
    let sigma = Tacmach.project gl in
    let env = Proofview.Goal.env gl in
    let sigma, _ = Typing.sort_of env sigma typ in
    let id = match name with
    | Name.Anonymous ->
      let id = Namegen.id_of_name_using_hdchar env sigma typ name in
      Namegen.next_ident_away_in_goal env id (Termops.vars_of_env env)
    | Name.Name id -> id
    in
    let (sigma, evar) = Evarutil.new_evar env sigma ~src ~naming:(Namegen.IntroFresh id) typ in
    Tacticals.tclTHEN (Proofview.Unsafe.tclEVARS sigma)
    (Tactics.pose_tac (Name.Name id) evar)
  end
