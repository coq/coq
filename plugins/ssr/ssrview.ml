(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names

open Ltac_plugin

open Proofview
open Notations

open Ssrcommon
open Ssrast

module AdaptorDb = struct

  type kind = Forward | Backward | Equivalence

  module AdaptorKind = struct
    type t = kind
    let compare = Pervasives.compare
  end
  module AdaptorMap = Map.Make(AdaptorKind)

  let term_view_adaptor_db =
    Summary.ref ~name:"view_adaptor_db" AdaptorMap.empty

  let get k =
    try AdaptorMap.find k !term_view_adaptor_db
    with Not_found -> []

  let cache_adaptor (_, (k, t)) =
    let lk = get k in
    if not (List.exists (Glob_ops.glob_constr_eq t) lk) then
      term_view_adaptor_db := AdaptorMap.add k (t :: lk) !term_view_adaptor_db

  let subst_adaptor ( subst, (k, t as a)) =
    let t' = Detyping.subst_glob_constr subst t in
    if t' == t then a else k, t'

  let classify_adaptor x = Libobject.Substitute x

  let in_db =
    Libobject.declare_object {
       (Libobject.default_object "VIEW_ADAPTOR_DB")
    with
       Libobject.open_function = (fun i o -> if i = 1 then cache_adaptor o);
       Libobject.cache_function = cache_adaptor;
       Libobject.subst_function = subst_adaptor;
       Libobject.classify_function = classify_adaptor }

  let declare kind terms =
    List.iter (fun term -> Lib.add_anonymous_leaf (in_db (kind,term)))
      (List.rev terms)

end

(* Forward View application code *****************************************)

module State : sig

  (* View storage API *)
  val vsINIT    : EConstr.t * Id.t list -> unit tactic
  val vsPUSH    : (EConstr.t -> (EConstr.t * Id.t list) tactic) -> unit tactic
  val vsCONSUME : (name:Id.t option -> EConstr.t -> to_clear:Id.t list -> unit tactic) -> unit tactic
  val vsASSERT_EMPTY : unit tactic

end = struct (* {{{ *)

type vstate = {
  subject_name : Id.t option;   (* top *)
    (* None if views are being applied to a term *)
  view : EConstr.t;  (* v2 (v1 top) *)
  to_clear : Id.t list;
}

include Ssrcommon.MakeState(struct
  type state = vstate option
  let init = None
end)

let vsINIT (view, to_clear) =
  tclSET (Some { subject_name = None; view; to_clear })

let vsPUSH k =
  tacUPDATE (fun s -> match s with
  | Some { subject_name; view; to_clear } ->
      k view >>= fun (view, clr) ->
      tclUNIT (Some { subject_name; view; to_clear = to_clear @ clr })
  | None ->
      Goal.enter_one ~__LOC__ begin fun gl ->
        let concl = Goal.concl gl in
        let id = (* We keep the orig name for checks in "in" tcl *)
          match EConstr.kind_of_type (Goal.sigma gl) concl with
          | Term.ProdType(Name.Name id, _, _)
            when Ssrcommon.is_discharged_id id -> id
          | _ -> mk_anon_id "view_subject" (Tacmach.New.pf_ids_of_hyps gl) in
        let view = EConstr.mkVar id in
        Ssrcommon.tclINTRO_ID id <*>
        k view >>= fun (view, to_clear) ->
        tclUNIT (Some { subject_name = Some id; view; to_clear })
      end)

let vsCONSUME k =
  tclGET (fun s -> match s with
  | Some { subject_name; view; to_clear } ->
        tclSET None <*>
        k ~name:subject_name view ~to_clear
  | None -> anomaly "vsCONSUME: empty storage")

let vsASSERT_EMPTY =
  tclGET (function
  | Some _ -> anomaly ("vsASSERT_EMPTY: not empty")
  | _ -> tclUNIT ())

end (* }}} *)

let intern_constr_expr { Genintern.genv; ltacvars = vars } sigma ce =
  let ltacvars = {
    Constrintern.empty_ltac_sign with Constrintern.ltac_vars = vars } in
  Constrintern.intern_gen Pretyping.WithoutTypeConstraint ~ltacvars genv sigma ce

(* Disambiguation of /t
    - t is ltac:(tactic args)
    - t is a term
   To allow for t being a notation, like "Notation foo x := ltac:(foo x)", we
   need to internalize t.
*)
let is_tac_in_term { body; glob_env; interp_env } =
  Goal.(enter_one ~__LOC__ begin fun goal ->
    let genv = env goal in
    let sigma = sigma goal in
    let ist = Ssrcommon.option_assert_get glob_env (Pp.str"not a term") in
    (* We use the env of the goal, not the global one *)
    let ist = { ist with Genintern.genv } in
    (* We unravel notations *)
    let g = intern_constr_expr ist sigma body in
    match DAst.get g with
    | Glob_term.GHole (_,_, Some x)
      when Genarg.has_type x (Genarg.glbwit Tacarg.wit_tactic)
        -> tclUNIT (`Tac (Genarg.out_gen (Genarg.glbwit Tacarg.wit_tactic) x))
    | _ -> tclUNIT (`Term (interp_env, g))
end)

(* To inject a constr into a glob_constr we use an Ltac variable *)
let tclINJ_CONSTR_IST ist p =
  let fresh_id = Ssrcommon.mk_internal_id "ssr_inj_constr_in_glob" in
  let ist = {
    ist with Geninterp.lfun =
      Id.Map.add fresh_id (Taccoerce.Value.of_constr p) ist.Geninterp.lfun} in
  tclUNIT (ist,Glob_term.GVar fresh_id)

let mkGHole =
  DAst.make
    (Glob_term.GHole(Evar_kinds.InternalHole, Namegen.IntroAnonymous, None))
let rec mkGHoles n = if n > 0 then mkGHole :: mkGHoles (n - 1) else []
let mkGApp f args =
  if args = [] then f
  else DAst.make (Glob_term.GApp (f, args))

(* From glob_constr to open_constr === (env,sigma,constr) *)
let interp_glob ist glob = Goal.enter_one ~__LOC__ begin fun goal ->
  let env = Goal.env goal in
  let sigma = Goal.sigma goal in
  Ssrprinters.ppdebug (lazy
    Pp.(str"interp-in: " ++ Printer.pr_glob_constr_env env glob));
  try
    let sigma,term = Tacinterp.interp_open_constr ist env sigma (glob,None) in
    Ssrprinters.ppdebug (lazy
      Pp.(str"interp-out: " ++ Printer.pr_econstr_env env sigma term));
    tclUNIT (env,sigma,term)
  with e ->
    Ssrprinters.ppdebug (lazy
    Pp.(str"interp-err: " ++ Printer.pr_glob_constr_env env glob));
     tclZERO e
end

(* Commits the term to the monad *)
(* I think we should make the API safe by storing here the original evar map,
 * so that one cannot commit it wrongly.
 * We could also commit the term automatically, but this makes the code less
 * modular, see the 2 functions below that would need to "uncommit" *)
let tclKeepOpenConstr (_env, sigma, t) = Unsafe.tclEVARS sigma <*> tclUNIT t

let tclADD_CLEAR_IF_ID (env, ist, t) x =
  Ssrprinters.ppdebug (lazy
    Pp.(str"tclADD_CLEAR_IF_ID: " ++ Printer.pr_econstr_env env ist t));
  let hd, _ = EConstr.decompose_app ist t in
  match EConstr.kind ist hd with
  | Constr.Var id when Ssrcommon.not_section_id id -> tclUNIT (x, [id])
  | _ -> tclUNIT (x,[])

let tclPAIR p x = tclUNIT (x, p)

(* The ssr heuristic : *)
(* Estimate a bound on the number of arguments of a raw constr. *)
(* This is not perfect, because the unifier may fail to         *)
(* typecheck the partial application, so we use a minimum of 5. *)
(* Also, we don't handle delayed or iterated coercions to       *)
(* FUNCLASS, which is probably just as well since these can     *)
(* lead to infinite arities.                                    *)
let guess_max_implicits ist glob =
  Proofview.tclORELSE
    (interp_glob ist (mkGApp glob (mkGHoles 6)) >>= fun (env,sigma,term) ->
     let term_ty = Retyping.get_type_of env sigma term in
     let ctx, _ = Reductionops.splay_prod env sigma term_ty in
     tclUNIT (List.length ctx + 6))
  (fun _ -> tclUNIT 5)

let pad_to_inductive ist glob = Goal.enter_one ~__LOC__ begin fun goal ->
  interp_glob ist glob >>= fun (env, sigma, term as ot) ->
  let term_ty = Retyping.get_type_of env sigma term in
  let ctx, i = Reductionops.splay_prod env sigma term_ty in
  let rel_ctx =
    List.map (fun (a,b) -> Context.Rel.Declaration.LocalAssum(a,b)) ctx in
  if not (Ssrcommon.isAppInd (EConstr.push_rel_context rel_ctx env) sigma i)
  then Tacticals.New.tclZEROMSG Pp.(str"not an inductive")
  else tclUNIT (mkGApp glob (mkGHoles (List.length ctx)))
       >>= tclADD_CLEAR_IF_ID ot
end

(* There are two ways of "applying" a view to term:            *)
(*  1- using a view hint if the view is an instance of some    *)
(*     (reflection) inductive predicate.                       *)
(*  2- applying the view if it coerces to a function, adding   *)
(*     implicit arguments.                                     *)
(* They require guessing the view hints and the number of      *)
(* implicits, respectively, which we do by brute force.        *)
(* Builds v p *)
let interp_view ~clear_if_id ist v p =
  let is_specialize hd =
    match DAst.get hd with Glob_term.GHole _ -> true | _ -> false in
  (* We cast the pile of views p into a term p_id *)
  tclINJ_CONSTR_IST ist p >>= fun (ist, p_id) ->
  let p_id = DAst.make p_id in
  match DAst.get v with
  | Glob_term.GApp (hd, rargs) when is_specialize hd ->
     Ssrprinters.ppdebug (lazy Pp.(str "specialize"));
     interp_glob ist (mkGApp p_id rargs)
     >>= tclKeepOpenConstr >>= tclPAIR []
  | _ ->
     Ssrprinters.ppdebug (lazy Pp.(str "view"));
     (* We find out how to build (v p) eventually using an adaptor *)
     let adaptors = AdaptorDb.(get Forward) in
     Proofview.tclORELSE
       (pad_to_inductive ist v >>= fun (vpad,clr) ->
        Ssrcommon.tclFIRSTa (List.map
          (fun a -> interp_glob ist (mkGApp a [vpad; p_id])) adaptors)
        >>= tclPAIR clr)
       (fun _ ->
        guess_max_implicits ist v >>= fun n ->
        Ssrcommon.tclFIRSTi (fun n ->
           interp_glob ist (mkGApp v (mkGHoles n @ [p_id]))) n
        >>= fun x -> tclADD_CLEAR_IF_ID x x)
     >>= fun (ot,clr) ->
       if clear_if_id
       then tclKeepOpenConstr ot >>= tclPAIR clr
       else tclKeepOpenConstr ot >>= tclPAIR []

(* we store in the state (v top), then (v1 (v2 top))... *)
let pile_up_view ~clear_if_id (ist, v) =
  let ist = Ssrcommon.option_assert_get ist (Pp.str"not a term") in
  State.vsPUSH (fun p -> interp_view ~clear_if_id ist v p)

let finalize_view s0 ?(simple_types=true) p =
Goal.enter_one ~__LOC__ begin fun g ->
  let env = Goal.env g in
  let sigma = Goal.sigma g in
  let evars_of_p = Evd.evars_of_term (EConstr.to_constr ~abort_on_undefined_evars:false sigma p) in
  let filter x _ = Evar.Set.mem x evars_of_p in
  let sigma = Typeclasses.resolve_typeclasses ~fail:false ~filter env sigma in
  let p = Reductionops.nf_evar sigma p in
  let get_body = function Evd.Evar_defined x -> x | _ -> assert false in
  let evars_of_econstr sigma t =
    Evarutil.undefined_evars_of_term sigma (EConstr.of_constr t) in
  let rigid_of s =
    List.fold_left (fun l k ->
      if Evd.is_defined sigma k then
        let bo = get_body Evd.(evar_body (find sigma k)) in
          k :: l @ Evar.Set.elements (evars_of_econstr sigma (EConstr.Unsafe.to_constr bo))
      else l
    ) [] s in
  let und0 = (* Unassigned evars in the initial goal *)
    let sigma0 = Tacmach.project s0 in
    let g0info = Evd.find sigma0 (Tacmach.sig_it s0) in
    let g0 = Evd.evars_of_filtered_evar_info g0info in
    List.filter (fun k -> Evar.Set.mem k g0)
      (List.map fst (Evar.Map.bindings (Evd.undefined_map sigma0))) in
  let rigid = rigid_of und0 in
  let n, p, to_prune, _ucst = pf_abs_evars2 s0 rigid (sigma, p) in
  let p = if simple_types then pf_abs_cterm s0 n p else p in
  Ssrprinters.ppdebug (lazy Pp.(str"view@finalized: " ++
    Printer.pr_econstr_env env sigma p));
  let sigma = List.fold_left Evd.remove sigma to_prune in
  Unsafe.tclEVARS sigma <*>
  tclUNIT p
end

let pose_proof subject_name p =
  Tactics.generalize [p] <*>
  Option.cata
    (fun id -> Ssrcommon.tclRENAME_HD_PROD (Name.Name id)) (tclUNIT())
    subject_name
  <*>
  Tactics.New.reduce_after_refine

let rec apply_all_views ~clear_if_id ending vs s0 =
  match vs with
  | [] -> ending s0
  | v :: vs ->
      Ssrprinters.ppdebug (lazy Pp.(str"piling..."));
      is_tac_in_term v >>= function
      | `Tac tac ->
           Ssrprinters.ppdebug (lazy Pp.(str"..a tactic"));
           ending s0 <*> Tacinterp.eval_tactic tac <*>
           Ssrcommon.tacSIGMA >>= apply_all_views ~clear_if_id ending vs
      | `Term v ->
           Ssrprinters.ppdebug (lazy Pp.(str"..a term"));
           pile_up_view ~clear_if_id v <*>
           apply_all_views ~clear_if_id ending vs s0

(* Entry points *********************************************************)

let tclIPAT_VIEWS ~views:vs ?(clear_if_id=false) ~conclusion:tac =
  let end_view_application s0 =
    State.vsCONSUME (fun ~name t ~to_clear ->
      let to_clear = Option.cata (fun x -> [x]) [] name @ to_clear in
      finalize_view s0 t >>= pose_proof name <*> tac ~to_clear) in
  tclINDEPENDENT begin
    State.vsASSERT_EMPTY <*>
    Ssrcommon.tacSIGMA >>=
      apply_all_views ~clear_if_id end_view_application vs <*>
    State.vsASSERT_EMPTY
  end

let tclWITH_FWD_VIEWS ~simple_types ~subject ~views:vs ~conclusion:tac =
  let ending_tac s0 =
    State.vsCONSUME (fun ~name:_ t ~to_clear:_ ->
      finalize_view s0 ~simple_types t >>= tac) in
  tclINDEPENDENT begin
    State.vsASSERT_EMPTY <*>
    State.vsINIT (subject,[]) <*>
    Ssrcommon.tacSIGMA >>=
      apply_all_views ~clear_if_id:false ending_tac vs <*>
    State.vsASSERT_EMPTY
  end

(* vim: set filetype=ocaml foldmethod=marker: *)
