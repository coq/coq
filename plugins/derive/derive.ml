(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Context.Named.Declaration
open Vernacentries.DefAttributes
open Constrexpr

let check_allowed_implicit ?loc = function
  | Generalized _ | Default (MaxImplicit | NonMaxImplicit) ->
    CErrors.user_err ?loc (Pp.str "Unexpected implicit argument annotation.")
  | Default Explicit -> ()

let check_allowed_binders = function
  | CLocalAssum (n::_, _, impl, _) -> check_allowed_implicit ?loc:n.CAst.loc impl
  | CLocalPattern _ -> () (* a priori acceptable, but interp_named_context_evars_as_arguments does not support it *)
  | CLocalDef (n, _, _, _) -> ()
  | CLocalAssum ([], _, _, _) -> assert false

let rec fill_assumptions env sigma = function
  | [] -> sigma, env, []
  | LocalAssum (na,t) :: ctx ->
    let sigma, ev = Evarutil.new_evar env sigma ~src:(Loc.tag @@ Evar_kinds.GoalEvar) ~typeclass_candidate:false t in
    let decl = LocalDef (na,ev,t) in
    let sigma, env, ctx = fill_assumptions (EConstr.push_named decl env) sigma ctx in
    sigma, env, decl :: ctx
  | LocalDef _ as decl :: ctx ->
    let sigma, env, ctx = fill_assumptions (EConstr.push_named decl env) sigma ctx in
    sigma, env, decl :: ctx

(** [start_deriving f suchthat lemma] starts a proof of [suchthat]
    (which can contain references to [f]) in the context extended by
    [f:=?x]. When the proof ends, [f] is defined as the value of [?x]
    and [lemma] as the proof. *)
let start_deriving ~atts bl suchthat name : Declare.Proof.t =

  let scope, _local, poly, program_mode, user_warns, typing_flags, using, clearbody =
    atts.scope, atts.locality, atts.polymorphic, atts.program, atts.user_warns, atts.typing_flags, atts.using, atts.clearbody in
  if program_mode then CErrors.user_err (Pp.str "Program mode not supported.");

  let env = Global.env () in
  let sigma = Evd.from_env env in
  let () = List.iter check_allowed_binders bl in
  let sigma, (impls_env, ((env', ctx'), _)) = Constrintern.interp_named_context_evars env sigma bl in
  let sigma, env', ctx' = fill_assumptions env sigma ctx' in
  let sigma = Evd.shelve sigma (List.map fst (Evar.Map.bindings (Evd.undefined_map sigma))) in
  let sigma, (suchthat, impargs) = Constrintern.interp_type_evars_impls env' sigma ~impls:impls_env suchthat in
  (* create the initial goals for the proof: |- Type ; |- ?1 ; f:=?2 |- suchthat *)
  let goals =
    let open Proofview in
    let rec aux env sigma = function
      | [] -> TCons ( env , sigma , suchthat , (fun sigma _ -> TNil sigma))
      | LocalAssum (id, t) :: _ -> assert false
      | LocalDef (id, c, t) as d :: ctx ->
        TCons ( env , sigma , t , (fun sigma ef' ->
            let sigma = Evd.define (fst (EConstr.destEvar sigma ef')) c sigma in
            aux (EConstr.push_named d env) sigma ctx)) in
    aux env sigma ctx' in
  let kind = Decls.(IsDefinition Definition) in
  let info = Declare.Info.make ~poly:(Attributes.is_universe_polymorphism ()) ~kind () in
  let extract_manual = function Some Impargs.{ impl_pos = (na,_,_); impl_expl = Manual; impl_max } -> Some (na, impl_max) | _ -> None in
  let cinfo =
    let open Declare.CInfo in
    List.map (fun d ->
        let name = get_id d in
        let impargs = Constrintern.implicits_of_decl_in_internalization_env name impls_env in
        let impargs = List.map CAst.make (List.map extract_manual impargs) in
        make ~name ~typ:() ~impargs ()) ctx' @
    [make ~name ~typ:() ~impargs ()] in
  let lemma = Declare.Proof.start_derive ~name ~info ~cinfo goals in
  Declare.Proof.map lemma ~f:(fun p ->
      Util.pi1 @@ Proof.run_tactic env Proofview.(tclFOCUS 1 1 shelve) p)
