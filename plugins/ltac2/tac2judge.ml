(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Tac2externals
open Tac2ffi
open Proofview.Notations
open EConstr
open Tac2core

module NamedDecl = Context.Named.Declaration

let return = Proofview.tclUNIT

let ltac2_plugin = "rocq-runtime.plugins.ltac2"

let pname s = { Tac2expr.mltac_plugin = ltac2_plugin; mltac_tactic = s }

let define s = define (pname s)

(** Auto printers *)

let pp_local_env env sigma (local_env:local_env) =
  let env = reset_local_env env local_env in
  Printer.pr_context_of env sigma

let pp_termj genv sigma {env; term; typ} =
  let open Pp in
  let env = reset_local_env genv env in
  hov 2
    (Printer.pr_context_of env sigma ++ str " |-" ++ spc() ++
     Printer.pr_econstr_env ~inctx:true env sigma term ++
     str " :" ++ spc() ++ Printer.pr_letype_env env sigma typ)

let pp_typej genv sigma {env; term; typ} = pp_termj genv sigma {env; term; typ=mkSort typ}

let () = Tac2print.register_val_printer Tac2quote.Refs.t_env { val_printer = fun env sigma v _ ->
    pp_local_env env sigma (repr_to local_env v) }
let () = Tac2print.register_val_printer Tac2quote.Refs.t_termj { val_printer = fun env sigma v _ ->
    pp_termj env sigma (repr_to termj v) }
let () = Tac2print.register_val_printer Tac2quote.Refs.t_typej { val_printer = fun env sigma v _ ->
    pp_typej env sigma (repr_to typej v) }

(** Externals *)

let () = define "env_of_termj" (termj @-> ret local_env) @@ fun t -> t.env

let () = define "env_of_typej" (typej @-> ret local_env) @@ fun t -> t.env

let () = define "env_hyps" (local_env @-> ret (list ident)) @@ fun env ->
  List.map NamedDecl.get_id env.local_named.env_named_ctx

let ret_err e = return (Error (Exninfo.capture e))

let catch_to_result f env sigma =
  try Proofview.Monad.map (fun x -> Ok x) (f env sigma)
  with e ->
    let e, info = Exninfo.capture e in
    set_bt info >>= fun info ->
    return (Error (e,info))

let () = define "hypj" (ident @-> local_env @-> tac (result termj)) @@ fun id ctx ->
  match EConstr.lookup_named_val id ctx.local_named with
  | exception Not_found ->
    ret_err @@
    err_invalid_arg (Some Pp.(str "Hypothesis " ++ quote (Id.print id) ++ str " not found"))
  | d ->
    let t = NamedDecl.get_type d in
    return (Ok { env = ctx; term = mkVar id; typ=t })

let () = define "hyp_valuej" (local_env @-> ident @-> tac (result (option termj))) @@ fun ctx id ->
  pf_apply_in ctx @@ fun env _ ->
  match EConstr.lookup_named id env with
  | exception Not_found ->
    ret_err @@
    err_invalid_arg (Some Pp.(str "Hypothesis " ++ quote (Id.print id) ++ str " not found"))
  | LocalAssum _ -> return (Ok None)
  | LocalDef (_,bdy,typ) -> return (Ok (Some { env = ctx; term = bdy; typ }))

let () = define "infer_termj" (local_env @-> constr @-> tac (result termj)) @@ fun ctx c ->
  pf_apply_in ctx @@ catch_to_result @@ fun env sigma ->
  let sigma, t = Typing.type_of env sigma c in
  Proofview.Unsafe.tclEVARS sigma <*>
  return { env = ctx; term = c; typ = t }

let () = define "termj_is_typej" (termj @-> tac (result typej)) @@ fun { env = ctx; term; typ } ->
  pf_apply_in ctx @@ catch_to_result @@ fun env sigma ->
  let sigma, tj = Typing.type_judgment env sigma (Environ.make_judge term typ) in
  Proofview.Unsafe.tclEVARS sigma <*>
  return { env = ctx; term = tj.utj_val; typ = tj.utj_type }

let () = define "typej_is_termj" (typej @-> ret termj) @@ fun { env; term; typ } ->
  { env; term; typ = mkSort typ }

let () = define "typej_of_termj" (termj @-> tac typej) @@ fun j ->
  pf_apply_in j.env @@ fun env sigma ->
  let s = Retyping.get_sort_of env sigma j.typ in
  return { env = j.env; term = j.typ; typ = s }

let () = define "sort_of_typej" (typej @-> ret sort) @@ fun j -> j.typ

let () = define "typej_of_sort" (local_env @-> sort @-> ret typej) @@ fun ctx s ->
  { env = ctx; term = mkSort s; typ = (ESorts.make @@ Sorts.super @@ EConstr.Unsafe.to_sorts s) }

let push_named_assum_tac ctx id t r =
  if Id.Map.mem id ctx.local_named.env_named_map then
    Tac2core.throw
      (err_invalid_arg
         (Some Pp.(str "Ltac2 judgement push_named_assum: " ++ Id.print id ++ str " not free.")))
  else
    let idr = Context.make_annot id r in
    let local_named = EConstr.push_named_context_val (LocalAssum (idr,t)) ctx.local_named in
    return { local_named; local_rel = ctx.local_rel }

let () =
  define "unsafe_push_named_assum" (local_env @-> ident @-> constr @-> relevance @-> tac local_env) @@ fun ctx id t r ->
  push_named_assum_tac ctx id t (ERelevance.make r)

let () = define "push_named_assum" (ident @-> typej @-> tac local_env) @@ fun id j ->
  Proofview.tclEVARMAP >>= fun sigma ->
  if not (CList.is_empty j.env.local_rel.env_rel_ctx) && not (Vars.closed0 sigma j.term) then
    (* is_empty test is a fast path, incorrect with unsafe terms but good enough in the safe case *)
    Tac2core.throw
      (err_invalid_arg
         (Some Pp.(str "Ltac2 judgement push_named_assum: non closed type.")))
  else
    push_named_assum_tac j.env id j.term (ESorts.relevance_of_sort j.typ)

let push_named_def_tac ctx id c t r =
  Proofview.tclEVARMAP >>= fun sigma ->
  if Id.Map.mem id ctx.local_named.env_named_map then
    Tac2core.throw
      (err_invalid_arg
         (Some Pp.(str "Ltac2 judgement push_named_def: " ++ Id.print id ++ str " not free.")))
  else
    let idr = Context.make_annot id r in
    let local_named = EConstr.push_named_context_val (LocalDef (idr,c,t)) ctx.local_named in
    return { local_named; local_rel = ctx.local_rel }

let () = define "unsafe_push_named_def" (local_env @-> ident @-> constr @-> constr @-> relevance @-> tac local_env) @@ fun ctx id c t r ->
  push_named_def_tac ctx id c t (ERelevance.make r)

let () = define "push_named_def" (ident @-> termj @-> tac local_env) @@ fun id j ->
  pf_apply_in j.env @@ fun env sigma ->
  if not (CList.is_empty j.env.local_rel.env_rel_ctx) &&
     (not (Vars.closed0 sigma j.typ) || not (Vars.closed0 sigma j.term)) then
    (* is_empty test is a fast path, incorrect with unsafe terms but good enough in the safe case *)
    Tac2core.throw
      (err_invalid_arg
         (Some Pp.(str "Ltac2 judgement push_named_def: non closed argument.")))
  else
    push_named_def_tac j.env id j.term j.typ (Retyping.relevance_of_term env sigma j.term)

let understand_uconstr_ty ~flags ~expected_type env sigma c =
  let open Ltac_pretype in
  let { closure; term } = c in
  let vars = {
    ltac_constrs = closure.typed;
    ltac_uconstrs = closure.untyped;
    ltac_idents = closure.idents;
    ltac_genargs = closure.genargs;
  } in
  Pretyping.understand_ltac_ty flags env sigma vars expected_type term

let () = define "pretype_judge" (pretype_flags @-> local_env @-> preterm @-> tac (result termj)) @@ fun flags ctx c ->
  pf_apply_in ctx @@ catch_to_result @@ fun env sigma ->
  let sigma, t, typ =
    understand_uconstr_ty ~flags ~expected_type:WithoutTypeConstraint env sigma c
  in
  let res = { env = ctx; term = t; typ } in
  Proofview.Unsafe.tclEVARS sigma <*>
  return res

let () = define "pretype_type_judge" (pretype_flags @-> local_env @-> preterm @-> tac (result typej)) @@ fun flags ctx c ->
  pf_apply_in ctx @@ catch_to_result @@ fun env sigma ->
  let sigma, t, ty =
    understand_uconstr_ty ~flags ~expected_type:IsType env sigma c
  in
  let s = destSort sigma ty in
  let res = { env = ctx; term = t; typ = s } in
  Proofview.Unsafe.tclEVARS sigma <*>
  return res

let () = define "pretype_in_expecting" (pretype_flags @-> preterm @-> typej @-> tac (result termj)) @@ fun flags c { env = ctx; term=ty; typ=s } ->
  pf_apply_in ctx @@ catch_to_result @@ fun env sigma ->
  let sigma, t, ty =
    understand_uconstr_ty ~flags ~expected_type:(OfType ty) env sigma c
  in
  let res = { env = ctx; term = t; typ = ty } in
  Proofview.Unsafe.tclEVARS sigma <*>
  return res

let () = define "message_of_env" (local_env @-> tac pp) @@ fun ctx ->
  pf_apply_in ctx @@ fun env sigma -> return (Printer.pr_context_of env sigma)

let () = define "message_of_constr_in_env" (local_env @-> constr @-> tac pp) @@ fun ctx c ->
  pf_apply_in ctx @@ fun env sigma -> return (Printer.pr_econstr_env env sigma c)

let () = define "term_of_termj" (termj @-> ret constr) @@ fun t -> t.term

let () = define "type_of_typej" (typej @-> ret constr) @@ fun t -> t.term

let () = define "unsafe_typej" (local_env @-> constr @-> sort @-> ret typej) @@ fun ctx t s ->
  { env = ctx; term=t; typ=s }

let () = define "unsafe_termj" (constr @-> typej @-> ret termj) @@ fun c j ->
  { env = j.env; term=c; typ=j.term }
