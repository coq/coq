(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Ltac_plugin

type _ ffi =
| Arg : ('a,'b,'c) Genarg.genarg_type * 'f ffi -> ('c -> 'f) ffi
| Nil : unit Proofview.tactic ffi

let rec length : type a. a ffi -> int =
  function Nil -> 0 | Arg(_,x) -> 1 + length x

let to_ltac name ffi f args =
  let rec aux
    : type a. a ffi -> a -> Geninterp.Val.t list -> unit Proofview.tactic
    = fun ffi f args ->
    match ffi with
    | Nil ->
        begin match args with
        | [] -> f
        | _::_ ->
           CErrors.anomaly ~label:"ssreflect"
             Pp.(str "FFI: too many arguments: " ++ str name) end
    | Arg(w,ffi) ->
        begin match args with
        | x :: xs ->
           let arg = Tacinterp.Value.cast (Genarg.topwit w) x in
           aux ffi (f arg) xs
        | [] ->
           CErrors.anomaly ~label:"ssreflect"
             Pp.(str "FFI: too few arguments: " ++ str name) end
  in
    aux ffi f args

let report_errors db_name = function
  | [] -> CErrors.anomaly Pp.(str "tclFIRST_WITH_ERRORS on an empty list")
  | [e] -> Util.iraise e
  | l -> CErrors.user_err ~hdr:"ssreflect"
           Pp.(str "Using the hint base " ++ str db_name ++
               str " the following errors were raised:" ++ fnl () ++ fnl () ++
               prlist_with_sep (fun () -> fnl () ++ fnl ()) CErrors.iprint
                 (List.map ExplainErr.process_vernac_interp_error (List.rev l)))

let rec tclFIRST_WITH_ERRORS n errors = function
  | [] -> report_errors n errors
  | x :: xs ->
      Proofview.tclORELSE x (fun e -> tclFIRST_WITH_ERRORS n (e::errors) xs)

let locate_tac_db name sigma goal secvars args =
  let db =
    try Hints.searchtable_map name
    with Not_found ->
      CErrors.anomaly ~label:"ssreflect"
        Pp.(str"hint db " ++ str name ++
            str " not declared (should be in ssreflect.v)") in
  let hs =
    match Hints.decompose_app_bound sigma goal with
    | Some goal_skel -> Hints.Hint_db.map_eauto sigma ~secvars goal_skel goal db
    | None -> Hints.Hint_db.map_none ~secvars db in
  if hs = [] then CErrors.anomaly Pp.(str "empty hint db " ++ str name);
  tclFIRST_WITH_ERRORS name []
    (hs |> List.map (fun h -> Hints.run_hint h.Hints.code (function
      | Hints.Extern ({ Hints.arg_names } as tac) ->
          if List.length arg_names != List.length args then
            CErrors.user_err ~hdr:"ssreflect"
              Pp.(str"wrong number of arguments for tactic " ++ str name);
          let args =
            List.fold_left2 (fun m id t -> Id.Map.add id t m)
              Id.Map.empty arg_names args in
          Auto.conclPattern args goal h.Hints.pat tac
      | _ -> CErrors.user_err ~hdr:"ssreflect"
            Pp.(str"only Hint Extern can be declared for " ++ str name))))

let call_tac name args : unit Proofview.tactic =
  Proofview.Goal.enter (fun gl ->
    let sigma = Proofview.Goal.sigma gl in
    let goal = Proofview.Goal.concl gl in
    let secvars = Auto.compute_secvars gl in
    locate_tac_db name sigma goal secvars args)

let to_ml name ffi =
  let rec aux : type a. a ffi -> Geninterp.Val.t list -> a
  = fun ffi args ->
    match ffi with
    | Nil -> call_tac name (List.rev args)
    | Arg(w,ffi) ->
        let open Geninterp in
        fun x ->
          let x = Val.inject (val_tag (Genarg.topwit w)) x in
          aux ffi (x :: args)
  in
    aux ffi []

let register_overloaded name ffi tac =
  let bios_ml = "ssreflect_plugin" in
  let name = "ssr_" ^ name in
  let nargs = length ffi in
  let args = CList.init nargs (fun i ->
               Id.of_string (Printf.sprintf "%s_arg_%d" name i)) in
  let mltac _ ist =
    let args =
      List.map (fun arg ->
        try Id.Map.find arg ist.Tacinterp.lfun
        with Not_found ->
          CErrors.anomaly Pp.(str "calling convention mismatch: " ++
            str name ++ str " arg " ++ Ppconstr.pr_id arg)
      ) args
    in
      to_ltac name ffi tac args in
  let mltac_name = { Tacexpr.mltac_plugin = bios_ml; mltac_tactic = name; } in
  let () = Tacenv.register_ml_tactic mltac_name [|mltac|] in
  let tac =
    Tacexpr.TacFun (List.map (fun x -> Name.Name x) args,
      Tacexpr.TacML (None,({Tacexpr.mltac_name; mltac_index = 0}, []))) in
  let obj () = Tacenv.register_ltac true false (Id.of_string name) tac in
  Mltop.declare_cache_obj obj bios_ml;
  to_ml name ffi
