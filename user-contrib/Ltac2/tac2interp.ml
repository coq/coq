(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors
open Names
open Proofview.Notations
open Tac2expr
open Tac2ffi

exception LtacError = Tac2ffi.LtacError

let backtrace : backtrace Evd.Store.field = Evd.Store.field ()

let print_ltac2_backtrace = ref false

let get_backtrace =
  Proofview.tclEVARMAP >>= fun sigma ->
  match Evd.Store.get (Evd.get_extra_data sigma) backtrace with
  | None -> Proofview.tclUNIT []
  | Some bt -> Proofview.tclUNIT bt

let set_backtrace bt =
  Proofview.tclEVARMAP >>= fun sigma ->
  let store = Evd.get_extra_data sigma in
  let store = Evd.Store.set store backtrace bt in
  let sigma = Evd.set_extra_data store sigma in
  Proofview.Unsafe.tclEVARS sigma

let with_frame frame tac =
  if !print_ltac2_backtrace then
    get_backtrace >>= fun bt ->
    set_backtrace (frame :: bt) >>= fun () ->
    tac >>= fun ans ->
    set_backtrace bt >>= fun () ->
    Proofview.tclUNIT ans
  else tac

type environment = Tac2env.environment = {
  env_ist : valexpr Id.Map.t;
}

let empty_environment = {
  env_ist = Id.Map.empty;
}

type closure = {
  mutable clos_env : valexpr Id.Map.t;
  (** Mutable so that we can implement recursive functions imperatively *)
  clos_var : Name.t list;
  (** Bound variables *)
  clos_exp : glb_tacexpr;
  (** Body *)
  clos_ref : ltac_constant option;
  (** Global constant from which the closure originates *)
}

let push_name ist id v = match id with
| Anonymous -> ist
| Name id -> { env_ist = Id.Map.add id v ist.env_ist }

let get_var ist id =
  try Id.Map.find id ist.env_ist with Not_found ->
    anomaly (str "Unbound variable " ++ Id.print id)

let get_ref ist kn =
  try
    let data = Tac2env.interp_global kn in
    data.Tac2env.gdata_expr
  with Not_found ->
    anomaly (str "Unbound reference" ++ KerName.print kn)

let return = Proofview.tclUNIT

let rec interp (ist : environment) = function
| GTacAtm (AtmInt n) -> return (Tac2ffi.of_int n)
| GTacAtm (AtmStr s) -> return (Tac2ffi.of_string (Bytes.of_string s))
| GTacVar id -> return (get_var ist id)
| GTacRef kn ->
  let data = get_ref ist kn in
  return (eval_pure (Some kn) data)
| GTacFun (ids, e) ->
  let cls = { clos_ref = None; clos_env = ist.env_ist; clos_var = ids; clos_exp = e } in
  let f = interp_app cls in
  return (Tac2ffi.of_closure f)
| GTacApp (f, args) ->
  interp ist f >>= fun f ->
  Proofview.Monad.List.map (fun e -> interp ist e) args >>= fun args ->
  Tac2ffi.apply (Tac2ffi.to_closure f) args
| GTacLet (false, el, e) ->
  let fold accu (na, e) =
    interp ist e >>= fun e ->
    return (push_name accu na e)
  in
  Proofview.Monad.List.fold_left fold ist el >>= fun ist ->
  interp ist e
| GTacLet (true, el, e) ->
  let map (na, e) = match e with
  | GTacFun (ids, e) ->
    let cls = { clos_ref = None; clos_env = ist.env_ist; clos_var = ids; clos_exp = e } in
    let f = Tac2ffi.of_closure (interp_app cls) in
    na, cls, f
  | _ -> anomaly (str "Ill-formed recursive function")
  in
  let fixs = List.map map el in
  let fold accu (na, _, cls) = match na with
  | Anonymous -> accu
  | Name id -> { env_ist = Id.Map.add id cls accu.env_ist }
  in
  let ist = List.fold_left fold ist fixs in
  (* Hack to make a cycle imperatively in the environment *)
  let iter (_, e, _) = e.clos_env <- ist.env_ist in
  let () = List.iter iter fixs in
  interp ist e
| GTacCst (_, n, []) -> return (Valexpr.make_int n)
| GTacCst (_, n, el) ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  return (Valexpr.make_block n (Array.of_list el))
| GTacCse (e, _, cse0, cse1) ->
  interp ist e >>= fun e -> interp_case ist e cse0 cse1
| GTacWth { opn_match = e; opn_branch = cse; opn_default = def } ->
  interp ist e >>= fun e -> interp_with ist e cse def
| GTacPrj (_, e, p) ->
  interp ist e >>= fun e -> interp_proj ist e p
| GTacSet (_, e, p, r) ->
  interp ist e >>= fun e ->
  interp ist r >>= fun r ->
  interp_set ist e p r
| GTacOpn (kn, el) ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  return (Tac2ffi.of_open (kn, Array.of_list el))
| GTacPrm (ml, el) ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  with_frame (FrPrim ml) (Tac2ffi.apply (Tac2env.interp_primitive ml) el)
| GTacExt (tag, e) ->
  let tpe = Tac2env.interp_ml_object tag in
  with_frame (FrExtn (tag, e)) (tpe.Tac2env.ml_interp ist e)

and interp_app f =
  let ans = fun args ->
    let { clos_env = ist; clos_var = ids; clos_exp = e; clos_ref = kn } = f in
    let frame = match kn with
    | None -> FrAnon e
    | Some kn -> FrLtac kn
    in
    let ist = { env_ist = ist } in
    let ist = List.fold_left2 push_name ist ids args in
    with_frame frame (interp ist e)
  in
  Tac2ffi.abstract (List.length f.clos_var) ans

and interp_case ist e cse0 cse1 =
  if Valexpr.is_int e then
    interp ist cse0.(Tac2ffi.to_int e)
  else
    let (n, args) = Tac2ffi.to_block e in
    let (ids, e) = cse1.(n) in
    let ist = CArray.fold_left2 push_name ist ids args in
    interp ist e

and interp_with ist e cse def =
  let (kn, args) = Tac2ffi.to_open e in
  let br = try Some (KNmap.find kn cse) with Not_found -> None in
  begin match br with
  | None ->
    let (self, def) = def in
    let ist = push_name ist self e in
    interp ist def
  | Some (self, ids, p) ->
    let ist = push_name ist self e in
    let ist = CArray.fold_left2 push_name ist ids args in
    interp ist p
  end

and interp_proj ist e p =
  return (Valexpr.field e p)

and interp_set ist e p r =
  let () = Valexpr.set_field e p r in
  return (Valexpr.make_int 0)

and eval_pure kn = function
| GTacAtm (AtmInt n) -> Valexpr.make_int n
| GTacRef kn ->
  let { Tac2env.gdata_expr = e } =
    try Tac2env.interp_global kn
    with Not_found -> assert false
  in
  eval_pure (Some kn) e
| GTacFun (na, e) ->
  let cls = { clos_ref = kn; clos_env = Id.Map.empty; clos_var = na; clos_exp = e } in
  let f = interp_app cls in
  Tac2ffi.of_closure f
| GTacCst (_, n, []) -> Valexpr.make_int n
| GTacCst (_, n, el) -> Valexpr.make_block n (Array.map_of_list eval_unnamed el)
| GTacOpn (kn, el) -> Tac2ffi.of_open (kn, Array.map_of_list eval_unnamed el)
| GTacAtm (AtmStr _) | GTacLet _ | GTacVar _ | GTacSet _
| GTacApp _ | GTacCse _ | GTacPrj _ | GTacPrm _ | GTacExt _ | GTacWth _ ->
  anomaly (Pp.str "Term is not a syntactical value")

and eval_unnamed e = eval_pure None e


(** Cross-boundary hacks. *)

open Geninterp

let val_env : environment Val.typ = Val.create "ltac2:env"
let env_ref = Id.of_string_soft "@@ltac2_env@@"

let extract_env (Val.Dyn (tag, v)) : environment =
match Val.eq tag val_env with
| None -> assert false
| Some Refl -> v

let get_env ist =
  try extract_env (Id.Map.find env_ref ist)
  with Not_found -> empty_environment

let set_env env ist =
  Id.Map.add env_ref (Val.Dyn (val_env, env)) ist
