(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open CErrors
open Genarg
open Names
open Proofview.Notations
open Tac2expr

exception LtacError of KerName.t * valexpr

let val_exn = Geninterp.Val.create "ltac2:exn"

type environment = valexpr Id.Map.t

let empty_environment = Id.Map.empty

let push_name ist id v = match id with
| Anonymous -> ist
| Name id -> Id.Map.add id v ist

let get_var ist id =
  try Id.Map.find id ist with Not_found ->
    anomaly (str "Unbound variable " ++ Id.print id)

let get_ref ist kn =
  try pi2 (Tac2env.interp_global kn) with Not_found ->
    anomaly (str "Unbound reference" ++ KerName.print kn)

let return = Proofview.tclUNIT

let rec interp ist = function
| GTacAtm (AtmInt n) -> return (ValInt n)
| GTacAtm (AtmStr s) -> return (ValStr (Bytes.of_string s))
| GTacVar id -> return (get_var ist id)
| GTacRef qid -> return (get_ref ist qid)
| GTacFun (ids, e) ->
  let cls = { clos_env = ist; clos_var = ids; clos_exp = e } in
  return (ValCls cls)
| GTacApp (f, args) ->
  interp ist f >>= fun f ->
  Proofview.Monad.List.map (fun e -> interp ist e) args >>= fun args ->
  interp_app f args
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
    let cls = { clos_env = ist; clos_var = ids; clos_exp = e } in
    na, cls
  | _ -> anomaly (str "Ill-formed recursive function")
  in
  let fixs = List.map map el in
  let fold accu (na, cls) = match na with
  | Anonymous -> accu
  | Name id -> Id.Map.add id (ValCls cls) accu
  in
  let ist = List.fold_left fold ist fixs in
  (** Hack to make a cycle imperatively in the environment *)
  let iter (_, e) = e.clos_env <- ist in
  let () = List.iter iter fixs in
  interp ist e
| GTacTup [] ->
  return (ValInt 0)
| GTacTup el | GTacArr el ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  return (ValBlk (0, Array.of_list el))
| GTacCst (_, n, []) -> return (ValInt n)
| GTacCst (_, n, el) ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  return (ValBlk (n, Array.of_list el))
| GTacCse (e, _, cse0, cse1) ->
  interp ist e >>= fun e -> interp_case ist e cse0 cse1
| GTacPrj (_, e, p) ->
  interp ist e >>= fun e -> interp_proj ist e p
| GTacSet (_, e, p, r) ->
  interp ist e >>= fun e ->
  interp ist r >>= fun r ->
  interp_set ist e p r
| GTacPrm (ml, el) ->
  Proofview.Monad.List.map (fun e -> interp ist e) el >>= fun el ->
  Tac2env.interp_primitive ml el
| GTacExt e ->
  let GenArg (Glbwit tag, e) = e in
  let tpe = Tac2env.interp_ml_object tag in
  tpe.Tac2env.ml_interp ist e >>= fun e -> return (ValExt e)

and interp_app f args = match f with
| ValCls { clos_env = ist; clos_var = ids; clos_exp = e } ->
  let rec push ist ids args = match ids, args with
  | [], [] -> interp ist e
  | [], _ :: _ -> interp ist e >>= fun f -> interp_app f args
  | _ :: _, [] ->
    let cls = { clos_env = ist; clos_var = ids; clos_exp = e } in
    return (ValCls cls)
  | id :: ids, arg :: args -> push (push_name ist id arg) ids args
  in
  push ist ids args
| ValExt _ | ValInt _ | ValBlk _ | ValStr _ ->
  anomaly (str "Unexpected value shape")

and interp_case ist e cse0 cse1 = match e with
| ValInt n -> interp ist cse0.(n)
| ValBlk (n, args) ->
  let (ids, e) = cse1.(n) in
  let ist = CArray.fold_left2 push_name ist ids args in
  interp ist e
| ValExt _ | ValStr _ | ValCls _ ->
  anomaly (str "Unexpected value shape")

and interp_proj ist e p = match e with
| ValBlk (_, args) ->
  return args.(p)
| ValInt _ | ValExt _ | ValStr _ | ValCls _ ->
  anomaly (str "Unexpected value shape")

and interp_set ist e p r = match e with
| ValBlk (_, args) ->
  let () = args.(p) <- r in
  return (ValInt 0)
| ValInt _ | ValExt _ | ValStr _ | ValCls _ ->
  anomaly (str "Unexpected value shape")
