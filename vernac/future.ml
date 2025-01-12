(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let not_ready_msg = ref (fun name ->
      Pp.strbrk("The value you are asking for ("^name^") is not ready yet. "^
                "Please wait or pass "^
                "the \"-async-proofs off\" option to Rocqide to disable "^
                "asynchronous script processing and don't pass \"-vio\" to "^
                "rocq compile."))
let not_here_msg = ref (fun name ->
      Pp.strbrk("The value you are asking for ("^name^") is not available "^
                "in this process. If you really need this, pass "^
                "the \"-async-proofs off\" option to Rocqide to disable "^
                "asynchronous script processing and don't pass \"-vio\" to "^
                "rocq compile."))

exception NotReady of string
exception NotHere of string

let _ = CErrors.register_handler (function
  | NotReady name -> Some (!not_ready_msg name)
  | NotHere name -> Some (!not_here_msg name)
  | _ -> None)

type fix_exn = Stateid.exn_info option

let eval_fix_exn f (e, info) = match f with
| None -> (e, info)
| Some { Stateid.id; valid } ->
  match Stateid.get info with
  | Some _ -> (e, info)
  | None ->
    let loc = Loc.get_loc info in
    let msg = CErrors.iprint (e, info) in
    let qf = Result.value ~default:[] (Quickfix.from_exception e) in
    let () = Feedback.(feedback ~id (Message (Error, loc, qf, msg))) in
    (e, Stateid.add info ~valid id)

module UUID = struct
  type t = int
  let invalid = 0
  let fresh =
    let count = ref invalid in
    fun () -> incr count; !count

  let compare = compare
  let equal = (==)
end

module UUIDMap = Map.Make(UUID)
module UUIDSet = Set.Make(UUID)

type 'a assignment = [ `Val of 'a | `Exn of Exninfo.iexn | `Comp of (unit -> 'a)]

(* Val is not necessarily a final state, so the
   computation restarts from the state stocked into Val *)
and 'a comp =
  | Delegated of (Mutex.t * Condition.t) option
  | Closure of (unit -> 'a)
  | Val of 'a
  | Exn of Exninfo.iexn  (* Invariant: this exception is always "fixed" as in fix_exn *)

and 'a computation =
  | Ongoing of string * (UUID.t * fix_exn * 'a comp ref) CEphemeron.key

let unnamed = "unnamed"

let create ?(name=unnamed) ?(uuid=UUID.fresh ()) ~fix_exn x =
  Ongoing (name, CEphemeron.create (uuid, fix_exn, ref x))
let get x =
  match x with
  | Ongoing (name, x) ->
      try let uuid, fix, c = CEphemeron.get x in name, uuid, fix, c
      with CEphemeron.InvalidKey ->
        name, UUID.invalid, None, ref (Exn (NotHere name, Exninfo.null))

type 'a value = [ `Val of 'a | `Exn of Exninfo.iexn  ]

let is_over kx = let _, _, _, x = get kx in match !x with
  | Val _ | Exn _ -> true
  | Closure _ | Delegated _ -> false

let is_exn kx = let _, _, _, x = get kx in match !x with
  | Exn _ -> true
  | Val _ | Closure _ | Delegated _ -> false

let peek_val kx = let _, _, _, x = get kx in match !x with
  | Val v -> Some v
  | Exn _ | Closure _ | Delegated _ -> None

let uuid kx = let _, id, _, _ = get kx in id

let from_val v = create ~fix_exn:None (Val v)

let create_delegate ?(blocking=true) ~name fix_exn =
  let sync =
    if blocking then Some (Mutex.create (), Condition.create ())
    else None
  in
  let ck = create ~name ~fix_exn (Delegated sync) in
  let assignment = fun v ->
    let _, _, fix_exn, c = get ck in
    let sync = match !c with Delegated s -> s | _ -> assert false in
    begin match v with
    | `Val v -> c := Val v
    | `Exn e -> c := Exn (eval_fix_exn fix_exn e)
    | `Comp f -> c := Closure f end;
    let iter (lock, cond) = CThread.with_lock lock ~scope:(fun () -> Condition.broadcast cond) in
    Option.iter iter sync
  in
  ck, assignment

(* TODO: get rid of try/catch to be stackless *)
let rec compute ck : 'a value =
  let name, _, fix_exn, c = get ck in
  match !c with
  | Val x -> `Val x
  | Exn (e, info) -> `Exn (e, info)
  | Delegated None -> raise (NotReady name)
  | Delegated (Some (lock, cond)) ->
    CThread.with_lock lock ~scope:(fun () -> Condition.wait cond lock); compute ck
  | Closure f ->
      try
        let data = f () in
        c := Val data; `Val data
      with e ->
        let e = Exninfo.capture e in
        let e = eval_fix_exn fix_exn e in
        match e with
        | (NotReady _, _) -> `Exn e
        | _ -> c := Exn e; `Exn e

let force x = match compute x with
  | `Val v -> v
  | `Exn e -> Exninfo.iraise e

let chain ck f =
  let name, uuid, fix_exn, c = get ck in
  create ~uuid ~name ~fix_exn (match !c with
  | Closure _ | Delegated _ -> Closure (fun () -> f (force ck))
  | Exn _ as x -> x
  | Val v -> Val (f v))

let create ~fix_exn f = create ~fix_exn (Closure f)

let replace kx y =
  let _, _, _, x = get kx in
  match !x with
  | Exn _ -> x := Closure (fun () -> force y)
  | _ -> CErrors.anomaly
           (Pp.str "A computation can be replaced only if is_exn holds.")

let chain x f =
  let y = chain x f in
  if is_over x then ignore(force y);
  y

let print f kx =
  let open Pp in
  let name, uid, _, x = get kx in
  let uid =
    if UUID.equal uid UUID.invalid then str "[#:" ++ str name ++ str "]"
    else str "[" ++ int uid ++ str":" ++ str name ++ str "]"
  in
  match !x with
  | Delegated _ -> str "Delegated" ++ uid
  | Closure _ -> str "Closure" ++ uid
  | Val x -> str "PureVal" ++ uid ++ spc () ++ hov 0 (f x)
  | Exn (e, _) -> str "Exn"  ++ uid ++ spc () ++ hov 0 (str (Printexc.to_string e))
