(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* To deal with side effects we have to save/restore the system state *)
let freeze = ref (fun () -> assert false : unit -> Dyn.t)
let unfreeze = ref (fun _ -> () : Dyn.t -> unit)
let set_freeze f g = freeze := f; unfreeze := g

exception NotReady
exception NotHere
let _ = Errors.register_handler (function
  | NotReady ->
      Pp.strbrk("The value you are asking for is not ready yet. " ^
                "Please wait or pass "^
                "the \"-async-proofs off\" option to CoqIDE to disable "^
                "asynchronous script processing.")
  | NotHere ->
      Pp.strbrk("The value you are asking for is not available "^
                "in this process. If you really need this, pass "^
                "the \"-async-proofs off\" option to CoqIDE to disable "^
                "asynchronous script processing.")
  | _ -> raise Errors.Unhandled)

type fix_exn = Exninfo.iexn -> Exninfo.iexn
let id x = prerr_endline "Future: no fix_exn.\nYou have probably created a Future.computation from a value without passing the ~fix_exn argument.  You probably want to chain with an already existing future instead."; x

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

type 'a assignement = [ `Val of 'a | `Exn of Exninfo.iexn | `Comp of 'a computation]

(* Val is not necessarily a final state, so the
   computation restarts from the state stocked into Val *)
and 'a comp =
  | Delegated of (unit -> unit)
  | Closure of (unit -> 'a)
  | Val of 'a * Dyn.t option
  | Exn of Exninfo.iexn  (* Invariant: this exception is always "fixed" as in fix_exn *)

and 'a comput =
  | Ongoing of (UUID.t * fix_exn * 'a comp ref) Ephemeron.key
  | Finished of 'a

and 'a computation = 'a comput ref

let create ?(uuid=UUID.fresh ()) f x =
  ref (Ongoing (Ephemeron.create (uuid, f, Pervasives.ref x)))
let get x =
  match !x with
  | Finished v -> UUID.invalid, id, ref (Val (v,None))
  | Ongoing x ->
      try Ephemeron.get x
      with Ephemeron.InvalidKey ->
        UUID.invalid, id, ref (Exn (NotHere, Exninfo.null))

type 'a value = [ `Val of 'a | `Exn of Exninfo.iexn  ]

let is_over kx = let _, _, x = get kx in match !x with
  | Val _ | Exn _ -> true
  | Closure _ | Delegated _ -> false

let is_val kx = let _, _, x = get kx in match !x with
  | Val _ -> true
  | Exn _ | Closure _ | Delegated _ -> false

let is_exn kx = let _, _, x = get kx in match !x with
  | Exn _ -> true
  | Val _ | Closure _ | Delegated _ -> false

let peek_val kx = let _, _, x = get kx in match !x with
  | Val (v, _) -> Some v
  | Exn _ | Closure _ | Delegated _ -> None

let uuid kx = let id, _, _ = get kx in id

let from_val ?(fix_exn=id) v = create fix_exn (Val (v, None))
let from_here ?(fix_exn=id) v = create fix_exn (Val (v, Some (!freeze ())))

let fix_exn_of ck = let _, fix_exn, _ = get ck in fix_exn

let create_delegate ?(blocking=true) fix_exn =
  let assignement signal ck = fun v ->
    let _, fix_exn, c = get ck in
    assert (match !c with Delegated _ -> true | _ -> false);
    begin match v with
    | `Val v -> c := Val (v, None)
    | `Exn e -> c := Exn (fix_exn e)
    | `Comp f -> let _, _, comp = get f in c := !comp end;
    signal () in
  let wait, signal =
    if not blocking then (fun () -> raise NotReady), ignore else
    let lock = Mutex.create () in
    let cond = Condition.create () in
    (fun () -> Mutex.lock lock; Condition.wait cond lock; Mutex.unlock lock),
    (fun () -> Mutex.lock lock; Condition.broadcast cond; Mutex.unlock lock) in
  let ck = create fix_exn (Delegated wait) in
  ck, assignement signal ck

(* TODO: get rid of try/catch to be stackless *)
let rec compute ~pure ck : 'a value =
  let _, fix_exn, c = get ck in
  match !c with
  | Val (x, _) -> `Val x
  | Exn (e, info) -> `Exn (e, info)
  | Delegated wait -> wait (); compute ~pure ck
  | Closure f ->
      try
        let data = f () in
        let state = if pure then None else Some (!freeze ()) in
        c := Val (data, state); `Val data
      with e ->
        let e = Errors.push e in
        let e = fix_exn e in
        match e with
        | (NotReady, _) -> `Exn e
        | _ -> c := Exn e; `Exn e

let force ~pure x = match compute ~pure x with
  | `Val v -> v
  | `Exn e -> Exninfo.iraise e

let chain ~pure ck f =
  let uuid, fix_exn, c = get ck in
  create ~uuid fix_exn (match !c with
  | Closure _ | Delegated _ -> Closure (fun () -> f (force ~pure ck))
  | Exn _ as x -> x
  | Val (v, None) when pure -> Closure (fun () -> f v)
  | Val (v, Some _) when pure -> Closure (fun () -> f v)
  | Val (v, Some state) -> Closure (fun () -> !unfreeze state; f v)
  | Val (v, None) ->
      match !ck with
      | Finished _ -> Errors.anomaly(Pp.str
          "Future.chain ~pure:false call on an already joined computation")
      | Ongoing _ -> Errors.anomaly(Pp.strbrk(
          "Future.chain ~pure:false call on a pure computation. "^
          "This can happen if the computation was initial created with "^
          "Future.from_val or if it was Future.chain ~pure:true with a "^
          "function and later forced.")))

let create fix_exn f = create fix_exn (Closure f)

let replace kx y =
  let _, _, x = get kx in
  match !x with
  | Exn _ -> x := Closure (fun () -> force ~pure:false y)
  | _ -> Errors.anomaly
           (Pp.str "A computation can be replaced only if is_exn holds")

let purify f x =
  let state = !freeze () in
  try
    let v = f x in
    !unfreeze state;
    v
  with e ->
    let e = Errors.push e in !unfreeze state; Exninfo.iraise e

let transactify f x =
  let state = !freeze () in
  try f x
  with e ->
    let e = Errors.push e in !unfreeze state; Exninfo.iraise e

let purify_future f x = if is_over x then f x else purify f x
let compute x = purify_future (compute ~pure:false) x
let force ~pure x = purify_future (force ~pure) x
let chain ?(greedy=true) ~pure x f =
  let y = chain ~pure x f in
  if is_over x && greedy then ignore(force ~pure y);
  y
let force x = force ~pure:false x

let join kx =
  let v = force kx in
  kx := Finished v;
  v

let sink kx = if is_val kx then ignore(join kx)

let split2 ?greedy x =
  chain ?greedy ~pure:true x (fun x -> fst x),
  chain ?greedy ~pure:true x (fun x -> snd x)

let map2 ?greedy f x l =
  CList.map_i (fun i y ->
    let xi = chain ?greedy ~pure:true x (fun x ->
        try List.nth x i
        with Failure _ | Invalid_argument _ ->
          Errors.anomaly (Pp.str "Future.map2 length mismatch")) in
    f xi y) 0 l

let print f kx =
  let open Pp in
  let (uid, _, x) = get kx in
  let uid =
    if UUID.equal uid UUID.invalid then str "[#]"
    else str "[" ++ int uid ++ str "]"
  in
  match !x with
  | Delegated _ -> str "Delegated" ++ uid
  | Closure _ -> str "Closure" ++ uid
  | Val (x, None) -> str "PureVal" ++ uid ++ spc () ++ hov 0 (f x)
  | Val (x, Some _) -> str "StateVal" ++ uid ++ spc () ++ hov 0 (f x)
  | Exn (e, _) -> str "Exn"  ++ uid ++ spc () ++ hov 0 (str (Printexc.to_string e))
