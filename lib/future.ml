(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* to avoid side effects *)
let freeze = ref (fun () -> assert false : unit -> Dyn.t)
let unfreeze = ref (fun _ -> () : Dyn.t -> unit)
let set_freeze f g = freeze := f; unfreeze := g

exception NotReady
exception NotHere
let _ = Errors.register_handler (function
  | NotReady ->
      Pp.strbrk("The value you are asking for is not ready yet. " ^
                "Please wait or pass "^
                "the \"-coq-slaves off\" option to CoqIDE to disable "^
                "asynchronous script processing.")
  | NotHere ->
      Pp.strbrk("The value you are asking for is not available "^
                "in this process. If you really need this, pass "^
                "the \"-coq-slaves off\" option to CoqIDE to disable"^
                "asynchronous script processing.")
  | _ -> raise Errors.Unhandled)

(* Val is not necessarily a final state, so the
   computation restarts from the state stocked into Val *)
type 'a comp =
  | Delegated
  | Dropped
  | Closure of (unit -> 'a)
  | Val of 'a * Dyn.t option
  | Exn of exn

type 'a computation = 'a comp ref

type 'a value = [ `Val of 'a | `Exn of exn ]

let is_over x = match !x with
  | Val _ | Exn _ -> true
  | Closure _ | Delegated | Dropped -> false

let is_val x = match !x with
  | Val _ -> true
  | Exn _ | Closure _ | Delegated | Dropped -> false

let peek_val x = match !x with
  | Val (v, _) -> Some v
  | Exn _ | Closure _ | Delegated | Dropped -> None

let from_val v = ref (Val (v, None))
let from_here v = ref (Val (v, Some (!freeze ())))
let proj = function
  | `Val (x, _ ) -> `Val x
  | `Exn e -> `Exn e

let create f = ref (Closure f)

type 'a assignement = [ `Val of 'a | `Exn of exn | `Comp of 'a computation]
let create_delegate () =
  let c = ref Delegated in
  c, (fun v ->
      assert (!c = Delegated);
      match v with
      | `Val v -> c := Val (v, None)
      | `Exn e -> c := Exn e
      | `Comp f -> c := !f)

(* TODO: get rid of try/catch *)
let compute ~pure c : 'a value = match !c with
  | Val (x, _) -> `Val x
  | Exn e -> `Exn e
  | Delegated -> `Exn NotReady
  | Dropped -> `Exn NotHere
  | Closure f ->
      try
        let data = f () in
        let state = if pure then None else Some (!freeze ()) in
        c := Val (data, state); `Val data
      with e ->
        let e = Errors.push e in
        match e with
        | NotReady -> `Exn e
        | _ -> c := Exn e; `Exn e

let force ~pure x = match compute ~pure x with
  | `Val v -> v
  | `Exn e -> raise e

let drop c = match !c with Closure _ | Val (_,Some _) -> ref Dropped | _ -> c

let chain ?(id="none") ?(pure=false) c f = ref (match !c with
  | Closure _ | Delegated | Dropped -> Closure (fun () -> f (force ~pure c))
  | Exn _ as x -> x
  | Val (v, None) -> Closure (fun () -> f v)
  | Val (v, Some _) when pure ->  Closure (fun () -> f v)
  | Val (v, Some state) ->
       prerr_endline ("Future: restarting (check if optimizable): " ^ id);
       Closure (fun () -> !unfreeze state; f v))

let create_here f = chain ~pure:false (from_here ()) f

let purify f x =
  let state = !freeze () in
  try
    let v = f x in
    !unfreeze state;
    v
  with e -> let e = Errors.push e in !unfreeze state; raise e

let purify_future f x =
  match !x with
  | Val _ | Exn _ | Delegated | Dropped -> f x
  | Closure _ -> purify f x

let compute x = purify_future (compute ~pure:false) x
let force x = purify_future (force ~pure:false) x

let join x =
  let v = force x in
  (x := match !x with
       | Val (x,_) -> Val (x, None)
       | Exn _ | Delegated | Dropped | Closure _ -> assert false);
  v

let split2 x =
  chain ~pure:true x (fun x -> fst x),
  chain ~pure:true x (fun x -> snd x)

let split3 x =
  chain ~pure:true x (fun x -> Util.pi1 x),
  chain ~pure:true x (fun x -> Util.pi2 x),
  chain ~pure:true x (fun x -> Util.pi3 x)

let map2 f x l =
  CList.map_i (fun i y ->
    let xi = chain ~pure:true x (fun x ->
        try List.nth x i
        with Failure _ | Invalid_argument _ ->
          Errors.anomaly (Pp.str "Future.map2 length mismatch")) in
    f xi y) 0 l
