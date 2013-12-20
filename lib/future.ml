(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2013     *)
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
                "the \"-async-proofs off\" option to CoqIDE to disable"^
                "asynchronous script processing.")
  | _ -> raise Errors.Unhandled)

type fix_exn = exn -> exn
let id x = prerr_endline "no fix_exn"; x

type 'a assignement = [ `Val of 'a | `Exn of exn | `Comp of 'a computation]

(* Val is not necessarily a final state, so the
   computation restarts from the state stocked into Val *)
and 'a comp =
  | Delegated of (unit -> 'a assignement)
      (* TODO in some cases one would like to block, sock here
         a mutex and a condition to make this possible *)
  | Closure of (unit -> 'a)
  | Val of 'a * Dyn.t option
  | Exn of exn (* Invariant: this exception is always "fixed" as in fix_exn *)

and 'a comput =
  | Ongoing of (fix_exn * 'a comp ref) Ephemeron.key
  | Finished of 'a

and 'a computation = 'a comput ref

let create f x = ref (Ongoing (Ephemeron.create (f, Pervasives.ref x)))
let get x =
  match !x with
  | Finished v -> (fun x -> x), ref( Val (v,None))
  | Ongoing x ->
      try Ephemeron.get x
      with Ephemeron.InvalidKey -> (fun x -> x), ref (Exn NotHere)

type 'a value = [ `Val of 'a | `Exn of exn ]

let is_over kx = let _, x = get kx in match !x with
  | Val _ | Exn _ -> true
  | Closure _ | Delegated _ -> false

let is_val kx = let _, x = get kx in match !x with
  | Val _ -> true
  | Exn _ | Closure _ | Delegated _ -> false

let is_exn kx = let _, x = get kx in match !x with
  | Exn _ -> true
  | Val _ | Closure _ | Delegated _ -> false

let peek_val kx = let _, x = get kx in match !x with
  | Val (v, _) -> Some v
  | Exn _ | Closure _ | Delegated _ -> None

let from_val ?(fix_exn=id) v = create fix_exn (Val (v, None))
let from_here ?(fix_exn=id) v = create fix_exn (Val (v, Some (!freeze ())))

let default_force () = raise NotReady
let assignement ck = fun v ->
  let fix_exn, c = get ck in
  assert (match !c with Delegated _ -> true | _ -> false);
  match v with
  | `Val v -> c := Val (v, None)
  | `Exn e -> c := Exn (fix_exn e)
  | `Comp f -> let _, comp = get f in c := !comp
let create_delegate ?(force=default_force) fix_exn =
  let ck = create fix_exn (Delegated force) in
  ck, assignement ck

(* TODO: get rid of try/catch to be stackless *)
let rec compute ~pure ck : 'a value =
  let fix_exn, c = get ck in
  match !c with
  | Val (x, _) -> `Val x
  | Exn e -> `Exn e
  | Delegated f -> assignement ck (f ()); compute ~pure ck
  | Closure f ->
      try
        let data = f () in
        let state = if pure then None else Some (!freeze ()) in
        c := Val (data, state); `Val data
      with e ->
        let e = Errors.push e in
        let e = fix_exn e in
        match e with
        | NotReady -> `Exn e
        | _ -> c := Exn e; `Exn e

let force ~pure x = match compute ~pure x with
  | `Val v -> v
  | `Exn e -> raise e

let chain ~pure ck f =
  let fix_exn, c = get ck in
  create fix_exn (match !c with
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
  let _, x = get kx in
  match !x with
  | Exn _ -> x := Closure (fun () -> force ~pure:false y)
  | _ -> Errors.anomaly (Pp.str "Only Exn futures can be replaced")

let purify f x =
  let state = !freeze () in
  try
    let v = f x in
    !unfreeze state;
    v
  with e -> let e = Errors.push e in !unfreeze state; raise e

let transactify f x =
  let state = !freeze () in
  try f x
  with e -> let e = Errors.push e in !unfreeze state; raise e

let purify_future f x = if is_over x then f x else purify f x
let compute x = purify_future (compute ~pure:false) x
let force x = purify_future (force ~pure:false) x
let chain ?(greedy=false) ~pure x f =
  let y = chain ~pure x f in
  if is_over x && greedy then ignore(force y);
  y

let join kx =
  let v = force kx in
  kx := Finished v;
  v

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
