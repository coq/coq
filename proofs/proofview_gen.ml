type ('a, 'b) list_view =
| Nil of exn
| Cons of 'a * 'b

module IO =
 struct
  type 'a t = unit -> 'a

  type 'a coq_Ref = 'a Pervasives.ref

  let ret = fun a -> (); fun () -> a

  let bind = fun a k -> (); fun () -> k (a ()) ()

  let ignore = fun a -> (); fun () -> ignore (a ())

  let seq = fun a k -> (); fun () -> a (); k ()

  let map = fun f a -> (); fun () -> f (a ())

  let ref = fun a -> (); fun () -> Pervasives.ref a

  let set = fun r a -> (); fun () -> Pervasives.(:=) r a

  let get = fun r -> (); fun () -> Pervasives.(!) r

  let raise = fun e -> (); fun () -> raise (Proof_errors.Exception e)

  let catch = fun s h -> ();
  fun () -> try s ()
  with Proof_errors.Exception e as src ->
    let src = Errors.push src in
    let e = Backtrace.app_backtrace ~src ~dst:e in
    h e ()

  let read_line = fun () -> try Pervasives.read_line () with e -> let e = Errors.push e in raise e ()

  let print_char = fun c -> (); fun () -> print_char c

  let print = fun s -> (); fun () -> try Pp.pp s; Pp.pp_flush () with e -> let e = Errors.push e in raise e ()

  let timeout = fun n t -> (); fun () ->
    Control.timeout n t (Proof_errors.Exception Proof_errors.Timeout)

end

type proofview = { solution : Evd.evar_map; comb : Goal.goal list }

type logicalState = proofview

type logicalMessageType = bool*(Goal.goal list*Goal.goal list)

type logicalEnvironment = Environ.env

module NonLogical =
 struct
  include IO
  type 'a ref = 'a IO.coq_Ref

  let new_ref = ref

  let run = fun x ->
  try x () with Proof_errors.Exception e as src ->
    let src = Errors.push src in
    let e = Backtrace.app_backtrace ~src ~dst:e in
    Pervasives.raise e
 end

module Logical =
 struct

  type rt = logicalEnvironment
  type wt = logicalMessageType
  type st = logicalState

  type state = {
    rstate : rt;
    wstate : wt;
    sstate : st;
  }

  let empty = (true, ([], []))

  let merge (b1, (l1, k1)) (b2, (l2, k2)) = (b1 && b2, (l1 @ l2, k1 @ k2))

  type 'a iolist =
    { iolist : 'r. (exn -> 'r IO.t) -> ('a -> (exn -> 'r IO.t) -> 'r IO.t) -> 'r IO.t }

  type 'a tactic = state -> ('a * state) iolist

  type 'a t = 'a tactic

  let zero e : 'a tactic = (); fun s ->
    { iolist = fun nil cons -> nil e }

  let plus m1 m2 : 'a tactic = (); fun s ->
    let m1 = m1 s in
    { iolist = fun nil cons -> m1.iolist (fun e -> (m2 e s).iolist nil cons) cons }

  let ret x : 'a tactic = (); fun s ->
    { iolist = fun nil cons -> cons (x, s) nil }

  let bind (m : 'a tactic) (f : 'a -> 'b tactic) : 'b tactic = (); fun s ->
    let m = m s in
    { iolist = fun nil cons -> m.iolist nil (fun (x, s) next -> (f x s).iolist next cons) }

  let seq (m : unit tactic) (f : 'a tactic) : 'a tactic = (); fun s ->
    let m = m s in
    { iolist = fun nil cons -> m.iolist nil (fun ((), s) next -> (f s).iolist next cons) }

  let map (f : 'a -> 'b) (m : 'a tactic) : 'b tactic = (); fun s ->
    let m = m s in
    { iolist = fun nil cons -> m.iolist nil (fun (x, s) next -> cons (f x, s) next) }

  let ignore (m : 'a tactic) : unit tactic = (); fun s ->
    let m = m s in
    { iolist = fun nil cons -> m.iolist nil (fun (_, s) next -> cons ((), s) next) }

  let lift (m : 'a IO.t) : 'a tactic = (); fun s ->
    { iolist = fun nil cons -> IO.bind m (fun x -> cons (x, s) nil) }

  (** State related *)

  let get : st tactic = (); fun s ->
    { iolist = fun nil cons -> cons (s.sstate, s) nil }

  let set (sstate : st) : unit tactic = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with sstate }) nil }

  let modify (f : st -> st) : unit tactic = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with sstate = f s.sstate }) nil }

  let current : rt tactic = (); fun s ->
    { iolist = fun nil cons -> cons (s.rstate, s) nil }

  let put (w : wt) : unit tactic = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with wstate = merge w s.wstate }) nil }

  (** List observation *)

  let once (m : 'a tactic) : 'a tactic = (); fun s ->
    let m = m s in
    { iolist = fun nil cons -> m.iolist nil (fun x _ -> cons x nil) }

  let break (f : exn -> bool) (m : 'a tactic) : 'a tactic = (); fun s ->
    let m = m s in
    { iolist = fun nil cons ->
      m.iolist nil (fun x next -> cons x (fun e -> if f e then nil e else next e))
    }

  type 'a reified = ('a, exn -> 'a reified) list_view IO.t

  let rec reflect (m : 'a reified) : 'a iolist =
    { iolist = fun nil cons ->
      let next = function
      | Nil e -> nil e
      | Cons (x, l) -> cons x (fun e -> (reflect (l e)).iolist nil cons)
      in
      IO.bind m next
    }

  let split (m : 'a tactic) : ('a, exn -> 'a t) list_view tactic = (); fun s ->
    let m = m s in
    let rnil e = IO.ret (Nil e) in
    let rcons p l = IO.ret (Cons (p, l)) in
    { iolist = fun nil cons ->
      IO.bind (m.iolist rnil rcons) begin function
      | Nil e -> cons (Nil e, s) nil
      | Cons ((x, s), l) ->
        let l e = (); fun _ -> reflect (l e) in
        cons (Cons (x, l), s) nil
      end }

  let run m r s =
    let s = { wstate = empty; rstate = r; sstate = s } in
    let m = m s in
    let nil e = IO.raise (Proof_errors.TacticFailure e) in
    let cons (x, s) _ = IO.ret ((x, s.sstate), s.wstate) in
    m.iolist nil cons

 end
