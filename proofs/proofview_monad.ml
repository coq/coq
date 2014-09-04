(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** This file defines the low-level monadic operations used by the
    tactic monad. The monad is divided into two layers: a non-logical
    layer which consists in operations which will not (or cannot) be
    backtracked in case of failure (input/output or persistent state)
    and a logical layer which handles backtracking, proof
    manipulation, and any other effect which needs to backtrack. *)

(** {6 States of the logical monad} *)

type proofview = { solution : Evd.evar_map; comb : Goal.goal list }

(** Read/write *)
type logicalState = proofview

(** Write only. Must be a monoid.

    Status (safe/unsafe) * ( shelved goals * given up ). *)
type logicalMessageType = bool*(Goal.goal list*Goal.goal list)

(** Read only *)
type logicalEnvironment = Environ.env


(** {6 Exceptions} *)


(** To help distinguish between exceptions raised by the IO monad from
    the one used natively by Coq, the former are wrapped in
    [Exception].  It is only used internally so that [catch] blocks of
    the IO monad would only catch exceptions raised by the [raise]
    function of the IO monad, and not for instance, by system
    interrupts. Also used in [Proofview] to avoid capturing exception
    from the IO monad ([Proofview] catches errors in its compatibility
    layer, and when lifting goal-level expressions). *)
exception Exception of exn
(** This exception is used to signal abortion in [timeout] functions. *)
exception Timeout
(** This exception is used by the tactics to signal failure by lack of
    successes, rather than some other exceptions (like system
    interrupts). *)
exception TacticFailure of exn

let _ = Errors.register_handler begin function
  | Timeout -> Errors.errorlabstrm "Some timeout function" (Pp.str"Timeout!")
  | Exception e -> Errors.print e
  | TacticFailure e -> Errors.print e
  | _ -> Pervasives.raise Errors.Unhandled
end

(** {6 Non-logical layer} *)

(** The non-logical monad is a simple [unit -> 'a] (i/o) monad. The
    operations are simple wrappers around corresponding usual
    operations and require little documentation. *)
module NonLogical =
struct
  type 'a t = unit -> 'a

  type 'a ref = 'a Pervasives.ref

  (* The functions in this module follow the pattern that they are
     defined with the form [(); fun ()->...]. This is an optimisation
     which signals to the compiler that the function is usually partially
     applied up to the [();]. Without this annotation, partial
     applications can be significantly slower.

     Documentation of this behaviour can be found at:
     https://ocaml.janestreet.com/?q=node/30 *)

  let ret a = (); fun () -> a

  let bind a k = (); fun () -> k (a ()) ()

  let ignore a = (); fun () -> ignore (a ())

  let seq a k = (); fun () -> a (); k ()

  let map f a = (); fun () -> f (a ())

  let ref a = (); fun () -> Pervasives.ref a

  (** [Pervasives.(:=)] *)
  let set r a = (); fun () -> r := a

  (** [Pervasives.(!)] *)
  let get = fun r -> (); fun () -> ! r

  (** [Pervasives.raise]. Except that exceptions are wrapped with
      {!Exception}. *)
  let raise = fun e -> (); fun () -> raise (Exception e)

  (** [try ... with ...] but restricted to {!Exception}. *)
  let catch = fun s h -> ();
    fun () -> try s ()
      with Exception e as src ->
        let src = Errors.push src in
        let e = Backtrace.app_backtrace ~src ~dst:e in
        h e ()

  let read_line = fun () -> try Pervasives.read_line () with e -> let e = Errors.push e in raise e ()

  let print_char = fun c -> (); fun () -> print_char c

  (** {!Pp.pp}. The buffer is also flushed. *)
  let print = fun s -> (); fun () -> try Pp.pp s; Pp.pp_flush () with e -> let e = Errors.push e in raise e ()

  let timeout = fun n t -> (); fun () ->
    Control.timeout n t (Exception Timeout)

  let make f = (); fun () ->
    try f ()
    with e when Errors.noncritical e ->
      let e = Errors.push e in
      Pervasives.raise (Exception e)

  let run = fun x ->
    try x () with Exception e as src ->
      let src = Errors.push src in
      let e = Backtrace.app_backtrace ~src ~dst:e in
      Pervasives.raise e
end

(** {6 Logical layer} *)

(** The logical monad is a backtracking monad on top of which is
    layered a state monad (which is used to implement all of read/write,
    read only, and write only effects). The state monad being layered on
    top of the backtracking monad makes it so that the state is
    backtracked on failure.

    Backtracking differs from regular exception in that, writing (+)
    for exception catching and (>>=) for bind, we require the
    following extra distributivity laws:

    x+(y+z) = (x+y)+z

    zero+x = x

    x+zero = x

    (x+y)>>=k = (x>>=k)+(y>>=k) *)

(** A view type for the logical monad, which is a form of list, hence
    we can decompose it with as a list. *)
type ('a, 'b) list_view =
  | Nil of exn
  | Cons of 'a * 'b

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

  (** Double-continuation backtracking monads are reasonable folklore
      for "search" implementations (including the Tac interactive
      prover's tactics). Yet it's quite hard to wrap your head around
      these.  I recommand reading a few times the "Backtracking,
      Interleaving, and Terminating Monad Transformers" paper by
      O. Kiselyov, C. Shan, D. Friedman, and A. Sabry.  The peculiar
      shape of the monadic type is reminiscent of that of the
      continuation monad transformer.

      The paper also contains the rational for the [split] abstraction.

      An explanation of how to derive such a monad from mathematical
      principles can be found in "Kan Extensions for Program
      Optimisation" by Ralf Hinze.

      A somewhat concrete view is that the type ['a iolist] is, in fact
      the impredicative encoding of the following stream type:

      [type 'a _iolist' = Nil of exn | Cons of 'a*'a iolist'
       and 'a iolist = 'a _iolist NonLogical.t]

      Using impredicative encoding avoids intermediate allocation and
      is, empirically, very efficient in Ocaml. It also has the
      practical benefit that the monadic operation are independent of
      the underlying monad, which simplifies the code and side-steps
      the limited inlining of Ocaml.

      In that vision, [bind] is simply [concat_map] (though the cps
      version is significantly simpler), [plus] is concatenation, and
      [split] is pattern-matching. *)
  type 'a iolist =
      { iolist : 'r. (exn -> 'r NonLogical.t) ->
                     ('a -> (exn -> 'r NonLogical.t) -> 'r NonLogical.t) ->
                     'r NonLogical.t }

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

  let lift (m : 'a NonLogical.t) : 'a tactic = (); fun s ->
    { iolist = fun nil cons -> NonLogical.bind m (fun x -> cons (x, s) nil) }

  (** State related *)

  let get : st tactic = (); fun s ->
    { iolist = fun nil cons -> cons (s.sstate, s) nil }

  let set (sstate : st) : unit tactic = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with sstate }) nil }

  let modify (f : st -> st) : unit tactic = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with sstate = f s.sstate }) nil }

  let current : rt tactic = (); fun s ->
    { iolist = fun nil cons -> cons (s.rstate, s) nil }

  let update (rstate : rt) : unit tactic = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with rstate }) nil }

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

  (** For [reflect] and [split] see the "Backtracking, Interleaving,
      and Terminating Monad Transformers" paper.  *)
  type 'a reified = ('a, exn -> 'a reified) list_view NonLogical.t

  let rec reflect (m : 'a reified) : 'a iolist =
    { iolist = fun nil cons ->
      let next = function
      | Nil e -> nil e
      | Cons (x, l) -> cons x (fun e -> (reflect (l e)).iolist nil cons)
      in
      NonLogical.bind m next
    }

  let split (m : 'a tactic) : ('a, exn -> 'a t) list_view tactic = (); fun s ->
    let m = m s in
    let rnil e = NonLogical.ret (Nil e) in
    let rcons p l = NonLogical.ret (Cons (p, l)) in
    { iolist = fun nil cons ->
      NonLogical.bind (m.iolist rnil rcons) begin function
      | Nil e -> cons (Nil e, s) nil
      | Cons ((x, s), l) ->
        let l e = (); fun _ -> reflect (l e) in
        cons (Cons (x, l), s) nil
      end }

  let run m r s =
    let s = { wstate = empty; rstate = r; sstate = s } in
    let m = m s in
    let nil e = NonLogical.raise (TacticFailure e) in
    let cons (x, s) _ = NonLogical.ret ((x, s.sstate), s.wstate) in
    m.iolist nil cons

 end
