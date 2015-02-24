(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
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

  (* The functions in this module follow the pattern that they are
     defined with the form [(); fun ()->...]. This is an optimisation
     which signals to the compiler that the function is usually partially
     applied up to the [();]. Without this annotation, partial
     applications can be significantly slower.

     Documentation of this behaviour can be found at:
     https://ocaml.janestreet.com/?q=node/30 *)

  include Monad.Make(struct
    type 'a t = unit -> 'a

    let return a = (); fun () -> a
    let (>>=) a k = (); fun () -> k (a ()) ()
    let (>>) a k = (); fun () -> a (); k ()
    let map f a = (); fun () -> f (a ())
  end)

  type 'a ref = 'a Pervasives.ref

  let ignore a = (); fun () -> ignore (a ())

  let ref a = (); fun () -> Pervasives.ref a

  (** [Pervasives.(:=)] *)
  let (:=) r a = (); fun () -> r := a

  (** [Pervasives.(!)] *)
  let (!) = fun r -> (); fun () -> ! r

  (** [Pervasives.raise]. Except that exceptions are wrapped with
      {!Exception}. *)
  let raise ?info = fun e -> (); fun () -> Exninfo.raise ?info (Exception e)

  (** [try ... with ...] but restricted to {!Exception}. *)
  let catch = fun s h -> ();
    fun () -> try s ()
      with Exception e as src ->
        let (src, info) = Errors.push src in
        h (e, info) ()

  let read_line = fun () -> try Pervasives.read_line () with e ->
    let (e, info) = Errors.push e in raise ~info e ()

  let print_char = fun c -> (); fun () -> print_char c

  (** {!Pp.pp}. The buffer is also flushed. *)
  let print = fun s -> (); fun () -> try Pp.msg_info s; Pp.pp_flush () with e ->
    let (e, info) = Errors.push e in raise ~info e ()

  let timeout = fun n t -> (); fun () ->
    Control.timeout n t (Exception Timeout)

  let make f = (); fun () ->
    try f ()
    with e when Errors.noncritical e ->
      let (e, info) = Errors.push e in
      Util.iraise (Exception e, info)

  let run = fun x ->
    try x () with Exception e as src ->
      let (src, info) = Errors.push src in
      Util.iraise (e, info)
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
  | Nil of Exninfo.iexn
  | Cons of 'a * 'b

module type Param = sig

  (** Read only *)
  type e

  (** Write only *)
  type w

  (** [w] must be a monoid *)
  val wunit : w
  val wprod : w -> w -> w

  (** Read-write *)
  type s

  (** Update-only. Essentially a writer on [u->u]. *)
  type u

  (** [u] must be pointed. *)
  val uunit : u

end


module Logical (P:Param) =
struct

  (** All three of environment, writer and state are coded as a single
      state-passing-style monad.*)
  type state = {
    rstate : P.e;
    ustate : P.u;
    wstate : P.w;
    sstate : P.s;
  }

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
  type rich_exn = Exninfo.iexn

  type 'a iolist =
      { iolist : 'r. (rich_exn -> 'r NonLogical.t) ->
                     ('a -> (rich_exn -> 'r NonLogical.t) -> 'r NonLogical.t) ->
                     'r NonLogical.t }

  include Monad.Make(struct
    type 'a t = state -> ('a * state) iolist

    let return x : 'a t = (); fun s ->
      { iolist = fun nil cons -> cons (x, s) nil }

    let (>>=) (m : 'a t) (f : 'a -> 'b t) : 'b t = (); fun s ->
      let m = m s in
      { iolist = fun nil cons ->
        m.iolist nil (fun (x, s) next -> (f x s).iolist next cons) }

    let (>>) (m : unit t) (f : 'a t) : 'a t = (); fun s ->
      let m = m s in
      { iolist = fun nil cons ->
        m.iolist nil (fun ((), s) next -> (f s).iolist next cons) }

    let map (f : 'a -> 'b) (m : 'a t) : 'b t = (); fun s ->
      let m = m s in
      { iolist = fun nil cons -> m.iolist nil (fun (x, s) next -> cons (f x, s) next) }

  end)

  let zero e : 'a t = (); fun s ->
    { iolist = fun nil cons -> nil e }

  let plus m1 m2 : 'a t = (); fun s ->
    let m1 = m1 s in
    { iolist = fun nil cons -> m1.iolist (fun e -> (m2 e s).iolist nil cons) cons }

  let ignore (m : 'a t) : unit t = (); fun s ->
    let m = m s in
    { iolist = fun nil cons -> m.iolist nil (fun (_, s) next -> cons ((), s) next) }

  let lift (m : 'a NonLogical.t) : 'a t = (); fun s ->
    { iolist = fun nil cons -> NonLogical.(m >>= fun x -> cons (x, s) nil) }

  (** State related *)

  let get : P.s t = (); fun s ->
    { iolist = fun nil cons -> cons (s.sstate, s) nil }

  let set (sstate : P.s) : unit t = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with sstate }) nil }

  let modify (f : P.s -> P.s) : unit t = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with sstate = f s.sstate }) nil }

  let current : P.e t = (); fun s ->
    { iolist = fun nil cons -> cons (s.rstate, s) nil }

  let local (type a) (e:P.e) (m:a t) : a t = (); fun s ->
    let m = m { s with rstate = e } in
    { iolist = fun nil cons ->
      m.iolist nil (fun (x,s') next -> cons (x,{s' with rstate=s.rstate}) next) }

  let put (w : P.w) : unit t = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with wstate = P.wprod s.wstate w }) nil }

  let update (f : P.u -> P.u) : unit t = (); fun s ->
    { iolist = fun nil cons -> cons ((), { s with ustate = f s.ustate }) nil }

  (** List observation *)

  let once (m : 'a t) : 'a t = (); fun s ->
    let m = m s in
    { iolist = fun nil cons -> m.iolist nil (fun x _ -> cons x nil) }

  let break (f : rich_exn -> rich_exn option) (m : 'a t) : 'a t = (); fun s ->
    let m = m s in
    { iolist = fun nil cons ->
      m.iolist nil (fun x next -> cons x (fun e -> match f e with None -> next e | Some e -> nil e))
    }

  (** For [reflect] and [split] see the "Backtracking, Interleaving,
      and Terminating Monad Transformers" paper.  *)
  type 'a reified = ('a, rich_exn -> 'a reified) list_view NonLogical.t

  let rec reflect (m : 'a reified) : 'a iolist =
    { iolist = fun nil cons ->
      let next = function
      | Nil e -> nil e
      | Cons (x, l) -> cons x (fun e -> (reflect (l e)).iolist nil cons)
      in
      NonLogical.(m >>= next)
    }

  let split (m : 'a t) : ('a, rich_exn -> 'a t) list_view t = (); fun s ->
    let m = m s in
    let rnil e = NonLogical.return (Nil e) in
    let rcons p l = NonLogical.return (Cons (p, l)) in
    { iolist = fun nil cons ->
      let open NonLogical in
      m.iolist rnil rcons >>= begin function
      | Nil e -> cons (Nil e, s) nil
      | Cons ((x, s), l) ->
        let l e = (); fun _ -> reflect (l e) in
        cons (Cons (x, l), s) nil
      end }

  let run m r s =
    let s = { wstate = P.wunit; ustate = P.uunit; rstate = r; sstate = s } in
    let m = m s in
    let rnil e = NonLogical.return (Nil e) in
    let rcons (x, s) l =
      let p = (x, s.sstate, s.wstate, s.ustate) in
      NonLogical.return (Cons (p, l))
    in
    m.iolist rnil rcons

  let repr x = x

 end
