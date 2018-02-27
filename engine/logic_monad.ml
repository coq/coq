(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

let _ = CErrors.register_handler begin function
  | Timeout -> CErrors.user_err ~hdr:"Some timeout function" (Pp.str"Timeout!")
  | Exception e -> CErrors.print e
  | TacticFailure e -> CErrors.print e
  | _ -> Pervasives.raise CErrors.Unhandled
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
        let (src, info) = CErrors.push src in
        h (e, info) ()

  let read_line = fun () -> try Pervasives.read_line () with e ->
    let (e, info) = CErrors.push e in raise ~info e ()

  let print_char = fun c -> (); fun () -> print_char c

  let timeout = fun n t -> (); fun () ->
    Control.timeout n t () (Exception Timeout)

  let make f = (); fun () ->
    try f ()
    with e when CErrors.noncritical e ->
      let (e, info) = CErrors.push e in
      Util.iraise (Exception e, info)

  (** Use the current logger. The buffer is also flushed. *)
  let print_debug   s = make (fun _ -> Feedback.msg_info s)
  let print_info    s = make (fun _ -> Feedback.msg_info s)
  let print_warning s = make (fun _ -> Feedback.msg_warning s)
  let print_notice  s = make (fun _ -> Feedback.msg_notice s)

  let run = fun x ->
    try x () with Exception e as src ->
      let (src, info) = CErrors.push src in
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
type ('a, 'b, 'e) list_view =
  | Nil of 'e
  | Cons of 'a * ('e -> 'b)

module BackState =
struct

  (** Double-continuation backtracking monads are reasonable folklore
      for "search" implementations (including the Tac interactive
      prover's tactics). Yet it's quite hard to wrap your head around
      these.  I recommand reading a few times the "Backtracking,
      Interleaving, and Terminating Monad Transformers" paper by
      O. Kiselyov, C. Shan, D. Friedman, and A. Sabry.  The peculiar
      shape of the monadic type is reminiscent of that of the
      continuation monad transformer.

      The paper also contains the rationale for the [split] abstraction.

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

  type ('a, 'i, 'o, 'e) t =
      { iolist : 'r. 'i -> ('e -> 'r NonLogical.t) ->
                     ('a -> 'o -> ('e -> 'r NonLogical.t) -> 'r NonLogical.t) ->
                     'r NonLogical.t }

  let return x =
    { iolist = fun s nil cons -> cons x s nil }

  let (>>=) m f =
    { iolist = fun s nil cons ->
      m.iolist s nil (fun x s next -> (f x).iolist s next cons) }

  let (>>) m f =
    { iolist = fun s nil cons ->
      m.iolist s nil (fun () s next -> f.iolist s next cons) }

  let map f m =
    { iolist = fun s nil cons -> m.iolist s nil (fun x s next -> cons (f x) s next) }

  let zero e =
    { iolist = fun _ nil cons -> nil e }

  let plus m1 m2 =
    { iolist = fun s nil cons -> m1.iolist s (fun e -> (m2 e).iolist s nil cons) cons }

  let ignore m =
    { iolist = fun s nil cons -> m.iolist s nil (fun _ s next -> cons () s next) }

  let lift m =
    { iolist = fun s nil cons -> NonLogical.(m >>= fun x -> cons x s nil) }

  (** State related *)

  let get =
    { iolist = fun s nil cons -> cons s s nil }

  let set s =
    { iolist = fun _ nil cons -> cons () s nil }

  let modify f =
    { iolist = fun s nil cons -> cons () (f s) nil }

  (** Exception manipulation *)

  let interleave src dst m =
    { iolist = fun s nil cons ->
      m.iolist s (fun e1 -> nil (src e1))
        (fun x s next -> cons x s (fun e2 -> next (dst e2)))
    }

  (** List observation *)

  let once m =
    { iolist = fun s nil cons -> m.iolist s nil (fun x s _ -> cons x s nil) }

  let break f m =
    { iolist = fun s nil cons ->
      m.iolist s nil (fun x s next -> cons x s (fun e -> match f e with None -> next e | Some e -> nil e))
    }

  (** For [reflect] and [split] see the "Backtracking, Interleaving,
      and Terminating Monad Transformers" paper.  *)
  type ('a, 'e) reified = ('a, ('a, 'e) reified, 'e) list_view NonLogical.t

  let rec reflect (m : ('a * 'o, 'e) reified) =
    { iolist = fun s0 nil cons ->
      let next = function
      | Nil e -> nil e
      | Cons ((x, s), l) -> cons x s (fun e -> (reflect (l e)).iolist s0 nil cons)
      in
      NonLogical.(m >>= next)
    }

  let split m : ((_, _, _) list_view, _, _, _) t =
    let rnil e = NonLogical.return (Nil e) in
    let rcons p s l = NonLogical.return (Cons ((p, s), l)) in
    { iolist = fun s nil cons ->
      let open NonLogical in
      m.iolist s rnil rcons >>= begin function
      | Nil e -> cons (Nil e) s nil
      | Cons ((x, s), l) ->
        let l e = reflect (l e) in
        cons (Cons (x, l)) s nil
      end }

  let run m s =
    let rnil e = NonLogical.return (Nil e) in
    let rcons x s l =
      let p = (x, s) in
      NonLogical.return (Cons (p, l))
    in
    m.iolist s rnil rcons

  let repr x = x
end

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

  module Unsafe =
  struct
    (** All three of environment, writer and state are coded as a single
        state-passing-style monad.*)
    type state = {
      rstate : P.e;
      ustate : P.u;
      wstate : P.w;
      sstate : P.s;
    }

    let make m = m
    let repr m = m
  end

  open Unsafe

  type state = Unsafe.state

  type iexn = Exninfo.iexn

  type 'a reified = ('a, iexn) BackState.reified

  (** Inherited from Backstate *)

  open BackState

  include Monad.Make(struct
    type 'a t = ('a, state, state, iexn) BackState.t
    let return = BackState.return
    let (>>=) = BackState.(>>=)
    let (>>) = BackState.(>>)
    let map = BackState.map
  end)

  let zero = BackState.zero
  let plus = BackState.plus
  let ignore = BackState.ignore
  let lift = BackState.lift
  let once = BackState.once
  let break = BackState.break
  let split = BackState.split
  let repr = BackState.repr

  (** State related. We specialize them here to ensure soundness (for reader and
      writer) and efficiency. *)

  let get =
    { iolist = fun s nil cons -> cons s.sstate s nil }

  let set (sstate : P.s) =
    { iolist = fun s nil cons -> cons () { s with sstate } nil }

  let modify (f : P.s -> P.s) =
    { iolist = fun s nil cons -> cons () { s with sstate = f s.sstate } nil }

  let current =
    { iolist = fun s nil cons -> cons s.rstate s nil }

  let local e m =
    { iolist = fun s nil cons ->
      m.iolist { s with rstate = e } nil
        (fun x s' next -> cons x {s' with rstate = s.rstate} next) }

  let put w =
    { iolist = fun s nil cons -> cons () { s with wstate = P.wprod s.wstate w } nil }

  let update (f : P.u -> P.u) =
    { iolist = fun s nil cons -> cons () { s with ustate = f s.ustate } nil }

  (** Monadic run is specialized to handle reader / writer *)

  let run m r s =
    let s = { wstate = P.wunit; ustate = P.uunit; rstate = r; sstate = s } in
    let rnil e = NonLogical.return (Nil e) in
    let rcons x s l =
      let p = (x, s.sstate, s.wstate, s.ustate) in
      NonLogical.return (Cons (p, l))
    in
    m.iolist s rnil rcons

 end
