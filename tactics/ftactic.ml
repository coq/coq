(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Proofview.Notations

(** Focussing tactics *)

type 'a focus =
| Uniform of 'a
| Depends of 'a list

(** Type of tactics potentially goal-dependent. If it contains a [Depends],
    then the length of the inner list is guaranteed to be the number of
    currently focussed goals. Otherwise it means the tactic does not depends
    on the current set of focussed goals. *)
type 'a t = 'a focus Proofview.tactic

let return (x : 'a) : 'a t = Proofview.tclUNIT (Uniform x)

let bind (type a) (type b) (m : a t) (f : a -> b t) : b t = m >>= function
| Uniform x -> f x
| Depends l ->
  let f arg = f arg >>= function
  | Uniform x ->
    (** We dispatch the uniform result on each goal under focus, as we know
        that the [m] argument was actually dependent. *)
    Proofview.Goal.goals >>= fun l ->
    let ans = List.map (fun _ -> x) l in
    Proofview.tclUNIT ans
  | Depends l -> Proofview.tclUNIT l
  in
  Proofview.tclDISPATCHL (List.map f l) >>= fun l ->
  Proofview.tclUNIT (Depends (List.concat l))

let nf_enter f =
  bind (Proofview.Goal.goals >>= fun l -> Proofview.tclUNIT (Depends l))
    (fun gl ->
      gl >>= fun gl ->
      Proofview.Goal.normalize gl >>= fun nfgl ->
      Proofview.V82.wrap_exceptions (fun () -> f nfgl))

let enter f =
  bind (Proofview.Goal.goals >>= fun l -> Proofview.tclUNIT (Depends l))
    (fun gl -> gl >>= fun gl -> Proofview.V82.wrap_exceptions (fun () -> f gl))

let with_env t =
  t >>= function
    | Uniform a ->
        Proofview.tclENV >>= fun env -> Proofview.tclUNIT (Uniform (env,a))
    | Depends l ->
        Proofview.Goal.goals >>= fun gs ->
        Proofview.Monad.(List.map (map Proofview.Goal.env) gs) >>= fun envs ->
        Proofview.tclUNIT (Depends (List.combine envs l))

let lift (type a) (t:a Proofview.tactic) : a t =
  Proofview.tclBIND t (fun x -> Proofview.tclUNIT (Uniform x))

(** If the tactic returns unit, we can focus on the goals if necessary. *)
let run m k = m >>= function
| Uniform v -> k v
| Depends l ->
  let tacs = List.map k l in
  Proofview.tclDISPATCH tacs

let (>>=) = bind

let (<*>) = fun m n -> bind m (fun () -> n)

module Self =
struct
  type 'a t = 'a focus Proofview.tactic
  let return = return
  let (>>=) = bind
  let (>>) = (<*>)
  let map f x = x >>= fun a -> return (f a)
end

module Ftac = Monad.Make(Self)
module List = Ftac.List

let debug_prompt = Tactic_debug.debug_prompt
