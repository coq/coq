(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Proofview.Notations

(** Focussing tactics *)

type 'a focus =
| Uniform of 'a
| Depends of 'a list

(** Type of tactics potentially goal-dependent. If it contains a [Depends],
    then the length of the inner list is guaranteed to be the number of
    currently focussed goals. Otherwise it means the tactic does not depend
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
    Proofview.Goal.goals >>= fun goals ->
    let ans = List.map (fun g -> (g,x)) goals in
    Proofview.tclUNIT ans
  | Depends l ->
    Proofview.Goal.goals >>= fun goals ->
    Proofview.tclUNIT (List.combine goals l)
  in
  (* After the tactic has run, some goals which were previously
     produced may have been solved by side effects. The values
     attached to such goals must be discarded, otherwise the list of
     result would not have the same length as the list of focused
     goals, which is an invariant of the [Ftactic] module. It is the
     reason why a goal is attached to each result above. *)
  let filter (g,x) =
    g >>= fun g ->
    Proofview.Goal.unsolved g >>= function
    | true -> Proofview.tclUNIT (Some x)
    | false -> Proofview.tclUNIT None
  in
  Proofview.tclDISPATCHL (List.map f l) >>= fun l ->
  Proofview.Monad.List.map_filter filter (List.concat l) >>= fun filtered ->
  Proofview.tclUNIT (Depends filtered)

let goals = Proofview.Goal.goals >>= fun l -> Proofview.tclUNIT (Depends l)

let nf_enter f =
  bind goals
    (fun gl ->
      gl >>= fun gl ->
      Proofview.Goal.normalize gl >>= fun nfgl ->
      Proofview.V82.wrap_exceptions (fun () -> f nfgl))

let enter f =
  bind goals
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

module Notations =
struct
  let (>>=) = bind
  let (<*>) = fun m n -> bind m (fun () -> n)
end
