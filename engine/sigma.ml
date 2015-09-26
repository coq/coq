(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a t = Evd.evar_map

type ('a, 'b) le = unit

let refl = ()
let cons _ _  = ()
let (+>) = fun _ _ -> ()

type ('a, 'r) sigma = Sigma : 'a * 's t * ('r, 's) le -> ('a, 'r) sigma

type 'a evar = Evar.t

let lift_evar evk () = evk

let to_evar_map evd = evd
let to_evar evk = evk

(** API *)

type 'r fresh = Fresh : 's evar * 's t * ('r, 's) le -> 'r fresh

let new_evar sigma ?naming info =
  let (sigma, evk) = Evd.new_evar sigma ?naming info in
  Fresh (evk, sigma, ())

let define evk c sigma =
  Sigma ((), Evd.define evk c sigma, ())

(** Run *)

type 'a run = { run : 'r. 'r t -> ('a, 'r) sigma }

let run sigma f : 'a * Evd.evar_map =
  let Sigma (x, sigma, ()) = f.run sigma in
  (x, sigma)

(** Monotonic references *)

type evdref = Evd.evar_map ref

let apply evdref f =
  let Sigma (x, sigma, ()) = f.run !evdref in
  evdref := sigma;
  x

let purify f =
  let f (sigma : Evd.evar_map) =
    let evdref = ref sigma in
    let ans = f evdref in
    Sigma (ans, !evdref, ())
  in
  { run = f }

(** Unsafe primitives *)

module Unsafe =
struct

let le = ()
let of_evar_map sigma = sigma
let of_evar evk = evk
let of_ref ref = ref
let of_pair (x, sigma) = Sigma (x, sigma, ())

end

module Notations =
struct
  type ('a, 'r) sigma_ = ('a, 'r) sigma =
    Sigma : 'a * 's t * ('r, 's) le -> ('a, 'r) sigma_

  let (+>) = fun _ _ -> ()

  type 'a run_ = 'a run = { run : 'r. 'r t -> ('a, 'r) sigma }
end
