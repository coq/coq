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

let here x s = Sigma (x, s, ())

(** API *)

type 'r fresh = Fresh : 's evar * 's t * ('r, 's) le -> 'r fresh

let new_evar sigma ?name info =
  let (sigma, evk) = Evd.new_evar sigma ?name info in
  Fresh (evk, sigma, ())

let define evk c sigma =
  Sigma ((), Evd.define evk c sigma, ())

let new_univ_level_variable ?loc ?name rigid sigma =
  let (sigma, u) = Evd.new_univ_level_variable ?loc ?name rigid sigma in
  Sigma (u, sigma, ())

let new_univ_variable ?loc ?name rigid sigma =
  let (sigma, u) = Evd.new_univ_variable ?loc ?name rigid sigma in
  Sigma (u, sigma, ())

let new_sort_variable ?loc ?name rigid sigma =
  let (sigma, u) = Evd.new_sort_variable ?loc ?name rigid sigma in
  Sigma (u, sigma, ())

let fresh_sort_in_family ?loc ?rigid env sigma s =
  let (sigma, s) = Evd.fresh_sort_in_family ?loc ?rigid env sigma s in
  Sigma (s, sigma, ())

let fresh_constant_instance ?loc env sigma cst =
  let (sigma, cst) = Evd.fresh_constant_instance ?loc env sigma cst in
  Sigma (cst, sigma, ())

let fresh_inductive_instance ?loc env sigma ind =
  let (sigma, ind) = Evd.fresh_inductive_instance ?loc env sigma ind in
  Sigma (ind, sigma, ())

let fresh_constructor_instance ?loc env sigma pc =
  let (sigma, c) = Evd.fresh_constructor_instance ?loc env sigma pc in
  Sigma (c, sigma, ())

let fresh_global ?loc ?rigid ?names env sigma r =
  let (sigma, c) = Evd.fresh_global ?loc ?rigid ?names env sigma r in
  Sigma (c, sigma, ())

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
