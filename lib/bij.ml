(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

type ('a,'b) t = { 
  f : ('a,'b) Gmap.t;
  finv : ('b,'a) Gmap.t }

let empty = { f = Gmap.empty; finv = Gmap.empty }

let map b x = Gmap.find x b.f

let pam b y = Gmap.find y b.finv

let dom b = Gmap.dom b.f

let rng b = Gmap.dom b.finv

let in_dom b x = Gmap.mem x b.f

let in_rng b y = Gmap.mem y b.finv

let add b (x,y) =
  if in_dom b x || in_rng b y then failwith "Bij.add";
  { f = Gmap.add x y b.f;
    finv = Gmap.add y x b.finv }

let remove b x =
  let y = try map b x with Not_found -> failwith "Bij.remove" in
  { f = Gmap.remove x b.f; finv = Gmap.remove y b.finv }

let app f b = Gmap.iter f b.f

let to_list b = Gmap.to_list b.f


