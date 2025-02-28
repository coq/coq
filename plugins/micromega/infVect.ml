(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Extend the vector type with an infinitesimal constant,
    This is need to turn a strict inequality e > 0
    into a weak inequality e - ϵ >= 0 for some ϵ > 0
 *)
open NumCompat
open Q.Notations


type var = int
type t = Inf.t * Vect.t
type vector = t

let hash (i1,v1)  =
  Hashtbl.hash (Inf.hash i1,Vect.hash v1)

let equal (i1,v1) (i2,v2) =
  Inf.equal i1 i2 && Vect.equal v1 v2

let compare (i1,v1) (i2,v2) =
  let cmp = Inf.compare i1 i2 in
  if cmp = 0 then Vect.compare v1 v2
  else cmp

let pp_gen pp_var o (i,v) =
  match Inf.is_zero i , Vect.is_null v with
  | true , true   -> output_string o "0"
  | true , false  -> Vect.pp_gen pp_var o v
  | false , true  -> Inf.pp o i
  | false , false -> Printf.fprintf o "%a+%a" Inf.pp i (Vect.pp_gen pp_var) v

let pp_var o v = Printf.fprintf o "x%i" v

let pp o v = pp_gen pp_var o v

let pp_smt o (i,v) =
  Printf.fprintf o "(+ %a %a)" Inf.pp_smt i Vect.pp_smt v

let variables (i,v) = Vect.variables v

let get_cst (i,v) = i

let decomp_cst (i,v) = (i,v)

let cst q = (Inf.cst q,Vect.null)

let is_constant (_,v) = Vect.is_null v


let null = (Inf.zero,Vect.null)

let is_null (i,v) = Inf.equal Inf.zero i  && Vect.is_null v

let get vr (_,v) = Vect.get vr v

let set vr q (i,v) = (i,Vect.set vr q v)

let update vr f (i,v) = (i,Vect.update vr f v)

let fresh (i,v) = Vect.fresh v


let gcd (i,l) =
  Z.gcd (Inf.gcd i) (Vect.gcd l)

let normalise (i,l) =
  let (gcd,ppcm) = Vect.fold (fun (g,p) _ n -> (Z.gcd g (Q.num n) , Z.ppcm p (Q.den n))) (Z.zero,Z.one) l in
  let m = Q.of_bigint ppcm // Q.of_bigint gcd in
  if m =/ Q.one
  then  (i,l)
  else (Inf.mulc m i, Vect.mul m l)

let add (c1,v1) (c2,v2) =
  (Inf.add c1 c2, Vect.add v1 v2)

let mul q (i,v) = (Inf.mulc q i, Vect.mul q v)

let mul_add c1 (i1,v1) c2 (i2,v2) =
  (Inf.add (Inf.mulc c1 i1) (Inf.mulc c2 i2),
   Vect.mul_add c1 v1 c2 v2)

let subst x (i,v) (i',v') =
  let (n,r) = Vect.subst x v v' in
  (Inf.add i' (Inf.mulc n i),r)

let uminus (i,v) = (Inf.uminus i, Vect.uminus v)

let of_vect v strict =
  let (c,v) = Vect.decomp_cst v in
  (Inf.cste c strict,v)

let of_cst c = (c,Vect.null)
