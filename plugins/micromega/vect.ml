(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open NumCompat
open Q.Notations
open Mutils

(** [t] is the type of vectors.
        A vector [(x1,v1) ; ... ; (xn,vn)] is such that:
        - variables indexes are ordered (x1 < ... < xn
        - values are all non-zero
 *)
type var = int

type mono = {var : var; coe : Q.t}
type t = mono list
type vector = t

(** [equal v1 v2 = true] if the vectors are syntactically equal. *)

let rec equal v1 v2 =
  match (v1, v2) with
  | [], [] -> true
  | [], _ -> false
  | _ :: _, [] -> false
  | {var = i1; coe = n1} :: v1, {var = i2; coe = n2} :: v2 ->
    Int.equal i1 i2 && n1 =/ n2 && equal v1 v2

let hash v =
  let rec hash i = function
    | [] -> i
    | {var = vr; coe = vl} :: l -> hash (i + Hashtbl.hash (vr, Q.to_float vl)) l
  in
  Hashtbl.hash (hash 0 v)

let null = []

let is_null v =
  match v with
  | [] -> true
  | [{var = 0; coe = x}] when Q.zero =/ x -> true
  | _ -> false

let pp_var_num pp_var o {var = v; coe = n} =
  if Int.equal v 0 then
    if Q.zero =/ n then () else Printf.fprintf o "%s" (Q.to_string n)
  else if Q.one =/ n then pp_var o v
  else if Q.minus_one =/ n then Printf.fprintf o "-%a" pp_var v
  else if Q.zero =/ n then ()
  else Printf.fprintf o "%s*%a" (Q.to_string n) pp_var v

let pp_var_num_smt pp_var o {var = v; coe = n} =
  let pp_num o q =
    let nn = Q.num n in
    let dn = Q.den n in
    if Z.equal dn Z.one then output_string o (Z.to_string nn)
    else Printf.fprintf o "(/ %s %s)" (Z.to_string nn) (Z.to_string dn)
  in
  if Int.equal v 0 then if Q.zero =/ n then () else pp_num o n
  else if Q.one =/ n then pp_var o v
  else if Q.minus_one =/ n then Printf.fprintf o "(- %a)" pp_var v
  else if Q.zero =/ n then ()
  else Printf.fprintf o "(* %a %a)" pp_num n pp_var v

let rec pp_gen pp_var o v =
  match v with
  | [] -> output_string o "0"
  | [e] -> pp_var_num pp_var o e
  | e :: l -> Printf.fprintf o "%a + %a" (pp_var_num pp_var) e (pp_gen pp_var) l

let pp_var o v = Printf.fprintf o "x%i" v
let pp o v = pp_gen pp_var o v

let pp_smt o v =
  let list o v =
    List.iter (fun e -> Printf.fprintf o "%a " (pp_var_num_smt pp_var) e) v
  in
  Printf.fprintf o "(+ %a)" list v

let from_list (l : Q.t list) =
  let rec xfrom_list i l =
    match l with
    | [] -> []
    | e :: l ->
      if e <>/ Q.zero then {var = i; coe = e} :: xfrom_list (i + 1) l
      else xfrom_list (i + 1) l
  in
  xfrom_list 0 l

let cons i v rst = if v =/ Q.zero then rst else {var = i; coe = v} :: rst

let rec update i f t =
  match t with
  | [] -> cons i (f Q.zero) []
  | x :: l -> (
    match Int.compare i x.var with
    | 0 -> cons x.var (f x.coe) l
    | -1 -> cons i (f Q.zero) t
    | 1 -> x :: update i f l
    | _ -> failwith "compare_num" )

let rec set i n t =
  match t with
  | [] -> cons i n []
  | x :: l -> (
    match Int.compare i x.var with
    | 0 -> cons x.var n l
    | -1 -> cons i n t
    | 1 -> x :: set i n l
    | _ -> failwith "compare_num" )

let cst n = if n =/ Q.zero then [] else [{var = 0; coe = n}]

let mul z t =
  if z =/ Q.zero then []
  else if z =/ Q.one then t
  else List.map (fun {var = i; coe = n} -> {var = i; coe = z */ n}) t

let div z t =
  if z <>/ Q.one then
    List.map (fun {var = x; coe = nx} -> {var = x; coe = nx // z}) t
  else t

let uminus t = List.map (fun {var = i; coe = n} -> {var = i; coe = Q.neg n}) t

let rec add (ve1 : t) (ve2 : t) =
  match (ve1, ve2) with
  | [], v | v, [] -> v
  | {var = v1; coe = c1} :: l1, {var = v2; coe = c2} :: l2 ->
    let cmp = Int.compare v1 v2 in
    if cmp == 0 then
      let s = c1 +/ c2 in
      if Q.zero =/ s then add l1 l2 else {var = v1; coe = s} :: add l1 l2
    else if cmp < 0 then {var = v1; coe = c1} :: add l1 ve2
    else {var = v2; coe = c2} :: add l2 ve1

let rec xmul_add (n1 : Q.t) (ve1 : t) (n2 : Q.t) (ve2 : t) =
  match (ve1, ve2) with
  | [], _ -> mul n2 ve2
  | _, [] -> mul n1 ve1
  | {var = v1; coe = c1} :: l1, {var = v2; coe = c2} :: l2 ->
    let cmp = Int.compare v1 v2 in
    if cmp == 0 then
      let s = (n1 */ c1) +/ (n2 */ c2) in
      if Q.zero =/ s then xmul_add n1 l1 n2 l2
      else {var = v1; coe = s} :: xmul_add n1 l1 n2 l2
    else if cmp < 0 then {var = v1; coe = n1 */ c1} :: xmul_add n1 l1 n2 ve2
    else {var = v2; coe = n2 */ c2} :: xmul_add n1 ve1 n2 l2

let mul_add n1 ve1 n2 ve2 =
  if n1 =/ Q.one && n2 =/ Q.one then add ve1 ve2 else xmul_add n1 ve1 n2 ve2

let compare : t -> t -> int =
  Mutils.Cmp.compare_list (fun x y ->
      Mutils.Cmp.compare_lexical
        [(fun () -> Int.compare x.var y.var); (fun () -> Q.compare x.coe y.coe)])

(** [tail v vect] returns
        - [None] if [v] is not a variable of the vector [vect]
        - [Some(vl,rst)]  where [vl] is the value of [v] in vector [vect]
        and [rst] is the remaining of the vector
        We exploit that vectors are ordered lists
 *)
let rec tail (v : var) (vect : t) =
  match vect with
  | [] -> None
  | {var = v'; coe = vl} :: vect' -> (
    match Int.compare v' v with
    | 0 -> Some (vl, vect) (* Ok, found *)
    | -1 -> tail v vect' (* Might be in the tail *)
    | _ -> None )

(* Hopeless *)

let get v vect = match tail v vect with None -> Q.zero | Some (vl, _) -> vl
let is_constant v = match v with [] | [{var = 0}] -> true | _ -> false
let get_cst vect = match vect with {var = 0; coe = v} :: _ -> v | _ -> Q.zero

let choose v =
  match v with [] -> None | {var = vr; coe = vl} :: rst -> Some (vr, vl, rst)

let rec fresh v =
  match v with [] -> 1 | [{var = v}] -> v + 1 | _ :: v -> fresh v

let variables v =
  List.fold_left (fun acc {var = x} -> ISet.add x acc) ISet.empty v

let decomp_cst v =
  match v with {var = 0; coe = vl} :: v -> (vl, v) | _ -> (Q.zero, v)

let decomp_fst v =
  match v with [] -> ((0, Q.zero), []) | x :: v -> ((x.var, x.coe), v)

let rec subst (vr : int) (e : t) (v : t) =
  match v with
  | [] -> []
  | {var = x; coe = n} :: v' -> (
    match Int.compare vr x with
    | 0 -> mul_add n e Q.one v'
    | -1 -> v
    | 1 -> add [{var = x; coe = n}] (subst vr e v')
    | _ -> assert false )

let fold f acc v = List.fold_left (fun acc x -> f acc x.var x.coe) acc v

let rec find p v =
  match v with
  | [] -> None
  | {var = v; coe = n} :: v' -> (
    match p v n with None -> find p v' | Some r -> Some r )

let for_all p l = List.for_all (fun {var = v; coe = n} -> p v n) l
let decr_var i v = List.map (fun x -> {x with var = x.var - i}) v
let incr_var i v = List.map (fun x -> {x with var = x.var + i}) v

let gcd v =
  let res =
    fold
      (fun c _ n ->
        assert (Int.equal (Z.compare (Q.den n) Z.one) 0);
        Z.gcd c (Q.num n))
      Z.zero v
  in
  if Int.equal (Z.compare res Z.zero) 0 then Z.one else res

let normalise v =
  let ppcm = fold (fun c _ n -> Z.ppcm c (Q.den n)) Z.one v in
  let gcd =
    let gcd = fold (fun c _ n -> Z.gcd c (Q.num n)) Z.zero v in
    if Int.equal (Z.compare gcd Z.zero) 0 then Z.one else gcd
  in
  List.map
    (fun {var = x; coe = v} ->
      {var = x; coe = v */ Q.of_bigint ppcm // Q.of_bigint gcd})
    v

let rec exists2 p vect1 vect2 =
  match (vect1, vect2) with
  | _, [] | [], _ -> None
  | {var = v1; coe = n1} :: vect1', {var = v2; coe = n2} :: vect2' ->
    if Int.equal v1 v2 then
      if p n1 n2 then Some (v1, n1, n2) else exists2 p vect1' vect2'
    else if v1 < v2 then exists2 p vect1' vect2
    else exists2 p vect1 vect2'

let dotproduct v1 v2 =
  let rec dot acc v1 v2 =
    match (v1, v2) with
    | [], _ | _, [] -> acc
    | {var = x1; coe = n1} :: v1', {var = x2; coe = n2} :: v2' ->
      if Int.equal x1 x2 then dot (acc +/ (n1 */ n2)) v1' v2'
      else if x1 < x2 then dot acc v1' v2
      else dot acc v1 v2'
  in
  dot Q.zero v1 v2

module Bound = struct
  type t = {cst : Q.t; var : var; coeff : Q.t}

  let of_vect (v : vector) =
    match v with
    | [{var = x; coe = v}] ->
      if Int.equal x 0 then None else Some {cst = Q.zero; var = x; coeff = v}
    | [{var = 0; coe = v}; {var = x; coe = v'}] ->
      Some {cst = v; var = x; coeff = v'}
    | _ -> None

  let to_vect { cst = k; var = v; coeff = c } =
    let () = assert (not (c =/ Q.zero)) in
    if k =/ Q.zero then [{var = v; coe = c}]
    else [{var = 0; coe = k}; {var = v; coe = c}]
end
