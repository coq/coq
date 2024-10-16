(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-20018                            *)
(*                                                                      *)
(************************************************************************)

open NumCompat
open Q.Notations
open Mutils
module Mc = Micromega

let max_nb_cstr = ref max_int

type var = int

let debug = false
let ( <+> ) = ( +/ )
let ( <*> ) = ( */ )

module Monomial : sig
  type t

  val const : t
  val is_const : t -> bool
  val var : var -> t
  val is_var : t -> bool
  val get_var : t -> var option
  val prod : t -> t -> t
  val factor : t -> var -> t option
  val compare : t -> t -> int
  val pp : out_channel -> t -> unit
  val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a
  val sqrt : t -> t option
  val variables : t -> ISet.t
  val degree : t -> int
  val subset : t -> t -> bool
  val output : out_channel -> t -> unit
end =
struct
  type t = int array
  (* Compact representation [| d; e₀; v₀; ...; eₙ; vₙ |] where
    d = Σi v_i is the multi-degree
    e_i gives the variable number as a diff, i.e. the variable at position i
        is Σi e_i, and e_i ≠ 0 for all i > 0
    v_i is the degree of e_i, must be ≠ 0
  *)

  let const = [|0|]

  let subset m1 m2 =
    m1.(0) <= m2.(0) &&

    let len1 = Array.length m1 in
    let len2 = Array.length m2 in

    let get_var m c v =
      v+m.(c) , m.(c+1) in

    let rec xsubset cur1 v1 e1 cur2 v2 e2 =
      match Int.compare v1 v2 with
      | 0 -> e1 <= e2 &&
             (if cur1 + 2 = len1
              then true
              else if cur2 + 2 = len2
              then false
              else
                let (v1,e1) = get_var m1 (cur1+2) v1 in
                let (v2,e2) = get_var m2 (cur2+2) v2 in
                xsubset (cur1+2) v1 e1 (cur2+2) v2 e2)
      | -1 -> false
      |  _ -> if cur2 + 2 = len2
        then false
        else  let (v2,e2) = get_var m2 (cur2+2) v2 in
          xsubset cur1 v1 e1 (cur2+2) v2 e2
    in
    if len1 <= 1 then true
    else if len2 <= 1 then false
    else xsubset 1 m1.(1) m1.(2) 1 m2.(1) m2.(2)

  let is_const (m : t) = match m with [|_|] -> true | _ -> false

  let var x = [|1; x; 1|]

  let is_var (m : t) = Int.equal m.(0) 1

  let get_var (m : t) = match m with
  | [|1; x; _|] -> Some x
  | _ -> None

  let prod (m1 : t) (m2 : t) =
    let len1 = Array.length m1 in
    let len2 = Array.length m2 in
    (* Compute the number of variables in the monomial *)
    let rec nvars accu cur1 cur2 i1 i2 =
      if Int.equal i1 len1 && Int.equal i2 len2 then accu
      else if Int.equal i1 len1 then accu + (len2 - i2)
      else if Int.equal i2 len2 then accu + (len1 - i1)
      else
        let ncur1 = cur1 + m1.(i1) in
        let ncur2 = cur2 + m2.(i2) in
        if ncur1 < ncur2 then nvars (accu + 2) ncur1 cur2 (i1 + 2) i2
        else if ncur1 > ncur2 then nvars (accu + 2) cur1 ncur2 i1 (i2 + 2)
        else nvars (accu + 2) ncur1 ncur2 (i1 + 2) (i2 + 2)
    in
    let n = nvars 1 0 0 1 1 in
    let m = Array.make n 0 in
    let () = m.(0) <- m1.(0) + m2.(0) in
    (* Set the variable exponents *)
    let rec set cur cur1 cur2 i i1 i2 =
      if Int.equal i1 len1 && Int.equal i2 len2 then ()
      else if Int.equal i1 len1 then
        let ncur2 = cur2 + m2.(i2) in
        let () = m.(i) <- ncur2 - cur in
        let () = m.(i + 1) <- m2.(i2 + 1) in
        set ncur2 cur1 ncur2 (i + 2) i1 (i2 + 2)
      else if Int.equal i2 len2 then
        let ncur1 = cur1 + m1.(i1) in
        let () = m.(i) <- ncur1 - cur in
        let () = m.(i + 1) <- m1.(i1 + 1) in
        set ncur1 ncur1 cur2 (i + 2) (i1 + 2) i2
      else
        let ncur1 = cur1 + m1.(i1) in
        let ncur2 = cur2 + m2.(i2) in
        if ncur1 < ncur2 then
          let () = m.(i) <- ncur1 - cur in
          let () = m.(i + 1) <- m1.(i1 + 1) in
          set ncur1 ncur1 cur2 (i + 2) (i1 + 2) i2
        else if ncur1 > ncur2 then
          let () = m.(i) <- ncur2 - cur in
          let () = m.(i + 1) <- m2.(i2 + 1) in
          set ncur2 cur1 ncur2 (i + 2) i1 (i2 + 2)
        else
          let () = m.(i) <- ncur1 - cur in
          let () = m.(i + 1) <- m1.(i1 + 1) + m2.(i2 + 1) in
          set ncur1 ncur1 ncur2 (i + 2) (i1 + 2) (i2 + 2)
    in
    let () = set 0 0 0 1 1 1 in
    m

  (*  [factor m x] returns [None] if [x] does not appear in [m], and decreases
      its exponent by one otherwise *)
  let factor (m : t) (x : var) =
    let len = Array.length m in
    let rec factor cur i =
      if Int.equal i len then None
      else
        let ncur = cur + m.(i) in
        let k = m.(i + 1) in
        if ncur < x then factor ncur (i + 2)
        else if x < ncur then None
        else if Int.equal k 1 then
          (* Need to squeeze out the binding for x *)
          let ans = Array.make (len - 2) 0 in
          let () = ans.(0) <- m.(0) - 1 in
          let () = Array.blit m 1 ans 1 (i - 1) in
          let () = Array.blit m (i + 2) ans i (len - i - 2) in
          (* Correct the diff *)
          let () = if not (Int.equal len (i + 2)) then ans.(i) <- ans.(i) + m.(i) in
          Some ans
        else
          let ans = Array.copy m in
          let () = ans.(0) <- ans.(0) - 1 in
          let () = ans.(i + 1) <- ans.(i + 1) - 1 in
          Some ans
    in
    factor 0 1

  let compare (m1 : t) (m2 : t) = CArray.compare Int.compare m1 m2

  let sqrt (m : t) = match m with
  | [|_|] -> Some const
  | _ ->
    let m = Array.copy m in
    let len = Array.length m in
    let () = m.(0) <- m.(0) / 2 in
    let rec set i =
      if Int.equal i len then ()
      else
        let v = m.(i + 1) in
        let () = if v mod 2 = 0 then m.(i + 1) <- v / 2 else raise_notrace Exit in
        set (i + 2)
    in
    try let () = set 1 in Some m with Exit -> None

  let degree (m : t) = m.(0)

  let fold f (m : t) accu =
    let len = Array.length m in
    let rec fold accu cur i =
      if Int.equal i len then accu
      else
        let cur = cur + m.(i) in
        let accu = f cur m.(i + 1) accu in
        fold accu cur (i + 2)
    in
    fold accu 0 1

  let output o m = fold (fun v i () -> Printf.fprintf o "x%i^%i" v i) m ()


  let variables (m : t) =
    fold (fun x _ accu -> ISet.add x accu) m ISet.empty

  let pp o m =
    let pp_elt o (k, v) =
      if v = 1 then Printf.fprintf o "x%i" k else Printf.fprintf o "x%i^%i" k v
    in
    let rec pp_list o l =
      match l with
      | [] -> ()
      | [e] -> pp_elt o e
      | e :: l -> Printf.fprintf o "%a*%a" pp_elt e pp_list l
    in
    pp_list o (List.rev @@ fold (fun x v accu -> (x, v) :: accu) m [])

end

module MonMap = struct
  include Map.Make (Monomial)

  let union f =
    merge (fun x v1 v2 ->
        match (v1, v2) with
        | None, None -> None
        | Some v, None | None, Some v -> Some v
        | Some v1, Some v2 -> f x v1 v2)
end

let pp_mon o (m, i) =
  if Monomial.is_const m then
    if Q.zero =/ i then () else Printf.fprintf o "%s" (Q.to_string i)
  else if Q.one =/ i then Monomial.pp o m
  else if Q.minus_one =/ i then Printf.fprintf o "-%a" Monomial.pp m
  else if Q.zero =/ i then ()
  else Printf.fprintf o "%s*%a" (Q.to_string i) Monomial.pp m

module Poly : (* A polynomial is a map of monomials *)
              (*
    This is probably a naive implementation
    (expected to be fast enough - Rocq is probably the bottleneck)
    *The new ring contribution is using a sparse Horner representation.
    *)
sig
  type t

  val pp : out_channel -> t -> unit
  val get : Monomial.t -> t -> Q.t
  val variable : var -> t
  val add : Monomial.t -> Q.t -> t -> t
  val constant : Q.t -> t
  val product : t -> t -> t
  val addition : t -> t -> t
  val uminus : t -> t
  val fold : (Monomial.t -> Q.t -> 'a -> 'a) -> t -> 'a -> 'a
  val factorise : var -> t -> t * t
end = struct
  (*normalisation bug : 0*x ... *)
  module P = Map.Make (Monomial)
  open P

  type t = Q.t P.t

  let pp o p = P.iter (fun mn i -> Printf.fprintf o "%a + " pp_mon (mn, i)) p

  (* Get the coefficient of monomial mn *)
  let get : Monomial.t -> t -> Q.t =
   fun mn p -> try find mn p with Not_found -> Q.zero

  (* The polynomial 1.x *)
  let variable : var -> t = fun x -> add (Monomial.var x) Q.one empty

  (*The constant polynomial *)
  let constant : Q.t -> t = fun c -> add Monomial.const c empty

  (* The addition of a monomial *)

  let add : Monomial.t -> Q.t -> t -> t =
   fun mn v p ->
    if Q.sign v = 0 then p
    else
      let vl = get mn p <+> v in
      if Q.sign vl = 0 then remove mn p else add mn vl p

  (** Design choice: empty is not a polynomial
     I do not remember why ....
   **)

  (* The product by a monomial *)
  let mult : Monomial.t -> Q.t -> t -> t =
   fun mn v p ->
    if Q.sign v = 0 then constant Q.zero
    else
      fold
        (fun mn' v' res -> P.add (Monomial.prod mn mn') (v <*> v') res)
        p empty

  let addition : t -> t -> t =
   fun p1 p2 -> fold (fun mn v p -> add mn v p) p1 p2

  let product : t -> t -> t =
   fun p1 p2 -> fold (fun mn v res -> addition (mult mn v p2) res) p1 empty

  let uminus : t -> t = fun p -> map (fun v -> Q.neg v) p
  let fold = P.fold

  let factorise x p =
    P.fold
      (fun m v (px, cx) ->
        match Monomial.factor m x with
        | None -> (px, add m v cx)
        | Some mx ->
          (add mx v px, cx))
      p
      (constant Q.zero, constant Q.zero)
end

type vector = Vect.t

type cstr = {coeffs : vector; op : op; cst : Q.t}

and op = Eq | Ge | Gt

exception Strict

let is_strict c = c.op = Gt
let eval_op = function Eq -> ( =/ ) | Ge -> ( >=/ ) | Gt -> ( >/ )
let string_of_op = function Eq -> "=" | Ge -> ">=" | Gt -> ">"

let compare_op o1 o2 =
  match (o1, o2) with
  | Eq, Eq -> 0
  | Eq, _ -> -1
  | _, Eq -> 1
  | Ge, Ge -> 0
  | Ge, _ -> -1
  | _, Ge -> 1
  | Gt, Gt -> 0

let output_cstr o {coeffs; op; cst} =
  Printf.fprintf o "%a %s %s" Vect.pp coeffs (string_of_op op) (Q.to_string cst)

let opMult o1 o2 =
  match (o1, o2) with Eq, _ | _, Eq -> Eq | Ge, _ | _, Ge -> Ge | Gt, Gt -> Gt

let opAdd o1 o2 =
  match (o1, o2) with Eq, x | x, Eq -> x | Gt, x | x, Gt -> Gt | Ge, Ge -> Ge

module LinPoly = struct
  (** A linear polynomial a0 + a1.x1 + ... + an.xn
      By convention, the constant a0 is the coefficient of the variable 0.
   *)

  type t = Vect.t

  module MonT = struct
    module MonoMap = Map.Make (Monomial)
    module IntMap = Map.Make (Int)

    (** A hash table might be preferable but requires a hash function. *)
    let (index_of_monomial : int MonoMap.t ref) = ref MonoMap.empty

    let (monomial_of_index : Monomial.t IntMap.t ref) = ref IntMap.empty
    let fresh = ref 0

    let reserve vr =
      if !fresh > vr then failwith (Printf.sprintf "Cannot reserve %i" vr)
      else fresh := vr + 1

    let safe_reserve vr = if !fresh > vr then () else fresh := vr + 1

    let get_fresh () =
      let vr = !fresh in
      incr fresh; vr

    let register m =
      try MonoMap.find m !index_of_monomial
      with Not_found ->
        let res = !fresh in
        index_of_monomial := MonoMap.add m res !index_of_monomial;
        monomial_of_index := IntMap.add res m !monomial_of_index;
        incr fresh;
        res

    let retrieve i = IntMap.find i !monomial_of_index

    let clear () =
      index_of_monomial := MonoMap.empty;
      monomial_of_index := IntMap.empty;
      fresh := 0;
      ignore (register Monomial.const)

    let _ = register Monomial.const
  end

  let var v = Vect.set (MonT.register (Monomial.var v)) Q.one Vect.null

  let of_monomial m =
    let v = MonT.register m in
    Vect.set v Q.one Vect.null

  let linpol_of_pol p =
    Poly.fold
      (fun mon num vct ->
        let vr = MonT.register mon in
        Vect.set vr num vct)
      p Vect.null

  let pol_of_linpol v =
    Vect.fold
      (fun p vr n -> Poly.add (MonT.retrieve vr) n p)
      (Poly.constant Q.zero) v

  let rocq_poly_of_linpol cst p =
    let pol_of_mon m =
      Monomial.fold
        (fun x v p ->
          Mc.PEmul (Mc.PEpow (Mc.PEX (CamlToCoq.positive x), CamlToCoq.n v), p))
        m
        (Mc.PEc (cst Q.one))
    in
    Vect.fold
      (fun acc x v ->
        let mn = MonT.retrieve x in
        Mc.PEadd (Mc.PEmul (Mc.PEc (cst v), pol_of_mon mn), acc))
      (Mc.PEc (cst Q.zero))
      p

  let pp_var o vr =
    try Monomial.pp o (MonT.retrieve vr) (* this is a non-linear variable *)
    with Not_found -> Printf.fprintf o "v%i" vr

  let pp o p = Vect.pp_gen pp_var o p
  let constant c = if Q.sign c = 0 then Vect.null else Vect.set 0 c Vect.null

  let is_linear p =
    Vect.for_all
      (fun v _ ->
        let mn = MonT.retrieve v in
        Monomial.is_var mn || Monomial.is_const mn)
      p

  let is_variable p =
    let (x, v), r = Vect.decomp_fst p in
    if Vect.is_null r && v >/ Q.zero then Monomial.get_var (MonT.retrieve x)
    else None

  let factorise x p =
    let px, cx = Poly.factorise x (pol_of_linpol p) in
    (linpol_of_pol px, linpol_of_pol cx)

  let is_linear_for x p =
    let a, b = factorise x p in
    Vect.is_constant a

  let search_all_linear p l =
    Vect.fold
      (fun acc x v ->
        if p v then
          let x' = MonT.retrieve x in
          match Monomial.get_var x' with
          | None -> acc
          | Some x -> if is_linear_for x l then x :: acc else acc
        else acc)
      [] l

  let min_list (l : int list) =
    match l with [] -> None | e :: l -> Some (List.fold_left min e l)

  let search_linear p l = min_list (search_all_linear p l)

  let mul_cst c p = Vect.mul c p

  let product p1 p2 =
    linpol_of_pol (Poly.product (pol_of_linpol p1) (pol_of_linpol p2))

  let addition p1 p2 = Vect.add p1 p2

  let of_vect v =
    Vect.fold
      (fun acc v vl -> addition (product (var v) (constant vl)) acc)
      Vect.null v

  let variables p =
    Vect.fold
      (fun acc v _ -> ISet.union (Monomial.variables (MonT.retrieve v)) acc)
      ISet.empty p

  let monomials p = Vect.fold (fun acc v _ -> ISet.add v acc) ISet.empty p

  let pp_goal typ o l =
    let vars =
      List.fold_left
        (fun acc p -> ISet.union acc (variables (fst p)))
        ISet.empty l
    in
    let pp_vars o i =
      ISet.iter (fun v -> Printf.fprintf o "(x%i : %s) " v typ) vars
    in
    Printf.fprintf o "forall %a\n" pp_vars vars;
    List.iteri
      (fun i (p, op) ->
        Printf.fprintf o "(H%i : %a %s 0)\n" i pp p (string_of_op op))
      l;
    Printf.fprintf o ", False\n"

  let collect_square p =
    Vect.fold
      (fun acc v _ ->
        let m = MonT.retrieve v in
        match Monomial.sqrt m with None -> acc | Some s -> MonMap.add s m acc)
      MonMap.empty p
end

module ProofFormat = struct
  type prf_rule =
    | Annot of string * prf_rule
    | Hyp of int
    | Def of int
    | Ref of int
    | Cst of Q.t
    | Zero
    | Square of Vect.t
    | MulC of Vect.t * prf_rule
    | Gcd of Z.t * prf_rule
    | MulPrf of prf_rule * prf_rule
    | AddPrf of prf_rule * prf_rule
    | CutPrf of prf_rule
    | LetPrf of prf_rule * prf_rule

  type proof =
    | Done
    | Step of int * prf_rule * proof
    | Split of int * Vect.t * proof * proof
    | Enum of int * prf_rule * Vect.t * prf_rule * proof list
    | ExProof of int * int * int * var * var * var * proof

  (* x = z - t, z >= 0, t >= 0 *)

  let rec output_prf_rule o = function
    | Annot (s, p) -> Printf.fprintf o "(%a)@%s" output_prf_rule p s
    | Hyp i -> Printf.fprintf o "Hyp %i" i
    | Def i -> Printf.fprintf o "Def %i" i
    | Ref i -> Printf.fprintf o "Ref %i" i
    | LetPrf (p1, p2) ->
      Printf.fprintf o "Let (%a) in %a" output_prf_rule p1 output_prf_rule p2
    | Cst c -> Printf.fprintf o "Cst %s" (Q.to_string c)
    | Zero -> Printf.fprintf o "Zero"
    | Square s -> Printf.fprintf o "(%a)^2" Poly.pp (LinPoly.pol_of_linpol s)
    | MulC (p, pr) ->
      Printf.fprintf o "(%a) * (%a)" Poly.pp (LinPoly.pol_of_linpol p)
        output_prf_rule pr
    | MulPrf (p1, p2) ->
      Printf.fprintf o "(%a) * (%a)" output_prf_rule p1 output_prf_rule p2
    | AddPrf (p1, p2) ->
      Printf.fprintf o "%a + %a" output_prf_rule p1 output_prf_rule p2
    | CutPrf p -> Printf.fprintf o "[%a]" output_prf_rule p
    | Gcd (c, p) -> Printf.fprintf o "(%a)/%s" output_prf_rule p (Z.to_string c)

  let rec output_proof o = function
    | Done -> Printf.fprintf o "."
    | Step (i, p, pf) ->
      Printf.fprintf o "%i:= %a\n ; %a" i output_prf_rule p output_proof pf
    | Split (i, v, p1, p2) ->
      Printf.fprintf o "%i:=%a ; { %a } { %a }" i Vect.pp v output_proof p1
        output_proof p2
    | Enum (i, p1, v, p2, pl) ->
      Printf.fprintf o "%i{%a<=%a<=%a}%a" i output_prf_rule p1 Vect.pp v
        output_prf_rule p2 (pp_list ";" output_proof) pl
    | ExProof (i, j, k, x, z, t, pr) ->
      Printf.fprintf o "%i := %i = %i - %i ; %i := %i >= 0 ; %i := %i >= 0 ; %a"
        i x z t j z k t output_proof pr

  module OrdPrfRule = struct
    type t = prf_rule

    let id_of_constr = function
      | Annot _ -> 0
      | Hyp _ -> 1
      | Def _ -> 2
      | Ref _ -> 3
      | Cst _ -> 4
      | Zero -> 5
      | Square _ -> 6
      | MulC _ -> 7
      | Gcd _ -> 8
      | MulPrf _ -> 9
      | AddPrf _ -> 10
      | CutPrf _ -> 11
      | LetPrf _ -> 12

    let cmp_pair c1 c2 (x1, x2) (y1, y2) =
      match c1 x1 y1 with 0 -> c2 x2 y2 | i -> i

    let rec compare p1 p2 =
      match (p1, p2) with
      | Annot (s1, p1), Annot (s2, p2) ->
        if s1 = s2 then compare p1 p2 else String.compare s1 s2
      | Hyp i, Hyp j -> Int.compare i j
      | Def i, Def j -> Int.compare i j
      | Ref i, Ref j -> Int.compare i j
      | Cst n, Cst m -> Q.compare n m
      | Zero, Zero -> 0
      | Square v1, Square v2 -> Vect.compare v1 v2
      | MulC (v1, p1), MulC (v2, p2) ->
        cmp_pair Vect.compare compare (v1, p1) (v2, p2)
      | Gcd (b1, p1), Gcd (b2, p2) ->
        cmp_pair Z.compare compare (b1, p1) (b2, p2)
      | MulPrf (p1, q1), MulPrf (p2, q2) ->
        cmp_pair compare compare (p1, q1) (p2, q2)
      | AddPrf (p1, q1), AddPrf (p2, q2) ->
        cmp_pair compare compare (p1, q1) (p2, q2)
      | CutPrf p, CutPrf p' -> compare p p'
      | LetPrf(p1,q1) , LetPrf(p2,q2) ->
        cmp_pair compare compare (p1, q1) (p2, q2)
      | _, _ -> Int.compare (id_of_constr p1) (id_of_constr p2)
  end

  module PrfRuleMap = Map.Make (OrdPrfRule)

  let rec pr_size = function
    | Annot (_, p) -> pr_size p
    | Zero | Square _ -> Q.zero
    | Hyp _ -> Q.one
    | Def _ -> Q.one
    | Ref _ -> Q.one
    | Cst n -> n
    | Gcd (i, p) -> pr_size p // Q.of_bigint i
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      pr_size p1 +/ pr_size p2
    | CutPrf p -> pr_size p
    | MulC (v, p) -> pr_size p

  let rec pr_unit  = function
    | Annot (_, p) -> pr_unit p
    | Zero | Square _ -> true
    | Hyp _ -> true
    | Def _ -> true
    | Cst n -> true
    | _ -> false

  let rec pr_rule_max_hyp = function
    | Annot (_, p) -> pr_rule_max_hyp p
    | Hyp i -> i
    | Def i -> -1
    | Ref i -> -1
    | Cst _ | Zero | Square _ -> -1
    | MulC (_, p) | CutPrf p | Gcd (_, p) -> pr_rule_max_hyp p
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      max (pr_rule_max_hyp p1) (pr_rule_max_hyp p2)

  let rec pr_rule_max_def = function
    | Annot (_, p) -> pr_rule_max_hyp p
    | Hyp i -> -1
    | Def i -> i
    | Ref _ -> -1
    | Cst _ | Zero | Square _ -> -1
    | MulC (_, p) | CutPrf p | Gcd (_, p) -> pr_rule_max_def p
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      max (pr_rule_max_def p1) (pr_rule_max_def p2)

  let rec proof_max_def = function
    | Done -> -1
    | Step (i, pr, prf) -> max i (max (pr_rule_max_def pr) (proof_max_def prf))
    | Split (i, _, p1, p2) -> max i (max (proof_max_def p1) (proof_max_def p2))
    | Enum (i, p1, _, p2, l) ->
      let m = max (pr_rule_max_def p1) (pr_rule_max_def p2) in
      List.fold_left (fun i prf -> max i (proof_max_def prf)) (max i m) l
    | ExProof (i, j, k, _, _, _, prf) ->
      max (max (max i j) k) (proof_max_def prf)

  (** [pr_rule_def_cut id pr] gives an explicit [id] to cut rules.
      This is because the Rocq proof format only accept they as a proof-step *)
  let pr_rule_def_cut m id p =
    let rec pr_rule_def_cut m id = function
      | Annot (_, p) -> pr_rule_def_cut m id p
      | MulC (p, prf) ->
        let bds, m, id', prf' = pr_rule_def_cut m id prf in
        (bds, m, id', MulC (p, prf'))
      | MulPrf (p1, p2) ->
        let bds1, m, id, p1 = pr_rule_def_cut m id p1 in
        let bds2, m, id, p2 = pr_rule_def_cut m id p2 in
        (bds2 @ bds1, m, id, MulPrf (p1, p2))
      | AddPrf (p1, p2) ->
        let bds1, m, id, p1 = pr_rule_def_cut m id p1 in
        let bds2, m, id, p2 = pr_rule_def_cut m id p2 in
        (bds2 @ bds1, m, id, AddPrf (p1, p2))
      | LetPrf (p1, p2) ->
        let bds1, m, id, p1 = pr_rule_def_cut m id p1 in
        let bds2, m, id, p2 = pr_rule_def_cut m id p2 in
        (bds2 @ bds1, m, id, LetPrf (p1, p2))
      | CutPrf p | Gcd (_, p) -> (
        let bds, m, id, p = pr_rule_def_cut m id p in
        try
          let id' = PrfRuleMap.find p m in
          (bds, m, id, Def id')
        with Not_found ->
          let m = PrfRuleMap.add p id m in
          ((id, p) :: bds, m, id + 1, Def id) )
      | (Square _ | Cst _ | Def _ | Hyp _ | Ref _ | Zero) as x -> ([], m, id, x)
    in
    pr_rule_def_cut m id p

  (* Do not define top-level cuts *)
  let pr_rule_def_cut m id = function
    | CutPrf p ->
      let bds, m, ids, p' = pr_rule_def_cut m id p in
      (bds, m, ids, CutPrf p')
    | p -> pr_rule_def_cut m id p

  let rec implicit_cut p = match p with CutPrf p -> implicit_cut p | _ -> p

  let rec pr_rule_collect_defs pr =
    match pr with
    | Annot (_, pr) -> pr_rule_collect_defs pr
    | Def i -> ISet.add i ISet.empty
    | Hyp i -> ISet.empty
    | Ref i -> ISet.empty
    | Cst _ | Zero | Square _ -> ISet.empty
    | MulC (_, pr) | Gcd (_, pr) | CutPrf pr -> pr_rule_collect_defs pr
    | MulPrf (p1, p2) | AddPrf (p1, p2) | LetPrf (p1, p2) ->
      ISet.union (pr_rule_collect_defs p1) (pr_rule_collect_defs p2)


  let add_proof x y =
    match (x, y) with Zero, p | p, Zero -> p | _ -> AddPrf (x, y)

  let rec mul_cst_proof c p =
    match p with
    | Annot (s, p) -> Annot (s, mul_cst_proof c p)
    | MulC (v, p') -> MulC (Vect.mul c v, p')
    | _ -> (
      match Q.sign c with
      | 0 -> Zero (* This is likely to be a bug *)
      | -1 ->
        MulC (LinPoly.constant c, p) (* [p] should represent an equality *)
      | 1 -> if Q.one =/ c then p else MulPrf (Cst c, p)
      | _ -> assert false )

  let sMulC v p =
    let c, v' = Vect.decomp_cst v in
    if Vect.is_null v' then mul_cst_proof c p else MulC (v, p)

  let mul_proof p1 p2 =
    match (p1, p2) with
    | Zero, _ | _, Zero -> Zero
    | Cst c, p | p, Cst c -> mul_cst_proof c p
    | _, _ -> MulPrf (p1, p2)

  let prf_rule_of_map m =
    PrfRuleMap.fold (fun k v acc -> add_proof (sMulC v k) acc) m Zero

  let rec dev_prf_rule p =
    match p with
    | Annot (s, p) -> dev_prf_rule p
    | Hyp _ | Def _ | Ref _ | Cst _ | Zero | Square _ ->
      PrfRuleMap.singleton p (LinPoly.constant Q.one)
    | MulC (v, p) ->
      PrfRuleMap.map (fun v1 -> LinPoly.product v v1) (dev_prf_rule p)
    | AddPrf (p1, p2) ->
      PrfRuleMap.merge
        (fun k o1 o2 ->
          match (o1, o2) with
          | None, None -> None
          | None, Some v | Some v, None -> Some v
          | Some v1, Some v2 -> Some (LinPoly.addition v1 v2))
        (dev_prf_rule p1) (dev_prf_rule p2)
    | MulPrf (p1, p2) -> (
      let p1' = dev_prf_rule p1 in
      let p2' = dev_prf_rule p2 in
      let p1'' = prf_rule_of_map p1' in
      let p2'' = prf_rule_of_map p2' in
      match p1'' with
      | Cst c -> PrfRuleMap.map (fun v1 -> Vect.mul c v1) p2'
      | _ -> PrfRuleMap.singleton (MulPrf (p1'', p2'')) (LinPoly.constant Q.one)
      )
    | Gcd (c, p) ->
      PrfRuleMap.singleton
        (Gcd (c, prf_rule_of_map (dev_prf_rule p)))
        (LinPoly.constant Q.one)
    | CutPrf p ->
      PrfRuleMap.singleton
        (CutPrf (prf_rule_of_map (dev_prf_rule p)))
        (LinPoly.constant Q.one)
    | LetPrf (p1, p2) ->
      let p1' = dev_prf_rule p1 in
      let p2' = dev_prf_rule p2 in
      let p1'' = prf_rule_of_map p1' in
      let p2'' = prf_rule_of_map p2' in
      PrfRuleMap.singleton (LetPrf (p1'', p2'')) (LinPoly.constant Q.one)

  let simplify_prf_rule p = prf_rule_of_map (dev_prf_rule p)

  (** [simplify_proof p] removes proof steps that are never re-used. *)
  let rec simplify_proof p =
    match p with
    | Done -> (Done, ISet.empty)
    | Step (i, pr, Done) -> (p, ISet.add i (pr_rule_collect_defs pr))
    | Step (i, pr, prf) ->
      let prf', hyps = simplify_proof prf in
      if not (ISet.mem i hyps) then (prf', hyps)
      else
        ( Step (i, pr, prf')
        , ISet.add i (ISet.union (pr_rule_collect_defs pr) hyps) )
    | Split (i, v, p1, p2) ->
      let p1, h1 = simplify_proof p1 in
      let p2, h2 = simplify_proof p2 in
      if not (ISet.mem i h1) then (p1, h1) (* Should not have computed p2 *)
      else if not (ISet.mem i h2) then (p2, h2)
      else (Split (i, v, p1, p2), ISet.add i (ISet.union h1 h2))
    | Enum (i, p1, v, p2, pl) ->
      let pl, hl = List.split (List.map simplify_proof pl) in
      let hyps = List.fold_left ISet.union ISet.empty hl in
      ( Enum (i, p1, v, p2, pl)
      , ISet.add i
          (ISet.union
             (ISet.union (pr_rule_collect_defs p1) (pr_rule_collect_defs p2))
             hyps) )
    | ExProof (i, j, k, x, z, t, prf) ->
      let prf', hyps = simplify_proof prf in
      if
        (not (ISet.mem i hyps))
        && (not (ISet.mem j hyps))
        && not (ISet.mem k hyps)
      then (prf', hyps)
      else
        ( ExProof (i, j, k, x, z, t, prf')
        , ISet.add i (ISet.add j (ISet.add k hyps)) )

  let rec normalise_proof id prf =
    match prf with
    | Done -> (id, Done)
    | Step (i, Gcd (c, p), Done) -> normalise_proof id (Step (i, p, Done))
    | Step (i, p, prf) ->
      let bds, m, id, p' =
        pr_rule_def_cut PrfRuleMap.empty id (simplify_prf_rule p)
      in
      let id, prf = normalise_proof id prf in
      let prf =
        List.fold_left
          (fun acc (i, p) -> Step (i, CutPrf p, acc))
          (Step (i, p', prf))
          bds
      in
      (id, prf)
    | Split (i, v, p1, p2) ->
      let id, p1 = normalise_proof id p1 in
      let id, p2 = normalise_proof id p2 in
      (id, Split (i, v, p1, p2))
    | ExProof (i, j, k, x, z, t, prf) ->
      let id, prf = normalise_proof id prf in
      (id, ExProof (i, j, k, x, z, t, prf))
    | Enum (i, p1, v, p2, pl) ->
      (* Why do I have  top-level cuts ? *)
      (* let p1 = implicit_cut p1 in
         let p2 = implicit_cut p2 in
         let (ids,prfs) = List.split (List.map (normalise_proof id) pl) in
           (List.fold_left max  0 ids ,
              Enum(i,p1,v,p2,prfs))
      *)
      let bds1, m, id, p1' =
        pr_rule_def_cut PrfRuleMap.empty id (implicit_cut p1)
      in
      let bds2, m, id, p2' = pr_rule_def_cut m id (implicit_cut p2) in
      let ids, prfs = List.split (List.map (normalise_proof id) pl) in
      ( List.fold_left max 0 ids
      , List.fold_left
          (fun acc (i, p) -> Step (i, CutPrf p, acc))
          (Enum (i, p1', v, p2', prfs))
          (bds2 @ bds1) )

  let normalise_proof id prf =
    let prf = fst (simplify_proof prf) in
    let res = normalise_proof id prf in
    if debug then
      Printf.printf "normalise_proof %a -> %a" output_proof prf output_proof
        (snd res);
    res

  (*
  let mul_proof p1 p2 =
    let res = mul_proof p1 p2 in
    Printf.printf "mul_proof %a %a = %a\n"
    output_prf_rule p1 output_prf_rule p2 output_prf_rule res; res

  let add_proof p1 p2 =
    let res = add_proof p1 p2 in
    Printf.printf "add_proof %a %a = %a\n"
    output_prf_rule p1 output_prf_rule p2 output_prf_rule res; res


  let sMulC v p =
    let res = sMulC v p in
    Printf.printf "sMulC %a %a = %a\n" Vect.pp v output_prf_rule p output_prf_rule res ;
    res

  let mul_cst_proof c p  =
    let res = mul_cst_proof c p in
    Printf.printf "mul_cst_proof %s %a = %a\n" (Num.string_of_num c) output_prf_rule p output_prf_rule res ;
    res
 *)

  let proof_of_farkas env vect =
    Vect.fold
      (fun prf x n -> add_proof (mul_cst_proof n (IMap.find x env)) prf)
      Zero vect

  module Env :
  sig
    type t
    val make : int -> t
    val id_of_def : int -> t -> int
    val id_of_hyp : int -> t -> int
    val push_ref : t -> t
    val push_def : int -> t -> t
  end =
  struct

    (* Environments are of the form refs @ defs @ hyps *)
    type t =
      {
        lref  : int;
        ndefs : int; (* Size of ldefs *)
        ldefs : int Int.Map.t;
        nhyps : int;
      }

    let push_ref { nhyps; ndefs; lref; ldefs } =
      { nhyps; ndefs; lref = lref + 1; ldefs }

    let push_def i { nhyps; ndefs; lref; ldefs } =
      let () = if lref <> 0 then failwith "Cannot push def" in
      { nhyps; ndefs = ndefs + 1; lref; ldefs = Int.Map.add i ndefs ldefs }

    let make n = { nhyps = n; ndefs = 0; lref = 0; ldefs = Int.Map.empty }

    let id_of_def def { nhyps; ndefs; lref; ldefs } =
      try
        let pos = Int.Map.find def ldefs in
        lref + (ndefs - pos - 1)
      with Not_found -> failwith "Cannot find def"

    let id_of_hyp h { nhyps; ndefs; lref; ldefs } =
      if 0 <= h && h < nhyps then lref + ndefs + h
      else failwith "Cannot find hyp"

  end


  let cmpl_prf_rule norm (cst : Q.t -> 'a) env prf =
    let rec cmpl env = function
      | Annot (s, p) -> cmpl env p
      | Ref i -> Mc.PsatzIn (CamlToCoq.nat i)
      | Hyp h -> Mc.PsatzIn (CamlToCoq.nat (Env.id_of_hyp h env))
      | Def d -> Mc.PsatzIn (CamlToCoq.nat (Env.id_of_def d env))
      | Cst i -> Mc.PsatzC (cst i)
      | Zero -> Mc.PsatzZ
      | MulPrf (p1, p2) -> Mc.PsatzMulE (cmpl env p1, cmpl env p2)
      | AddPrf (p1, p2) -> Mc.PsatzAdd (cmpl env p1, cmpl env p2)
      | LetPrf (p1, p2) -> Mc.PsatzLet (cmpl env p1, cmpl (Env.push_ref env) p2)
      | MulC (lp, p) ->
        let lp = norm (LinPoly.rocq_poly_of_linpol cst lp) in
        Mc.PsatzMulC (lp, cmpl env p)
      | Square lp -> Mc.PsatzSquare (norm (LinPoly.rocq_poly_of_linpol cst lp))
      | _ -> failwith "Cuts should already be compiled"
    in
    cmpl env prf

  let cmpl_prf_rule_z env r =
    cmpl_prf_rule Mc.normZ (fun x -> CamlToCoq.bigint (Q.num x)) env r

  let cmpl_pol_z lp =
    try
      let cst x = CamlToCoq.bigint (Q.num x) in
      Mc.normZ (LinPoly.rocq_poly_of_linpol cst lp)
    with x ->
      Printf.printf "cmpl_pol_z %s %a\n" (Printexc.to_string x) LinPoly.pp lp;
      raise x

  let rec cmpl_proof env prf =
    match prf with
    | Done -> Mc.DoneProof
    | Step (i, p, prf) -> (
      match p with
      | CutPrf p' ->
        Mc.CutProof (cmpl_prf_rule_z env p', cmpl_proof (Env.push_def i env) prf)
      | _ -> Mc.RatProof (cmpl_prf_rule_z env p, cmpl_proof (Env.push_def i  env) prf)
      )
    | Split (i, v, p1, p2) ->
      Mc.SplitProof
        ( cmpl_pol_z v
        , cmpl_proof (Env.push_def i env) p1
        , cmpl_proof (Env.push_def i env) p2 )
    | Enum (i, p1, _, p2, l) ->
      Mc.EnumProof
        ( cmpl_prf_rule_z env p1
        , cmpl_prf_rule_z env p2
        , List.map (cmpl_proof (Env.push_def i env)) l )
    | ExProof (i, j, k, x, _, _, prf) ->
      Mc.ExProof
        (CamlToCoq.positive x, cmpl_proof (Env.push_def i  (Env.push_def j (Env.push_def k env))) prf)

  let compile_proof env prf =
    let id = 1 + proof_max_def prf in
    let _, prf = normalise_proof id prf in
    cmpl_proof env prf

end

module WithProof = struct
  type t = (LinPoly.t * op) * ProofFormat.prf_rule

  let repr p = p

  let proof p = snd p

  let polynomial ((p, _), _) = p

  (* The comparison ignores proofs on purpose *)
  let compare : t -> t -> int =
   fun ((lp1, o1), _) ((lp2, o2), _) ->
    let c = Vect.compare lp1 lp2 in
    if c = 0 then compare_op o1 o2 else c

  let annot s (p, prf) = (p, ProofFormat.Annot (s, prf))

  let output o ((lp, op), prf) =
    Printf.fprintf o "%a %s 0 by %a\n" LinPoly.pp lp (string_of_op op)
      ProofFormat.output_prf_rule prf

  let output_sys o l = List.iter (Printf.fprintf o "%a\n" output) l

  exception InvalidProof

  let zero = ((Vect.null, Eq), ProofFormat.Zero)
  let const n = ((LinPoly.constant n, Ge), ProofFormat.Cst n)
  let of_cstr (c, prf) = ((Vect.set 0 (Q.neg c.cst) c.coeffs, c.op), prf)

  let product : t -> t -> t =
   fun ((p1, o1), prf1) ((p2, o2), prf2) ->
    ((LinPoly.product p1 p2, opMult o1 o2), ProofFormat.mul_proof prf1 prf2)

  let addition : t -> t -> t =
   fun ((p1, o1), prf1) ((p2, o2), prf2) ->
    ((Vect.add p1 p2, opAdd o1 o2), ProofFormat.add_proof prf1 prf2)

  let neg : t -> t =
   fun ((p1, o1), prf1) ->
    match o1 with
    | Eq ->
      ((Vect.mul Q.minus_one p1, o1), ProofFormat.mul_cst_proof Q.minus_one prf1)
    | _ -> failwith "neg: invalid proof"

  let mul_cst c ((p1, o1), prf1) =
    let () = match o1 with
    | Eq -> ()
    | Gt | Ge -> assert (c >/ Q.zero)
    in
    let p = LinPoly.mul_cst c p1 in
    let prf = ProofFormat.mul_cst_proof c prf1 in
    ((p, o1), prf)

  let mult p ((p1, o1), prf1) =
    match o1 with
    | Eq -> ((LinPoly.product p p1, o1), ProofFormat.sMulC p prf1)
    | Gt | Ge ->
      let n, r = Vect.decomp_cst p in
      if Vect.is_null r && n >/ Q.zero then
        ((LinPoly.product p p1, o1), ProofFormat.mul_cst_proof n prf1)
      else (
        if debug then
          Printf.printf "mult_error %a [*] %a\n" LinPoly.pp p output
            ((p1, o1), prf1);
        raise InvalidProof )

  let def p op i = ((p, op), ProofFormat.Def i)

  let mkhyp p op i = ((p, op), ProofFormat.Hyp i)

  let square p q = ((p, Ge), ProofFormat.Square q)

  let cutting_plane ((p, o), prf) =
    let c, p' = Vect.decomp_cst p in
    let g = Vect.gcd p' in
    if Z.equal Z.one g || c =/ Q.zero || not (Z.equal (Q.den c) Z.one) then None
      (* Nothing to do *)
    else
      let c1 = c // Q.of_bigint g in
      let c1' = Q.floor c1 in
      if c1 =/ c1' then None
      else
        match o with
        | Eq ->
          Some ((Vect.set 0 Q.minus_one Vect.null, Eq), ProofFormat.CutPrf prf)
        | Gt -> failwith "cutting_plane ignore strict constraints"
        | Ge ->
          (* This is a non-trivial common divisor *)
          Some
            ( (Vect.set 0 c1' (Vect.div (Q.of_bigint g) p), o)
            , ProofFormat.CutPrf prf )

  let construct_sign p =
    let c, p' = Vect.decomp_cst p in
    if Vect.is_null p' then
      Some
        ( match Q.sign c with
        | 0 -> (true, Eq, ProofFormat.Zero)
        | 1 -> (true, Gt, ProofFormat.Cst c)
        | _ (*-1*) -> (false, Gt, ProofFormat.Cst (Q.neg c)) )
    else None

  let get_sign l p =
    match construct_sign p with
    | None -> (
      try
        let (p', o), prf =
          List.find (fun ((p', o), prf) -> Vect.equal p p') l
        in
        Some (true, o, prf)
      with Not_found -> (
        let p = Vect.uminus p in
        try
          let (p', o), prf =
            List.find (fun ((p', o), prf) -> Vect.equal p p') l
          in
          Some (false, o, prf)
        with Not_found -> None ) )
    | Some s -> Some s

  let mult_sign : bool -> t -> t =
   fun b ((p, o), prf) -> if b then ((p, o), prf) else ((Vect.uminus p, o), prf)

  let rec linear_pivot sys ((lp1, op1), prf1) x ((lp2, op2), prf2) =
    (* lp1 = a1.x + b1 *)
    let a1, b1 = LinPoly.factorise x lp1 in
    (* lp2 = a2.x + b2 *)
    let a2, b2 = LinPoly.factorise x lp2 in
    if Vect.is_null a2 then (* We are done *)
      Some ((lp2, op2), prf2)
    else
      match (op1, op2) with
      | Eq, (Ge | Gt) -> (
        match get_sign sys a1 with
        | None -> None (* Impossible to pivot without sign information *)
        | Some (b, o, prf) ->
          let sa1 = mult_sign b ((a1, o), prf) in
          let sa2 = if b then Vect.uminus a2 else a2 in
          let (lp2, op2), prf2 =
            addition
              (product sa1 ((lp2, op2), prf2))
              (mult sa2 ((lp1, op1), prf1))
          in
          linear_pivot sys ((lp1, op1), prf1) x ((lp2, op2), prf2) )
      | Eq, Eq ->
        let (lp2, op2), prf2 =
          addition
            (mult a1 ((lp2, op2), prf2))
            (mult (Vect.uminus a2) ((lp1, op1), prf1))
        in
        linear_pivot sys ((lp1, op1), prf1) x ((lp2, op2), prf2)
      | (Ge | Gt), (Ge | Gt) -> (
        match (get_sign sys a1, get_sign sys a2) with
        | Some (b1, o1, p1), Some (b2, o2, p2) ->
          if b1 <> b2 then
            let (lp2, op2), prf2 =
              addition
                (product (mult_sign b1 ((a1, o1), p1)) ((lp2, op2), prf2))
                (product (mult_sign b2 ((a2, o2), p2)) ((lp1, op1), prf1))
            in
            linear_pivot sys ((lp1, op1), prf1) x ((lp2, op2), prf2)
          else None
        | _ -> None )
      | (Ge | Gt), Eq -> failwith "pivot: equality as second argument"

  let linear_pivot sys ((lp1, op1), prf1) x ((lp2, op2), prf2) =
    match linear_pivot sys ((lp1, op1), prf1) x ((lp2, op2), prf2) with
    | None -> None
    | Some (c, p) -> Some (c, ProofFormat.simplify_prf_rule p)

  let is_substitution strict ((p, o), prf) =
    let pred v = if strict then v =/ Q.one || v =/ Q.minus_one else true in
    match o with Eq -> LinPoly.search_linear pred p | _ -> None

  let sort (sys : t list) =
    let size ((p, o), prf) =
      let _, p' = Vect.decomp_cst p in
      let (x, q), p' = Vect.decomp_fst p' in
      Vect.fold
        (fun (l, (q, x)) x' q' ->
          let q' = Q.abs q' in
          (l + 1, if q </ q then (q, x) else (q', x')))
        (1, (Q.abs q, x))
        p
    in
    let cmp ((l1, (q1, _)), ((_, o), _)) ((l2, (q2, _)), ((_, o'), _)) =
      if l1 < l2 then -1 else if l1 = l2 then Q.compare q1 q2 else 1
    in
    List.sort cmp (List.rev_map (fun wp -> (size wp, wp)) sys)

  let iterate_pivot p sys0 =
    let elim sys =
      let oeq, sys' = extract p sys in
      match oeq with
      | None -> None
      | Some (v, pc) -> simplify (linear_pivot sys0 pc v) sys'
    in
    iterate_until_stable elim (List.map snd (sort sys0))

  let subst_constant is_int sys =
    let is_integer q = Q.(q =/ floor q) in
    let is_constant ((c, o), p) =
      match o with
      | Ge | Gt -> None
      | Eq -> (
        Vect.Bound.(
          match of_vect c with
          | None -> None
          | Some b ->
            if (not is_int) || is_integer (b.cst // b.coeff) then
              Monomial.get_var (LinPoly.MonT.retrieve b.var)
            else None) )
    in
    iterate_pivot is_constant sys

  let subst sys0 = iterate_pivot (is_substitution true) sys0

  let saturate_subst b sys0 =
    let select = is_substitution b in
    let gen (v, pc) ((c, op), prf) =
      if ISet.mem v (LinPoly.variables c) then
        linear_pivot sys0 pc v ((c, op), prf)
      else None
    in
    saturate select gen sys0

  let simple_pivot (q1, x) ((v1, o1), prf1) ((v2, o2), prf2) =
    let q2 = Vect.get x v2 in
    if q2 =/ Q.zero then None
    else
      let cv1, cv2 =
        if Q.sign q1 <> Q.sign q2 then (Q.abs q2, Q.abs q1)
        else
          match (o1, o2) with
          | Eq, _ -> (q2, Q.abs q1)
          | _, Eq -> (Q.abs q2, q2)
          | _, _ -> (Q.zero, Q.zero)
      in
      if cv2 =/ Q.zero then None
      else
        Some
          ( (Vect.mul_add cv1 v1 cv2 v2, opAdd o1 o2)
          , ProofFormat.add_proof
              (ProofFormat.mul_cst_proof cv1 prf1)
              (ProofFormat.mul_cst_proof cv2 prf2) )

end

module BoundWithProof =
struct

type t = Vect.Bound.t * op * ProofFormat.prf_rule

let make ((p, o), prf) = match Vect.Bound.of_vect p with
| None -> None
| Some b -> Some (b, o, prf)

let padd (o1, prf1) (o2, prf2) = (opAdd o1 o2, ProofFormat.add_proof prf1 prf2)

let pmul (o1, prf1) (o2, prf2) = (opMult o1 o2, ProofFormat.mul_proof prf1 prf2)

let plet (o1,p1) (o2,p2) f  =
    match ProofFormat.pr_unit p1 , ProofFormat.pr_unit p2 with
    | true , true -> f (o1,p1) (o2,p2)
    | false , false ->
      let (o,prf) = f (o1,ProofFormat.Ref 1) (o2,ProofFormat.Ref 0) in
      (o, ProofFormat.LetPrf(p1,ProofFormat.LetPrf(p2,prf)))
    | true , false ->
      let (o,prf) = f (o1,p1) (o2,ProofFormat.Ref 0) in
      (o, ProofFormat.LetPrf(p2,prf))
    | false , true ->
      let (o,prf) = f (o1,ProofFormat.Ref 0) (o2,p2) in
      (o,ProofFormat.LetPrf(p1,prf))

let pext c (o, prf) =
  if c =/ Q.zero then (Eq, ProofFormat.Zero)
  else (o, ProofFormat.mul_cst_proof c prf)

let mul_bound (b1, o1, prf1) (b2, o2, prf2) =
  let open Vect.Bound in
  match (b1, b2) with
  | {cst = c1; var = v1; coeff = c1'},
    {cst = c2; var = v2; coeff = c2'} ->
    let good_coeff b o =
      match o with
      | Eq -> Some (Q.neg b)
      | _ -> if b <=/ Q.zero then Some (Q.neg b) else None
    in
    match (good_coeff c1 o2, good_coeff c2 o1) with
    | None, _ | _, None -> None
    | Some c1, Some c2 ->
      let w1 = (o1, prf1) in
      let w2 = (o2, prf2) in
      let (o, prf) = plet w1 w2 (fun w1 w2 -> padd (padd (pmul w1 w2) (pext c1 w2)) (pext c2 w1)) in
      let b = {
        cst = Q.neg (c1 */ c2);
        var = LinPoly.MonT.register (Monomial.prod (LinPoly.MonT.retrieve v1) (LinPoly.MonT.retrieve v2));
        coeff = c1' */ c2';
      } in
      Some (b, o, prf)

let bound (b, _, _) = b

let proof (b, o, w) =
  let p = Vect.Bound.to_vect b in
  ((p, o), w)
end

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
