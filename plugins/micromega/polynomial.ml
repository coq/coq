(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

open Num
module Utils = Mutils
open Utils

module Mc = Micromega

let max_nb_cstr = ref max_int

type var = int

let debug = false

let (<+>) = add_num
let (<*>) = mult_num

module Monomial :
sig
  type t
  val const : t
  val is_const : t -> bool
  val var : var -> t
  val is_var : t -> bool
  val get_var : t -> var option
  val prod : t -> t -> t
  val exp  : t -> int -> t
  val div  : t -> t -> t *  int
  val compare : t -> t -> int
  val pp : out_channel -> t -> unit
  val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a
  val sqrt : t -> t option
  val variables : t -> ISet.t
end
  =  struct
  (* A monomial is represented by a multiset of variables  *)
  module Map = Map.Make(Int)
  open Map

  type t = int Map.t

  let is_singleton m =
    try
      let (k,v) = choose m in
      let (l,e,r) = split k m in
      if is_empty l && is_empty r
      then Some(k,v) else None
    with Not_found -> None

  let pp o m =
    let pp_elt o (k,v)=
      if v = 1 then Printf.fprintf o "x%i" k
      else  Printf.fprintf o "x%i^%i" k v in

    let rec pp_list o l =
      match l with
        [] -> ()
      | [e] -> pp_elt o e
      | e::l -> Printf.fprintf o "%a*%a" pp_elt e pp_list l in

    pp_list o  (Map.bindings m)



  (* The monomial that corresponds to a constant *)
  let const = Map.empty

  let sum_degree m = Map.fold (fun _ n s -> s + n) m 0

  (* Total ordering of monomials *)
  let compare: t -> t -> int =
    fun m1 m2 ->
    let s1 = sum_degree m1
    and s2 = sum_degree m2 in
    if Int.equal s1 s2 then Map.compare Int.compare m1 m2
    else Int.compare s1 s2

  let is_const m = (m = Map.empty)

  (* The monomial 'x' *)
  let var x = Map.add x 1 Map.empty

  let is_var m =
    match is_singleton m with
    | None -> false
    | Some (_,i) -> i = 1

  let get_var m =
    match is_singleton m with
    | None -> None
    | Some (k,i) -> if i = 1 then Some k else None


  let sqrt m =
    if is_const m then None
    else
      try
        Some (Map.fold (fun v i acc ->
                  let i' = i / 2 in
                  if i mod 2 = 0
                  then add v i' acc
                  else raise Not_found) m const)
      with Not_found -> None


  (* Get the degre of a variable in a monomial *)
  let find x m = try find x m with Not_found -> 0

  (* Product of monomials *)
  let prod m1 m2 = Map.fold (fun k d m -> add k ((find k m) + d) m) m1 m2

  let exp m n =
    let rec exp acc n =
      if n = 0 then acc
      else  exp (prod acc m) (n - 1) in

    exp const n

  (*  [div m1 m2 = mr,n] such that mr * (m2)^n = m1 *)
  let div m1 m2 =
    let n = fold (fun x i n -> let i' = find x m1 in
                               let nx = i' / i in
                               min n nx) m2 max_int in

    let mr = fold (fun x i' m ->
                 let i = find x m2 in
                 let ir = i' - i * n in
                 if ir = 0 then m
                 else add x ir m) m1 empty in
    (mr,n)


  let variables m = fold (fun v i acc -> ISet.add v acc) m ISet.empty

  let fold = fold

end

module MonMap =
  struct
    include Map.Make(Monomial)

    let union f = merge
                          (fun x v1 v2 ->
                            match v1 , v2 with
                            | None , None -> None
                            | Some v , None | None , Some v -> Some v
                            | Some v1 , Some v2 -> f x v1 v2)
  end

let pp_mon o (m, i) =
  if Monomial.is_const m
  then if eq_num (Int 0) i then ()
       else Printf.fprintf o "%s" (string_of_num i)
  else
    match i with
    | Int 1  -> Monomial.pp o m
    | Int -1 -> Printf.fprintf o "-%a" Monomial.pp m
    | Int 0  -> ()
    |  _     -> Printf.fprintf o "%s*%a" (string_of_num i) Monomial.pp m



module Poly :
(* A polynomial is a map of monomials *)
(*
    This is probably a naive implementation
    (expected to be fast enough - Coq is probably the bottleneck)
    *The new ring contribution is using a sparse Horner representation.
    *)
sig
  type t
  val pp : out_channel -> t -> unit
  val get : Monomial.t -> t -> num
  val variable : var -> t
  val add : Monomial.t -> num -> t -> t
  val constant : num -> t
  val product : t -> t -> t
  val addition : t -> t -> t
  val uminus : t -> t
  val fold : (Monomial.t -> num -> 'a -> 'a) -> t -> 'a -> 'a
  val factorise : var -> t  -> t * t
end =  struct
  (*normalisation bug : 0*x ... *)
  module P = Map.Make(Monomial)
  open P

  type t = num P.t


  let pp o p = P.iter (fun mn i  -> Printf.fprintf o "%a + " pp_mon (mn, i)) p


  (* Get the coefficient of monomial mn *)
  let get : Monomial.t -> t -> num =
    fun mn p -> try find mn p with Not_found -> (Int 0)


  (* The polynomial 1.x *)
  let variable : var -> t =
    fun  x ->  add (Monomial.var x) (Int 1) empty

  (*The constant polynomial *)
  let constant : num -> t =
    fun c ->  add (Monomial.const) c empty

  (* The addition of a monomial *)

  let add : Monomial.t -> num -> t -> t =
    fun mn v p ->
    if sign_num v = 0 then p
    else
      let vl = (get mn p) <+> v in
      if sign_num vl = 0 then
        remove mn p
      else add mn vl p


  (** Design choice: empty is not a polynomial
     I do not remember why ....
   **)

  (* The product by a monomial *)
  let mult : Monomial.t -> num -> t -> t =
    fun mn v p ->
    if sign_num v = 0
    then constant (Int 0)
    else
      fold (fun mn' v' res -> P.add (Monomial.prod mn mn') (v<*>v') res) p empty


  let  addition : t -> t -> t =
    fun p1 p2 -> fold (fun mn v p -> add mn v p) p1 p2


  let product : t -> t -> t =
    fun p1 p2 ->
    fold (fun mn v res -> addition (mult mn v p2) res ) p1 empty


  let uminus : t -> t =
    fun p -> map (fun v -> minus_num v) p

  let fold = P.fold

  let factorise x p =
    let x = Monomial.var x in
    P.fold (fun m v (px,cx) ->
        let (m1,i) = Monomial.div m x in
        if i = 0
        then (px, add m v cx)
        else
          let mx = Monomial.prod m1 (Monomial.exp x (i-1)) in
          (add mx v px,cx) ) p (constant (Int 0) , constant (Int 0))

end



type vector = Vect.t

type cstr = {coeffs : vector ; op : op ; cst : num}
and op = |Eq | Ge | Gt

exception Strict

let is_strict c = Pervasives.(=) c.op  Gt

let eval_op = function
  | Eq -> (=/)
  | Ge -> (>=/)
  | Gt -> (>/)


let string_of_op = function Eq -> "=" | Ge -> ">=" | Gt -> ">"

let output_cstr o { coeffs ; op ; cst } =
  Printf.fprintf o "%a %s %s" Vect.pp coeffs (string_of_op op) (string_of_num cst)


let opMult o1 o2 =
  match o1, o2 with
  | Eq , _ | _ , Eq -> Eq
  | Ge , _ | _ , Ge -> Ge
  | Gt , Gt -> Gt

let opAdd o1 o2 =
  match o1, o2 with
  | Eq , x | x , Eq -> x
  | Gt , x | x , Gt -> Gt
  | Ge , Ge -> Ge




module LinPoly = struct
  (** A linear polynomial a0 + a1.x1 + ... + an.xn
      By convention, the constant a0 is the coefficient of the variable 0.
   *)

  type t = Vect.t

  module MonT =  struct
    module MonoMap = Map.Make(Monomial)
    module IntMap  = Map.Make(Int)

    (** A hash table might be preferable but requires a hash function. *)
    let (index_of_monomial : int MonoMap.t ref) = ref (MonoMap.empty)
    let (monomial_of_index : Monomial.t IntMap.t ref) = ref (IntMap.empty)
    let fresh = ref 0

    let clear () =
      index_of_monomial := MonoMap.empty;
      monomial_of_index := IntMap.empty ;
      fresh := 0


    let register m =
      try
        MonoMap.find m !index_of_monomial
      with Not_found ->
        begin
          let res = !fresh in
          index_of_monomial := MonoMap.add m res !index_of_monomial ;
          monomial_of_index := IntMap.add res m !monomial_of_index ;
          incr fresh ; res
        end

    let retrieve i = IntMap.find i !monomial_of_index

    let _ = register Monomial.const

  end

  let var v = Vect.set (MonT.register (Monomial.var v)) (Int 1) Vect.null

  let of_monomial m =
    let v = MonT.register m in
    Vect.set v (Int 1) Vect.null

  let linpol_of_pol p =
      Poly.fold
        (fun  mon num vct  ->
          let vr = MonT.register mon in
          Vect.set vr num vct) p Vect.null

  let pol_of_linpol v =
    Vect.fold (fun p vr n -> Poly.add (MonT.retrieve vr) n p) (Poly.constant (Int 0)) v

  let  coq_poly_of_linpol cst p =

    let pol_of_mon m =
      Monomial.fold (fun x v p -> Mc.PEmul(Mc.PEpow(Mc.PEX(CamlToCoq.positive x),CamlToCoq.n v),p)) m (Mc.PEc (cst (Int 1))) in

    Vect.fold (fun acc x v ->
        let mn = MonT.retrieve x in
        Mc.PEadd(Mc.PEmul(Mc.PEc (cst v), pol_of_mon mn),acc)) (Mc.PEc (cst  (Int 0))) p

  let pp_var o vr =
    try
      Monomial.pp o (MonT.retrieve vr) (* this is a non-linear variable *)
    with  Not_found -> Printf.fprintf o "v%i" vr


  let pp o p =   Vect.pp_gen pp_var o p


  let constant c =
    if sign_num c = 0
    then Vect.null
    else Vect.set 0 c Vect.null


  let is_linear p =
    Vect.for_all (fun v _ ->
        let mn = (MonT.retrieve v) in
        Monomial.is_var mn || Monomial.is_const mn) p

  let is_variable p =
    let ((x,v),r) = Vect.decomp_fst p in
    if Vect.is_null r && v >/ Int 0
    then Monomial.get_var (MonT.retrieve x)
    else None


  let factorise x p =
    let (px,cx) = Poly.factorise x (pol_of_linpol p) in
    (linpol_of_pol px, linpol_of_pol cx)


  let is_linear_for x p =
    let (a,b) = factorise x p in
    Vect.is_constant a

  let search_all_linear p l =
    Vect.fold (fun acc x v ->
        if p v
        then
          let x' = MonT.retrieve x in
          match Monomial.get_var x' with
          | None -> acc
          | Some x ->
             if is_linear_for x l
             then x::acc
             else acc
        else acc) [] l

  let min_list (l:int list) =
    match l with
    | [] -> None
    | e::l -> Some (List.fold_left Pervasives.min e l)

  let search_linear p l =
    min_list (search_all_linear p l)


  let product p1 p2 =
    linpol_of_pol (Poly.product (pol_of_linpol p1) (pol_of_linpol p2))

  let addition p1 p2 = Vect.add p1 p2


  let of_vect v =
    Vect.fold (fun acc v vl -> addition (product (var v) (constant vl)) acc) Vect.null v

  let variables p = Vect.fold
                     (fun acc v _ ->
                        ISet.union (Monomial.variables (MonT.retrieve v)) acc) ISet.empty p


  let pp_goal typ  o l =
    let vars = List.fold_left (fun acc p -> ISet.union acc (variables (fst p))) ISet.empty l in
    let pp_vars o i = ISet.iter (fun v -> Printf.fprintf o "(x%i : %s) " v typ) vars in

    Printf.fprintf o "forall %a\n" pp_vars vars ;
    List.iteri (fun i (p,op) -> Printf.fprintf o "(H%i : %a %s 0)\n" i pp p (string_of_op op)) l;
    Printf.fprintf o ", False\n"





  let collect_square p  =
    Vect.fold (fun acc  v _  ->
        let m = (MonT.retrieve v) in
        match Monomial.sqrt m with
        | None   -> acc
        | Some s -> MonMap.add s m acc
      ) MonMap.empty p


end

module ProofFormat =  struct
  open Big_int

  type prf_rule =
    | Annot of string * prf_rule
    | Hyp of int
    | Def of int
    | Cst  of Num.num
    | Zero
    | Square of Vect.t
    | MulC of Vect.t * prf_rule
    | Gcd of Big_int.big_int * prf_rule
    | MulPrf of prf_rule * prf_rule
    | AddPrf of prf_rule * prf_rule
    | CutPrf of prf_rule

  type proof =
    | Done
    | Step of int * prf_rule * proof
    | Enum of int * prf_rule * Vect.t * prf_rule * proof list


  let rec output_prf_rule o = function
    | Annot(s,p) -> Printf.fprintf o "(%a)@%s" output_prf_rule p s
    | Hyp i -> Printf.fprintf o "Hyp %i" i
    | Def i -> Printf.fprintf o "Def %i" i
    | Cst c -> Printf.fprintf o "Cst %s" (string_of_num c)
    | Zero  -> Printf.fprintf o "Zero"
    | Square s -> Printf.fprintf o "(%a)^2" Poly.pp (LinPoly.pol_of_linpol s)
    | MulC(p,pr) -> Printf.fprintf o "(%a) * (%a)" Poly.pp (LinPoly.pol_of_linpol p) output_prf_rule pr
    | MulPrf(p1,p2) -> Printf.fprintf o "(%a) * (%a)" output_prf_rule p1 output_prf_rule p2
    | AddPrf(p1,p2) -> Printf.fprintf o "%a + %a" output_prf_rule p1 output_prf_rule p2
    | CutPrf(p) -> Printf.fprintf o "[%a]" output_prf_rule p
    | Gcd(c,p)  -> Printf.fprintf o "(%a)/%s" output_prf_rule p (string_of_big_int c)

  let rec output_proof o = function
    | Done -> Printf.fprintf o "."
    | Step(i,p,pf) -> Printf.fprintf o "%i:= %a ; %a" i output_prf_rule p output_proof pf
    | Enum(i,p1,v,p2,pl) -> Printf.fprintf o "%i{%a<=%a<=%a}%a" i
                              output_prf_rule p1 Vect.pp v output_prf_rule p2
                              (pp_list ";" output_proof) pl

  let rec pr_size = function
    | Annot(_,p) -> pr_size p
    | Zero| Square _ -> Int 0
    | Hyp _      -> Int 1
    | Def _      -> Int 1
    | Cst n      ->  n
    | Gcd(i, p)    -> pr_size p // (Big_int i)
    | MulPrf(p1,p2) | AddPrf(p1,p2) -> pr_size p1 +/ pr_size p2
    | CutPrf p    -> pr_size p
    | MulC(v, p) -> pr_size p


  let rec pr_rule_max_id = function
    | Annot(_,p) -> pr_rule_max_id p
    | Hyp i | Def i -> i
    | Cst _ | Zero | Square _ -> -1
    | MulC(_,p) | CutPrf p | Gcd(_,p) -> pr_rule_max_id p
    | MulPrf(p1,p2)| AddPrf(p1,p2) -> max (pr_rule_max_id p1) (pr_rule_max_id p2)

  let rec proof_max_id = function
    | Done -> -1
    | Step(i,pr,prf) -> max i (max (pr_rule_max_id pr) (proof_max_id prf))
    | Enum(i,p1,_,p2,l) ->
       let m = max (pr_rule_max_id p1) (pr_rule_max_id p2) in
       List.fold_left (fun i prf -> max i (proof_max_id prf)) (max i m) l


  let rec pr_rule_def_cut id = function
    | Annot(_,p) -> pr_rule_def_cut id p
    | MulC(p,prf) ->
       let (bds,id',prf') = pr_rule_def_cut id prf  in
       (bds, id', MulC(p,prf'))
    | MulPrf(p1,p2) ->
       let (bds1,id,p1) = pr_rule_def_cut id p1 in
       let (bds2,id,p2) = pr_rule_def_cut id p2 in
       (bds2@bds1,id,MulPrf(p1,p2))
    | AddPrf(p1,p2) ->
       let (bds1,id,p1) = pr_rule_def_cut id p1 in
       let (bds2,id,p2) = pr_rule_def_cut id p2 in
       (bds2@bds1,id,AddPrf(p1,p2))
    | CutPrf p ->
       let (bds,id,p) = pr_rule_def_cut id p in
       ((id,p)::bds,id+1,Def id)
    | Gcd(c,p) ->
       let (bds,id,p) = pr_rule_def_cut id p in
       ((id,p)::bds,id+1,Def id)
    | Square _|Cst _|Def _|Hyp _|Zero as x -> ([],id,x)


  (* Do not define top-level cuts *)
  let pr_rule_def_cut id = function
    | CutPrf p ->
       let (bds,ids,p') = pr_rule_def_cut id p in
       bds,ids, CutPrf p'
    |    p     -> pr_rule_def_cut id p


  let rec implicit_cut p =
    match p with
    | CutPrf p -> implicit_cut p
    |   _      -> p


  let rec pr_rule_collect_hyps pr =
    match pr with
    | Annot(_,pr) -> pr_rule_collect_hyps pr
    | Hyp i | Def i -> ISet.add i ISet.empty
    | Cst _ | Zero | Square _ -> ISet.empty
    | MulC(_,pr) | Gcd(_,pr)| CutPrf pr -> pr_rule_collect_hyps pr
    | MulPrf(p1,p2) | AddPrf(p1,p2) -> ISet.union (pr_rule_collect_hyps p1) (pr_rule_collect_hyps p2)

  let simplify_proof p  =
    let rec simplify_proof p =
      match p with
      | Done -> (Done, ISet.empty)
      | Step(i,pr,Done) -> (p, ISet.add i (pr_rule_collect_hyps pr))
      | Step(i,pr,prf) ->
         let (prf',hyps) = simplify_proof prf in
         if not (ISet.mem i hyps)
         then (prf',hyps)
         else
           (Step(i,pr,prf'), ISet.add i (ISet.union (pr_rule_collect_hyps pr) hyps))
      | Enum(i,p1,v,p2,pl) ->
         let (pl,hl) = List.split (List.map simplify_proof pl) in
         let hyps = List.fold_left ISet.union ISet.empty hl in
         (Enum(i,p1,v,p2,pl),ISet.add i (ISet.union (ISet.union (pr_rule_collect_hyps p1) (pr_rule_collect_hyps p2)) hyps)) in
    fst (simplify_proof p)


  let rec normalise_proof id prf =
    match prf with
    | Done -> (id,Done)
    | Step(i,Gcd(c,p),Done) ->  normalise_proof id (Step(i,p,Done))
    | Step(i,p,prf) ->
       let bds,id,p' = pr_rule_def_cut id p in
       let (id,prf) = normalise_proof id prf in
       let prf = List.fold_left (fun  acc (i,p)  -> Step(i, CutPrf p,acc))
                   (Step(i,p',prf)) 	  bds in

       (id,prf)
    | Enum(i,p1,v,p2,pl) ->
       (* Why do I have  top-level cuts ? *)
       (*      let p1 = implicit_cut p1 in
      let p2 = implicit_cut p2 in
      let (ids,prfs) = List.split (List.map (normalise_proof id) pl) in
        (List.fold_left max  0 ids ,
           Enum(i,p1,v,p2,prfs))
        *)

       let bds1,id,p1' = pr_rule_def_cut id (implicit_cut p1) in
       let bds2,id,p2' = pr_rule_def_cut id (implicit_cut p2) in
       let (ids,prfs) = List.split (List.map (normalise_proof id) pl) in
       (List.fold_left max  0 ids ,
        List.fold_left (fun  acc (i,p)  -> Step(i, CutPrf p,acc))
          (Enum(i,p1',v,p2',prfs)) (bds2@bds1))


  let normalise_proof id prf =
    let prf = simplify_proof prf in
    let res = normalise_proof id prf in
    if debug then Printf.printf "normalise_proof %a -> %a" output_proof  prf output_proof (snd res) ;
    res

  module OrdPrfRule =
    struct
      type t = prf_rule

      let id_of_constr = function
        | Annot _ -> 0
        | Hyp _  -> 1
        | Def _  -> 2
        | Cst _   -> 3
        | Zero   -> 4
        | Square _ -> 5
        | MulC  _  -> 6
        | Gcd _    -> 7
        | MulPrf _ -> 8
        | AddPrf _ -> 9
        | CutPrf _ -> 10

      let cmp_pair c1 c2 (x1,x2) (y1,y2) =
        match c1 x1 y1 with
        |  0 -> c2 x2 y2
        |  i -> i


      let rec compare p1 p2 =
        match p1, p2 with
        | Annot(s1,p1) , Annot(s2,p2) -> if s1 = s2 then compare p1 p2
                                         else Pervasives.compare s1 s2
        | Hyp i       , Hyp j        -> Pervasives.compare i j
        | Def i       , Def j        -> Pervasives.compare i j
        | Cst n       , Cst m        -> Num.compare_num n m
        | Zero        , Zero         -> 0
        | Square v1   , Square v2    -> Vect.compare v1 v2
        | MulC(v1,p1) , MulC(v2,p2)  -> cmp_pair Vect.compare compare (v1,p1) (v2,p2)
        | Gcd(b1,p1)  , Gcd(b2,p2)   -> cmp_pair Big_int.compare_big_int compare (b1,p1) (b2,p2)
        | MulPrf(p1,q1) , MulPrf(p2,q2) -> cmp_pair compare compare (p1,q1) (p2,q2)
        | AddPrf(p1,q1) , MulPrf(p2,q2) -> cmp_pair compare compare (p1,q1) (p2,q2)
        | CutPrf p      , CutPrf p'     -> compare p p'
        |   _          ,   _            -> Pervasives.compare (id_of_constr p1) (id_of_constr p2)

    end




  let add_proof x y =
    match x, y with
    | Zero , p | p , Zero -> p
    | _    -> AddPrf(x,y)


  let rec mul_cst_proof c p =
    match p with
    | Annot(s,p) -> Annot(s,mul_cst_proof c p)
    | MulC(v,p') -> MulC(Vect.mul c v,p')
    | _  ->
       match  sign_num c with
       | 0 -> Zero (* This is likely to be a bug *)
       | -1 -> MulC(LinPoly.constant c, p) (* [p] should represent an equality *)
       | 1 ->
          if eq_num (Int 1) c
          then p
          else MulPrf(Cst c,p)
       | _ -> assert false


  let sMulC v p =
    let (c,v') = Vect.decomp_cst v in
    if Vect.is_null v' then mul_cst_proof c p
    else  MulC(v,p)


  let mul_proof p1 p2 =
    match p1 , p2 with
    | Zero , _ | _ , Zero -> Zero
    | Cst c , p | p , Cst c -> mul_cst_proof c p
    |   _  ,  _ ->
         MulPrf(p1,p2)


    module PrfRuleMap = Map.Make(OrdPrfRule)

    let prf_rule_of_map m =
      PrfRuleMap.fold (fun k v acc -> add_proof (sMulC v k) acc) m Zero


    let rec dev_prf_rule p =
      match p with
      | Annot(s,p) -> dev_prf_rule p
      | Hyp _ | Def _ | Cst _ | Zero | Square _ -> PrfRuleMap.singleton p (LinPoly.constant (Int 1))
      | MulC(v,p) -> PrfRuleMap.map (fun v1 -> LinPoly.product v v1) (dev_prf_rule p)
      | AddPrf(p1,p2) -> PrfRuleMap.merge (fun k o1 o2 ->
                             match o1 , o2 with
                             | None , None -> None
                             | None , Some v | Some v, None -> Some v
                             | Some v1 , Some v2 -> Some (LinPoly.addition v1 v2)) (dev_prf_rule p1) (dev_prf_rule p2)
      | MulPrf(p1, p2) ->
         begin
           let p1' = dev_prf_rule p1 in
           let p2' = dev_prf_rule p2 in

           let p1'' = prf_rule_of_map p1' in
           let p2'' = prf_rule_of_map p2' in

           match p1'' with
           | Cst c -> PrfRuleMap.map (fun v1 -> Vect.mul c v1) p2'
           | _     -> PrfRuleMap.singleton (MulPrf(p1'',p2'')) (LinPoly.constant (Int 1))
         end
      |   _  -> PrfRuleMap.singleton p (LinPoly.constant (Int 1))

    let simplify_prf_rule p =
      prf_rule_of_map (dev_prf_rule p)


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
    Vect.fold (fun prf x n ->
        add_proof (mul_cst_proof n (IMap.find x env)) prf) Zero vect




  module Env =  struct

    let rec string_of_int_list l =
      match l with
      | [] -> ""
      | i::l -> Printf.sprintf "%i,%s" i (string_of_int_list l)


    let id_of_hyp hyp l =
      let rec xid_of_hyp i l' =
        match l' with
        | [] -> failwith (Printf.sprintf "id_of_hyp %i %s" hyp (string_of_int_list l))
        | hyp'::l' -> if Pervasives.(=) hyp hyp' then i else xid_of_hyp (i+1) l' in
      xid_of_hyp 0 l

  end

  let cmpl_prf_rule norm (cst:num-> 'a)  env prf =
    let rec cmpl =
      function
      | Annot(s,p) -> cmpl p
      | Hyp i | Def i -> Mc.PsatzIn (CamlToCoq.nat (Env.id_of_hyp i env))
      | Cst i         -> Mc.PsatzC (cst i)
      | Zero          -> Mc.PsatzZ
      | MulPrf(p1,p2)      -> Mc.PsatzMulE(cmpl p1, cmpl p2)
      | AddPrf(p1,p2)      -> Mc.PsatzAdd(cmpl p1 , cmpl p2)
      | MulC(lp,p)  -> let lp = norm (LinPoly.coq_poly_of_linpol cst lp) in
                       Mc.PsatzMulC(lp,cmpl p)
      | Square lp      -> Mc.PsatzSquare (norm (LinPoly.coq_poly_of_linpol cst lp))
      | _                  -> failwith "Cuts should already be compiled" in
    cmpl prf




  let cmpl_prf_rule_z env r = cmpl_prf_rule Mc.normZ (fun x -> CamlToCoq.bigint (numerator x)) env r

  let rec cmpl_proof env =  function
    | Done ->  Mc.DoneProof
    | Step(i,p,prf) ->
       begin
         match p with
         | CutPrf p' ->
            Mc.CutProof(cmpl_prf_rule_z env p', cmpl_proof (i::env) prf)
         |   _       -> Mc.RatProof(cmpl_prf_rule_z env p,cmpl_proof (i::env) prf)
       end
    | Enum(i,p1,_,p2,l) ->
       Mc.EnumProof(cmpl_prf_rule_z env p1,cmpl_prf_rule_z env p2,List.map (cmpl_proof (i::env)) l)


  let compile_proof env prf =
    let id = 1 + proof_max_id prf in
    let _,prf = normalise_proof id prf in
    cmpl_proof env prf

  let rec eval_prf_rule env = function
    | Annot(s,p) -> eval_prf_rule env p
    | Hyp i | Def i -> env i
    | Cst n    -> (Vect.set 0 n Vect.null,
                   match Num.compare_num n (Int 0) with
                   | 0 -> Ge
                   | 1 -> Gt
                   | _ -> failwith "eval_prf_rule : negative constant"
                  )
    | Zero     -> (Vect.null, Ge)
    | Square v -> (LinPoly.product v v,Ge)
    | MulC(v, p) ->
       let (p1,o) = eval_prf_rule env p in
       begin match o with
       | Eq -> (LinPoly.product v p1,Eq)
       |  _  ->
           Printf.fprintf stdout "MulC(%a,%a) invalid 2d arg %a %s" Vect.pp v  output_prf_rule p Vect.pp p1 (string_of_op o);
           failwith "eval_prf_rule : not an equality"
       end
    | Gcd(g,p)      -> let (v,op) = eval_prf_rule env p in
                       (Vect.div (Big_int g) v, op)
    | MulPrf(p1,p2) ->
       let (v1,o1) = eval_prf_rule env p1 in
       let (v2,o2) = eval_prf_rule env p2 in
       (LinPoly.product v1 v2, opMult o1 o2)
    | AddPrf(p1,p2) ->
       let (v1,o1) = eval_prf_rule env p1 in
       let (v2,o2) = eval_prf_rule env p2 in
       (LinPoly.addition v1 v2, opAdd o1 o2)
    | CutPrf p      -> eval_prf_rule env p


  let is_unsat (p,o) =
    let (c,r) = Vect.decomp_cst p in
    if Vect.is_null r
    then not (eval_op o c (Int 0))
    else false

  let rec eval_proof env p =
    match p with
    | Done -> failwith "Proof is not finished"
    | Step(i, prf, rst) ->
       let (p,o) = eval_prf_rule (fun i -> IMap.find i env) prf in
       if is_unsat (p,o) then true
       else
         if Pervasives.(=) rst Done
         then
           begin
             Printf.fprintf stdout "Last inference %a %s\n" LinPoly.pp p (string_of_op o);
             false
           end
         else  eval_proof (IMap.add i (p,o) env) rst
    | Enum(i,r1,v,r2,l) -> let _ = eval_prf_rule (fun i -> IMap.find i env) r1  in
                           let _ = eval_prf_rule (fun i -> IMap.find i env) r2  in
                           (* Should check bounds *)
                           failwith "Not implemented"

end

module WithProof =  struct

  type t = ((LinPoly.t * op) * ProofFormat.prf_rule)

  let annot s (p,prf) = (p, ProofFormat.Annot(s,prf))

  let output o ((lp,op),prf) =
    Printf.fprintf o "%a %s 0 by %a\n" LinPoly.pp lp (string_of_op op) ProofFormat.output_prf_rule prf

  let output_sys o l =
    List.iter (Printf.fprintf o "%a\n" output) l

  exception InvalidProof

  let  zero = ((Vect.null,Eq), ProofFormat.Zero)

  let  const n = ((LinPoly.constant n,Ge), ProofFormat.Cst n)

  let of_cstr (c,prf)  =
    (Vect.set 0 (Num.minus_num (c.cst)) c.coeffs,c.op), prf

  let product : t -> t -> t = fun ((p1,o1),prf1) ((p2,o2),prf2) ->
    ((LinPoly.product p1 p2 , opMult o1 o2), ProofFormat.mul_proof prf1 prf2)

  let addition : t -> t -> t = fun ((p1,o1),prf1) ((p2,o2),prf2) ->
    ((Vect.add p1 p2, opAdd o1 o2), ProofFormat.add_proof prf1 prf2)

  let mult p ((p1,o1),prf1) =
    match o1 with
    | Eq -> ((LinPoly.product p p1,o1), ProofFormat.sMulC p  prf1)
    | Gt| Ge  -> let (n,r) = Vect.decomp_cst p in
                 if Vect.is_null r && n >/ Int 0
                 then ((LinPoly.product p p1, o1), ProofFormat.mul_cst_proof n prf1)
                 else raise InvalidProof


  let cutting_plane ((p,o),prf) =
    let (c,p') = Vect.decomp_cst p in
    let g =  (Vect.gcd p') in
    if (Big_int.eq_big_int Big_int.unit_big_int g) || c =/ Int 0 ||
         not (Big_int.eq_big_int (denominator c) Big_int.unit_big_int)
    then None (* Nothing to do *)
    else
      let c1  = c // (Big_int g) in
      let c1' = Num.floor_num c1 in
      if c1 =/ c1'
      then None
      else
        match o with
        | Eq -> Some ((Vect.set 0 (Int (-1)) Vect.null,Eq), ProofFormat.Gcd(g,prf))
        | Gt -> failwith "cutting_plane ignore strict constraints"
        | Ge ->
           (* This is a non-trivial common divisor *)
           Some ((Vect.set 0 c1' (Vect.div (Big_int g) p),o),ProofFormat.Gcd(g, prf))


  let construct_sign p =
    let (c,p') = Vect.decomp_cst p in
    if Vect.is_null p'
    then
      Some (begin  match sign_num c with
            | 0  -> (true, Eq, ProofFormat.Zero)
            | 1  -> (true,Gt, ProofFormat.Cst c)
            | _ (*-1*) -> (false,Gt, ProofFormat.Cst (minus_num c))
            end)
    else None


  let get_sign l p =
    match construct_sign p with
    | None -> begin
        try
          let ((p',o),prf) =
            List.find (fun ((p',o),prf) -> Vect.equal p p') l in
          Some (true,o,prf)
        with Not_found ->
          let p = Vect.uminus p in
          try
            let ((p',o),prf) =  List.find (fun ((p',o),prf) -> Vect.equal p p') l in
            Some (false,o,prf)
          with Not_found -> None
      end
    | Some s -> Some s


  let mult_sign : bool -> t -> t = fun b ((p,o),prf) ->
    if b then ((p,o),prf)
    else ((Vect.uminus p,o),prf)


  let rec linear_pivot sys ((lp1,op1), prf1) x ((lp2,op2), prf2) =

    (* lp1 = a1.x + b1 *)
    let (a1,b1) = LinPoly.factorise x lp1 in

    (* lp2 = a2.x + b2 *)
    let (a2,b2) = LinPoly.factorise x lp2 in

    if Vect.is_null a2
    then (* We are done *)
      Some ((lp2,op2),prf2)
    else
      match op1,op2 with
      | Eq , (Ge|Gt) -> begin
          match get_sign sys a1 with
          | None -> None (* Impossible to pivot without sign information *)
          | Some(b,o,prf) ->
             let sa1 = mult_sign b ((a1,o),prf) in
             let sa2 = if b then (Vect.uminus a2) else a2 in

             let ((lp2,op2),prf2) =
               addition (product sa1 ((lp2,op2),prf2))
                 (mult sa2 ((lp1,op1),prf1)) in
             linear_pivot sys ((lp1,op1),prf1) x ((lp2,op2),prf2)

        end
      | Eq , Eq ->
         let ((lp2,op2),prf2) = addition (mult a1 ((lp2,op2),prf2))
                                  (mult (Vect.uminus a2) ((lp1,op1),prf1)) in
         linear_pivot sys ((lp1,op1),prf1) x ((lp2,op2),prf2)

      | (Ge | Gt) , (Ge| Gt) -> begin
          match  get_sign sys a1 , get_sign sys a2 with
          | Some(b1,o1,p1) , Some(b2,o2,p2) ->
             if b1 <>  b2
             then
               let ((lp2,op2),prf2) =
                 addition (product (mult_sign b1 ((a1,o1), p1)) ((lp2,op2),prf2))
                   (product (mult_sign b2 ((a2,o2), p2)) ((lp1,op1),prf1)) in
               linear_pivot sys ((lp1,op1),prf1) x ((lp2,op2),prf2)
             else None
          |   _  -> None
        end
      | (Ge|Gt) , Eq -> failwith "pivot: equality as second argument"

  let linear_pivot sys ((lp1,op1), prf1) x ((lp2,op2), prf2) =
    match linear_pivot sys ((lp1,op1), prf1) x ((lp2,op2), prf2) with
    | None -> None
    | Some (c,p) -> Some(c, ProofFormat.simplify_prf_rule p)


let is_substitution strict ((p,o),prf) =
  let pred v = if strict then v =/ Int 1 || v =/ Int (-1) else true in

  match o with
  | Eq -> LinPoly.search_linear pred  p
  | _  -> None


let subst1 sys0 =
  let (oeq,sys') = extract (is_substitution true) sys0 in
  match oeq with
    | None -> sys0
    | Some(v,pc) ->
       match simplify (linear_pivot sys0 pc v) sys' with
       | None -> sys0
       | Some sys' -> sys'



let subst sys0 =
  let elim sys =
    let (oeq,sys') = extract (is_substitution true) sys in
    match oeq with
    | None -> None
    | Some(v,pc) ->  simplify (linear_pivot sys0 pc v) sys' in

  iterate_until_stable elim sys0


let saturate_subst b sys0  =
  let select = is_substitution b in
  let gen (v,pc) ((c,op),prf) =
    if ISet.mem v (LinPoly.variables c)
    then linear_pivot sys0 pc v ((c,op),prf)
    else None
  in
  saturate select gen sys0


end


(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
