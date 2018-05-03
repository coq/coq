(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-20011                            *)
(*                                                                      *)
(************************************************************************)

open Num
module Utils = Mutils
open Utils

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
 val prod : t -> t -> t
 val exp  : t -> int -> t
 val div  : t -> t -> t *  int
 val compare : t -> t -> int
 val pp : out_channel -> t -> unit
 val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a
 val sqrt : t -> t option 
end
 =
struct
 (* A monomial is represented by a multiset of variables  *)
 module Map = Map.Make(Int)
 open Map
 
 type t = int Map.t

 let pp o m = Map.iter 
   (fun k v -> 
      if v = 1 then Printf.fprintf o "x%i." k
      else     Printf.fprintf o "x%i^%i." k v) m


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
   try
     not (Map.fold (fun _ i fk -> 
		 if fk = true (* first key *)
		 then 
		   if i = 1 then false
		   else raise Not_found
		 else raise Not_found) m true)
   with Not_found -> false

 let sqrt m = 
   if is_const m then None
   else
     try 
       Some (Map.fold (fun v i acc ->
			 let i' = i / 2 in
			   if i mod 2 = 0
			   then add v i' m
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


 let fold = fold

end

module Poly :
 (* A polynomial is a map of monomials *)
 (* 
    This is probably a naive implementation 
    (expected to be fast enough - Coq is probably the bottleneck)
    *The new ring contribution is using a sparse Horner representation.
 *)
sig
 type t
 val get : Monomial.t -> t -> num
 val variable : var -> t
 val add : Monomial.t -> num -> t -> t
 val constant : num -> t
 val product : t -> t -> t
 val addition : t -> t -> t
 val uminus : t -> t
 val fold : (Monomial.t -> num -> 'a -> 'a) -> t -> 'a -> 'a
 val is_linear : t -> bool
end =
struct
 (*normalisation bug : 0*x ... *)
 module P = Map.Make(Monomial)
 open P

 type t = num P.t

 (* Get the coefficient of monomial mn *)
 let get : Monomial.t -> t -> num = 
  fun mn p -> try find mn p with Not_found -> (Int 0)


 (* The polynomial 1.x *)
 let variable : var -> t =
  fun  x ->  add (Monomial.var x) (Int 1) empty
   
 (*The constant polynomial *)
 let constant : num -> t =
  fun c -> add (Monomial.const) c empty

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

 let is_linear p = P.fold (fun m _ acc -> acc && (Monomial.is_const m || Monomial.is_var m)) p true

(* let is_linear p = 
   let res = is_linear p in
     Printf.printf "is_linear %a = %b\n" pp p res ; res
*)
end


module Vect =
  struct
    (** [t] is the type of vectors.
	A vector [(x1,v1) ; ... ; (xn,vn)] is such that:
	- variables indexes are ordered (x1 <c ... < xn
	- values are all non-zero
    *)
    type var = int
    type t = (var * num) list

(** [equal v1 v2 = true] if the vectors are syntactically equal. *)

    let rec equal v1 v2 =
      match v1 , v2 with
	| [] , []   -> true
	| [] , _    -> false
	| _::_ , [] -> false
	| (i1,n1)::v1 , (i2,n2)::v2 ->
	    (Int.equal i1 i2) && n1 =/ n2 && equal v1 v2

    let hash v =
      let rec hash i = function
	| [] -> i
	| (vr,vl)::l ->  hash (i + (Hashtbl.hash (vr, float_of_num vl))) l in
	Hashtbl.hash (hash 0 v )


    let null = []

    let pp_vect o vect =
      List.iter (fun (v,n) -> Printf.printf "%sx%i + " (string_of_num n) v) vect

    let from_list (l: num list) =
      let rec xfrom_list i l =
	match l with
	  | [] -> []
	  | e::l ->
	      if e <>/ Int 0
	      then (i,e)::(xfrom_list (i+1) l)
	      else xfrom_list (i+1) l in

	xfrom_list 0 l

    let zero_num = Int 0


    let to_list m =
      let rec xto_list i l =
	match l with
	  | [] -> []
	  |	(x,v)::l' ->
		  if i = x then v::(xto_list (i+1) l') else zero_num ::(xto_list (i+1) l) in
	xto_list 0 m


    let cons i v rst = if v =/ Int 0 then rst else (i,v)::rst

    let rec update i f t =
      match t with
	| [] -> cons i (f zero_num) []
	| (k,v)::l ->
	    match Int.compare i k with
	  | 0 -> cons k (f v) l
	  | -1 -> cons i (f zero_num) t
	  |  1 -> (k,v) ::(update i f l)
	  |  _  -> failwith "compare_num"

    let rec set i n t =
      match t with
	| [] -> cons i n []
	| (k,v)::l ->
	    match Int.compare i k with
	      | 0 -> cons k n l
	      | -1 -> cons i n t
	      |  1 -> (k,v) :: (set i n l)
	      |  _  -> failwith "compare_num"

    let mul z t =
      match z with
	| Int 0 -> []
	| Int 1 -> t
	|  _    -> List.map (fun (i,n) -> (i, mult_num z n)) t


    let rec add v1 v2  =
      match v1 , v2 with
	| (x1,n1)::v1' , (x2,n2)::v2' ->
	    if x1 = x2
	    then
	      let n' = n1  +/ n2 in
		if n' =/ Int 0 then add v1' v2'
		else
		  let res = add v1' v2'  in
		    (x1,n') ::res
	    else if x1 < x2
	    then let res = add v1' v2   in
	      (x1, n1)::res
	    else let res = add v1 v2'  in
	      (x2, n2)::res
	|  [] , [] -> []
	|  [] ,  _ ->  v2
	|  _  , [] ->  v1 




    let compare : t -> t -> int = Mutils.Cmp.compare_list (fun x y -> Mutils.Cmp.compare_lexical
      [
	(fun () -> Int.compare (fst x) (fst y));
	(fun () -> compare_num (snd x) (snd y))])

    (** [tail v vect] returns
	- [None] if [v] is not a variable of the vector [vect]
	- [Some(vl,rst)]  where [vl] is the value of [v] in vector [vect]
        and [rst] is the remaining of the vector
	We exploit that vectors are ordered lists
    *)
    let rec tail (v:var) (vect:t) =
      match vect with
	| [] -> None
	| (v',vl)::vect' ->
	    match Int.compare v' v with
	      | 0 -> Some (vl,vect) (* Ok, found *)
	      | -1 -> tail v vect' (* Might be in the tail *)
	      | _  -> None (* Hopeless *)

    let get v vect =
      match tail v vect with
	| None -> None
	| Some(vl,_) -> Some vl


    let rec fresh v =
	match v with
	  | [] -> 1
	  | [v,_] -> v + 1
	  | _::v  -> fresh v

  end

type vector = Vect.t

type cstr_compat = {coeffs : vector ; op : op ; cst : num}
and op = |Eq | Ge

let string_of_op = function Eq -> "=" | Ge -> ">="

let output_cstr o {coeffs = coeffs ; op = op ; cst = cst} = 
  Printf.fprintf o "%a %s %s" Vect.pp_vect coeffs (string_of_op op) (string_of_num cst)

let opMult o1 o2 = 
  match o1, o2 with
    | Eq , Eq -> Eq
    | Eq , Ge | Ge , Eq -> Ge
    | Ge , Ge -> Ge

open Big_int

type prf_rule = 
  | Hyp of int 
  | Def of int
  | Cst  of big_int
  | Zero
  | Square of (Vect.t * num) 
  | MulC of (Vect.t * num) * prf_rule 
  | Gcd of big_int * prf_rule 
  | MulPrf of prf_rule * prf_rule
  | AddPrf of prf_rule * prf_rule
  | CutPrf of prf_rule
      
type proof = 
  | Done
  | Step of int * prf_rule * proof
  | Enum of int * prf_rule * Vect.t * prf_rule * proof list 
      

let rec output_prf_rule o = function
  | Hyp i -> Printf.fprintf o "Hyp %i" i
  | Def i -> Printf.fprintf o "Def %i" i
  | Cst c -> Printf.fprintf o "Cst %s" (string_of_big_int c)
  | Zero  -> Printf.fprintf o "Zero"
  | Square _ -> Printf.fprintf o "( )^2"
  | MulC(p,pr) -> Printf.fprintf o "P * %a" output_prf_rule pr
  | MulPrf(p1,p2) -> Printf.fprintf o "%a * %a" output_prf_rule p1 output_prf_rule p2
  | AddPrf(p1,p2) -> Printf.fprintf o "%a + %a" output_prf_rule p1 output_prf_rule p2
  | CutPrf(p) -> Printf.fprintf o "[%a]" output_prf_rule p
  | Gcd(c,p)  -> Printf.fprintf o "(%a)/%s" output_prf_rule p (string_of_big_int c)

let rec output_proof o = function
  | Done -> Printf.fprintf o "."
  | Step(i,p,pf) -> Printf.fprintf o "%i:= %a ; %a" i output_prf_rule p output_proof pf
  | Enum(i,p1,v,p2,pl) -> Printf.fprintf o "%i{%a<=%a<=%a}%a" i 
      output_prf_rule p1 Vect.pp_vect v output_prf_rule p2
	(pp_list output_proof) pl

let rec pr_rule_max_id = function
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
  let res = normalise_proof id prf in
  if debug then Printf.printf "normalise_proof %a -> %a" output_proof  prf output_proof (snd res) ; 
    res



let add_proof x y = 
  match x, y with 
   | Zero , p | p , Zero -> p
   | _    -> AddPrf(x,y)


let mul_proof c p = 
  match  sign_big_int c with
   | 0 -> Zero (* This is likely to be a bug *)
   | -1 -> MulC(([],Big_int c),p) (* [p] should represent an equality *)
   | 1 -> 
       if eq_big_int c unit_big_int
       then p
       else MulPrf(Cst c,p)
   | _ -> assert false


let mul_proof_ext (p,c) prf = 
  match p with
   | [] -> mul_proof (numerator c) prf
   |  _ -> MulC((p,c),prf)
  

module LinPoly = 
struct
  type t = Vect.t * num

  module MonT = 
  struct
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


  end 

  let normalise (v,c) = 
    (List.sort  (fun x y -> Int.compare (fst x) (fst y)) v , c)


  let output_mon o (x,v) = 
    Printf.fprintf o "%s.%a +" (string_of_num v) Monomial.pp (MonT.retrieve x)



  let output_cstr o {coeffs = coeffs ; op = op ; cst = cst} = 
    Printf.fprintf o "%a %s %s" (pp_list output_mon) coeffs (string_of_op op) (string_of_num cst)



  let linpol_of_pol p = 
    let (v,c) = 
      Poly.fold 
	(fun  mon num (vct,cst)  -> 
	   if Monomial.is_const mon then (vct,num) 
	   else
	     let vr = MonT.register mon in
	       ((vr,num)::vct,cst)) p ([], Int 0) in
      normalise (v,c)

  let mult v m (vect,c) =
    if Monomial.is_const m
    then
      (Vect.mul v vect, v <*> c)
    else
      if sign_num v <> 0
      then
	let hd = 
	  if sign_num c <> 0
	  then [MonT.register m,v <*> c]
	  else [] in
	  
	let vect = hd @ (List.map (fun (x,n) -> 
					let x = MonT.retrieve x in
					let x_m = MonT.register (Monomial.prod m x) in
					  (x_m, v <*> n)) vect ) in
	  normalise (vect , Int 0)
      else ([],Int 0)

  let mult v m (vect,c) = 
    let (vect',c') = mult v m (vect,c) in
      if debug then 
      Printf.printf "mult %s %a (%a,%s) -> (%a,%s)\n" (string_of_num v) Monomial.pp m 
	(pp_list output_mon) vect (string_of_num c) 
	(pp_list output_mon) vect' (string_of_num c') ;
      (vect',c')



  let make_lin_pol v mon =
    if Monomial.is_const mon
    then [] , v
    else [MonT.register mon, v],Int 0

      




  let xpivot_eq (c,prf) x v (c',prf') = 
    if debug then Printf.printf "xpivot_eq {%a} %a %s {%a}\n" 
      output_cstr c 
      Monomial.pp (MonT.retrieve x)
      (string_of_num v) output_cstr c' ; 


    let {coeffs = coeffs ; op = op ; cst = cst} = c' in
    let m = MonT.retrieve x in

    let apply_pivot (vqn,q,n) (c',prf') = 
      (* Morally, we have (Vect.get (q*x^n) c'.coeffs) = vmn with n >=0 *)

      let cc' = abs_num v in
      let cc_num  = Int (- (sign_num v)) <*> vqn in
      let cc_mon  = Monomial.prod q (Monomial.exp m (n-1)) in

      let (c_coeff,c_cst) = mult cc_num cc_mon (c.coeffs, minus_num c.cst) in
	
      let c' = {coeffs = Vect.add (Vect.mul cc' c'.coeffs) c_coeff ; op = op ; cst = (minus_num c_cst) <+> (cc' <*> c'.cst)} in
      let prf' = add_proof 
	(mul_proof_ext (make_lin_pol cc_num cc_mon) prf)
	(mul_proof (numerator cc') prf') in

	if debug then Printf.printf "apply_pivot -> {%a}\n" output_cstr c' ; 
	(c',prf') in


    let cmp (q,n) (q',n') = 
      if n < n' then -1
      else if n = n' then  Monomial.compare q q'
      else 1 in

      
    let find_pivot (c',prf') = 
      let (v,q,n) = List.fold_left 
	(fun (v,q,n) (x,v') -> 
	   let x = MonT.retrieve x in 
	   let (q',n') = Monomial.div x m in
	     if cmp (q,n) (q',n') = -1 then (v',q',n') else (v,q,n)) (Int 0, Monomial.const,0) c'.coeffs in
	if n > 0 then Some (v,q,n) else None in

    let rec pivot (q,n) (c',prf') = 
      match find_pivot (c',prf') with
       | None -> (c',prf') 
       | Some(v,q',n') -> 
	   if cmp (q',n')  (q,n) = -1
	   then pivot (q',n') (apply_pivot (v,q',n') (c',prf'))
	   else (c',prf') in

      pivot (Monomial.const,max_int) (c',prf')


  let pivot_eq x (c,prf)   = 
    match Vect.get x c.coeffs with
     | None -> (fun x -> None)
     | Some v -> fun cp' -> Some (xpivot_eq (c,prf) x v cp')


end
