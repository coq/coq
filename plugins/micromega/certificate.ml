(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

(* We take as input a list of polynomials [p1...pn] and return an unfeasibility
   certificate polynomial. *)

(*open Micromega.Polynomial*)
open Big_int
open Num
open Sos_lib

module Mc = Micromega
module Ml2C = Mutils.CamlToCoq
module C2Ml = Mutils.CoqToCaml

let (<+>) = add_num
let (<->) = minus_num
let (<*>) = mult_num

type var = Mc.positive

module Monomial :
sig
 type t
 val const : t
 val var : var -> t
 val find : var -> t -> int
 val mult : var -> t -> t
 val prod : t -> t -> t
 val compare : t -> t -> int
 val pp : out_channel -> t -> unit
 val fold : (var -> int -> 'a -> 'a) -> t -> 'a -> 'a
end
 =
struct
 (* A monomial is represented by a multiset of variables  *)
 module Map = Map.Make(struct type t = var let compare = Pervasives.compare end)
 open Map

 type t = int Map.t

 (* The monomial that corresponds to a constant *)
 let const = Map.empty

 (* The monomial 'x' *)
 let var x = Map.add x 1 Map.empty

 (* Get the degre of a variable in a monomial *)
 let find x m = try find x m with Not_found -> 0

 (* Multiply a monomial by a variable *)
 let mult x m = add x (  (find x m) + 1) m

 (* Product of monomials *)
 let prod m1 m2 = Map.fold (fun k d m -> add k ((find k m) + d) m) m1 m2

 (* Total ordering of monomials *)
 let compare m1 m2 = Map.compare Pervasives.compare m1 m2

 let pp o m = Map.iter (fun k v ->
  if v = 1 then Printf.fprintf o "x%i." (C2Ml.index k)
  else     Printf.fprintf o "x%i^%i." (C2Ml.index k) v) m

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
 val mult : Monomial.t -> num -> t -> t
 val product : t -> t -> t
 val addition : t -> t -> t
 val uminus : t -> t
 val fold : (Monomial.t -> num -> 'a -> 'a) -> t -> 'a -> 'a
 val pp : out_channel -> t -> unit
 val compare : t -> t -> int
 val is_null : t -> bool
end =
struct
 (*normalisation bug : 0*x ... *)
 module P = Map.Make(Monomial)
 open P

 type t = num P.t

 let pp o p = P.iter (fun k v ->
  if compare_num v (Int 0) <> 0
  then
   if Monomial.compare Monomial.const k = 0
   then         Printf.fprintf o "%s " (string_of_num v)
   else Printf.fprintf o "%s*%a " (string_of_num v) Monomial.pp k) p

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
   let vl = (get mn p) <+> v in
    add mn vl p


 (** Design choice: empty is not a polynomial
     I do not remember why ....
 **)

 (* The product by a monomial *)
 let mult : Monomial.t -> num -> t -> t =
  fun mn v p ->
   fold (fun mn' v' res -> P.add (Monomial.prod mn mn') (v<*>v') res) p empty


 let  addition : t -> t -> t =
  fun p1 p2 -> fold (fun mn v p -> add mn v p) p1 p2


 let product : t -> t -> t =
  fun p1 p2 ->
   fold (fun mn v res -> addition (mult mn v p2) res ) p1 empty


 let uminus : t -> t =
  fun p -> map (fun v -> minus_num v) p

 let fold = P.fold

 let is_null p = fold (fun mn vl b -> b & sign_num vl = 0) p  true

 let compare = compare compare_num
end

open Mutils
type 'a number_spec = {
 bigint_to_number : big_int -> 'a;
 number_to_num : 'a  -> num;
 zero : 'a;
 unit : 'a;
 mult : 'a -> 'a -> 'a;
 eqb  : 'a -> 'a -> bool
}

let z_spec = {
 bigint_to_number = Ml2C.bigint ;
 number_to_num = (fun x -> Big_int (C2Ml.z_big_int x));
 zero = Mc.Z0;
 unit = Mc.Zpos Mc.XH;
 mult = Mc.zmult;
 eqb  = Mc.zeq_bool
}


let q_spec = {
 bigint_to_number = (fun x -> {Mc.qnum = Ml2C.bigint x; Mc.qden = Mc.XH});
 number_to_num = C2Ml.q_to_num;
 zero = {Mc.qnum = Mc.Z0;Mc.qden = Mc.XH};
 unit = {Mc.qnum =  (Mc.Zpos Mc.XH) ; Mc.qden = Mc.XH};
 mult = Mc.qmult;
 eqb  = Mc.qeq_bool
}

let r_spec = z_spec




let dev_form n_spec  p =
 let rec dev_form p =
  match p with
   | Mc.PEc z ->  Poly.constant (n_spec.number_to_num z)
   | Mc.PEX v ->  Poly.variable v
   | Mc.PEmul(p1,p2) ->
      let p1 = dev_form p1 in
      let p2 = dev_form p2 in
       Poly.product p1 p2
   | Mc.PEadd(p1,p2) -> Poly.addition (dev_form p1) (dev_form p2)
   | Mc.PEopp p ->  Poly.uminus (dev_form p)
   | Mc.PEsub(p1,p2) ->  Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))
   | Mc.PEpow(p,n)   ->
      let p = dev_form p in
      let n = C2Ml.n n in
      let rec pow n =
       if n = 0
       then Poly.constant (n_spec.number_to_num n_spec.unit)
       else Poly.product p (pow (n-1)) in
       pow n in
  dev_form p


let monomial_to_polynomial mn =
 Monomial.fold
  (fun v i acc ->
   let mn = if i = 1 then Mc.PEX v else Mc.PEpow (Mc.PEX v ,Ml2C.n i) in
    if acc = Mc.PEc (Mc.Zpos Mc.XH)
    then mn
    else Mc.PEmul(mn,acc))
  mn
  (Mc.PEc (Mc.Zpos Mc.XH))

let list_to_polynomial vars l =
 assert (List.for_all (fun x -> ceiling_num x =/ x) l);
 let var x = monomial_to_polynomial (List.nth vars x)  in
 let rec xtopoly p i = function
  | [] -> p
  | c::l -> if c =/  (Int 0) then xtopoly p (i+1) l
    else let c = Mc.PEc (Ml2C.bigint (numerator c)) in
    let mn =
     if c =  Mc.PEc (Mc.Zpos Mc.XH)
     then var i
     else Mc.PEmul (c,var i) in
    let p' = if p = Mc.PEc Mc.Z0 then mn else
      Mc.PEadd (mn, p) in
     xtopoly p' (i+1) l in

  xtopoly (Mc.PEc Mc.Z0) 0 l

let rec fixpoint f x =
 let y' = f x in
  if y' = x then y'
  else fixpoint f y'








let  rec_simpl_cone n_spec e =
 let simpl_cone =
  Mc.simpl_cone n_spec.zero n_spec.unit n_spec.mult n_spec.eqb in

 let rec rec_simpl_cone  = function
 | Mc.PsatzMulE(t1, t2) ->
    simpl_cone  (Mc.PsatzMulE (rec_simpl_cone t1, rec_simpl_cone t2))
 | Mc.PsatzAdd(t1,t2)  ->
    simpl_cone (Mc.PsatzAdd (rec_simpl_cone t1, rec_simpl_cone t2))
 |  x           -> simpl_cone x in
  rec_simpl_cone e


let simplify_cone n_spec c = fixpoint (rec_simpl_cone n_spec) c

type cone_prod =
  Const of cone
  | Ideal of cone *cone
  | Mult of cone * cone
  | Other of cone
and cone =   Mc.zWitness



let factorise_linear_cone c =

 let rec cone_list  c l =
  match c with
   | Mc.PsatzAdd (x,r) -> cone_list  r (x::l)
   |  _        ->  c :: l in

 let factorise c1 c2 =
  match c1 , c2 with
   | Mc.PsatzMulC(x,y) , Mc.PsatzMulC(x',y') ->
      if x = x' then Some (Mc.PsatzMulC(x, Mc.PsatzAdd(y,y'))) else None
   | Mc.PsatzMulE(x,y) , Mc.PsatzMulE(x',y') ->
      if x = x' then Some (Mc.PsatzMulE(x, Mc.PsatzAdd(y,y'))) else None
   |  _     -> None in

 let rec rebuild_cone l pending  =
  match l with
   | [] -> (match pending with
      | None -> Mc.PsatzZ
      | Some p -> p
     )
   | e::l ->
      (match pending with
       | None -> rebuild_cone l (Some e)
       | Some p -> (match factorise p e with
          | None -> Mc.PsatzAdd(p, rebuild_cone l (Some e))
          | Some f -> rebuild_cone l (Some f) )
      ) in

  (rebuild_cone (List.sort Pervasives.compare (cone_list c [])) None)



(* The binding with Fourier might be a bit obsolete
   -- how does it handle equalities ? *)

(* Certificates are elements of the cone such that P = 0  *)

(* To begin with, we search for certificates of the form:
   a1.p1 + ... an.pn + b1.q1 +... + bn.qn + c = 0
   where pi >= 0 qi > 0
   ai >= 0
   bi >= 0
   Sum bi + c >= 1
   This is a linear problem: each monomial is considered as a variable.
   Hence, we can use fourier.

   The variable c is at index 0
*)

open Mfourier
   (*module Fourier = Fourier(Vector.VList)(SysSet(Vector.VList))*)
   (*module Fourier = Fourier(Vector.VSparse)(SysSetAlt(Vector.VSparse))*)
(*module Fourier = Mfourier.Fourier(Vector.VSparse)(*(SysSetAlt(Vector.VMap))*)*)

(*module Vect = Fourier.Vect*)
(*open Fourier.Cstr*)

(* fold_left followed by a rev ! *)

let constrain_monomial mn l  =
 let coeffs = List.fold_left (fun acc p -> (Poly.get mn p)::acc) [] l in
  if mn = Monomial.const
  then
   { coeffs = Vect.from_list ((Big_int unit_big_int):: (List.rev coeffs)) ;
     op = Eq ;
     cst = Big_int zero_big_int  }
  else
   { coeffs = Vect.from_list ((Big_int zero_big_int):: (List.rev coeffs)) ;
     op = Eq ;
     cst = Big_int zero_big_int  }


let positivity l =
 let rec xpositivity i l =
  match l with
   | [] -> []
   | (_,Mc.Equal)::l -> xpositivity (i+1) l
   | (_,_)::l ->
      {coeffs = Vect.update (i+1) (fun _ -> Int 1) Vect.null ;
       op = Ge ;
       cst = Int 0 }  :: (xpositivity (i+1) l)
 in
  xpositivity 0 l


let string_of_op = function
 | Mc.Strict -> "> 0"
 | Mc.NonStrict -> ">= 0"
 | Mc.Equal -> "= 0"
 | Mc.NonEqual -> "<> 0"



(* If the certificate includes at least one strict inequality,
   the obtained polynomial can also be 0 *)
let build_linear_system l =

 (* Gather the monomials:  HINT add up of the polynomials *)
 let l' = List.map fst l in
 let monomials =
  List.fold_left (fun acc p -> Poly.addition p acc) (Poly.constant (Int 0)) l'
 in  (* For each monomial, compute a constraint *)
 let s0 =
  Poly.fold (fun mn _ res -> (constrain_monomial mn l')::res) monomials [] in
  (* I need at least something strictly positive *)
 let strict = {
  coeffs = Vect.from_list ((Big_int unit_big_int)::
                            (List.map (fun (x,y) ->
			      match y with Mc.Strict ->
				  Big_int unit_big_int
                              | _ -> Big_int zero_big_int) l));
  op = Ge ; cst = Big_int unit_big_int } in
  (* Add the positivity constraint *)
  {coeffs = Vect.from_list ([Big_int unit_big_int]) ;
   op = Ge ;
   cst = Big_int zero_big_int}::(strict::(positivity l)@s0)


let big_int_to_z = Ml2C.bigint

(* For Q, this is a pity that the certificate has been scaled
   -- at a lower layer, certificates are using nums... *)
let make_certificate n_spec (cert,li) =
 let bint_to_cst = n_spec.bigint_to_number in
  match cert with
   | [] -> failwith "empty_certificate"
   | e::cert' ->
      let cst = match compare_big_int e zero_big_int with
       | 0 -> Mc.PsatzZ
       | 1 ->  Mc.PsatzC (bint_to_cst e)
       | _ -> failwith "positivity error"
      in
      let rec scalar_product cert l =
       match cert with
        | [] -> Mc.PsatzZ
        | c::cert -> match l with
           | [] -> failwith "make_certificate(1)"
           | i::l ->
              let r = scalar_product cert l in
               match compare_big_int c  zero_big_int with
                | -1 -> Mc.PsatzAdd (
                   Mc.PsatzMulC (Mc.Pc ( bint_to_cst c), Mc.PsatzIn (Ml2C.nat i)),
                   r)
                | 0  -> r
                | _ ->  Mc.PsatzAdd (
                   Mc.PsatzMulE (Mc.PsatzC (bint_to_cst c), Mc.PsatzIn (Ml2C.nat i)),
                   r) in

        ((factorise_linear_cone
             (simplify_cone n_spec (Mc.PsatzAdd (cst, scalar_product cert' li)))))


exception Found of Monomial.t

exception Strict

let primal l =
  let vr = ref 0 in
  let module Mmn = Map.Make(Monomial) in

  let vect_of_poly map p =
    Poly.fold (fun mn vl (map,vect) ->
      if mn = Monomial.const
      then (map,vect)
      else
	let (mn,m) = try (Mmn.find mn map,map) with Not_found -> let res = (!vr, Mmn.add mn !vr map) in incr vr ; res in
	  (m,if sign_num vl = 0 then vect else (mn,vl)::vect)) p (map,[]) in

  let op_op = function Mc.NonStrict -> Ge |Mc.Equal -> Eq | _ -> raise Strict in

  let cmp x y = Pervasives.compare (fst x) (fst y) in

   snd (List.fold_right (fun  (p,op) (map,l) ->
      let (mp,vect) = vect_of_poly map p in
      let cstr = {coeffs = List.sort cmp vect; op = op_op op ; cst = minus_num (Poly.get Monomial.const p)} in

	(mp,cstr::l)) l (Mmn.empty,[]))

let dual_raw_certificate (l:  (Poly.t * Mc.op1) list) =
(*  List.iter (fun (p,op) -> Printf.fprintf stdout "%a %s 0\n" Poly.pp p (string_of_op op) ) l ; *)


 let sys = build_linear_system l in

   try
   match Fourier.find_point sys with
    | Inr _ -> None
    | Inl cert ->  Some (rats_to_ints (Vect.to_list cert))
       (* should not use rats_to_ints *)
  with x ->
   if debug
   then (Printf.printf "raw certificate %s" (Printexc.to_string x);
         flush stdout) ;
   None


let raw_certificate l =
  try
    let p = primal l in
      match Fourier.find_point p with
	| Inr prf ->
	    if debug then Printf.printf "AProof : %a\n" pp_proof prf ;
	    let cert = List.map (fun (x,n) -> x+1,n) (fst (List.hd (Proof.mk_proof p prf))) in
	      if debug then Printf.printf "CProof : %a" Vect.pp_vect cert ;
	      Some (rats_to_ints (Vect.to_list cert))
	| Inl _   -> None
  with Strict ->
    (* Fourier elimination should handle > *)
    dual_raw_certificate l


let simple_linear_prover (*to_constant*) l =
 let (lc,li) = List.split l in
  match raw_certificate lc with
   |  None -> None (* No certificate *)
   | Some cert -> (* make_certificate to_constant*)Some (cert,li)



let linear_prover n_spec l  =
 let li = List.combine l (interval 0 (List.length l -1)) in
 let (l1,l') = List.partition
  (fun (x,_) -> if snd x = Mc.NonEqual then true else false) li in
 let l' = List.map
  (fun ((x,y),i) -> match y with
                   Mc.NonEqual -> failwith "cannot happen"
                  |  y -> ((dev_form n_spec x, y),i)) l' in

  simple_linear_prover (*n_spec*) l'


let linear_prover n_spec l  =
 try linear_prover n_spec l with
   x -> (print_string (Printexc.to_string x); None)

let linear_prover_with_cert spec l =
  match linear_prover spec l with
    | None -> None
    | Some cert -> Some (make_certificate spec cert)



(* zprover.... *)

(* I need to gather the set of variables --->
   Then go for fold
   Once I have an interval, I need a certificate : 2 other fourier elims.
   (I could probably get the certificate directly
   as it is done in the fourier contrib.)
*)

let make_linear_system l =
 let l' = List.map fst l in
 let monomials = List.fold_left (fun acc p -> Poly.addition p acc)
  (Poly.constant (Int 0)) l' in
 let monomials = Poly.fold
  (fun mn _ l -> if mn = Monomial.const then l else mn::l) monomials [] in
  (List.map (fun (c,op) ->
   {coeffs = Vect.from_list (List.map (fun mn ->  (Poly.get mn c)) monomials) ;
    op = op ;
    cst = minus_num ( (Poly.get Monomial.const c))}) l
    ,monomials)


let pplus x y = Mc.PEadd(x,y)
let pmult x y = Mc.PEmul(x,y)
let pconst x = Mc.PEc x
let popp x = Mc.PEopp x

let debug = false

(* keep track of enumerated vectors *)
let rec mem p x  l =
 match l with  [] -> false | e::l -> if p x e then true else mem p x l

let rec remove_assoc p x l =
 match l with [] -> [] | e::l -> if p x (fst e) then
  remove_assoc p x l else e::(remove_assoc p x l)

let eq x y = Vect.compare x y = 0

let  remove e  l  = List.fold_left (fun l x -> if eq x e then l else x::l) [] l


(* The prover is (probably) incomplete --
   only searching for naive cutting planes *)

let candidates sys =
 let ll = List.fold_right (
  fun (e,k) r ->
   match k with
    | Mc.NonStrict -> (dev_form z_spec e , Ge)::r
    | Mc.Equal     ->  (dev_form z_spec e , Eq)::r
       (* we already know the bound -- don't compute it again *)
    | _     -> failwith "Cannot happen candidates") sys [] in

 let (sys,var_mn) = make_linear_system ll in
 let vars = mapi (fun _ i -> Vect.set i (Int 1) Vect.null) var_mn in
  (List.fold_left (fun l cstr ->
   let gcd = Big_int (Vect.gcd cstr.coeffs) in
    if gcd =/ (Int 1) && cstr.op = Eq
    then l
    else  (Vect.mul (Int 1 // gcd) cstr.coeffs)::l) [] sys) @ vars




let rec xzlinear_prover planes sys =
 match linear_prover z_spec sys with
  | Some prf ->  Some (Mc.RatProof (make_certificate z_spec prf,Mc.DoneProof))
  | None     -> (* find the candidate with the smallest range *)
     (* Grrr - linear_prover is also calling 'make_linear_system' *)
     let ll = List.fold_right (fun (e,k) r -> match k with
       Mc.NonEqual -> r
      | k -> (dev_form z_spec e ,
             match k with
               Mc.NonStrict -> Ge
              | Mc.Equal              -> Eq
              | Mc.Strict | Mc.NonEqual -> failwith "Cannot happen") :: r) sys [] in
     let (ll,var) = make_linear_system ll in
     let candidates = List.fold_left (fun  acc vect ->
      match Fourier.optimise vect ll with
       | None -> acc
       | Some i ->
(*	  Printf.printf "%s in %s\n" (Vect.string vect) (string_of_intrvl i) ; *)
	  flush stdout ;
	  (vect,i) ::acc)  [] planes in

     let smallest_interval =
      match List.fold_left (fun (x1,i1) (x2,i2) ->
       if Itv.smaller_itv i1 i2
       then (x1,i1) else (x2,i2)) (Vect.null,(None,None)) candidates
      with
       | (x,(Some i, Some j))  -> Some(i,x,j)
       |   x        ->   None (* This might be a cutting plane *)
      in
      match smallest_interval with
       | Some (lb,e,ub) ->
          let (lbn,lbd) =
           (Ml2C.bigint (sub_big_int (numerator lb)  unit_big_int),
           Ml2C.bigint (denominator lb)) in
          let (ubn,ubd) =
           (Ml2C.bigint (add_big_int unit_big_int (numerator ub)) ,
           Ml2C.bigint (denominator ub)) in
          let expr = list_to_polynomial var (Vect.to_list e) in
           (match
             (*x <= ub ->  x  > ub *)
             linear_prover  z_spec
              ((pplus (pmult (pconst ubd) expr) (popp (pconst  ubn)),
                      Mc.NonStrict) :: sys),
            (* lb <= x  -> lb > x *)
            linear_prover z_spec
             ((pplus (popp (pmult  (pconst lbd) expr)) (pconst lbn),
                     Mc.NonStrict)::sys)
            with
             | Some cub , Some clb  ->
                (match zlinear_enum  (remove e planes)   expr
                  (ceiling_num lb)  (floor_num ub) sys
                 with
                  | None -> None
                  | Some prf ->
		      let bound_proof (c,l) = make_certificate z_spec (List.tl c , List.tl (List.map (fun x -> x -1) l)) in

                     Some (Mc.EnumProof((*Ml2C.q lb,expr,Ml2C.q ub,*) bound_proof clb, bound_proof cub,prf)))
             | _ -> None
           )
       |  _ -> None
and zlinear_enum  planes expr clb cub l =
 if clb >/  cub
 then Some []
 else
  let pexpr = pplus (popp (pconst (Ml2C.bigint (numerator clb)))) expr in
  let sys' = (pexpr, Mc.Equal)::l in
   (*let enum =  *)
   match xzlinear_prover planes sys' with
    | None -> if debug then print_string "zlp?"; None
    | Some prf -> if debug then print_string "zlp!";
    match zlinear_enum planes expr (clb +/ (Int 1)) cub l with
     | None -> None
     | Some prfl -> Some (prf :: prfl)

let zlinear_prover sys =
 let candidates = candidates sys in
 (*  Printf.printf "candidates %d" (List.length candidates) ; *)
 (*let t0 = Sys.time () in*)
 let res = xzlinear_prover candidates sys in
   (*Printf.printf "Time prover : %f" (Sys.time () -. t0) ;*) res

open Sos_types
open Mutils

let rec scale_term t =
 match t with
  | Zero    -> unit_big_int , Zero
  | Const n ->  (denominator n) , Const (Big_int (numerator n))
  | Var n   -> unit_big_int , Var n
  | Inv _   -> failwith "scale_term : not implemented"
  | Opp t   -> let s, t = scale_term t in s, Opp t
  | Add(t1,t2) -> let s1,y1 = scale_term t1 and s2,y2 = scale_term t2 in
    let g = gcd_big_int s1 s2 in
    let s1' = div_big_int s1 g in
    let s2' = div_big_int s2 g in
    let e = mult_big_int g (mult_big_int s1' s2') in
     if (compare_big_int e unit_big_int) = 0
     then (unit_big_int, Add (y1,y2))
     else 	e, Add (Mul(Const (Big_int s2'), y1),
		       Mul (Const (Big_int s1'), y2))
  | Sub _ -> failwith "scale term: not implemented"
  | Mul(y,z) ->       let s1,y1 = scale_term y and s2,y2 = scale_term z in
		       mult_big_int s1 s2 , Mul (y1, y2)
  |  Pow(t,n) -> let s,t = scale_term t in
		  power_big_int_positive_int s  n , Pow(t,n)
  |   _ -> failwith "scale_term : not implemented"

let scale_term t =
 let (s,t') = scale_term t in
  s,t'


let get_index_of_ith_match f i l  =
 let rec get j res l =
  match l with
   | [] -> failwith "bad index"
   | e::l -> if f e
     then
       (if j = i then res else get (j+1) (res+1) l )
     else get j (res+1) l in
  get 0 0 l


let rec scale_certificate pos = match pos with
 | Axiom_eq i ->  unit_big_int , Axiom_eq i
 | Axiom_le i ->  unit_big_int , Axiom_le i
 | Axiom_lt i ->   unit_big_int , Axiom_lt i
 | Monoid l   -> unit_big_int , Monoid l
 | Rational_eq n ->  (denominator n) , Rational_eq (Big_int (numerator n))
 | Rational_le n ->  (denominator n) , Rational_le (Big_int (numerator n))
 | Rational_lt n ->  (denominator n) , Rational_lt (Big_int (numerator n))
 | Square t -> let s,t' =  scale_term t in
		mult_big_int s s , Square t'
 | Eqmul (t, y) -> let s1,y1 = scale_term t and s2,y2 = scale_certificate y in
		    mult_big_int s1 s2 , Eqmul (y1,y2)
 | Sum (y, z) -> let s1,y1 = scale_certificate y
   and s2,y2 = scale_certificate z in
   let g = gcd_big_int s1 s2 in
   let s1' = div_big_int s1 g in
   let s2' = div_big_int s2 g in
    mult_big_int g (mult_big_int s1' s2'),
    Sum (Product(Rational_le (Big_int s2'), y1),
	Product (Rational_le (Big_int s1'), y2))
 | Product (y, z) ->
    let s1,y1 = scale_certificate y and s2,y2 = scale_certificate z in
     mult_big_int s1 s2 , Product (y1,y2)


open Micromega
 let rec term_to_q_expr = function
  | Const n ->  PEc (Ml2C.q n)
  | Zero   ->  PEc ( Ml2C.q (Int 0))
  | Var s   ->  PEX (Ml2C.index
		      (int_of_string (String.sub s 1 (String.length s - 1))))
  | Mul(p1,p2) ->  PEmul(term_to_q_expr p1, term_to_q_expr p2)
  | Add(p1,p2) ->   PEadd(term_to_q_expr p1, term_to_q_expr p2)
  | Opp p ->   PEopp (term_to_q_expr p)
  | Pow(t,n) ->  PEpow (term_to_q_expr t,Ml2C.n n)
  | Sub(t1,t2) ->  PEsub (term_to_q_expr t1,  term_to_q_expr t2)
  | _ -> failwith "term_to_q_expr: not implemented"

 let term_to_q_pol e = Mc.norm_aux (Ml2C.q (Int 0)) (Ml2C.q (Int 1)) Mc.qplus  Mc.qmult Mc.qminus Mc.qopp Mc.qeq_bool (term_to_q_expr e)


 let rec product l =
   match l with
     | [] -> Mc.PsatzZ
     | [i] -> Mc.PsatzIn (Ml2C.nat i)
     | i ::l -> Mc.PsatzMulE(Mc.PsatzIn (Ml2C.nat i), product l)


let  q_cert_of_pos  pos =
 let rec _cert_of_pos = function
   Axiom_eq i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_le i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_lt i ->  Mc.PsatzIn (Ml2C.nat i)
  | Monoid l  -> product l
  | Rational_eq n | Rational_le n | Rational_lt n ->
     if compare_num n (Int 0) = 0 then Mc.PsatzZ else
      Mc.PsatzC (Ml2C.q   n)
  | Square t -> Mc.PsatzSquare (term_to_q_pol  t)
  | Eqmul (t, y) -> Mc.PsatzMulC(term_to_q_pol t, _cert_of_pos y)
  | Sum (y, z) -> Mc.PsatzAdd  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.PsatzMulE (_cert_of_pos y, _cert_of_pos z) in
  simplify_cone q_spec (_cert_of_pos pos)


 let rec term_to_z_expr = function
  | Const n ->  PEc (Ml2C.bigint (big_int_of_num n))
  | Zero   ->  PEc ( Z0)
  | Var s   ->  PEX (Ml2C.index
		      (int_of_string (String.sub s 1 (String.length s - 1))))
  | Mul(p1,p2) ->  PEmul(term_to_z_expr p1, term_to_z_expr p2)
  | Add(p1,p2) ->   PEadd(term_to_z_expr p1, term_to_z_expr p2)
  | Opp p ->   PEopp (term_to_z_expr p)
  | Pow(t,n) ->  PEpow (term_to_z_expr t,Ml2C.n n)
  | Sub(t1,t2) ->  PEsub (term_to_z_expr t1,  term_to_z_expr t2)
  | _ -> failwith "term_to_z_expr: not implemented"

 let term_to_z_pol e = Mc.norm_aux (Ml2C.z 0) (Ml2C.z 1) Mc.zplus  Mc.zmult Mc.zminus Mc.zopp Mc.zeq_bool (term_to_z_expr e)

let  z_cert_of_pos  pos =
 let s,pos = (scale_certificate pos) in
 let rec _cert_of_pos = function
   Axiom_eq i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_le i ->  Mc.PsatzIn (Ml2C.nat i)
  | Axiom_lt i ->  Mc.PsatzIn (Ml2C.nat i)
  | Monoid l  -> product l
  | Rational_eq n | Rational_le n | Rational_lt n ->
     if compare_num n (Int 0) = 0 then Mc.PsatzZ else
      Mc.PsatzC (Ml2C.bigint (big_int_of_num  n))
  | Square t -> Mc.PsatzSquare (term_to_z_pol  t)
  | Eqmul (t, y) -> Mc.PsatzMulC(term_to_z_pol t, _cert_of_pos y)
  | Sum (y, z) -> Mc.PsatzAdd  (_cert_of_pos y, _cert_of_pos z)
  | Product (y, z) -> Mc.PsatzMulE (_cert_of_pos y, _cert_of_pos z) in
  simplify_cone z_spec (_cert_of_pos pos)

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
