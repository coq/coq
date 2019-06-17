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
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

(* We take as input a list of polynomials [p1...pn] and return an unfeasibility
   certificate polynomial. *)

let debug = false

open Big_int
open Num
open Polynomial

module Mc = Micromega
module Ml2C = Mutils.CamlToCoq
module C2Ml = Mutils.CoqToCaml

let use_simplex = ref true


type ('prf,'model) res =
   | Prf of 'prf
   | Model of 'model
   | Unknown

type zres = (Mc.zArithProof , (int * Mc.z  list)) res

type qres = (Mc.q Mc.psatz , (int * Mc.q  list)) res


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
    mult = Mc.Z.mul;
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

let dev_form n_spec  p =
  let rec dev_form p =
    match p with
    | Mc.PEc z ->  Poly.constant (n_spec.number_to_num z)
    | Mc.PEX v ->  Poly.variable (C2Ml.positive v)
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
         if Int.equal n 0
         then Poly.constant (n_spec.number_to_num n_spec.unit)
         else Poly.product p (pow (n-1)) in
       pow n in
  dev_form p

let rec fixpoint f x =
  let y' = f x in
  if Pervasives.(=) y' x then y'
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

   The variable c is at index 1
 *)

(* fold_left followed by a rev ! *)

let constrain_variable v l =
  let coeffs = List.fold_left (fun acc p -> (Vect.get v p.coeffs)::acc) [] l in
  { coeffs = Vect.from_list ((Big_int zero_big_int):: (Big_int zero_big_int):: (List.rev coeffs)) ;
    op = Eq ; 
    cst = Big_int zero_big_int  }



let constrain_constant l =
  let coeffs = List.fold_left (fun acc p -> minus_num p.cst ::acc) [] l in
  { coeffs = Vect.from_list ((Big_int zero_big_int):: (Big_int unit_big_int):: (List.rev coeffs)) ;
    op = Eq ; 
    cst = Big_int zero_big_int  }

let positivity l = 
  let rec xpositivity i l =
    match l with
    | [] -> []
    | c::l -> match c.op with
              | Eq -> xpositivity (i+1) l
              |  _ ->
                  {coeffs = Vect.update (i+1) (fun _ -> Int 1) Vect.null ;
                   op = Ge ;
                   cst = Int 0 }  :: (xpositivity (i+1) l)
  in
  xpositivity 1 l


let cstr_of_poly (p,o) =
  let (c,l) = Vect.decomp_cst p in
  {coeffs = l; op = o ; cst = minus_num c}



let variables_of_cstr c = Vect.variables c.coeffs


(* If the certificate includes at least one strict inequality, 
   the obtained polynomial can also be 0 *)

let build_dual_linear_system l =

  let variables =
    List.fold_left (fun acc p -> ISet.union acc (variables_of_cstr p)) ISet.empty l in
  (* For each monomial, compute a constraint *)
  let s0 =
    ISet.fold (fun mn  res -> (constrain_variable mn l)::res) variables [] in
  let c  = constrain_constant l in

  (* I need at least something strictly positive *)
  let strict = {
      coeffs = Vect.from_list ((Big_int zero_big_int) :: (Big_int unit_big_int)::
                                 (List.map (fun c ->  if is_strict c then Big_int unit_big_int else Big_int zero_big_int) l));
      op = Ge ; cst = Big_int unit_big_int } in
  (* Add the positivity constraint *)
  {coeffs = Vect.from_list ([Big_int zero_big_int ;Big_int unit_big_int]) ;
   op = Ge ;
   cst = Big_int zero_big_int}::(strict::(positivity l)@c::s0)
open Util

(** [direct_linear_prover l] does not handle strict inegalities *)
let fourier_linear_prover l =
  match Mfourier.Fourier.find_point l with
  | Inr prf ->
     if debug then Printf.printf "AProof : %a\n" Mfourier.pp_proof prf ;
     let cert = (*List.map (fun (x,n) -> x+1,n)*) (fst (List.hd (Mfourier.Proof.mk_proof l prf))) in
     if debug then Printf.printf "CProof : %a" Vect.pp cert ;
  (*Some (rats_to_ints (Vect.to_list cert))*)
     Some (Vect.normalise cert)
  | Inl _   -> None


let direct_linear_prover l =
  if !use_simplex
  then Simplex.find_unsat_certificate l
  else fourier_linear_prover l

let find_point l =
   if !use_simplex
   then Simplex.find_point l
   else match Mfourier.Fourier.find_point l with
        | Inr _ -> None
        | Inl cert -> Some cert

let optimise v l =
  if !use_simplex
  then Simplex.optimise v l
  else Mfourier.Fourier.optimise v l



let dual_raw_certificate l =
  if debug
  then begin
      Printf.printf "dual_raw_certificate\n";
      List.iter (fun c -> Printf.fprintf stdout "%a\n" output_cstr c) l
    end;

  let sys = build_dual_linear_system l in

  if debug then begin
      Printf.printf "dual_system\n";
      List.iter (fun c -> Printf.fprintf stdout "%a\n" output_cstr c) sys
    end;

  try
    match find_point sys with
    | None -> None
    | Some cert ->
       match Vect.choose cert with
       | None -> failwith "dual_raw_certificate: empty_certificate"
       | Some _ ->
          (*Some (rats_to_ints (Vect.to_list (Vect.decr_var 2 (Vect.set 1 (Int 0) cert))))*)
          Some (Vect.normalise (Vect.decr_var 2 (Vect.set 1 (Int 0) cert)))
               (* should not use rats_to_ints *)
  with x when CErrors.noncritical x ->
        if debug
        then (Printf.printf "dual raw certificate %s" (Printexc.to_string x);
              flush stdout) ;
        None



let simple_linear_prover l =
  try
    direct_linear_prover l
  with Strict ->
    (* Fourier elimination should handle > *)
    dual_raw_certificate l

let env_of_list l =
  snd (List.fold_left (fun (i,m) p -> (i+1,IMap.add i p m)) (0,IMap.empty) l)




let linear_prover_cstr sys =
  let (sysi,prfi) = List.split sys in


  match simple_linear_prover sysi with
  | None -> None
  | Some cert -> Some (ProofFormat.proof_of_farkas (env_of_list prfi) cert)

let linear_prover_cstr  =
  if debug
  then
    fun sys ->
    Printf.printf "<linear_prover"; flush stdout ;
    let res = linear_prover_cstr sys in
    Printf.printf ">"; flush stdout ;
    res
  else linear_prover_cstr



let compute_max_nb_cstr l d =
  let len = List.length l in
  max len (max d (len * d))


let develop_constraint z_spec (e,k) =
  (dev_form z_spec e,
   match k with
   | Mc.NonStrict -> Ge
   | Mc.Equal     -> Eq
   | Mc.Strict    -> Gt
   | _     -> assert false
  )

(** A single constraint can be unsat for the following reasons:
    - 0 >= c for c a negative constant
    - 0 =  c for c a non-zero constant
    - e = c  when the coeffs of e are all integers and c is rational
 *)

type checksat =
  | Tauto (* Tautology *)
  | Unsat of ProofFormat.prf_rule (* Unsatisfiable *)
  | Cut of cstr * ProofFormat.prf_rule (* Cutting plane *)
  | Normalise of cstr * ProofFormat.prf_rule (* Coefficients may be normalised i.e relatively prime *)

exception FoundProof of  ProofFormat.prf_rule


(** [check_sat]
    - detects constraints that are not satisfiable;
    - normalises constraints and generate cuts.
 *)

let check_int_sat (cstr,prf) =
  let {coeffs=coeffs ; op=op ; cst=cst} = cstr in
  match Vect.choose coeffs with
  | None ->
     if eval_op op (Int 0) cst then Tauto else Unsat prf
  | _  ->
     let gcdi =  Vect.gcd coeffs in
     let gcd = Big_int gcdi in
     if eq_num gcd (Int 1)
     then Normalise(cstr,prf)
     else
       if Int.equal (sign_num (mod_num cst gcd)) 0
       then (* We can really normalise *)
         begin
           assert (sign_num gcd >=1 ) ;
           let cstr = {
               coeffs = Vect.div gcd  coeffs;
               op = op ; cst = cst // gcd
             } in
           Normalise(cstr,ProofFormat.Gcd(gcdi,prf))
                    (*		    Normalise(cstr,CutPrf prf)*)
         end
       else
         match op with
         | Eq -> Unsat (ProofFormat.CutPrf prf)
         | Ge ->
            let cstr = {
                coeffs = Vect.div gcd coeffs;
                op = op ; cst = ceiling_num (cst // gcd)
              } in Cut(cstr,ProofFormat.CutPrf prf)
         | Gt -> failwith "check_sat : Unexpected operator"


let apply_and_normalise check f psys =
  List.fold_left (fun acc pc' ->
      match f pc' with
      | None -> pc'::acc
      | Some pc' ->
         match check pc' with
         | Tauto -> acc
         | Unsat prf -> raise (FoundProof prf)
         | Cut(c,p)  -> (c,p)::acc
         | Normalise (c,p) -> (c,p)::acc
    ) [] psys



let is_linear_for v pc =
  LinPoly.is_linear (fst (fst pc)) || LinPoly.is_linear_for v (fst (fst pc))




(*let non_linear_pivot sys pc v pc' =
  if LinPoly.is_linear (fst (fst pc'))
  then None (* There are other ways to deal with those *)
  else WithProof.linear_pivot sys pc v pc'
 *)

let is_linear_substitution sys ((p,o),prf) =
  let pred v =  v =/ Int 1 || v =/ Int (-1)  in
  match o with
  | Eq -> begin
      match
        List.filter (fun v -> List.for_all (is_linear_for v) sys) (LinPoly.search_all_linear pred p)
      with
      | [] -> None
      | v::_  -> Some v (* make a choice *)
    end
  | _  -> None


let elim_simple_linear_equality sys0 =

  let elim sys =
    let (oeq,sys') = extract (is_linear_substitution sys) sys in
    match oeq with
    | None -> None
    | Some(v,pc) -> simplify (WithProof.linear_pivot sys0 pc v) sys' in

  iterate_until_stable elim sys0



let output_sys o sys =
  List.iter (fun s -> Printf.fprintf o "%a\n" WithProof.output s) sys

let subst sys =
  let sys' = WithProof.subst sys in
  if debug then Printf.fprintf stdout "[subst:\n%a\n==>\n%a\n]" output_sys sys output_sys sys' ;
  sys'



(** [saturate_linear_equality sys] generate new constraints
    obtained by eliminating linear equalities by pivoting.
    For integers, the obtained constraints are  sound but not complete.
 *)
  let saturate_by_linear_equalities sys0 =
    WithProof.saturate_subst false sys0


let saturate_by_linear_equalities sys =
  let sys' = saturate_by_linear_equalities sys in
  if debug then Printf.fprintf stdout "[saturate_by_linear_equalities:\n%a\n==>\n%a\n]" output_sys sys output_sys sys' ;
  sys'



(* let saturate_linear_equality_non_linear sys0 =
  let (l,_) = extract_all (is_substitution false) sys0 in
  let rec elim l acc =
    match l with
    | [] -> acc
    | (v,pc)::l' ->
       let nc = saturate (non_linear_pivot sys0 pc v) (sys0@acc) in
       elim l' (nc@acc) in
  elim l []
 *)

let bounded_vars (sys: WithProof.t list) =
  let l =  (fst (extract_all (fun ((p,o),prf) ->
                     LinPoly.is_variable p
                   ) sys)) in
  List.fold_left (fun acc (i,wp) -> IMap.add i wp acc) IMap.empty l

let rec power n p =
  if n = 1 then p
  else WithProof.product p (power (n-1) p)

let bound_monomial mp m =
  if  Monomial.is_var m || Monomial.is_const m
  then None
  else
     try
       Some (Monomial.fold
               (fun v i acc ->
                 let wp = IMap.find v mp in
                 WithProof.product (power i wp) acc) m (WithProof.const (Int 1))
         )
     with Not_found -> None


let bound_monomials (sys:WithProof.t list) =
  let mp = bounded_vars sys in
  let m  =
    List.fold_left (fun acc ((p,_),_) ->
        Vect.fold (fun acc v _ -> let m = LinPoly.MonT.retrieve v in
                                  match bound_monomial mp m with
                                  | None -> acc
                                  | Some r -> IMap.add v r acc) acc p) IMap.empty sys in
  IMap.fold (fun _ e acc -> e::acc) m []


let develop_constraints prfdepth n_spec sys =
  LinPoly.MonT.clear ();
  max_nb_cstr := compute_max_nb_cstr sys prfdepth ;
  let sys = List.map (develop_constraint n_spec) sys in
  List.mapi (fun i (p,o) -> ((LinPoly.linpol_of_pol p,o),ProofFormat.Hyp i)) sys

let square_of_var i =
  let x = LinPoly.var i in
  ((LinPoly.product x x,Ge),(ProofFormat.Square  x))

  
(** [nlinear_preprocess  sys]  augments the system [sys] by performing some limited non-linear reasoning.
    For instance, it asserts that the x² ≥0 but also that if c₁ ≥ 0 ∈ sys and c₂ ≥ 0 ∈ sys then c₁ × c₂ ≥ 0.
    The resulting system is linearised.
 *)

let nlinear_preprocess  (sys:WithProof.t list) =

  let is_linear =  List.for_all (fun ((p,_),_) -> LinPoly.is_linear p) sys in

  if is_linear then sys
  else
    let collect_square =
      List.fold_left (fun acc ((p,_),_) -> MonMap.union (fun k e1 e2 -> Some e1) acc (LinPoly.collect_square p)) MonMap.empty sys in
    let sys = MonMap.fold (fun s m acc ->
                  let s = LinPoly.of_monomial s in
                  let m = LinPoly.of_monomial m in
                  ((m, Ge), (ProofFormat.Square s))::acc) collect_square  sys in

    let collect_vars = List.fold_left (fun acc p -> ISet.union acc (LinPoly.variables (fst (fst p)))) ISet.empty sys in

    let sys = ISet.fold (fun i acc -> square_of_var i :: acc) collect_vars sys  in

    let sys = sys @ (all_pairs WithProof.product sys) in
  
    if debug then begin
        Printf.fprintf stdout "Preprocessed\n";
        List.iter (fun s -> Printf.fprintf stdout "%a\n" WithProof.output s) sys;
      end ;

    List.map (WithProof.annot "P") sys



let nlinear_prover prfdepth sys =
  let sys = develop_constraints prfdepth q_spec sys in
  let sys1 = elim_simple_linear_equality sys in
  let sys2 = saturate_by_linear_equalities sys1 in
  let sys = nlinear_preprocess sys1@sys2 in
  let sys = List.map (fun ((p,o),prf) -> (cstr_of_poly (p,o), prf)) sys in
  let id  = (List.fold_left
              (fun acc (_,r) -> max acc (ProofFormat.pr_rule_max_id r)) 0 sys) in
  let env = CList.interval 0 id in
  match linear_prover_cstr sys with
  | None -> Unknown
  | Some cert ->
     Prf (ProofFormat.cmpl_prf_rule Mc.normQ CamlToCoq.q env cert)


let linear_prover_with_cert prfdepth sys =
  let sys = develop_constraints prfdepth q_spec sys in
  (*  let sys = nlinear_preprocess  sys in *)
  let sys = List.map (fun (c,p) -> cstr_of_poly c,p) sys in

  match linear_prover_cstr sys with
  | None -> Unknown
  | Some cert ->
     Prf (ProofFormat.cmpl_prf_rule Mc.normQ CamlToCoq.q (List.mapi (fun i e -> i) sys) cert)

(* The prover is (probably) incomplete -- 
   only searching for naive cutting planes *)

open Sos_types

let rec scale_term t = 
  match t with
  | Zero    -> unit_big_int , Zero
  | Const n ->  (denominator n) , Const (Big_int (numerator n))
  | Var n   -> unit_big_int , Var n
  | Opp t   -> let s, t = scale_term t in s, Opp t
  | Add(t1,t2) -> let s1,y1 = scale_term t1 and s2,y2 = scale_term t2 in
                  let g = gcd_big_int s1 s2 in
                  let s1' = div_big_int s1 g in
                  let s2' = div_big_int s2 g in
                  let e = mult_big_int g (mult_big_int s1' s2') in
                  if Int.equal (compare_big_int e unit_big_int) 0
                  then (unit_big_int, Add (y1,y2))
                  else 	e, Add (Mul(Const (Big_int s2'), y1),
		                Mul (Const (Big_int s1'), y2))
  | Sub _ -> failwith "scale term: not implemented"
  | Mul(y,z) ->       let s1,y1 = scale_term y and s2,y2 = scale_term z in
                      mult_big_int s1 s2 , Mul (y1, y2)
  |  Pow(t,n) -> let s,t = scale_term t in
                 power_big_int_positive_int s  n , Pow(t,n)

let scale_term t =
  let (s,t') = scale_term t in
  s,t'

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
       if Int.equal (compare_num n (Int 0)) 0 then Mc.PsatzZ else
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

let term_to_z_pol e = Mc.norm_aux (Ml2C.z 0) (Ml2C.z 1) Mc.Z.add  Mc.Z.mul Mc.Z.sub Mc.Z.opp Mc.zeq_bool (term_to_z_expr e)

let  z_cert_of_pos  pos = 
  let s,pos = (scale_certificate pos) in
  let rec _cert_of_pos = function
      Axiom_eq i ->  Mc.PsatzIn (Ml2C.nat i)
    | Axiom_le i ->  Mc.PsatzIn (Ml2C.nat i)
    | Axiom_lt i ->  Mc.PsatzIn (Ml2C.nat i)
    | Monoid l  -> product l
    | Rational_eq n | Rational_le n | Rational_lt n ->
       if Int.equal (compare_num n (Int 0)) 0 then Mc.PsatzZ else
         Mc.PsatzC (Ml2C.bigint (big_int_of_num  n))
    | Square t -> Mc.PsatzSquare (term_to_z_pol  t)
    | Eqmul (t, y) ->
       let is_unit =
         match t with
         | Const n -> n =/ Int 1
         |   _     -> false in
       if is_unit
       then _cert_of_pos y
       else Mc.PsatzMulC(term_to_z_pol t, _cert_of_pos y)
    | Sum (y, z) -> Mc.PsatzAdd  (_cert_of_pos y, _cert_of_pos z)
    | Product (y, z) -> Mc.PsatzMulE (_cert_of_pos y, _cert_of_pos z) in
  simplify_cone z_spec (_cert_of_pos pos)

(** All constraints (initial or derived) have an index and have a justification i.e., proof.
    Given a constraint, all the coefficients are always integers.
 *)
open Mutils
open Num
open Big_int
open Polynomial



type prf_sys = (cstr * ProofFormat.prf_rule) list



(** Proof generating pivoting over variable v *)
let pivot v (c1,p1) (c2,p2) = 
  let {coeffs = v1 ; op = op1 ; cst = n1} = c1
  and {coeffs = v2 ; op = op2 ; cst = n2} = c2 in



  (* Could factorise gcd... *)
  let xpivot cv1 cv2 =
    (
      {coeffs = Vect.add (Vect.mul cv1 v1) (Vect.mul cv2 v2) ;
       op = opAdd op1 op2 ;
       cst = n1 */ cv1 +/ n2 */ cv2 },

      ProofFormat.add_proof (ProofFormat.mul_cst_proof  cv1 p1) (ProofFormat.mul_cst_proof  cv2 p2)) in

  match Vect.get v v1 , Vect.get v v2 with
  | Int 0 , _ | _ , Int 0 -> None
  |  a   ,  b   ->
      if Int.equal ((sign_num a) * (sign_num b)) (-1)
      then
        let cv1 = abs_num b
        and cv2 = abs_num a  in
        Some (xpivot cv1 cv2)
      else
        if op1 == Eq
        then
          let cv1 = minus_num (b */ (Int (sign_num a)))
          and cv2 = abs_num a in
          Some (xpivot cv1 cv2)
        else if op2 == Eq
        then
          let cv1 = abs_num b
          and cv2 = minus_num (a */ (Int  (sign_num b))) in
          Some (xpivot cv1 cv2)
        else  None (* op2 could be Eq ... this might happen *)


let simpl_sys sys = 
  List.fold_left (fun acc (c,p) ->
      match check_int_sat (c,p) with
      | Tauto -> acc
      | Unsat prf -> raise (FoundProof prf)
      | Cut(c,p)  -> (c,p)::acc
      | Normalise (c,p) -> (c,p)::acc) [] sys


(** [ext_gcd a b] is the extended Euclid algorithm.
    [ext_gcd a b = (x,y,g)] iff [ax+by=g]
    Source: http://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
 *)
let rec ext_gcd a b = 
  if Int.equal (sign_big_int b) 0
  then (unit_big_int,zero_big_int)
  else
    let (q,r) = quomod_big_int a b in
    let (s,t) = ext_gcd b r in
    (t, sub_big_int s (mult_big_int q t))

let extract_coprime (c1,p1) (c2,p2) = 
  if c1.op == Eq && c2.op == Eq
  then Vect.exists2 (fun n1 n2 ->
           Int.equal (compare_big_int (gcd_big_int (numerator n1) (numerator n2)) unit_big_int) 0)
           c1.coeffs c2.coeffs
  else None

let extract2 pred l =
  let rec xextract2 rl l =
    match l with
    | [] -> (None,rl) (* Did not find *)
    | e::l ->
       match extract (pred e) l with
       | None,_ -> xextract2 (e::rl) l
       | Some (r,e'),l' -> Some (r,e,e'), List.rev_append rl l' in

  xextract2 [] l


let extract_coprime_equation psys =
  extract2 extract_coprime psys






let pivot_sys v pc psys = apply_and_normalise check_int_sat (pivot v pc) psys

let reduce_coprime psys = 
  let oeq,sys = extract_coprime_equation psys in
  match oeq with
  | None -> None (* Nothing to do *)
  | Some((v,n1,n2),(c1,p1),(c2,p2) ) ->
     let (l1,l2) = ext_gcd (numerator n1) (numerator n2) in
     let l1' = Big_int l1 and l2' = Big_int l2 in
     let cstr =
       {coeffs = Vect.add (Vect.mul l1' c1.coeffs) (Vect.mul l2' c2.coeffs);
        op = Eq ;
        cst = (l1' */ c1.cst) +/ (l2' */ c2.cst)
       } in
     let prf = ProofFormat.add_proof (ProofFormat.mul_cst_proof  l1' p1) (ProofFormat.mul_cst_proof  l2' p2) in

     Some (pivot_sys v (cstr,prf) ((c1,p1)::sys))

(** If there is an equation [eq] of the form 1.x + e = c, do a pivot over x with equation [eq] *)
let reduce_unary psys = 
  let is_unary_equation (cstr,prf) =
    if cstr.op == Eq
    then
      Vect.find (fun v n -> if n =/ (Int 1) || n=/ (Int (-1)) then Some v else None) cstr.coeffs
    else None in

  let (oeq,sys) =  extract is_unary_equation psys in
  match oeq with
  | None -> None (* Nothing to do *)
  | Some(v,pc) ->
     Some(pivot_sys v pc sys)


let reduce_var_change psys = 

  let rec rel_prime vect =
    match Vect.choose vect with
    | None -> None
    | Some(x,v,vect) ->
       let v = numerator v in
       match Vect.find (fun x' v' ->
                           let v' = numerator v' in
                           if eq_big_int (gcd_big_int  v v') unit_big_int
                           then  Some(x',v') else None) vect with
       | Some(x',v') ->  Some ((x,v),(x', v'))
       | None  -> rel_prime vect in

  let rel_prime (cstr,prf) =  if cstr.op == Eq then rel_prime cstr.coeffs else None in

  let (oeq,sys) = extract rel_prime psys in

  match oeq with
  | None -> None
  | Some(((x,v),(x',v')),(c,p)) ->
     let (l1,l2) = ext_gcd  v  v' in
     let l1,l2 = Big_int l1 , Big_int l2 in


     let pivot_eq (c',p') =
       let {coeffs = coeffs ; op = op ; cst = cst} = c' in
       let vx = Vect.get x coeffs in
       let vx' = Vect.get x' coeffs in
       let m = minus_num (vx */ l1 +/ vx' */ l2) in
       Some ({coeffs =
                Vect.add (Vect.mul m c.coeffs) coeffs ; op = op ; cst = m */ c.cst +/ cst} ,
             ProofFormat.add_proof (ProofFormat.mul_cst_proof m p) p') in

     Some (apply_and_normalise check_int_sat pivot_eq sys)


let reduction_equations psys =
  iterate_until_stable (app_funs
                          [reduce_unary ; reduce_coprime ;
                           reduce_var_change (*; reduce_pivot*)]) psys





(** [get_bound sys] returns upon success an interval (lb,e,ub) with proofs *)
let get_bound sys = 
  let is_small (v,i) =
    match Itv.range i with
    | None -> false
    | Some i -> i <=/ (Int 1) in

  let select_best (x1,i1) (x2,i2) =
    if Itv.smaller_itv i1 i2
    then (x1,i1) else (x2,i2) in

  (* For lia, there are no equations => these precautions are not needed *)
  (* For nlia, there are equations => do not enumerate over equations! *)
  let all_planes sys =
    let (eq,ineq) = List.partition (fun c -> c.op == Eq) sys in
    match eq with
    | [] -> List.rev_map (fun c -> c.coeffs) ineq
    | _  ->
       List.fold_left (fun acc c ->
           if List.exists (fun c' -> Vect.equal c.coeffs c'.coeffs) eq
           then acc else c.coeffs ::acc) [] ineq in

  let smallest_interval =
    List.fold_left
      (fun acc vect ->
        if is_small acc
        then acc
        else
          match optimise vect sys with
          | None -> acc
          | Some i ->
             if debug then Printf.printf "Found a new bound %a in %a" Vect.pp vect Itv.pp i;
             select_best (vect,i) acc)  (Vect.null, (None,None)) (all_planes sys) in
  let smallest_interval =
    match smallest_interval
    with
    | (x,(Some i, Some j))  -> Some(i,x,j)
    |   x        ->   None (* This should not be possible *)
  in
  match smallest_interval with
  | Some (lb,e,ub) ->
     let (lbn,lbd) = (sub_big_int (numerator lb)  unit_big_int, denominator lb) in
     let (ubn,ubd) = (add_big_int unit_big_int (numerator ub) , denominator ub) in
     (match
        (* x <= ub ->  x  > ub *)
        direct_linear_prover   ({coeffs = Vect.mul (Big_int ubd)  e ; op = Ge ; cst = Big_int ubn} :: sys),
        (* lb <= x  -> lb > x *)
        direct_linear_prover
          ({coeffs = Vect.mul (minus_num (Big_int lbd)) e ; op = Ge ; cst = minus_num (Big_int lbn)} :: sys)
      with
      | Some cub , Some clb  -> Some(List.tl (Vect.to_list clb),(lb,e,ub), List.tl (Vect.to_list cub))
      |         _            -> failwith "Interval without proof"
     )
  | None -> None


let check_sys sys = 
  List.for_all (fun (c,p) -> Vect.for_all (fun _ n -> sign_num n <> 0) c.coeffs) sys

open ProofFormat

let xlia (can_enum:bool)  reduction_equations  sys = 


  let rec enum_proof (id:int) (sys:prf_sys)  =
    if debug then (Printf.printf "enum_proof\n" ; flush stdout) ;
    assert (check_sys sys) ;

    let nsys,prf = List.split sys in
    match get_bound nsys with
    | None -> Unknown (* Is the systeme really unbounded ? *)
    | Some(prf1,(lb,e,ub),prf2) ->
       if debug then Printf.printf "Found interval: %a in [%s;%s] -> " Vect.pp e (string_of_num lb) (string_of_num ub) ;
       (match start_enum  id  e  (ceiling_num lb)  (floor_num ub) sys
        with
        | Prf prfl ->
           Prf(ProofFormat.Enum(id,ProofFormat.proof_of_farkas (env_of_list prf) (Vect.from_list prf1),e,
                     ProofFormat.proof_of_farkas (env_of_list prf) (Vect.from_list prf2),prfl))
        | _ -> Unknown
       )

  and start_enum id e clb cub sys  =
    if clb >/ cub
    then Prf []
    else
      let eq = {coeffs = e ; op = Eq ; cst = clb} in
      match aux_lia (id+1) ((eq, ProofFormat.Def id) :: sys) with
      | Unknown | Model _ -> Unknown
      | Prf prf  ->
         match start_enum id e (clb +/ (Int 1)) cub sys with
         | Prf l -> Prf (prf::l)
         | _ -> Unknown


  and aux_lia (id:int)  (sys:prf_sys)   =
    assert (check_sys sys) ;
    if debug then Printf.printf "xlia:  %a \n" (pp_list ";" (fun o (c,_) -> output_cstr o c)) sys ;
    try
      let sys = reduction_equations sys in
      if debug then
        Printf.printf "after reduction:  %a \n" (pp_list ";" (fun o (c,_) -> output_cstr o c)) sys ;
      match linear_prover_cstr sys with
      | Some prf -> Prf (Step(id,prf,Done))
      | None ->  if can_enum then enum_proof id sys else Unknown
    with FoundProof prf ->
      (* [reduction_equations] can find a proof *)
      Prf(Step(id,prf,Done)) in

  (*  let sys' = List.map (fun (p,o) -> Mc.norm0 p , o) sys in*)
  let id  = 1 + (List.fold_left
              (fun acc (_,r) -> max acc (ProofFormat.pr_rule_max_id r)) 0 sys) in
  let orpf =
    try
      let sys = simpl_sys sys in
      aux_lia id sys
    with FoundProof pr -> Prf(Step(id,pr,Done)) in
  match orpf with
  | Unknown | Model _ -> Unknown
  | Prf prf ->
     let env = CList.interval 0 (id - 1) in
     if debug then begin
         Printf.fprintf stdout "direct proof %a\n" output_proof prf;
         flush stdout;
       end;
       let prf = compile_proof env prf in
     (*try
	     if Mc.zChecker sys' prf then Some prf else 
	     raise Certificate.BadCertificate
	     with Failure s -> (Printf.printf "%s" s ; Some prf)
      *) Prf prf

let xlia_simplex env red sys =
  let compile_prf sys prf =
    let id  = 1 + (List.fold_left
                          (fun acc (_,r) -> max acc (ProofFormat.pr_rule_max_id r)) 0 sys) in
    let env = CList.interval 0 (id - 1) in
    Prf (compile_proof env prf) in

  try
    let sys = red sys in

    match Simplex.integer_solver sys with
    | None -> Unknown
    | Some prf -> compile_prf sys prf
  with FoundProof prf -> compile_prf sys (Step(0,prf,Done))

let xlia env0 en red sys =
  if !use_simplex then xlia_simplex env0 red sys
  else xlia en red sys


let dump_file = ref None

let gen_bench (tac, prover) can_enum prfdepth sys =
  let res = prover can_enum prfdepth sys in
  (match !dump_file with
  | None -> ()
  | Some file ->
     begin
       let o = open_out (Filename.temp_file ~temp_dir:(Sys.getcwd ()) file ".v") in
       let sys = develop_constraints prfdepth z_spec sys in
       Printf.fprintf o "Require Import ZArith Lia. Open Scope Z_scope.\n";
       Printf.fprintf o "Goal %a.\n" (LinPoly.pp_goal "Z") (List.map fst sys) ;
       begin
         match res with
         | Unknown | Model _ ->
            Printf.fprintf o "Proof.\n intros. Fail %s.\nAbort.\n" tac
         | Prf res ->
            Printf.fprintf o "Proof.\n intros. %s.\nQed.\n" tac
       end
       ;
         flush o ;
       close_out o ;
     end);
  res

let lia (can_enum:bool) (prfdepth:int) sys = 
  let sys = develop_constraints prfdepth z_spec sys in
  if debug then begin
      Printf.fprintf stdout "Input problem\n";
      List.iter (fun s -> Printf.fprintf stdout "%a\n" WithProof.output s) sys;
      Printf.fprintf stdout "Input problem\n";
      let string_of_op = function Eq -> "=" | Ge -> ">=" | Gt -> ">" in
      List.iter (fun ((p,op),_) -> Printf.fprintf stdout "(assert (%s %a))\n" (string_of_op op) Vect.pp_smt p) sys;
    end;
  let sys = subst sys in
  let bnd = bound_monomials sys in (* To deal with non-linear monomials *)
  let sys = bnd@(saturate_by_linear_equalities sys)@sys in


  let sys' = List.map (fun ((p,o),prf) -> (cstr_of_poly (p,o), prf)) sys in
  xlia (List.map fst sys) can_enum reduction_equations sys'

let make_cstr_system sys =
  List.map (fun ((p,o),prf) -> (cstr_of_poly (p,o), prf)) sys

let nlia enum prfdepth sys = 
  let sys = develop_constraints prfdepth z_spec sys in
  let is_linear =  List.for_all (fun ((p,_),_) -> LinPoly.is_linear p) sys in

  if debug then begin
      Printf.fprintf stdout "Input problem\n";
      List.iter (fun s -> Printf.fprintf stdout "%a\n" WithProof.output s) sys;
    end;

  if is_linear
  then xlia (List.map fst sys) enum reduction_equations (make_cstr_system sys)
  else
    (*
      let sys1 = elim_every_substitution sys in
      No: if a wrong equation is chosen, the proof may fail.
      It would only be safe if the variable is linear...
     *)
    let sys1 = elim_simple_linear_equality sys in
    let sys2 = saturate_by_linear_equalities sys1 in
    let sys3 = nlinear_preprocess (sys1@sys2) in

    let sys4  = make_cstr_system ((*sys2@*)sys3) in
    (* [reduction_equations] is too brutal - there should be some non-linear reasoning  *)
    xlia (List.map fst sys) enum  reduction_equations sys4

(* For regression testing, if bench = true generate a Coq goal *)

let lia can_enum prfdepth sys =
  gen_bench ("lia",lia) can_enum prfdepth sys

let nlia enum prfdepth sys =
  gen_bench ("nia",nlia) enum prfdepth sys





(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
