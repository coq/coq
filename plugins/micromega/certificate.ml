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
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

(* We take as input a list of polynomials [p1...pn] and return an unfeasibility
   certificate polynomial. *)

let debug = false

open Polynomial
module Mc = Micromega
module Ml2C = Mutils.CamlToCoq
module C2Ml = Mutils.CoqToCaml
open NumCompat
open Q.Notations
open Mutils

(* If set to some [file], arithmetic goals are dumped in [file].v *)

let { Goptions.get = dump_file } =
  Goptions.declare_stringopt_option_and_ref
    ~key:["Dump"; "Arith"]
    ~value:None
    ()

type ('prf, 'model) res = Prf of 'prf | Model of 'model | Unknown
type zres = (Mc.zArithProof, int * Mc.z list) res
type qres = (Mc.q Mc.psatz, int * Mc.q list) res

type 'a number_spec =
  { bigint_to_number : Z.t -> 'a
  ; number_to_num : 'a -> Q.t
  ; zero : 'a
  ; unit : 'a
  ; mult : 'a -> 'a -> 'a
  ; eqb : 'a -> 'a -> bool }

let z_spec =
  { bigint_to_number = Ml2C.bigint
  ; number_to_num = (fun x -> Q.of_bigint (C2Ml.z_big_int x))
  ; zero = Mc.Z0
  ; unit = Mc.Zpos Mc.XH
  ; mult = Mc.Z.mul
  ; eqb = Mc.Z.eqb }

let q_spec =
  { bigint_to_number = (fun x -> {Mc.qnum = Ml2C.bigint x; Mc.qden = Mc.XH})
  ; number_to_num = C2Ml.q_to_num
  ; zero = {Mc.qnum = Mc.Z0; Mc.qden = Mc.XH}
  ; unit = {Mc.qnum = Mc.Zpos Mc.XH; Mc.qden = Mc.XH}
  ; mult = Mc.qmult
  ; eqb = Mc.qeq_bool }

let dev_form n_spec p =
  let rec dev_form p =
    match p with
    | Mc.PEc z -> Poly.constant (n_spec.number_to_num z)
    | Mc.PEX v -> Poly.variable (C2Ml.positive v)
    | Mc.PEmul (p1, p2) ->
      let p1 = dev_form p1 in
      let p2 = dev_form p2 in
      Poly.product p1 p2
    | Mc.PEadd (p1, p2) -> Poly.addition (dev_form p1) (dev_form p2)
    | Mc.PEopp p -> Poly.uminus (dev_form p)
    | Mc.PEsub (p1, p2) ->
      Poly.addition (dev_form p1) (Poly.uminus (dev_form p2))
    | Mc.PEpow (p, n) ->
      let p = dev_form p in
      let n = C2Ml.n n in
      let rec pow n =
        if Int.equal n 0 then Poly.constant (n_spec.number_to_num n_spec.unit)
        else Poly.product p (pow (n - 1))
      in
      pow n
  in
  dev_form p

let rec fixpoint f x =
  let y' = f x in
  if y' = x then y' else fixpoint f y'

let rec_simpl_cone n_spec e =
  let simpl_cone =
    Mc.simpl_cone n_spec.zero n_spec.unit n_spec.mult n_spec.eqb
  in
  let rec rec_simpl_cone = function
    | Mc.PsatzMulE (t1, t2) ->
      simpl_cone (Mc.PsatzMulE (rec_simpl_cone t1, rec_simpl_cone t2))
    | Mc.PsatzAdd (t1, t2) ->
      simpl_cone (Mc.PsatzAdd (rec_simpl_cone t1, rec_simpl_cone t2))
    | x -> simpl_cone x
  in
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
  let coeffs = List.fold_left (fun acc p -> Vect.get v p.coeffs :: acc) [] l in
  { coeffs =
      Vect.from_list
        (Q.of_bigint Z.zero :: Q.of_bigint Z.zero :: List.rev coeffs)
  ; op = Eq
  ; cst = Q.of_bigint Z.zero }

let constrain_constant l =
  let coeffs = List.fold_left (fun acc p -> Q.neg p.cst :: acc) [] l in
  { coeffs =
      Vect.from_list (Q.of_bigint Z.zero :: Q.of_bigint Z.one :: List.rev coeffs)
  ; op = Eq
  ; cst = Q.of_bigint Z.zero }

let positivity l =
  let rec xpositivity i l =
    match l with
    | [] -> []
    | c :: l -> (
      match c.op with
      | Eq -> xpositivity (i + 1) l
      | _ ->
        { coeffs = Vect.update (i + 1) (fun _ -> Q.one) Vect.null
        ; op = Ge
        ; cst = Q.zero }
        :: xpositivity (i + 1) l )
  in
  xpositivity 1 l

let cstr_of_poly (p, o) =
  let c, l = Vect.decomp_cst p in
  {coeffs = l; op = o; cst = Q.neg c}

let make_cstr_system sys =
  let map wp =
    let ((p, o), prf) = WithProof.repr wp in
    (cstr_of_poly (p, o), prf)
  in
  List.map map sys

let variables_of_cstr c = Vect.variables c.coeffs

(* If the certificate includes at least one strict inequality,
   the obtained polynomial can also be 0 *)

let build_dual_linear_system l =
  let variables =
    List.fold_left
      (fun acc p -> ISet.union acc (variables_of_cstr p))
      ISet.empty l
  in
  (* For each monomial, compute a constraint *)
  let s0 =
    ISet.fold (fun mn res -> constrain_variable mn l :: res) variables []
  in
  let c = constrain_constant l in
  (* I need at least something strictly positive *)
  let strict =
    { coeffs =
        Vect.from_list
          ( Q.of_bigint Z.zero :: Q.of_bigint Z.one
          :: List.map
               (fun c ->
                 if is_strict c then Q.of_bigint Z.one else Q.of_bigint Z.zero)
               l )
    ; op = Ge
    ; cst = Q.of_bigint Z.one }
  in
  (* Add the positivity constraint *)
  { coeffs = Vect.from_list [Q.of_bigint Z.zero; Q.of_bigint Z.one]
  ; op = Ge
  ; cst = Q.of_bigint Z.zero }
  :: ((strict :: positivity l) @ (c :: s0))


let output_cstr_sys o sys =
  List.iter
    (fun (c, wp) ->
      Printf.fprintf o "%a by %a\n" output_cstr c ProofFormat.output_prf_rule wp)
    sys

let output_sys o sys =
  List.iter (fun s -> Printf.fprintf o "%a\n" WithProof.output s) sys

let tr_sys str f sys =
  let sys' = f sys in
  if debug then
    Printf.fprintf stdout "[%s\n%a=>\n%a]\n" str output_sys sys output_sys sys';
  sys'

let tr_cstr_sys str f sys =
  let sys' = f sys in
  if debug then
    Printf.fprintf stdout "[%s\n%a=>\n%a]\n" str output_cstr_sys sys
      output_cstr_sys sys';
  sys'

let dual_raw_certificate l =
  if debug then begin
    Printf.printf "dual_raw_certificate\n";
    List.iter (fun c -> Printf.fprintf stdout "%a\n" output_cstr c) l
  end;
  let sys = build_dual_linear_system l in
  if debug then begin
    Printf.printf "dual_system\n";
    List.iter (fun c -> Printf.fprintf stdout "%a\n" output_cstr c) sys
  end;
  try
    match Simplex.find_point sys with
    | None -> None
    | Some cert -> (
      match Vect.choose cert with
      | None -> failwith "dual_raw_certificate: empty_certificate"
      | Some _ ->
        (*Some (rats_to_ints (Vect.to_list (Vect.decr_var 2 (Vect.set 1 Q.zero cert))))*)
        Some (Vect.normalise (Vect.decr_var 2 (Vect.set 1 Q.zero cert))) )
    (* should not use rats_to_ints *)
  with x when CErrors.noncritical x ->
    if debug then (
      Printf.printf "dual raw certificate %s" (Printexc.to_string x);
      flush stdout );
    None

let simple_linear_prover l =
  try Simplex.find_unsat_certificate l
  with Strict ->  dual_raw_certificate l

let env_of_list l =
  snd
    (List.fold_left (fun (i, m) p -> (i + 1, IMap.add i p m)) (0, IMap.empty) l)

let linear_prover_cstr sys =
  let sysi, prfi = List.split sys in
  match simple_linear_prover sysi with
  | None -> None
  | Some cert -> Some (ProofFormat.proof_of_farkas (env_of_list prfi) cert)

let linear_prover_cstr =
  if debug then ( fun sys ->
    Printf.printf "<linear_prover";
    flush stdout;
    let res = linear_prover_cstr sys in
    Printf.printf ">"; flush stdout; res )
  else linear_prover_cstr

let compute_max_nb_cstr l d =
  let len = List.length l in
  max len (max d (len * d))

let develop_constraint z_spec (e, k) =
  ( dev_form z_spec e
  , match k with
    | Mc.NonStrict -> Ge
    | Mc.Equal -> Eq
    | Mc.Strict -> Gt
    | _ -> assert false )

(** A single constraint can be unsat for the following reasons:
    - 0 >= c for c a negative constant
    - 0 =  c for c a non-zero constant
    - e = c  when the coeffs of e are all integers and c is rational
 *)

type checksat =
  | Tauto (* Tautology *)
  | Unsat of ProofFormat.prf_rule (* Unsatisfiable *)
  | Cut of cstr * ProofFormat.prf_rule (* Cutting plane *)
  | Normalise of cstr * ProofFormat.prf_rule

(* Coefficients may be normalised i.e relatively prime *)

exception FoundProof of ProofFormat.prf_rule

(** [check_sat]
    - detects constraints that are not satisfiable;
    - normalises constraints and generate cuts.
 *)

let check_int_sat (cstr, prf) =
  let {coeffs; op; cst} = cstr in
  match Vect.choose coeffs with
  | None -> if eval_op op Q.zero cst then Tauto else Unsat prf
  | _ -> (
    let gcdi = Vect.gcd coeffs in
    let gcd = Q.of_bigint gcdi in
    if gcd =/ Q.one then Normalise (cstr, prf)
    else if Int.equal (Q.sign (Q.mod_ cst gcd)) 0 then begin
      (* We can really normalise *)
      assert (Q.sign gcd >= 1);
      let cstr = {coeffs = Vect.div gcd coeffs; op; cst = cst // gcd} in
      Normalise (cstr, ProofFormat.Gcd (gcdi, prf))
      (*		    Normalise(cstr,CutPrf prf)*)
    end
    else
      match op with
      | Eq -> Unsat (ProofFormat.CutPrf prf)
      | Ge ->
        let cstr =
          {coeffs = Vect.div gcd coeffs; op; cst = Q.ceiling (cst // gcd)}
        in
        Cut (cstr, ProofFormat.CutPrf prf)
      | Gt -> failwith "check_sat : Unexpected operator" )

let apply_and_normalise check f psys =
  List.fold_left
    (fun acc pc' ->
      match f pc' with
      | None -> pc' :: acc
      | Some pc' -> (
        match check pc' with
        | Tauto -> acc
        | Unsat prf -> raise (FoundProof prf)
        | Cut (c, p) -> (c, p) :: acc
        | Normalise (c, p) -> (c, p) :: acc ))
    [] psys

let is_linear_for v pc =
  LinPoly.is_linear (WithProof.polynomial pc) || LinPoly.is_linear_for v (WithProof.polynomial pc)

(*let non_linear_pivot sys pc v pc' =
  if LinPoly.is_linear (fst (fst pc'))
  then None (* There are other ways to deal with those *)
  else WithProof.linear_pivot sys pc v pc'
 *)

let is_linear_substitution sys wp =
  let (p, o), _ = WithProof.repr wp in
  let pred v = v =/ Q.one || v =/ Q.minus_one in
  match o with
  | Eq -> (
    match
      List.filter
        (fun v -> List.for_all (is_linear_for v) sys)
        (LinPoly.search_all_linear pred p)
    with
    | [] -> None
    | v :: _ -> Some v (* make a choice *) )
  | _ -> None

let elim_simple_linear_equality sys0 =
  let elim sys =
    let oeq, sys' = extract (is_linear_substitution sys) sys in
    match oeq with
    | None -> None
    | Some (v, pc) -> simplify (WithProof.linear_pivot sys0 pc v) sys'
  in
  iterate_until_stable elim sys0

let subst sys = tr_sys "subst" WithProof.subst sys

(** [saturate_linear_equality sys] generate new constraints
    obtained by eliminating linear equalities by pivoting.
    For integers, the obtained constraints are  sound but not complete.
 *)
let saturate_by_linear_equalities sys0 = WithProof.saturate_subst false sys0

let saturate_by_linear_equalities sys =
  tr_sys "saturate_by_linear_equalities" saturate_by_linear_equalities sys


let elim_redundant sys =
  let module VectMap = Map.Make (Vect) in
  let elim_eq sys =
    List.fold_left
      (fun acc wp ->
        let (_, o), _ = WithProof.repr wp in
        match o with
        | Gt -> assert false
        | Ge -> wp :: acc
        | Eq -> wp :: WithProof.neg wp :: acc)
      [] sys
  in
  let of_list l =
    List.fold_left
      (fun m wp ->
        let (v, o), _ = WithProof.repr wp in
        let q, v' = Vect.decomp_cst v in
        try
          let q', wp' = VectMap.find v' m in
          match Q.compare q q' with
          | 0 -> if o = Eq then VectMap.add v' (q, wp) m else m
          | 1 -> m
          | _ -> VectMap.add v' (q, wp) m
        with Not_found -> VectMap.add v' (q, wp) m)
      VectMap.empty l
  in
  let to_list m = VectMap.fold (fun _ (_, wp) sys -> wp :: sys) m [] in
  to_list (of_list (elim_eq sys))

let elim_redundant sys = tr_sys "elim_redundant" elim_redundant sys

let bound_monomials (sys : WithProof.t list) =
  let (all_bounds,_) = extract_all BoundWithProof.make sys in
  let mon = List.mapi (fun i b ->
      let v = (BoundWithProof.bound b).Vect.Bound.var in
      let m = LinPoly.MonT.retrieve v in
      (i,(v,m,b))) all_bounds in

  let vars = List.fold_left
      (fun acc wp -> ISet.union (LinPoly.monomials (WithProof.polynomial wp)) acc)
      ISet.empty sys in

  let rec build_constraints l =
    match l with
    |[] -> Linsolve.empty
    | (i,(_,m',_)) ::l ->
      let c = build_constraints l in
      let cm = Monomial.fold (fun x d acc -> Linsolve.make_mon x i d acc) m' Linsolve.empty in
      Linsolve.merge c cm
  in

  let eqn = build_constraints mon in


  let set_constants_for m e =
    Monomial.fold (fun x d acc -> Linsolve.set_constant x d e :: acc) m [] in


  (* [exp_bound b j] computes the bound at the power j for j >=1.
     The current algorithm is not complete. It performs iterative multiplications. *)
  let rec exp_bound b j =
    if j = 1 then Some b
    else
      let b1 = exp_bound b (j/2) in
      match b1 with
      | None -> None
      | Some b1 ->
        match BoundWithProof.mul_bound b1 b1 with
        | None -> None
        | Some b1_b1 ->
          if j mod 2 = 0
          then Some b1_b1
          else BoundWithProof.mul_bound b b1_b1 in

  let rec bound_using_sol sol =
    match sol with
    | [] -> None
    | [x,j] -> let (_,_,b) = List.assoc x mon in
      exp_bound b j
    | (x,j)::sol'-> let (_,_,b) = List.assoc x mon in
      match exp_bound b j with
      | None -> None
      | Some b -> match bound_using_sol sol' with
        |None -> None
        | Some b' -> BoundWithProof.mul_bound b b' in

  let bound_one_monomial x =
    let m = LinPoly.MonT.retrieve x in
    if Monomial.degree m <= 1
    then []
    else
      let eqn = set_constants_for m eqn in
      if debug then Printf.printf "Equations : %a\n" Linsolve.output_equations eqn ; flush stdout;
      let sol = Linsolve.solve_and_enum  eqn in
      if debug then Printf.printf "Solutions %i \n %a\n"  (List.length sol) Linsolve.output_solutions sol;
      let l = elim_redundant (CList.map_filter (fun s -> Option.map BoundWithProof.proof (bound_using_sol s)) sol) in
      if debug then Printf.printf "New bounds %a" output_sys l; l
  in

  ISet.fold (fun m acc -> List.rev_append (bound_one_monomial m) acc) vars []


let bound_monomials sys= tr_sys "bound_monomials" bound_monomials sys

let develop_constraints prfdepth n_spec sys =
  LinPoly.MonT.clear ();
  max_nb_cstr := compute_max_nb_cstr sys prfdepth;
  let sys = List.map (develop_constraint n_spec) sys in
  let sys = List.mapi (fun i (p, o) -> WithProof.mkhyp (LinPoly.linpol_of_pol p) o i) sys in
  ProofFormat.Env.make (List.length sys), sys

let square_of_var i =
  let x = LinPoly.var i in
  WithProof.square (LinPoly.product x x) x

(** [nlinear_preprocess  sys]  augments the system [sys] by performing some limited non-linear reasoning.
    For instance, it asserts that the x² ≥0 but also that if c₁ ≥ 0 ∈ sys and c₂ ≥ 0 ∈ sys then c₁ × c₂ ≥ 0.
    The resulting system is linearised.
 *)

let nlinear_preprocess (sys : WithProof.t list) =
  let is_linear = List.for_all (fun wp -> LinPoly.is_linear @@ WithProof.polynomial wp) sys in
  if is_linear then sys
  else
    let collect_square =
      List.fold_left
        (fun acc wp ->
          MonMap.union (fun k e1 e2 -> Some e1) acc (LinPoly.collect_square @@ WithProof.polynomial wp))
        MonMap.empty sys
    in
    let sys =
      MonMap.fold
        (fun s m acc ->
          let s = LinPoly.of_monomial s in
          let m = LinPoly.of_monomial m in
          (WithProof.square m s) :: acc)
        collect_square sys
    in
    let collect_vars =
      List.fold_left
        (fun acc p -> ISet.union acc (LinPoly.variables (WithProof.polynomial p)))
        ISet.empty sys
    in
    let sys =
      ISet.fold (fun i acc -> square_of_var i :: acc) collect_vars sys
    in
    let sys = sys @ all_pairs WithProof.product sys in
    List.map (WithProof.annot "P") sys

let nlinear_preprocess = tr_sys "nlinear_preprocess" nlinear_preprocess

let nlinear_prover prfdepth sys =
  let env, sys = develop_constraints prfdepth q_spec sys in
  let sys1 = elim_simple_linear_equality sys in
  let sys2 = saturate_by_linear_equalities sys1 in
  let sys = nlinear_preprocess sys1 @ sys2 in
  let sys = make_cstr_system sys in
  match linear_prover_cstr sys with
  | None -> Unknown
  | Some cert -> Prf (ProofFormat.cmpl_prf_rule Mc.normQ CamlToCoq.q env cert)

let linear_prover_with_cert prfdepth sys =
  let env, sys = develop_constraints prfdepth q_spec sys in
  (*  let sys = nlinear_preprocess  sys in *)
  let sys = make_cstr_system sys in
  match linear_prover_cstr sys with
  | None -> Unknown
  | Some cert ->
    Prf
      (ProofFormat.cmpl_prf_rule Mc.normQ CamlToCoq.q
         env
         cert)

(* The prover is (probably) incomplete --
   only searching for naive cutting planes *)

open Sos_types

let rec scale_term t =
  match t with
  | Zero -> (Z.one, Zero)
  | Const n -> (Q.den n, Const (Q.of_bigint (Q.num n)))
  | Var n -> (Z.one, Var n)
  | Opp t ->
    let s, t = scale_term t in
    (s, Opp t)
  | Add (t1, t2) ->
    let s1, y1 = scale_term t1 and s2, y2 = scale_term t2 in
    let g = Z.gcd s1 s2 in
    let s1' = Z.div s1 g in
    let s2' = Z.div s2 g in
    let e = Z.mul g (Z.mul s1' s2') in
    if Int.equal (Z.compare e Z.one) 0 then (Z.one, Add (y1, y2))
    else
      ( e
      , Add
          (Mul (Const (Q.of_bigint s2'), y1), Mul (Const (Q.of_bigint s1'), y2))
      )
  | Sub _ -> failwith "scale term: not implemented"
  | Mul (y, z) ->
    let s1, y1 = scale_term y and s2, y2 = scale_term z in
    (Z.mul s1 s2, Mul (y1, y2))
  | Pow (t, n) ->
    let s, t = scale_term t in
    (Z.power_int s n, Pow (t, n))

let scale_term t =
  let s, t' = scale_term t in
  (s, t')

let rec scale_certificate pos =
  match pos with
  | Axiom_eq i -> (Z.one, Axiom_eq i)
  | Axiom_le i -> (Z.one, Axiom_le i)
  | Axiom_lt i -> (Z.one, Axiom_lt i)
  | Monoid l -> (Z.one, Monoid l)
  | Rational_eq n -> (Q.den n, Rational_eq (Q.of_bigint (Q.num n)))
  | Rational_le n -> (Q.den n, Rational_le (Q.of_bigint (Q.num n)))
  | Rational_lt n -> (Q.den n, Rational_lt (Q.of_bigint (Q.num n)))
  | Square t ->
    let s, t' = scale_term t in
    (Z.mul s s, Square t')
  | Eqmul (t, y) ->
    let s1, y1 = scale_term t and s2, y2 = scale_certificate y in
    (Z.mul s1 s2, Eqmul (y1, y2))
  | Sum (y, z) ->
    let s1, y1 = scale_certificate y and s2, y2 = scale_certificate z in
    let g = Z.gcd s1 s2 in
    let s1' = Z.div s1 g in
    let s2' = Z.div s2 g in
    ( Z.mul g (Z.mul s1' s2')
    , Sum
        ( Product (Rational_le (Q.of_bigint s2'), y1)
        , Product (Rational_le (Q.of_bigint s1'), y2) ) )
  | Product (y, z) ->
    let s1, y1 = scale_certificate y and s2, y2 = scale_certificate z in
    (Z.mul s1 s2, Product (y1, y2))

module Z_ = Z
open Micromega

let rec term_to_q_expr = function
  | Const n -> PEc (Ml2C.q n)
  | Zero -> PEc (Ml2C.q Q.zero)
  | Var s ->
    PEX (Ml2C.index (int_of_string (String.sub s 1 (String.length s - 1))))
  | Mul (p1, p2) -> PEmul (term_to_q_expr p1, term_to_q_expr p2)
  | Add (p1, p2) -> PEadd (term_to_q_expr p1, term_to_q_expr p2)
  | Opp p -> PEopp (term_to_q_expr p)
  | Pow (t, n) -> PEpow (term_to_q_expr t, Ml2C.n n)
  | Sub (t1, t2) -> PEsub (term_to_q_expr t1, term_to_q_expr t2)

let term_to_q_pol e =
  Mc.norm_aux (Ml2C.q Q.zero) (Ml2C.q Q.one) Mc.qplus Mc.qmult Mc.qminus Mc.qopp
    Mc.qeq_bool (term_to_q_expr e)

let rec product l =
  match l with
  | [] -> Mc.PsatzZ
  | [i] -> Mc.PsatzIn (Ml2C.nat i)
  | i :: l -> Mc.PsatzMulE (Mc.PsatzIn (Ml2C.nat i), product l)

let q_cert_of_pos pos =
  let rec _cert_of_pos = function
    | Axiom_eq i -> Mc.PsatzIn (Ml2C.nat i)
    | Axiom_le i -> Mc.PsatzIn (Ml2C.nat i)
    | Axiom_lt i -> Mc.PsatzIn (Ml2C.nat i)
    | Monoid l -> product l
    | Rational_eq n | Rational_le n | Rational_lt n ->
      if Int.equal (Q.compare n Q.zero) 0 then Mc.PsatzZ
      else Mc.PsatzC (Ml2C.q n)
    | Square t -> Mc.PsatzSquare (term_to_q_pol t)
    | Eqmul (t, y) -> Mc.PsatzMulC (term_to_q_pol t, _cert_of_pos y)
    | Sum (y, z) -> Mc.PsatzAdd (_cert_of_pos y, _cert_of_pos z)
    | Product (y, z) -> Mc.PsatzMulE (_cert_of_pos y, _cert_of_pos z)
  in
  simplify_cone q_spec (_cert_of_pos pos)

let rec term_to_z_expr = function
  | Const n -> PEc (Ml2C.bigint (Q.to_bigint n))
  | Zero -> PEc Z0
  | Var s ->
    PEX (Ml2C.index (int_of_string (String.sub s 1 (String.length s - 1))))
  | Mul (p1, p2) -> PEmul (term_to_z_expr p1, term_to_z_expr p2)
  | Add (p1, p2) -> PEadd (term_to_z_expr p1, term_to_z_expr p2)
  | Opp p -> PEopp (term_to_z_expr p)
  | Pow (t, n) -> PEpow (term_to_z_expr t, Ml2C.n n)
  | Sub (t1, t2) -> PEsub (term_to_z_expr t1, term_to_z_expr t2)

let term_to_z_pol e =
  Mc.norm_aux (Ml2C.z 0) (Ml2C.z 1) Mc.Z.add Mc.Z.mul Mc.Z.sub Mc.Z.opp
    Mc.Z.eqb (term_to_z_expr e)

let z_cert_of_pos pos =
  let s, pos = scale_certificate pos in
  let rec _cert_of_pos = function
    | Axiom_eq i -> Mc.PsatzIn (Ml2C.nat i)
    | Axiom_le i -> Mc.PsatzIn (Ml2C.nat i)
    | Axiom_lt i -> Mc.PsatzIn (Ml2C.nat i)
    | Monoid l -> product l
    | Rational_eq n | Rational_le n | Rational_lt n ->
      if Int.equal (Q.compare n Q.zero) 0 then Mc.PsatzZ
      else Mc.PsatzC (Ml2C.bigint (Q.to_bigint n))
    | Square t -> Mc.PsatzSquare (term_to_z_pol t)
    | Eqmul (t, y) ->
      let is_unit = match t with Const n -> n =/ Q.one | _ -> false in
      if is_unit then _cert_of_pos y
      else Mc.PsatzMulC (term_to_z_pol t, _cert_of_pos y)
    | Sum (y, z) -> Mc.PsatzAdd (_cert_of_pos y, _cert_of_pos z)
    | Product (y, z) -> Mc.PsatzMulE (_cert_of_pos y, _cert_of_pos z)
  in
  simplify_cone z_spec (_cert_of_pos pos)

(** All constraints (initial or derived) have an index and have a justification i.e., proof.
    Given a constraint, all the coefficients are always integers.
 *)
open Mutils

open Polynomial

(** Proof generating pivoting over variable v.
    Assumes [a] is the non-zero coefficient for [v] in [c1]. *)
let pivot v (a, c1, p1) (c2, p2) =
  let {coeffs = v1; op = op1; cst = n1} = c1
  and {coeffs = v2; op = op2; cst = n2} = c2 in
  let () = assert (op1 == Eq) in
  (* Could factorise gcd... *)
  let xpivot cv1 cv2 =
    ( { coeffs = Vect.add (Vect.mul cv1 v1) (Vect.mul cv2 v2)
      ; op = opAdd Eq op2
      ; cst = (n1 */ cv1) +/ (n2 */ cv2) }
    , ProofFormat.add_proof
        (ProofFormat.mul_cst_proof cv1 p1)
        (ProofFormat.mul_cst_proof cv2 p2) )
  in
  let b = Vect.get v v2 in
  if b =/ Q.zero then None
  else if Int.equal (Q.sign a * Q.sign b) (-1) then
    let cv1 = Q.abs b and cv2 = Q.abs a in
    Some (xpivot cv1 cv2)
  else
    let cv1 = Q.neg (b */ Q.of_int (Q.sign a)) and cv2 = Q.abs a in
    Some (xpivot cv1 cv2)

let pivot v c1 c2 =
  let res = pivot v c1 c2 in
  ( match res with
  | None -> ()
  | Some (c, _) ->
    if Vect.get v c.coeffs =/ Q.zero then ()
    else Printf.printf "pivot error %a\n" output_cstr c );
  res


(** [ext_gcd a b] is the extended Euclid algorithm.
    [ext_gcd a b = (x,y,g)] iff [ax+by=g]
    Source: http://en.wikipedia.org/wiki/Extended_Euclidean_algorithm
 *)
let rec ext_gcd a b =
  if Int.equal (Z_.sign b) 0 then (Z_.one, Z_.zero)
  else
    let q, r = Z_.quomod a b in
    let s, t = ext_gcd b r in
    (t, Z_.sub s (Z_.mul q t))

let extract_coprime (c1, p1) (c2, p2) =
  let () = assert (c1.op == Eq) in
  if c2.op == Eq then
    Vect.exists2
      (fun n1 n2 ->
        Int.equal (Z_.compare (Z_.gcd (Q.num n1) (Q.num n2)) Z_.one) 0)
      c1.coeffs c2.coeffs
  else None

let extract_coprime_equation psys =
  let rec xextract2 rl l =
    match l with
    | [] -> (None, rl) (* Did not find *)
    | e :: l ->
      match (fst e).op with
      | Eq ->
        begin match extract (extract_coprime e) l with
        | None, _ -> xextract2 (e :: rl) l
        | Some (r, e'), l' -> (Some (r, e, e'), List.rev_append rl l')
        end
      | Gt | Ge -> xextract2 (e :: rl) l
  in
  xextract2 [] psys

let pivot_sys v (cstr, prf) psys =
  let a = Vect.get v cstr.coeffs in
  if a =/ Q.zero then List.rev psys
  else apply_and_normalise check_int_sat (pivot v (a, cstr, prf)) psys

let reduce_coprime psys =
  let oeq, sys = extract_coprime_equation psys in
  match oeq with
  | None -> None (* Nothing to do *)
  | Some ((v, n1, n2), (c1, p1), (c2, p2)) ->
    let l1, l2 = ext_gcd (Q.num n1) (Q.num n2) in
    let l1' = Q.of_bigint l1 and l2' = Q.of_bigint l2 in
    let cstr =
      { coeffs = Vect.add (Vect.mul l1' c1.coeffs) (Vect.mul l2' c2.coeffs)
      ; op = Eq
      ; cst = (l1' */ c1.cst) +/ (l2' */ c2.cst) }
    in
    let prf =
      ProofFormat.add_proof
        (ProofFormat.mul_cst_proof l1' p1)
        (ProofFormat.mul_cst_proof l2' p2)
    in
    Some (pivot_sys v (cstr, prf) ((c1, p1) :: sys))

(*let pivot_sys v pc sys = tr_cstr_sys "pivot_sys" (pivot_sys v pc) sys*)

(** If there is an equation [eq] of the form 1.x + e = c, do a pivot over x with equation [eq] *)
let reduce_unary psys =
  let is_unary_equation (cstr, prf) =
    if cstr.op == Eq then
      Vect.find
        (fun v n -> if n =/ Q.one || n =/ Q.minus_one then Some v else None)
        cstr.coeffs
    else None
  in
  let oeq, sys = extract is_unary_equation psys in
  match oeq with
  | None -> None (* Nothing to do *)
  | Some (v, (cstr, prf)) ->
    let () = assert (cstr.op == Eq) in
    Some (pivot_sys v (cstr, prf) sys)

let reduce_var_change psys =
  let rec rel_prime vect =
    match Vect.choose vect with
    | None -> None
    | Some (x, v, vect) -> (
      let v = Q.num v in
      match
        Vect.find
          (fun x' v' ->
            let v' = Q.num v' in
            if Z_.equal (Z_.gcd v v') Z_.one then Some (x', v') else None)
          vect
      with
      | Some (x', v') -> Some ((x, v), (x', v'))
      | None -> rel_prime vect )
  in
  let rel_prime (cstr, prf) =
    if cstr.op == Eq then rel_prime cstr.coeffs else None
  in
  let oeq, sys = extract rel_prime psys in
  match oeq with
  | None -> None
  | Some (((x, v), (x', v')), (c, p)) ->
    let l1, l2 = ext_gcd v v' in
    let l1, l2 = (Q.of_bigint l1, Q.of_bigint l2) in
    let pivot_eq (c', p') =
      let {coeffs; op; cst} = c' in
      let vx = Vect.get x coeffs in
      let vx' = Vect.get x' coeffs in
      let m = Q.neg ((vx */ l1) +/ (vx' */ l2)) in
      Some
        ( { coeffs = Vect.add (Vect.mul m c.coeffs) coeffs
          ; op
          ; cst = (m */ c.cst) +/ cst }
        , ProofFormat.add_proof (ProofFormat.mul_cst_proof m p) p' )
    in
    Some (apply_and_normalise check_int_sat pivot_eq sys)

let reduction_equations psys =
  iterate_until_stable
    (app_funs
       [reduce_unary; reduce_coprime; reduce_var_change (*; reduce_pivot*)])
    psys

let reduction_equations = tr_cstr_sys "reduction_equations" reduction_equations

open ProofFormat

let xlia env sys =
  let sys = make_cstr_system sys in
  match reduction_equations sys with
  | sys ->
    let sys = List.map WithProof.of_cstr sys in
    begin match Simplex.integer_solver sys with
    | None -> Unknown
    | Some prf -> Prf (compile_proof env prf)
    end
  | exception FoundProof prf ->
    Prf (compile_proof env (Step (0, prf, Done)))


let gen_bench (tac, prover)  prfdepth sys =
  let res = prover  prfdepth sys in
  ( match dump_file () with
  | None -> ()
  | Some file ->
    let o = open_out (Filename.temp_file ~temp_dir:(Sys.getcwd ()) file ".v") in
    let _, sys = develop_constraints prfdepth z_spec sys in
    Printf.fprintf o "Require Import ZArith Lia. Open Scope Z_scope.\n";
    Printf.fprintf o "Goal %a.\n" (LinPoly.pp_goal "Z") (List.map (fun wp -> fst @@ WithProof.repr wp) sys);
    begin
      match res with
      | Unknown | Model _ ->
        Printf.fprintf o "Proof.\n intros. Fail %s.\nAbort.\n" tac
      | Prf res -> Printf.fprintf o "Proof.\n intros. %s.\nQed.\n" tac
    end;
    flush o; close_out o );
  res

let normalise sys =
  List.fold_left
    (fun acc s ->
      match WithProof.cutting_plane s with
      | None -> s :: acc
      | Some s' -> s' :: acc)
    [] sys

let normalise = tr_sys "normalise" normalise


(** [fourier_small] performs some variable elimination and keeps the cutting planes.
    To decide which elimination to perform, the constraints are sorted according to
    1 - the number of variables
    2 - the value of the smallest coefficient
    Given the smallest constraint, we eliminate the variable with the smallest coefficient.
    The rational is that a constraint with a single variable provides some bound information.
    When there are several variables, we hope to eliminate all the variables.
    A necessary condition is to take the variable with the smallest coefficient *)

let try_pivot qx wp wp' =
  match WithProof.simple_pivot qx wp wp' with
  | None -> None
  | Some wp2 ->
    match WithProof.cutting_plane wp2 with
    | Some wp2 -> Some wp2
    | None -> None

let fourier_small (sys : WithProof.t list) =
  let module WPset = Set.Make(WithProof) in
  let gen_pivot acc qx wp l =
    let fold acc wp' =
      match try_pivot qx wp wp' with
      | None -> acc
      | Some wp2 -> WPset.add wp2 acc
    in
    let acc = WPset.fold (fun wp acc -> fold acc wp) acc acc in
    List.fold_left (fun acc (_,wp') -> fold acc wp') acc l
  in
  let rec all_pivots acc l =
    match l with
    | [] -> acc
    | ((_, qx), wp) :: l' -> all_pivots (gen_pivot acc qx wp l') l'
  in
  let sys = WithProof.sort sys in
  let res = all_pivots WPset.empty sys in
  WPset.elements res

let fourier_small = tr_sys "fourier_small" fourier_small

(** [propagate_bounds sys] generate new constraints by exploiting bounds.
    A bound is a constraint of the form c + a.x >= 0
 *)

let rev_concat l =
  let rec conc acc l =
    match l with [] -> acc | l1 :: lr -> conc (List.rev_append l1 acc) lr
  in
  conc [] l

let pre_process sys =
  let sys = normalise sys in
  let bnd1 = bound_monomials sys in
  let sys1 = normalise (subst (List.rev_append sys bnd1)) in
  let pbnd1 = fourier_small sys1 in
  let sys2 = elim_redundant (List.rev_append pbnd1 sys1) in
  let bnd2 = bound_monomials sys2 in
  (* Should iterate ? *)
  let sys =
    rev_concat [bnd2; saturate_by_linear_equalities sys2; sys2]
  in
  sys

let lia (prfdepth : int) sys =
  let env, sys = develop_constraints prfdepth z_spec sys in
  if debug then begin
    Printf.fprintf stdout "Input problem\n";
    List.iter (fun s -> Printf.fprintf stdout "%a\n" WithProof.output s) sys;
    Printf.fprintf stdout "Input problem\n";
    let string_of_op = function Eq -> "=" | Ge -> ">=" | Gt -> ">" in
    List.iter
      (fun wp ->
        let ((p, op), _) = WithProof.repr wp in
        Printf.fprintf stdout "(assert (%s %a))\n" (string_of_op op) Vect.pp_smt
          p)
      sys
  end;
  let sys = pre_process sys in
  xlia env sys

let nlia prfdepth sys =
  let env, sys = develop_constraints prfdepth z_spec sys in
  let is_linear = List.for_all (fun wp -> LinPoly.is_linear @@ WithProof.polynomial wp) sys in
  if debug then begin
    Printf.fprintf stdout "Input problem\n";
    List.iter (fun s -> Printf.fprintf stdout "%a\n" WithProof.output s) sys
  end;
  if is_linear then
    xlia env (pre_process sys)
  else
    (*
      let sys1 = elim_every_substitution sys in
      No: if a wrong equation is chosen, the proof may fail.
      It would only be safe if the variable is linear...
     *)
    let sys1 =
      normalise
        (elim_simple_linear_equality (WithProof.subst_constant true sys))
    in
    let bnd1 = bound_monomials sys1 in
    let sys2 = saturate_by_linear_equalities sys1 in
    let sys3 = nlinear_preprocess (rev_concat [bnd1; sys1; sys2]) in
    xlia env sys3

(* For regression testing, if bench = true generate a Rocq goal *)

let lia  prfdepth sys = gen_bench ("lia", lia)  prfdepth sys
let nlia  prfdepth sys = gen_bench ("nia", nlia)  prfdepth sys

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
