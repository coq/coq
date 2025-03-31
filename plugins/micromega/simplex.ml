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
open Polynomial
open Mutils

type ('a, 'b) sum = Inl of 'a | Inr of 'b

let debug = false

(** Exploiting profiling information *)

let profile_info = ref []
let nb_pivot = ref 0

type profile_info =
  { number_of_successes : int
  ; number_of_failures : int
  ; success_pivots : int
  ; failure_pivots : int
  ; average_pivots : int
  ; maximum_pivots : int }

let init_profile =
  { number_of_successes = 0
  ; number_of_failures = 0
  ; success_pivots = 0
  ; failure_pivots = 0
  ; average_pivots = 0
  ; maximum_pivots = 0 }

let get_profile_info () =
  let update_profile
      { number_of_successes
      ; number_of_failures
      ; success_pivots
      ; failure_pivots
      ; average_pivots
      ; maximum_pivots } (b, i) =
    { number_of_successes = (number_of_successes + if b then 1 else 0)
    ; number_of_failures = (number_of_failures + if b then 0 else 1)
    ; success_pivots = (success_pivots + if b then i else 0)
    ; failure_pivots = (failure_pivots + if b then 0 else i)
    ; average_pivots = average_pivots + 1 (* number of proofs *)
    ; maximum_pivots = max maximum_pivots i }
  in
  let p = List.fold_left update_profile init_profile !profile_info in
  profile_info := [];
  { p with
    average_pivots =
      ( try (p.success_pivots + p.failure_pivots) / p.average_pivots
        with Division_by_zero -> 0 ) }

(* SMT output for debugging *)

(*
let pp_smt_row o (k, v) =
  Printf.fprintf o "(assert (= x%i %a))\n" k Vect.pp_smt v

let pp_smt_assert_tbl o tbl = IMap.iter (fun k v -> pp_smt_row o (k, v)) tbl

let pp_smt_goal_tbl o tbl =
  let pp_rows o tbl =
    IMap.iter (fun k v -> Printf.fprintf o "(= x%i %a)" k Vect.pp_smt v) tbl
  in
  Printf.fprintf o "(assert (not (and %a)))\n" pp_rows tbl

let pp_smt_vars s o var =
  ISet.iter
    (fun i ->
      Printf.fprintf o "(declare-const x%i %s);%a\n" i s LinPoly.pp_var i)
    (ISet.remove 0 var)

let pp_smt_goal s o tbl1 tbl2 =
  let set_of_row vr v = ISet.add vr (Vect.variables v) in
  let var =
    IMap.fold (fun k v acc -> ISet.union (set_of_row k v) acc) tbl1 ISet.empty
  in
  Printf.fprintf o "(echo \"%s\")\n(push) %a  %a %a (check-sat) (pop)\n" s
    (pp_smt_vars "Real") var pp_smt_assert_tbl tbl1 pp_smt_goal_tbl tbl2;
  flush stdout

let pp_smt_cut o lp c =
  let var =
    ISet.remove 0
      (List.fold_left
         (fun acc ((c, o), _) -> ISet.union (Vect.variables c) acc)
         ISet.empty lp)
  in
  let pp_list o l =
    List.iter
      (fun ((c, _), _) -> Printf.fprintf o "(assert (>= %a 0))\n" Vect.pp_smt c)
      l
  in
  Printf.fprintf o
    "(push) \n\
     (echo \"new cut\")\n\
     %a %a (assert (not (>= %a 0)))\n\
     (check-sat) (pop)\n"
    (pp_smt_vars "Int") var pp_list lp Vect.pp_smt c

let pp_smt_sat o lp sol =
  let var =
    ISet.remove 0
      (List.fold_left
         (fun acc ((c, o), _) -> ISet.union (Vect.variables c) acc)
         ISet.empty lp)
  in
  let pp_list o l =
    List.iter
      (fun ((c, _), _) -> Printf.fprintf o "(assert (>= %a 0))\n" Vect.pp_smt c)
      l
  in
  let pp_model o v =
    Vect.fold
      (fun () v x ->
        Printf.fprintf o "(assert (= x%i %a))\n" v Vect.pp_smt (Vect.cst x))
      () v
  in
  Printf.fprintf o
    "(push) \n(echo \"check base\")\n%a %a %a\n(check-sat) (pop)\n"
    (pp_smt_vars "Real") var pp_list lp pp_model sol
 *)

type iset = unit IMap.t

(** Mapping basic variables to their equation.
                                 All variables >= than a threshold rst are restricted.*)
type tableau = InfVect.t IMap.t
type solution = Inf.t IMap.t
type qsolution = Vect.t

module Restricted = struct
  type t =
    { base : int  (** All variables above [base] are restricted *)
    ; exc : int option  (** Except [exc] which is currently optimised *) }

  let pp o {base; exc} =
    Printf.fprintf o ">= %a " LinPoly.pp_var base;
    match exc with
    | None -> Printf.fprintf o "-"
    | Some x -> Printf.fprintf o "-%a" LinPoly.pp_var base

  let is_exception (x : var) (r : t) =
    match r.exc with None -> false | Some x' -> x = x'

  let restrict x rst =
    if is_exception x rst then {base = rst.base; exc = None}
    else failwith (Printf.sprintf "Cannot restrict %i" x)

  let is_restricted x r0 = x >= r0.base && not (is_exception x r0)
  let make x = {base = x; exc = None}
  let set_exc x rst = {base = rst.base; exc = Some x}

  let fold rst f m acc =
    IMap.fold
      (fun k v acc -> if is_exception k rst then acc else f k v acc)
      (IMap.from rst.base m) acc
end

let pp_row o v =
  let (i,v) = InfVect.decomp_cst v in
  Printf.fprintf o "%a + %a"  Inf.pp i LinPoly.pp  v

let output_tableau o (t:tableau) =
  IMap.iter
    (fun k v -> Printf.fprintf o "%a = %a\n" LinPoly.pp_var k pp_row v)
    t

let output_env o t =
  IMap.iter (fun k v -> Printf.fprintf o "%i : %a\n" k WithProof.output v) t

let output_vars o m =
  IMap.iter (fun k _ -> Printf.fprintf o "%a " LinPoly.pp_var k) m

(** A tableau is feasible iff for every basic restricted variable xi,
   we have ci>=0.

   When all the non-basic variables are set to 0, the value of a basic
   variable xi is necessarily ci.  If xi is restricted, it is feasible
   if ci>=0.
 *)

let unfeasible (rst : Restricted.t) (tbl:tableau) =
  Restricted.fold rst
    (fun k v m -> if Inf.ge_0 (InfVect.get_cst v)  then m else IMap.add k () m)
    tbl IMap.empty

let is_feasible rst tb = IMap.is_empty (unfeasible rst tb)

(** Let a1.x1+...+an.xn be a vector of non-basic variables.
    It is maximised if all the xi are restricted
    and the ai are negative.

    If xi>= 0 (restricted)  and ai is negative,
    the maximum for ai.xi is obtained for xi = 0

    Otherwise, it is possible to make ai.xi arbitrarily big:
    - if xi is not restricted, take +/- oo depending on the sign of ai
    - if ai is positive, take +oo
 *)

let is_maximised_vect rst v =
  Vect.for_all
    (fun xi ai ->
      if ai >/ Q.zero then false else Restricted.is_restricted xi rst)
    v

(** [is_maximised rst v]
    @return None if the variable is not maximised
    @return Some v where v is the maximal value
 *)
let is_maximised rst v =
  try
    let vl, v = InfVect.decomp_cst v in
    if is_maximised_vect rst v then Some vl else None
  with Not_found -> None

(** A variable xi is unbounded if for every
    equation xj= ...ai.xi ...
    if ai < 0 then xj is not restricted.
    As a result, even if we
    increase the value of xi, it is always
    possible to adjust the value of xj without
    violating a restriction.
 *)

type result =
  | Max of Inf.t   (** Maximum is reached *)
  | Ubnd of var  (** Problem is unbounded *)
  | Feas  (** Problem is feasible *)

type pivot = Done of result | Pivot of int * int * Inf.t
type simplex = Opt of tableau * result

(** For a row, x = ao.xo+...+ai.xi
    a valid pivot variable is such that it can improve the value of xi.
    it is the case, if xi is unrestricted (increase if ai> 0, decrease if ai < 0)
                    xi is restricted but ai > 0

This is the entering variable.
 *)

let rec find_pivot_column (rst : Restricted.t) (r : Vect.t) =
  match Vect.choose r with
  | None -> failwith "find_pivot_column"
  | Some (xi, ai, r') ->
    if ai </ Q.zero then
      if Restricted.is_restricted xi rst then find_pivot_column rst r'
        (* ai.xi cannot be improved *)
      else (xi, -1) (* r is not restricted, sign of ai does not matter *)
    else (* ai is positive, xi can be increased *)
      (xi, 1)

(** Finding the variable leaving the basis is more subtle because we need to:
    - increase the objective function
    - make sure that the entering variable has a feasible value
    - but also that after pivoting all the other basic variables are still feasible.
    This explains why we choose the pivot with the smallest score
 *)

let min_score s (i1, sc1) =
  match s with
  | None -> Some (i1, sc1)
  | Some (i0, sc0) ->
    if Inf.lt sc0  sc1 then s
    else if Inf.lt sc1  sc0 then Some (i1, sc1)
    else if i0 < i1 then s
    else Some (i1, sc1)

let find_pivot_row rst (tbl:tableau) j sgn =
  Restricted.fold rst
    (fun i' v res ->
      let aij = InfVect.get j v in
      if Q.of_int sgn */ aij </ Q.zero then
        (* This would improve *)
        let score' = Inf.abs (Inf.divc (InfVect.get_cst v)  aij) in
        min_score res (i', score')
      else res)
    tbl None

let safe_find err x (t:tableau) =
  try IMap.find x t
  with Not_found ->
    if debug then
      Printf.fprintf stdout "safe_find %s x%i %a\n" err x output_tableau t;
    failwith err

(** [find_pivot vr t] aims at improving the objective function of the basic variable vr *)
let find_pivot vr (rst : Restricted.t) tbl =
  (* Get the objective of the basic variable vr *)
  let v = safe_find "find_pivot" vr tbl in
  match is_maximised rst v with
  | Some mx -> Done (Max mx) (* Maximum is reached; we are done *)
  | None -> (
    (* Extract the vector *)
    let _, v = InfVect.decomp_cst v in
    let j', sgn = find_pivot_column rst v in
    match find_pivot_row rst (IMap.remove vr tbl) j' sgn with
    | None -> Done (Ubnd j')
    | Some (i', sc) -> Pivot (i', j', sc) )

(** [solve_column c r e]
    @param c  is a non-basic variable
    @param r  is a basic variable
    @param e  is a vector such that r = e
     and e is of the form  ai.c+e'
    @return the vector (-r + e').-1/ai i.e
     c = (r - e')/ai
 *)

let solve_column (c : var) (r : var) (e : InfVect.t) : InfVect.t =
  let a = InfVect.get c e in
  if a =/ Q.zero then failwith "Cannot solve column"
  else
    let a' = Q.minus_one // a in
    InfVect.mul a' (InfVect.set r Q.minus_one (InfVect.set c Q.zero e))

(** [pivot_row r c e]
    @param c is such that c = e
    @param r is a vector r = g.c + r'
    @return g.e+r' *)

let pivot_row (row : InfVect.t) (c : var) (e : InfVect.t) : InfVect.t =
  let g = InfVect.get c row in
  if g =/ Q.zero then row else InfVect.mul_add g e Q.one (InfVect.set c Q.zero row)

let pivot_with (m : tableau) (v : var) (p : InfVect.t) =
  IMap.map (fun (r : InfVect.t) -> pivot_row r v p) m

let pivot (m : tableau) (r : var) (c : var) =
  incr nb_pivot;
  let row = safe_find "pivot" r m in
  let piv = solve_column c r row in
  IMap.add c piv (pivot_with (IMap.remove r m) c piv)

let adapt_unbounded vr x rst (tbl:tableau) =
  if  Inf.ge_0 (InfVect.get_cst (IMap.find vr tbl)) then tbl else pivot tbl vr x

module BaseSet = Set.Make (struct
  type t = iset

  let compare = IMap.compare (fun x y -> 0)
end)

let get_base tbl = IMap.mapi (fun k _ -> ()) tbl

let simplex opt vr rst (tbl:tableau) =
  let b = ref BaseSet.empty in
  let rec simplex opt vr rst (tbl:tableau) =
    ( if debug then
      let base = get_base tbl in
      if BaseSet.mem base !b then Printf.fprintf stdout "Cycling detected\n"
      else b := BaseSet.add base !b );
    if debug && not (is_feasible rst tbl) then begin
      let m = unfeasible rst tbl in
      Printf.fprintf stdout "Simplex error\n";
      Printf.fprintf stdout "The current tableau is not feasible\n";
      Printf.fprintf stdout "Restricted >= %a\n" Restricted.pp rst;
      output_tableau stdout tbl;
      Printf.fprintf stdout "Error for variables %a\n" output_vars m
    end;
    if (not opt) && Inf.ge_0 (InfVect.get_cst (IMap.find vr tbl)) then
      Opt (tbl, Feas)
    else
      match find_pivot vr rst tbl with
      | Done r -> (
        match r with
        | Max _ -> Opt (tbl, r)
        | Ubnd x ->
          let t' = adapt_unbounded vr x rst tbl in
          Opt (t', r)
        | Feas -> raise (Invalid_argument "find_pivot") )
      | Pivot (i, j, s) ->
        if debug then begin
          Printf.fprintf stdout "Find pivot for x%i(%a)\n" vr Inf.pp s;
          Printf.fprintf stdout "Leaving variable x%i\n" i;
          Printf.fprintf stdout "Entering variable x%i\n" j
        end;
        let m' = pivot tbl i j in
        simplex opt vr rst m'
  in
  simplex opt vr rst tbl

type certificate = Unsat of Vect.t | Sat of tableau * var option

(** [normalise_row t v]
    @return a row obtained by pivoting the basic variables of the vector v
 *)

let normalise_row (t : tableau) (v : InfVect.t) =
  let (i,v) = InfVect.decomp_cst v in
  Vect.fold
    (fun acc vr ai ->
      try
        let e = IMap.find vr t in
        InfVect.add (InfVect.mul ai e) acc
      with Not_found -> InfVect.add (InfVect.set vr ai InfVect.null) acc)
    (InfVect.of_cst i) v


let normalise_row (t : tableau) (v : InfVect.t) =
  let v' = normalise_row t v in
  if debug then Printf.fprintf stdout "Normalised Optimising %a\n" pp_row v';
  v'

let add_row (nw : var) (t : tableau) (v : InfVect.t) : tableau =
  IMap.add nw (normalise_row t v) t

(** [push_real] performs reasoning over the rationals *)
let push_real (opt : bool) (nw : var) (v : InfVect.t) (rst : Restricted.t)
    (t : tableau) : certificate =
  if debug then begin
    Printf.fprintf stdout "Current Tableau\n%a\n" output_tableau t;
    Printf.fprintf stdout "Optimising %a=%a\n" LinPoly.pp_var nw pp_row v
  end;
  match simplex opt nw rst (add_row nw t v) with
  | Opt (t', r) -> (
    (* Look at the optimal *)
    match r with
    | Ubnd x ->
      if debug then
        Printf.printf "The objective is unbounded (variable %a)\n"
          LinPoly.pp_var x;
      Sat (t', Some x) (* This is sat and we can extract a value *)
    | Feas -> Sat (t', None)
    | Max n ->
      if debug then begin
        Printf.printf "The objective is maximised %a\n" Inf.pp n;
        Printf.printf "%a = %a\n" LinPoly.pp_var nw pp_row (IMap.find nw t')
      end;
      if Inf.ge_0 n then Sat (t', None)
      else
        let v' = safe_find "push_real" nw t' in
        let v' = snd (InfVect.decomp_cst v') in
        Unsat (Vect.set nw Q.one (Vect.set 0 Q.zero (Vect.mul Q.minus_one v')))
    )

(** One complication is that equalities needs some pre-processing.
 *)
open Mutils

open Polynomial

(*type varmap = (int * bool) IMap.t*)

let find_solution rst (tbl:tableau) : solution =
  IMap.filter_map
              (fun vr v ->
                if Restricted.is_restricted vr rst then None
                else Some (InfVect.get_cst v))
              tbl

(* let find_full_solution rst (tbl:tableau) =
   IMap.map (fun  v -> InfVect.get_cst v) tbl *)

let find_q_solution rst (tbl:tableau) =
  IMap.fold (fun vr v res ->
      let c = fst (Inf.decomp (InfVect.get_cst v)) in
      Vect.set vr c res) tbl Vect.null



let eval_solution sol v =
  let (c,v) = InfVect.decomp_cst v in
  Vect.fold (fun acc k c ->
      try
        Inf.add acc (Inf.mulc c (IMap.find k sol))
      with  Not_found -> acc) c v

let choose_conflict (sol : solution) (l : (var * InfVect.t) list) =
  let rec most_violating l e (x, v) rst =
    match l with
    | [] -> Some ((x, v), rst)
    | (x', v') :: l ->
      let e' = eval_solution sol v' in
      if Inf.lt e' e then most_violating l e' (x', v') ((x, v) :: rst)
      else most_violating l e (x, v) ((x', v') :: rst)
  in
  match l with
  | [] -> None
  | (x, v) :: l ->
    let e = eval_solution sol v in
    most_violating l e (x, v) []

let rec solve opt (l:(var * InfVect.t) list) (rst : Restricted.t) (t : tableau) =
  let sol = find_solution rst t in
  match choose_conflict sol l with
  | None -> Inl (rst, t, None)
  | Some ((vr, v), l) -> (
    match push_real opt vr v (Restricted.set_exc vr rst) t with
    | Sat (t', x) -> (
      match l with [] -> Inl (rst, t', x) | _ -> solve opt l rst t' )
    | Unsat c -> Inr c )

let fresh_var l =
  1
  +
  try
    ISet.max_elt
      (List.fold_left
         (fun acc c -> ISet.union acc (Vect.variables c.coeffs))
         ISet.empty l)
  with Not_found -> 0

module PrfEnv = struct
  type t = WithProof.t IMap.t

  let empty = IMap.empty

  let register prf env =
    let fr = LinPoly.MonT.get_fresh () in
    (fr, IMap.add fr prf env)

  (* let register_def (v, op) {fresh; env} =
     LinPoly.MonT.reserve fresh;
     (fresh, {fresh = fresh + 1; env = IMap.add fresh ((v, op), Def fresh) env}) *)

  let set_prf i prf env = IMap.add i prf env
  let find idx env = IMap.find idx env

  let rec of_list acc env l =
    match l with
    | [] -> (acc, env)
    | wp :: l -> (
      let ((lp, op), prf) = WithProof.repr wp in
      match op with
      | Gt ->
         let f, env' = register wp env in
         of_list ((f, InfVect.of_vect lp true) :: acc) env' l
      | Ge ->
        (* Simply register *)
        let f, env' = register wp env in
        of_list ((f, InfVect.of_vect lp false) :: acc) env' l
      | Eq ->
        (* Generate two constraints *)
        let f1, env = register wp env in
        let wp' = WithProof.neg wp in
        let f2, env = register wp' env in
        let (lp', _), _ = WithProof.repr wp' in
        of_list ((f1, InfVect.of_vect lp false) :: (f2, InfVect.of_vect lp' false) :: acc) env l )

  let map f env = IMap.map f env
end

let make_env (l : Polynomial.cstr list) =
  PrfEnv.of_list [] PrfEnv.empty
    (List.rev_map WithProof.of_cstr
       (List.mapi (fun i x -> (x, ProofFormat.Hyp i)) l))

(** [make_certificate env l] makes very strong assumptions
    about the form of the environment.
    Each proof is assumed to be either:
    - an hypothesis Hyp i
    - or, the negation of an hypothesis (MulC(-1,Hyp i))
 *)

let make_certificate env l =
  Vect.normalise
    (Vect.fold
       (fun acc x n ->
         let wp = PrfEnv.find x env in
         ProofFormat.(
           match WithProof.proof wp with
           | Hyp i -> Vect.set i n acc
           | MulC (_, Hyp i) -> Vect.set i (Q.neg n) acc
           | _ -> failwith "make_certificate: invalid proof"))
       Vect.null l)

let find_unsat_certificate (l : Polynomial.cstr list) =
  let l', env = make_env l in
  let vr = fresh_var l in
  match solve false l' (Restricted.make vr) IMap.empty with
  | Inr c -> Some (make_certificate env c)
  | Inl _ -> None

open Polynomial
open ProofFormat

let make_farkas_certificate (env : PrfEnv.t) v =
  let fold acc x n =
    let wp = PrfEnv.find x env in
    add_proof acc (mul_cst_proof n (WithProof.proof wp))
  in
  Vect.fold fold Zero v

let make_farkas_proof (env : PrfEnv.t) v =
  Vect.fold
    (fun wp x n ->
      WithProof.addition wp (WithProof.mul_cst n (PrfEnv.find x env)))
    WithProof.zero v

let frac_num n = n -/ Q.floor n

type ('a, 'b) hitkind =
  | Forget
  (* Not interesting *)
  | Hit of 'a
  (* Yes, we have a positive result *)
  | Keep of 'b

let violation sol vect =
  let sol = Vect.set 0 Q.one sol in
  let c = Vect.get 0 vect in
  if Q.zero =/ c then Vect.dotproduct sol vect
  else Q.abs (Vect.dotproduct sol vect // c)

let cut isZ env rmin sol (rst : Restricted.t) (tbl:tableau) (x, v) =
  let n, r = InfVect.decomp_cst v in
  let (n,_)    = Inf.decomp n in (* Ignore epsilon part - for now *)
  let fn = frac_num (Q.abs n) in
  if fn =/ Q.zero then Forget (* The solution is integral *)
  else
    (* The cut construction is from:
       Letchford and Lodi. Strengthening Chvatal-Gomory cuts and Gomory fractional cuts.

       We implement the classic Proposition 2 from the "known results"
    *)

    (* Proposition 3 requires all the variables to be restricted and is
       therefore not always applicable. *)
    (* let ccoeff_prop1 v = frac_num v in
       let ccoeff_prop3 v =
         (* mixed integer cut *)
         let fv = frac_num v in
         Num.min_num fv (fn */ (Q.one -/ fv) // (Q.one -/ fn))
       in
       let ccoeff_prop3 =
         if Restricted.is_restricted x rst then ("Prop3", ccoeff_prop3)
         else ("Prop1", ccoeff_prop1)
       in *)
    let n0_5 = Q.one // Q.two in
    (* If the fractional part [fn] is small, we construct the t-cut.
       If the fractional part [fn] is big, we construct the t-cut of the negated row.
       (This is only a cut if all the fractional variables are restricted.)
    *)
    let ccoeff_prop2 =
      let tmin =
        if fn </ n0_5 then (* t-cut *)
          Q.ceiling (n0_5 // fn)
        else
          (* multiply by -1 & t-cut *)
          Q.neg (Q.ceiling (n0_5 // (Q.one -/ fn)))
      in
      ("Prop2", fun v -> frac_num (v */ tmin))
    in
    let ccoeff = ccoeff_prop2 in
    let cut_vector ccoeff =
      Vect.fold
        (fun acc x n ->
          if Restricted.is_restricted x rst then Vect.set x (ccoeff n) acc
          else acc)
        Vect.null r
    in
    let lcut =
      ( fst ccoeff
      , make_farkas_proof env (Vect.normalise (cut_vector (snd ccoeff))) )
    in
    let check_cutting_plane (p, c) =
      match WithProof.cutting_plane_isz isZ c with
      | None ->
        if debug then
          Printf.printf "%s: This is not a cutting plane for %a\n%a:" p
            LinPoly.pp_var x WithProof.output c;
        None
      | Some wp ->
        if debug then (
          Printf.printf "%s: This is a cutting plane for %a:" p LinPoly.pp_var x;
          Printf.printf "(viol %f) %a\n"
            (Q.to_float (violation sol (WithProof.polynomial wp)))
            WithProof.output wp);
        Some (x, wp)
    in
    match check_cutting_plane lcut with
    | Some r -> Hit r
    | None ->
      let has_unrestricted =
        Vect.fold
          (fun acc v vl -> acc || not (Restricted.is_restricted v rst))
          false r
      in
      if has_unrestricted then Keep (x, v) else Forget

let merge_result_old oldr f x =
  match oldr with
  | Hit v -> Hit v
  | Forget -> (
    match f x with Forget -> Forget | Hit v -> Hit v | Keep v -> Keep v )
  | Keep v -> (
    match f x with Forget -> Keep v | Keep v' -> Keep v | Hit v -> Hit v )

let merge_best lt oldr newr =
  match (oldr, newr) with
  | x, Forget -> x
  | Hit v, Hit v' -> if lt v v' then Hit v else Hit v'
  | _, Hit v | Hit v, _ -> Hit v
  | Forget, Keep v -> Keep v
  | Keep v, Keep v' -> Keep v'

(*let size_vect v =
  let abs z = if Z.compare z Z.zero < 0 then Z.neg z else z in
  Vect.fold
    (fun acc _ q -> Z.add (abs (Q.num q)) (Z.add (Q.den q) acc))
    Z.zero v
 *)

let find_cut isZ nb env u (sol:qsolution)  rst (tbl:tableau) =
  if nb = 0 then
    IMap.fold
      (fun x v acc -> merge_result_old acc (cut isZ env u sol rst tbl) (x, v))
      tbl Forget
  else
    let lt (_, wp1) (_, wp2) =
      (*violation sol v1 >/ violation sol v2*)
      ProofFormat.pr_size (WithProof.proof wp1) </ ProofFormat.pr_size  (WithProof.proof wp2)
    in
    IMap.fold
      (fun x v acc -> merge_best lt acc (cut isZ env u sol rst tbl (x, v)))
      tbl Forget



let find_split isZ env tbl rst =
  let is_split x v =
    (* Maybe we can cut over a restricted variable. TODO
     *)
    if Restricted.is_restricted x rst then None
    else
      let n , _ = InfVect.decomp_cst v in
      match Inf.frac_num n with
      | None -> None
      | Some fn ->
         let fn = Q.abs fn in
         let score = Q.min fn (Q.one -/ fn) in
         let vect = Vect.set x Q.one (Vect.cst (fst (Inf.decomp n))) in
         if LinPoly.is_integer isZ vect then
           Some (Vect.normalise vect, score)
         else None
  in
  IMap.fold
    (fun x v acc ->
      match is_split x v with
      | None -> acc
      | Some (v, s) -> (
        match acc with
        | None -> Some (v, s)
        | Some (v', s') -> if s' >/ s then acc else Some (v, s) ))
    tbl None

let var_of_vect v = fst (fst (Vect.decomp_fst v))

let eliminate_variable (bounded, env, (tbl:tableau)) x =
  if debug then
    Printf.printf "Eliminating variable %a from tableau\n%a\n" LinPoly.pp_var x
      output_tableau tbl;
  (* We identify the new variables with the constraint. *)
  let vr = LinPoly.MonT.get_fresh () in
  let vr1 = LinPoly.MonT.get_fresh () in
  let vr2 = LinPoly.MonT.get_fresh () in
  let z = LinPoly.var vr1 in
  let zv = var_of_vect z in
  let t = LinPoly.var vr2 in
  let tv = var_of_vect t in
  (* x = z - t *)
  let xdef = Vect.add z (Vect.uminus t) in
  let xp = WithProof.def (Vect.set x Q.one (Vect.uminus xdef)) Eq vr in
  let zp = WithProof.def z Ge zv in
  let tp = WithProof.def t Ge tv in
  (* Pivot the current tableau using xdef *)
  let tbl = IMap.map (fun v -> InfVect.subst x (InfVect.of_vect xdef false) v) tbl in
  (* Pivot the proof environment *)
  let env =
    PrfEnv.map
      (fun lp ->
        let ai = Vect.get x (WithProof.polynomial lp) in
        if ai =/ Q.zero then lp
        else WithProof.addition (WithProof.mul_cst (Q.neg ai) xp) lp)
      env
  in
  (* Add the variables to the environment *)
  let env =
    PrfEnv.set_prf vr xp (PrfEnv.set_prf zv zp (PrfEnv.set_prf tv tp env))
  in
  (* Remember the mapping *)
  let bounded = IMap.add x (vr, zv, tv) bounded in
  if debug then (
    Printf.printf "Tableau without\n %a\n" output_tableau tbl;
    Printf.printf "Environment\n %a\n" output_env env );
  (bounded, env, tbl)

let integer_solver isZ lp =
  let insert_row vr v rst tbl =
    match push_real true vr v rst tbl with
    | Sat (t', x) ->
      (*pp_smt_goal stdout tbl vr v t';*)
      Inl (Restricted.restrict vr rst, t', x)
    | Unsat c -> Inr c
  in
  let vr0 = LinPoly.MonT.get_fresh () in
  (* Initialise the proof environment mapping variables of the simplex to their proof. *)
  let l', env =
    PrfEnv.of_list [] PrfEnv.empty (List.rev lp)
  in
  let nb = ref 0 in
  let rec isolve env cr res =
    incr nb;
    match res with
    | Inr c ->
      Some
        (Step
           ( LinPoly.MonT.get_fresh ()
           , make_farkas_certificate env (Vect.normalise c)
           , Done ))
    | Inl (rst, tbl, x) -> (
      if debug then begin
        Printf.fprintf stdout "Looking for a cut\n";
        Printf.fprintf stdout "Restricted %a ...\n" Restricted.pp rst;
        Printf.fprintf stdout "Current Tableau\n%a\n" output_tableau tbl;
        flush stdout
      end;
      if !nb mod 3 = 0 then
        match find_split isZ env tbl rst with
        | None ->
          None (* There is no hope, there should be an integer solution *)
        | Some (v, s) -> (
          let vr = LinPoly.MonT.get_fresh () in
          let wp1 = WithProof.def v Ge vr in
          let wp2 = WithProof.def (Vect.mul Q.minus_one v) Ge vr in
          match (WithProof.cutting_plane wp1, WithProof.cutting_plane wp2) with
          | None, _ | _, None ->
            failwith "Error: splitting over an integer variable"
          | Some wp1, Some wp2 -> (
            if debug then
              Printf.fprintf stdout "Splitting over (%s) %a:%a or %a \n"
                (Q.to_string s) LinPoly.pp_var vr WithProof.output wp1
                WithProof.output wp2;
            let v1', v2' = (WithProof.polynomial wp1, WithProof.polynomial wp2) in
            if debug then
              Printf.fprintf stdout "Solving with %a\n" LinPoly.pp v1';
            let res1 = insert_row vr (InfVect.of_vect v1' false) (Restricted.set_exc vr rst) tbl in
            let prf1 = isolve (IMap.add vr (WithProof.def v1' Ge vr) env) cr res1 in
            match prf1 with
            | None -> None
            | Some prf1 ->
              let prf', hyps = ProofFormat.simplify_proof prf1 in
              if not (ISet.mem vr hyps) then Some prf'
              else (
                if debug then
                  Printf.fprintf stdout "Solving with %a\n" Vect.pp v2';
                let res2 = insert_row vr (InfVect.of_vect v2' false) (Restricted.set_exc vr rst) tbl in
                let prf2 =
                  isolve (IMap.add vr (WithProof.def v2' Ge vr) env) cr res2
                in
                match prf2 with
                | None -> None
                | Some prf2 -> Some (Split (vr, v, prf1, prf2)) ) ) )
      else
        let sol = find_q_solution rst tbl in
        match find_cut isZ (!nb mod 2) env cr (*x*) sol rst tbl with
        | Forget ->
          None (* There is no hope, there should be an integer solution *)
        | Hit (cr, wp) -> (
          let (v, op), cut = WithProof.repr wp in
          let vr = LinPoly.MonT.get_fresh () in
          if op = Eq then
            begin (* This is a contradiction *)
            if debug then
              Printf.fprintf stdout "Found a contradiction\n %a\n" WithProof.output wp;
            Some (Step (vr, CutPrf cut, Done))
            end
          else begin
            if debug then Printf.fprintf stdout "Found a cut\n %a\n" WithProof.output wp;
            let res = insert_row vr (InfVect.of_vect v false) (Restricted.set_exc vr rst) tbl in
            let prf =
              isolve (IMap.add vr (WithProof.def v op vr) env) (Some cr) res
            in
            match prf with
            | None -> None
            | Some p -> Some (Step (vr, CutPrf cut, p)) end)
        | Keep (x, v) -> (
          if debug then
            Printf.fprintf stdout "Remove %a from Tableau\n" LinPoly.pp_var x;
          let bounded, env, tbl =
            Vect.fold
              (fun acc x n ->
                if x <> 0 && not (Restricted.is_restricted x rst) then
                  eliminate_variable acc x
                else acc)
              (IMap.empty, env, tbl) (snd (InfVect.decomp_cst v))
          in
          let prf = isolve env cr (Inl (rst, tbl, None)) in
          match prf with
          | None -> None
          | Some pf ->
            Some
              (IMap.fold
                 (fun x (vr, zv, tv) acc ->
                   ExProof (vr, zv, tv, x, zv, tv, acc))
                 bounded pf) ) )
  in
  let res = solve true l' (Restricted.make vr0) IMap.empty in
  isolve env None res

let integer_solver isZ lp =
  nb_pivot := 0;
  if debug then
    Printf.printf "Input integer solver\n%a\n" WithProof.output_sys lp;
  match integer_solver isZ lp with
  | None ->
    profile_info := (false, !nb_pivot) :: !profile_info;
    None
  | Some prf ->
    profile_info := (true, !nb_pivot) :: !profile_info;
    if debug then
      Printf.fprintf stdout "Proof %a\n" ProofFormat.output_proof prf;
    Some prf
