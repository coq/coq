(* ========================================================================= *)
(* - This code originates from John Harrison's HOL LIGHT 2.30                *)
(*   (see file LICENSE.sos for license, copyright and disclaimer)            *)
(* - Laurent Théry (thery@sophia.inria.fr) has isolated the HOL              *)
(*   independent bits                                                        *)
(* - Frédéric Besson (fbesson@irisa.fr) is using it to feed  micromega       *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Nonlinear universal reals procedure using SOS decomposition.              *)
(* ========================================================================= *)
open Num;;
open Sos_types;;
open Sos_lib;;

(*
prioritize_real();;
*)

let debugging = ref false;;

exception Sanity;;

(* ------------------------------------------------------------------------- *)
(* Turn a rational into a decimal string with d sig digits.                  *)
(* ------------------------------------------------------------------------- *)

let decimalize =
  let rec normalize y =
    if abs_num y </ Int 1 // Int 10 then normalize (Int 10 */ y) - 1
    else if abs_num y >=/ Int 1 then normalize (y // Int 10) + 1
    else 0 in
  fun d x ->
    if x =/ Int 0 then "0.0" else
    let y = abs_num x in
    let e = normalize y in
    let z = pow10(-e) */ y +/ Int 1 in
    let k = round_num(pow10 d */ z) in
    (if x </ Int 0 then "-0." else "0.") ^
    implode(List.tl(explode(string_of_num k))) ^
    (if e = 0 then "" else "e"^string_of_int e);;

(* ------------------------------------------------------------------------- *)
(* Iterations over numbers, and lists indexed by numbers.                    *)
(* ------------------------------------------------------------------------- *)

let rec itern k l f a =
  match l with
    [] -> a
  | h::t -> itern (k + 1) t f (f h k a);;

let rec iter (m,n) f a =
  if n < m then a
  else iter (m+1,n) f (f m a);;

(* ------------------------------------------------------------------------- *)
(* The main types.                                                           *)
(* ------------------------------------------------------------------------- *)

type vector = int*(int,num)func;;

type matrix = (int*int)*(int*int,num)func;;

type monomial = (vname,int)func;;

type poly = (monomial,num)func;;

(* ------------------------------------------------------------------------- *)
(* Assignment avoiding zeros.                                                *)
(* ------------------------------------------------------------------------- *)

let (|-->) x y a = if y =/ Int 0 then a else (x |-> y) a;;

(* ------------------------------------------------------------------------- *)
(* This can be generic.                                                      *)
(* ------------------------------------------------------------------------- *)

let element (d,v) i = tryapplyd v i (Int 0);;

let mapa f (d,v) =
  d,foldl (fun a i c -> (i |--> f(c)) a) undefined v;;

let is_zero (d,v) =
  match v with
    Empty -> true
  | _ -> false;;

(* ------------------------------------------------------------------------- *)
(* Vectors. Conventionally indexed 1..n.                                     *)
(* ------------------------------------------------------------------------- *)

let vector_0 n = (n,undefined:vector);;

let dim (v:vector) = fst v;;

let vector_const c n =
  if c =/ Int 0 then vector_0 n
  else (n,List.fold_right (fun k -> k |-> c) (1--n) undefined :vector);;

let vector_cmul c (v:vector) =
  let n = dim v in
  if c =/ Int 0 then vector_0 n
  else n,mapf (fun x -> c */ x) (snd v)

let vector_of_list l =
  let n = List.length l in
  (n,List.fold_right2 (|->) (1--n) l undefined :vector);;

(* ------------------------------------------------------------------------- *)
(* Matrices; again rows and columns indexed from 1.                          *)
(* ------------------------------------------------------------------------- *)

let matrix_0 (m,n) = ((m,n),undefined:matrix);;

let dimensions (m:matrix) = fst m;;

let matrix_cmul c (m:matrix) =
  let (i,j) = dimensions m in
  if c =/ Int 0 then matrix_0 (i,j)
  else (i,j),mapf (fun x -> c */ x) (snd m);;

let matrix_neg (m:matrix) = (dimensions m,mapf minus_num (snd m) :matrix);;

let matrix_add (m1:matrix) (m2:matrix) =
  let d1 = dimensions m1 and d2 = dimensions m2 in
  if d1 <> d2 then failwith "matrix_add: incompatible dimensions"
  else (d1,combine (+/) (fun x -> x =/ Int 0) (snd m1) (snd m2) :matrix);;

let row k (m:matrix) =
  let i,j = dimensions m in
  (j,
   foldl (fun a (i,j) c -> if i = k then (j |-> c) a else a) undefined (snd m)
   : vector);;

let column k (m:matrix) =
  let i,j = dimensions m in
  (i,
   foldl (fun a (i,j) c -> if j = k then (i |-> c) a else a) undefined (snd m)
   : vector);;

let diagonal (v:vector) =
  let n = dim v in
  ((n,n),foldl (fun a i c -> ((i,i) |-> c) a) undefined (snd v) : matrix);;

(* ------------------------------------------------------------------------- *)
(* Monomials.                                                                *)
(* ------------------------------------------------------------------------- *)

let monomial_eval assig (m:monomial) =
  foldl (fun a x k -> a */ power_num (apply assig x) (Int k))
        (Int 1) m;;

let monomial_1 = (undefined:monomial);;

let monomial_var x = (x |=> 1 :monomial);;

let (monomial_mul:monomial->monomial->monomial) =
  combine (+) (fun x -> false);;

let monomial_degree x (m:monomial) = tryapplyd m x 0;;

let monomial_multidegree (m:monomial) = foldl (fun a x k -> k + a) 0 m;;

let monomial_variables m = dom m;;

(* ------------------------------------------------------------------------- *)
(* Polynomials.                                                              *)
(* ------------------------------------------------------------------------- *)

let eval assig (p:poly) =
  foldl (fun a m c -> a +/ c */ monomial_eval assig m) (Int 0) p;;

let poly_0 = (undefined:poly);;

let poly_isconst (p:poly) = foldl (fun a m c -> m = monomial_1 && a) true p;;

let poly_var x = ((monomial_var x) |=> Int 1 :poly);;

let poly_const c =
  if c =/ Int 0 then poly_0 else (monomial_1 |=> c);;

let poly_cmul c (p:poly) =
  if c =/ Int 0 then poly_0
  else mapf (fun x -> c */ x) p;;

let poly_neg (p:poly) = (mapf minus_num p :poly);;

let poly_add (p1:poly) (p2:poly) =
  (combine (+/) (fun x -> x =/ Int 0) p1 p2 :poly);;

let poly_sub p1 p2 = poly_add p1 (poly_neg p2);;

let poly_cmmul (c,m) (p:poly) =
  if c =/ Int 0 then poly_0
  else if m = monomial_1 then mapf (fun d -> c */ d) p
  else foldl (fun a m' d -> (monomial_mul m m' |-> c */ d) a) poly_0 p;;

let poly_mul (p1:poly) (p2:poly) =
  foldl (fun a m c -> poly_add (poly_cmmul (c,m) p2) a) poly_0 p1;;

let poly_square p = poly_mul p p;;

let rec poly_pow p k =
  if k = 0 then poly_const (Int 1)
  else if k = 1 then p
  else let q = poly_square(poly_pow p (k / 2)) in
       if k mod 2 = 1 then poly_mul p q else q;;

let degree x (p:poly) = foldl (fun a m c -> max (monomial_degree x m) a) 0 p;;

let multidegree (p:poly) =
  foldl (fun a m c -> max (monomial_multidegree m) a) 0 p;;

let poly_variables (p:poly) =
  foldr (fun m c -> union (monomial_variables m)) p [];;

(* ------------------------------------------------------------------------- *)
(* Order monomials for human presentation.                                   *)
(* ------------------------------------------------------------------------- *)

let humanorder_varpow (x1,k1) (x2,k2) = x1 < x2 || x1 = x2 && k1 > k2;;

let humanorder_monomial =
  let rec ord l1 l2 = match (l1,l2) with
    _,[] -> true
  | [],_ -> false
  | h1::t1,h2::t2 -> humanorder_varpow h1 h2 || h1 = h2 && ord t1 t2 in
  fun m1 m2 -> m1 = m2 ||
               ord (sort humanorder_varpow (graph m1))
                   (sort humanorder_varpow (graph m2));;

(* ------------------------------------------------------------------------- *)
(* Conversions to strings.                                                   *)
(* ------------------------------------------------------------------------- *)

let string_of_vname (v:vname): string = (v: string);;

let string_of_varpow x k =
  if k = 1 then string_of_vname x else string_of_vname x^"^"^string_of_int k;;

let string_of_monomial m =
  if m = monomial_1 then "1" else
  let vps = List.fold_right (fun (x,k) a -> string_of_varpow x k :: a)
                            (sort humanorder_varpow (graph m)) [] in
  String.concat "*" vps;;

let string_of_cmonomial (c,m) =
  if m = monomial_1 then string_of_num c
  else if c =/ Int 1 then string_of_monomial m
  else string_of_num c ^ "*" ^ string_of_monomial m;;

let string_of_poly (p:poly) =
  if p = poly_0 then "<<0>>" else
  let cms = sort (fun (m1,_) (m2,_) -> humanorder_monomial m1 m2) (graph p) in
  let s =
    List.fold_left (fun a (m,c) ->
             if c </ Int 0 then a ^ " - " ^ string_of_cmonomial(minus_num c,m)
             else a ^ " + " ^ string_of_cmonomial(c,m))
          "" cms in
  let s1 = String.sub s 0 3
  and s2 = String.sub s 3 (String.length s - 3) in
  "<<" ^(if s1 = " + " then s2 else "-"^s2)^">>";;

(* ------------------------------------------------------------------------- *)
(* Printers.                                                                 *)
(* ------------------------------------------------------------------------- *)

(*
let print_vector v = Format.print_string(string_of_vector 0 20 v);;

let print_matrix m = Format.print_string(string_of_matrix 20 m);;

let print_monomial m = Format.print_string(string_of_monomial m);;

let print_poly m = Format.print_string(string_of_poly m);;

#install_printer print_vector;;
#install_printer print_matrix;;
#install_printer print_monomial;;
#install_printer print_poly;;
*)

(* ------------------------------------------------------------------------- *)
(* Conversion from  term.                                                 *)
(* ------------------------------------------------------------------------- *)

let rec poly_of_term t = match t with
  Zero -> poly_0
| Const n -> poly_const n
| Var x -> poly_var x
| Opp t1 -> poly_neg (poly_of_term t1)
| Inv t1 ->
      let p = poly_of_term t1 in
      if poly_isconst p then poly_const(Int 1 // eval undefined p)
      else failwith "poly_of_term: inverse of non-constant polyomial"
| Add (l, r) -> poly_add (poly_of_term l) (poly_of_term r)
| Sub (l, r) -> poly_sub (poly_of_term l) (poly_of_term r)
| Mul (l, r) -> poly_mul (poly_of_term l) (poly_of_term r)
| Div (l, r) ->
      let p = poly_of_term l and q = poly_of_term r in
      if poly_isconst q then poly_cmul (Int 1 // eval undefined q) p
      else failwith "poly_of_term: division by non-constant polynomial"
| Pow (t, n) ->
      poly_pow (poly_of_term t) n;;

(* ------------------------------------------------------------------------- *)
(* String of vector (just a list of space-separated numbers).                *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_vector (v:vector) =
  let n = dim v in
  let strs = List.map (o (decimalize 20)  (element v)) (1--n) in
  String.concat " " strs ^ "\n";;

(* ------------------------------------------------------------------------- *)
(* String for a matrix numbered k, in SDPA sparse format.                    *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_matrix k (m:matrix) =
  let pfx = string_of_int k ^ " 1 " in
  let ms = foldr (fun (i,j) c a -> if i > j then a else ((i,j),c)::a)
                 (snd m) [] in
  let mss = sort (increasing fst) ms in
  List.fold_right (fun ((i,j),c) a ->
     pfx ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) mss "";;

(* ------------------------------------------------------------------------- *)
(* String in SDPA sparse format for standard SDP problem:                    *)
(*                                                                           *)
(*    X = v_1 * [M_1] + ... + v_m * [M_m] - [M_0] must be PSD                *)
(*    Minimize obj_1 * v_1 + ... obj_m * v_m                                 *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_problem comment obj mats =
  let m = List.length mats - 1
  and n,_ = dimensions (List.hd mats) in
  "\"" ^ comment ^ "\"\n" ^
  string_of_int m ^ "\n" ^
  "1\n" ^
  string_of_int n ^ "\n" ^
  sdpa_of_vector obj ^
  List.fold_right2 (fun k m a -> sdpa_of_matrix (k - 1) m ^ a)
          (1--List.length mats) mats "";;

(* ------------------------------------------------------------------------- *)
(* More parser basics.                                                       *)
(* ------------------------------------------------------------------------- *)

let word s =
   end_itlist (fun p1 p2 -> (p1 ++ p2) >> (fun (s,t) -> s^t))
              (List.map a (explode s));;
let token s =
  many (some isspace) ++ word s ++ many (some isspace)
  >> (fun ((_,t),_) -> t);;

let decimal =
  let (||) = parser_or in
  let numeral = some isnum in
  let decimalint = atleast 1 numeral >> ((o) Num.num_of_string  implode) in
  let decimalfrac = atleast 1 numeral
    >> (fun s -> Num.num_of_string(implode s) // pow10 (List.length s)) in
  let decimalsig =
    decimalint ++ possibly (a "." ++ decimalfrac >> snd)
    >> (function (h,[x]) -> h +/ x | (h,_) -> h) in
  let signed prs =
       a "-" ++ prs >> ((o) minus_num snd)
    || a "+" ++ prs >> snd
    || prs in
  let exponent = (a "e" || a "E") ++ signed decimalint >> snd in
    signed decimalsig ++ possibly exponent
    >> (function (h,[x]) -> h */ power_num (Int 10) x | (h,_) -> h);;

let mkparser p s =
  let x,rst = p(explode s) in
  if rst = [] then x else failwith "mkparser: unparsed input";;

(* ------------------------------------------------------------------------- *)
(* Parse back a vector.                                                      *)
(* ------------------------------------------------------------------------- *)

let _parse_sdpaoutput, parse_csdpoutput =
  let (||) = parser_or in
  let vector =
    token "{" ++ listof decimal (token ",") "decimal" ++ token "}"
               >> (fun ((_,v),_) -> vector_of_list v) in
  let rec skipupto dscr prs inp =
      (dscr ++ prs >> snd
    || some (fun c -> true) ++ skipupto dscr prs >> snd) inp in
  let ignore inp = (),[] in
  let sdpaoutput =
    skipupto (word "xVec" ++ token "=")
             (vector ++ ignore >> fst) in
  let csdpoutput =
    (decimal ++ many(a " " ++ decimal >> snd) >> (fun (h,t) -> h::t)) ++
    (a " " ++ a "\n" ++ ignore) >> ((o) vector_of_list fst) in
  mkparser sdpaoutput,mkparser csdpoutput;;

(* ------------------------------------------------------------------------- *)
(* The default parameters. Unfortunately this goes to a fixed file.          *)
(* ------------------------------------------------------------------------- *)

let _sdpa_default_parameters =
"100     unsigned int maxIteration;\
\n1.0E-7  double 0.0 < epsilonStar;\
\n1.0E2   double 0.0 < lambdaStar;\
\n2.0     double 1.0 < omegaStar;\
\n-1.0E5  double lowerBound;\
\n1.0E5   double upperBound;\
\n0.1     double 0.0 <= betaStar <  1.0;\
\n0.2     double 0.0 <= betaBar  <  1.0, betaStar <= betaBar;\
\n0.9     double 0.0 < gammaStar  <  1.0;\
\n1.0E-7  double 0.0 < epsilonDash;\
\n";;

(* ------------------------------------------------------------------------- *)
(* These were suggested by Makoto Yamashita for problems where we are        *)
(* right at the edge of the semidefinite cone, as sometimes happens.         *)
(* ------------------------------------------------------------------------- *)

let sdpa_alt_parameters =
"1000    unsigned int maxIteration;\
\n1.0E-7  double 0.0 < epsilonStar;\
\n1.0E4   double 0.0 < lambdaStar;\
\n2.0     double 1.0 < omegaStar;\
\n-1.0E5  double lowerBound;\
\n1.0E5   double upperBound;\
\n0.1     double 0.0 <= betaStar <  1.0;\
\n0.2     double 0.0 <= betaBar  <  1.0, betaStar <= betaBar;\
\n0.9     double 0.0 < gammaStar  <  1.0;\
\n1.0E-7  double 0.0 < epsilonDash;\
\n";;

let _sdpa_params = sdpa_alt_parameters;;

(* ------------------------------------------------------------------------- *)
(* CSDP parameters; so far I'm sticking with the defaults.                   *)
(* ------------------------------------------------------------------------- *)

let csdp_default_parameters =
"axtol=1.0e-8\
\natytol=1.0e-8\
\nobjtol=1.0e-8\
\npinftol=1.0e8\
\ndinftol=1.0e8\
\nmaxiter=100\
\nminstepfrac=0.9\
\nmaxstepfrac=0.97\
\nminstepp=1.0e-8\
\nminstepd=1.0e-8\
\nusexzgap=1\
\ntweakgap=0\
\naffine=0\
\nprintlevel=1\
\n";;

let csdp_params = csdp_default_parameters;;

(* ------------------------------------------------------------------------- *)
(* Now call CSDP on a problem and parse back the output.                     *)
(* ------------------------------------------------------------------------- *)

let run_csdp dbg obj mats =
  let input_file = Filename.temp_file "sos" ".dat-s" in
  let output_file =
    String.sub input_file 0 (String.length input_file - 6) ^ ".out"
  and params_file = Filename.concat temp_path "param.csdp" in
  file_of_string input_file (sdpa_of_problem "" obj mats);
  file_of_string params_file csdp_params;
  let rv = Sys.command("cd "^temp_path^"; csdp "^input_file ^
                        " " ^ output_file ^
                       (if dbg then "" else "> /dev/null")) in
  let op = string_of_file output_file in
  let res = parse_csdpoutput op in
  ((if dbg then ()
    else (Sys.remove input_file; Sys.remove output_file));
    rv,res);;

(* ------------------------------------------------------------------------- *)
(* Try some apparently sensible scaling first. Note that this is purely to   *)
(* get a cleaner translation to floating-point, and doesn't affect any of    *)
(* the results, in principle. In practice it seems a lot better when there   *)
(* are extreme numbers in the original problem.                              *)
(* ------------------------------------------------------------------------- *)

let scale_then =
  let common_denominator amat acc =
    foldl (fun a m c -> lcm_num (denominator c) a) acc amat
  and maximal_element amat acc =
    foldl (fun maxa m c -> max_num maxa (abs_num c)) acc amat in
  fun solver obj mats ->
    let cd1 = List.fold_right common_denominator mats (Int 1)
    and cd2 = common_denominator (snd obj)  (Int 1) in
    let mats' = List.map (mapf (fun x -> cd1 */ x)) mats
    and obj' = vector_cmul cd2 obj in
    let max1 = List.fold_right maximal_element mats' (Int 0)
    and max2 = maximal_element (snd obj') (Int 0) in
    let scal1 = pow2 (20-int_of_float(log(float_of_num max1) /. log 2.0))
    and scal2 = pow2 (20-int_of_float(log(float_of_num max2) /. log 2.0)) in
    let mats'' = List.map (mapf (fun x -> x */ scal1)) mats'
    and obj'' = vector_cmul scal2 obj' in
    solver obj'' mats'';;

(* ------------------------------------------------------------------------- *)
(* Round a vector to "nice" rationals.                                       *)
(* ------------------------------------------------------------------------- *)

let nice_rational n x = round_num (n */ x) // n;;

let nice_vector n = mapa (nice_rational n);;

(* ------------------------------------------------------------------------- *)
(* Reduce linear program to SDP (diagonal matrices) and test with CSDP. This *)
(* one tests A [-1;x1;..;xn] >= 0 (i.e. left column is negated constants).   *)
(* ------------------------------------------------------------------------- *)

let linear_program_basic a =
  let m,n = dimensions a in
  let mats =  List.map (fun j -> diagonal (column j a)) (1--n)
  and obj = vector_const (Int 1) m in
  let rv,res = run_csdp false obj mats in
  if rv = 1 || rv = 2 then false
  else if rv = 0 then true
  else failwith "linear_program: An error occurred in the SDP solver";;

(* ------------------------------------------------------------------------- *)
(* Test whether a point is in the convex hull of others. Rather than use     *)
(* computational geometry, express as linear inequalities and call CSDP.     *)
(* This is a bit lazy of me, but it's easy and not such a bottleneck so far. *)
(* ------------------------------------------------------------------------- *)

let in_convex_hull pts pt =
  let pts1 = (1::pt) :: List.map (fun x -> 1::x) pts in
  let pts2 = List.map (fun p -> List.map (fun x -> -x) p @ p) pts1 in
  let n = List.length pts + 1
  and v = 2 * (List.length pt + 1) in
  let m = v + n - 1 in
  let mat =
    (m,n),
    itern 1 pts2 (fun pts j -> itern 1 pts (fun x i -> (i,j) |-> Int x))
                 (iter (1,n) (fun i -> (v + i,i+1) |-> Int 1) undefined) in
  linear_program_basic mat;;

(* ------------------------------------------------------------------------- *)
(* Filter down a set of points to a minimal set with the same convex hull.   *)
(* ------------------------------------------------------------------------- *)

let minimal_convex_hull =
  let augment1 = function
    | [] -> assert false
    | (m::ms) -> if in_convex_hull ms m then ms else ms@[m] in
  let augment m ms = funpow 3 augment1 (m::ms) in
  fun mons ->
    let mons' = List.fold_right augment (List.tl mons) [List.hd mons] in
    funpow (List.length mons') augment1 mons';;

(* ------------------------------------------------------------------------- *)
(* Stuff for "equations" (generic A->num functions).                         *)
(* ------------------------------------------------------------------------- *)

let equation_cmul c eq =
  if c =/ Int 0 then Empty else mapf (fun d -> c */ d) eq;;

let equation_add eq1 eq2 = combine (+/) (fun x -> x =/ Int 0) eq1 eq2;;

let equation_eval assig eq =
  let value v = apply assig v in
  foldl (fun a v c -> a +/ value(v) */ c) (Int 0) eq;;

(* ------------------------------------------------------------------------- *)
(* Eliminate all variables, in an essentially arbitrary order.               *)
(* ------------------------------------------------------------------------- *)

let eliminate_all_equations one =
  let choose_variable eq =
    let (v,_) = choose eq in
    if v = one then
      let eq' = undefine v eq in
      if is_undefined eq' then failwith "choose_variable" else
      let (w,_) = choose eq' in w
    else v in
  let rec eliminate dun eqs =
    match eqs with
      [] -> dun
    | eq::oeqs ->
        if is_undefined eq then eliminate dun oeqs else
        let v = choose_variable eq in
        let a = apply eq v in
        let eq' = equation_cmul (Int(-1) // a) (undefine v eq) in
        let elim e =
          let b = tryapplyd e v (Int 0) in
          if b =/ Int 0 then e else
          equation_add e (equation_cmul (minus_num b // a) eq) in
        eliminate ((v |-> eq') (mapf elim dun)) (List.map elim oeqs) in
  fun eqs ->
    let assig = eliminate undefined eqs in
    let vs = foldl (fun a x f -> subtract (dom f) [one] @ a) [] assig in
    setify vs,assig;;

(* ------------------------------------------------------------------------- *)
(* Hence produce the "relevant" monomials: those whose squares lie in the    *)
(* Newton polytope of the monomials in the input. (This is enough according  *)
(* to Reznik: "Extremal PSD forms with few terms", Duke Math. Journal,       *)
(* vol 45, pp. 363--374, 1978.                                               *)
(*                                                                           *)
(* These are ordered in sort of decreasing degree. In particular the         *)
(* constant monomial is last; this gives an order in diagonalization of the  *)
(* quadratic form that will tend to display constants.                       *)
(* ------------------------------------------------------------------------- *)

let newton_polytope pol =
  let vars = poly_variables pol in
  let mons = List.map (fun m -> List.map (fun x -> monomial_degree x m) vars) (dom pol)
  and ds = List.map (fun x -> (degree x pol + 1) / 2) vars in
  let all = List.fold_right (fun n -> allpairs (fun h t -> h::t) (0--n)) ds [[]]
  and mons' = minimal_convex_hull mons in
  let all' =
    List.filter (fun m -> in_convex_hull mons' (List.map (fun x -> 2 * x) m)) all in
  List.map (fun m -> List.fold_right2 (fun v i a -> if i = 0 then a else (v |-> i) a)
                        vars m monomial_1) (List.rev all');;

(* ------------------------------------------------------------------------- *)
(* Diagonalize (Cholesky/LDU) the matrix corresponding to a quadratic form.  *)
(* ------------------------------------------------------------------------- *)

let diag m =
  let nn = dimensions m in
  let n = fst nn in
  if snd nn <> n then failwith "diagonalize: non-square matrix" else
  let rec diagonalize i m =
    if is_zero m then [] else
    let a11 = element m (i,i) in
    if a11 </ Int 0 then failwith "diagonalize: not PSD"
    else if a11 =/ Int 0 then
      if is_zero(row i m) then diagonalize (i + 1) m
      else failwith "diagonalize: not PSD"
    else
      let v = row i m in
      let v' = mapa (fun a1k -> a1k // a11) v in
      let m' =
      (n,n),
      iter (i+1,n) (fun j ->
          iter (i+1,n) (fun k ->
              ((j,k) |--> (element m (j,k) -/ element v j */ element v' k))))
          undefined in
      (a11,v')::diagonalize (i + 1) m' in
  diagonalize 1 m;;

(* ------------------------------------------------------------------------- *)
(* Adjust a diagonalization to collect rationals at the start.               *)
(* ------------------------------------------------------------------------- *)

let deration d =
  if d = [] then Int 0,d else
  let adj(c,l) =
    let a = foldl (fun a i c -> lcm_num a (denominator c)) (Int 1) (snd l) //
            foldl (fun a i c -> gcd_num a (numerator c)) (Int 0) (snd l) in
    (c // (a */ a)),mapa (fun x -> a */ x) l in
  let d' = List.map adj d in
  let a = List.fold_right ((o) lcm_num ( (o) denominator fst)) d' (Int 1) //
          List.fold_right ((o) gcd_num ( (o) numerator fst)) d' (Int 0)  in
  (Int 1 // a),List.map (fun (c,l) -> (a */ c,l)) d';;

(* ------------------------------------------------------------------------- *)
(* Enumeration of monomials with given multidegree bound.                    *)
(* ------------------------------------------------------------------------- *)

let rec enumerate_monomials d vars =
  if d < 0 then []
  else if d = 0 then [undefined]
  else if vars = [] then [monomial_1] else
  let alts =
    List.map (fun k -> let oths = enumerate_monomials (d - k) (List.tl vars) in
                  List.map (fun ks -> if k = 0 then ks else (List.hd vars |-> k) ks) oths)
        (0--d) in
  end_itlist (@) alts;;

(* ------------------------------------------------------------------------- *)
(* Enumerate products of distinct input polys with degree <= d.              *)
(* We ignore any constant input polynomials.                                 *)
(* Give the output polynomial and a record of how it was derived.            *)
(* ------------------------------------------------------------------------- *)

let rec enumerate_products d pols =
  if d = 0 then [poly_const num_1,Rational_lt num_1] else if d < 0 then [] else
  match pols with
    [] -> [poly_const num_1,Rational_lt num_1]
  | (p,b)::ps -> let e = multidegree p in
                 if e = 0 then enumerate_products d ps else
                 enumerate_products d ps @
                 List.map (fun (q,c) -> poly_mul p q,Product(b,c))
                     (enumerate_products (d - e) ps);;

(* ------------------------------------------------------------------------- *)
(* Multiply equation-parametrized poly by regular poly and add accumulator.  *)
(* ------------------------------------------------------------------------- *)

let epoly_pmul p q acc =
  foldl (fun a m1 c ->
           foldl (fun b m2 e ->
                        let m =  monomial_mul m1 m2 in
                        let es = tryapplyd b m undefined in
                        (m |-> equation_add (equation_cmul c e) es) b)
                 a q) acc p;;

(* ------------------------------------------------------------------------- *)
(* Convert regular polynomial. Note that we treat (0,0,0) as -1.             *)
(* ------------------------------------------------------------------------- *)

let epoly_of_poly p =
  foldl (fun a m c -> (m |-> ((0,0,0) |=> minus_num c)) a) undefined p;;

(* ------------------------------------------------------------------------- *)
(* String for block diagonal matrix numbered k.                              *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_blockdiagonal k m =
  let pfx = string_of_int k ^" " in
  let ents =
    foldl (fun a (b,i,j) c -> if i > j then a else ((b,i,j),c)::a) [] m in
  let entss = sort (increasing fst) ents in
  List.fold_right (fun ((b,i,j),c) a ->
     pfx ^ string_of_int b ^ " " ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) entss "";;

(* ------------------------------------------------------------------------- *)
(* SDPA for problem using block diagonal (i.e. multiple SDPs)                *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_blockproblem comment nblocks blocksizes obj mats =
  let m = List.length mats - 1 in
  "\"" ^ comment ^ "\"\n" ^
  string_of_int m ^ "\n" ^
  string_of_int nblocks ^ "\n" ^
  (String.concat " " (List.map string_of_int blocksizes)) ^
  "\n" ^
  sdpa_of_vector obj ^
  List.fold_right2 (fun k m a -> sdpa_of_blockdiagonal (k - 1) m ^ a)
          (1--List.length mats) mats "";;

(* ------------------------------------------------------------------------- *)
(* Hence run CSDP on a problem in block diagonal form.                       *)
(* ------------------------------------------------------------------------- *)

let run_csdp dbg nblocks blocksizes obj mats =
  let input_file = Filename.temp_file "sos" ".dat-s" in
  let output_file =
    String.sub input_file 0 (String.length input_file - 6) ^ ".out"
  and params_file = Filename.concat temp_path "param.csdp" in
  file_of_string input_file
   (sdpa_of_blockproblem "" nblocks blocksizes obj mats);
  file_of_string params_file csdp_params;
  let rv = Sys.command("cd "^temp_path^"; csdp "^input_file ^
                        " " ^ output_file ^
                       (if dbg then "" else "> /dev/null")) in
  let op = string_of_file output_file in
  let res = parse_csdpoutput op in
  ((if dbg then ()
    else (Sys.remove input_file; Sys.remove output_file));
    rv,res);;

let csdp nblocks blocksizes obj mats =
  let rv,res = run_csdp (!debugging) nblocks blocksizes obj mats in
  (if rv = 1 || rv = 2 then failwith "csdp: Problem is infeasible"
   else if rv = 3 then ()
    (*Format.print_string "csdp warning: Reduced accuracy";
     Format.print_newline() *)
   else if rv <> 0 then failwith("csdp: error "^string_of_int rv)
   else ());
  res;;

(* ------------------------------------------------------------------------- *)
(* 3D versions of matrix operations to consider blocks separately.           *)
(* ------------------------------------------------------------------------- *)

let bmatrix_add = combine (+/) (fun x -> x =/ Int 0);;

let bmatrix_cmul c bm =
  if c =/ Int 0 then undefined
  else mapf (fun x -> c */ x) bm;;

let bmatrix_neg = bmatrix_cmul (Int(-1));;

(* ------------------------------------------------------------------------- *)
(* Smash a block matrix into components.                                     *)
(* ------------------------------------------------------------------------- *)

let blocks blocksizes bm =
  List.map (fun (bs,b0) ->
        let m = foldl
          (fun a (b,i,j) c -> if b = b0 then ((i,j) |-> c) a else a)
          undefined bm in
        (((bs,bs),m):matrix))
      (List.combine blocksizes (1--List.length blocksizes));;

(* ------------------------------------------------------------------------- *)
(* Positiv- and Nullstellensatz. Flag "linf" forces a linear representation. *)
(* ------------------------------------------------------------------------- *)

let real_positivnullstellensatz_general linf d eqs leqs pol =
  let vars = List.fold_right ((o) union poly_variables) (pol::eqs @ List.map fst leqs) [] in
  let monoid =
    if linf then
      (poly_const num_1,Rational_lt num_1)::
      (List.filter (fun (p,c) -> multidegree p <= d) leqs)
    else enumerate_products d leqs in
  let nblocks = List.length monoid in
  let mk_idmultiplier k p =
    let e = d - multidegree p in
    let mons = enumerate_monomials e vars in
    let nons = List.combine mons (1--List.length mons) in
    mons,
    List.fold_right (fun (m,n) -> (m |-> ((-k,-n,n) |=> Int 1))) nons undefined in
  let mk_sqmultiplier k (p,c) =
    let e = (d - multidegree p) / 2 in
    let mons = enumerate_monomials e vars in
    let nons = List.combine mons (1--List.length mons) in
    mons,
    List.fold_right (fun (m1,n1) ->
      List.fold_right (fun (m2,n2) a ->
          let m = monomial_mul m1 m2 in
          if n1 > n2 then a else
          let c = if n1 = n2 then Int 1 else Int 2 in
          let e = tryapplyd a m undefined in
          (m |-> equation_add ((k,n1,n2) |=> c) e) a)
         nons)
       nons undefined in
  let sqmonlist,sqs = List.split(List.map2 mk_sqmultiplier (1--List.length monoid) monoid)
  and idmonlist,ids =  List.split(List.map2 mk_idmultiplier (1--List.length eqs) eqs) in
  let blocksizes = List.map List.length sqmonlist in
  let bigsum =
    List.fold_right2 (fun p q a -> epoly_pmul p q a) eqs ids
            (List.fold_right2 (fun (p,c) s a -> epoly_pmul p s a) monoid sqs
                     (epoly_of_poly(poly_neg pol))) in
  let eqns = foldl (fun a m e -> e::a) [] bigsum in
  let pvs,assig = eliminate_all_equations (0,0,0) eqns in
  let qvars = (0,0,0)::pvs in
  let allassig = List.fold_right (fun v -> (v |-> (v |=> Int 1))) pvs assig in
  let mk_matrix v =
    foldl (fun m (b,i,j) ass -> if b < 0 then m else
                                let c = tryapplyd ass v (Int 0) in
                                if c =/ Int 0 then m else
                                ((b,j,i) |-> c) (((b,i,j) |-> c) m))
          undefined allassig in
  let diagents = foldl
    (fun a (b,i,j) e -> if b > 0 && i = j then equation_add e a else a)
    undefined allassig in
  let mats = List.map mk_matrix qvars
  and obj = List.length pvs,
            itern 1 pvs (fun v i -> (i |--> tryapplyd diagents v (Int 0)))
                        undefined in
  let raw_vec = if pvs = [] then vector_0 0
                else scale_then (csdp nblocks blocksizes) obj mats in
  let find_rounding d =
   (if !debugging then
     (Format.print_string("Trying rounding with limit "^string_of_num d);
      Format.print_newline())
    else ());
    let vec = nice_vector d raw_vec in
    let blockmat = iter (1,dim vec)
     (fun i a -> bmatrix_add (bmatrix_cmul (element vec i) (List.nth mats i)) a)
     (bmatrix_neg (List.nth mats 0)) in
    let allmats = blocks blocksizes blockmat in
    vec,List.map diag allmats in
  let vec,ratdias =
    if pvs = [] then find_rounding num_1
    else tryfind find_rounding (List.map Num.num_of_int (1--31) @
                                List.map pow2 (5--66)) in
  let newassigs =
    List.fold_right (fun k -> List.nth pvs (k - 1) |-> element vec k)
           (1--dim vec) ((0,0,0) |=> Int(-1)) in
  let finalassigs =
    foldl (fun a v e -> (v |-> equation_eval newassigs e) a) newassigs
          allassig in
  let poly_of_epoly p =
    foldl (fun a v e -> (v |--> equation_eval finalassigs e) a)
          undefined p in
  let mk_sos mons =
    let mk_sq (c,m) =
        c,List.fold_right (fun k a -> (List.nth mons (k - 1) |--> element m k) a)
                 (1--List.length mons) undefined in
    List.map mk_sq in
  let sqs = List.map2 mk_sos sqmonlist ratdias
  and cfs = List.map poly_of_epoly ids in
  let msq = List.filter (fun (a,b) -> b <> []) (List.map2 (fun a b -> a,b) monoid sqs) in
  let eval_sq sqs = List.fold_right
   (fun (c,q) -> poly_add (poly_cmul c (poly_mul q q))) sqs poly_0 in
  let sanity =
    List.fold_right (fun ((p,c),s) -> poly_add (poly_mul p (eval_sq s))) msq
           (List.fold_right2 (fun p q -> poly_add (poly_mul p q)) cfs eqs
                    (poly_neg pol)) in
  if not(is_undefined sanity) then raise Sanity else
  cfs,List.map (fun (a,b) -> snd a,b) msq;;

(* ------------------------------------------------------------------------- *)
(* The ordering so we can create canonical HOL polynomials.                  *)
(* ------------------------------------------------------------------------- *)

let dest_monomial mon = sort (increasing fst) (graph mon);;

let monomial_order =
  let rec lexorder l1 l2 =
    match (l1,l2) with
      [],[] -> true
    | vps,[] -> false
    | [],vps -> true
    | ((x1,n1)::vs1),((x2,n2)::vs2) ->
          if x1 < x2 then true
          else if x2 < x1 then false
          else if n1 < n2 then false
          else if n2 < n1 then true
          else lexorder vs1 vs2 in
  fun m1 m2 ->
    if m2 = monomial_1 then true else if m1 = monomial_1 then false else
    let mon1 = dest_monomial m1 and mon2 = dest_monomial m2 in
    let deg1 = List.fold_right ((o) (+) snd) mon1 0
    and deg2 = List.fold_right ((o) (+) snd) mon2 0 in
    if deg1 < deg2 then false else if deg1 > deg2 then true
    else lexorder mon1 mon2;;

(* ------------------------------------------------------------------------- *)
(* Map back polynomials and their composites to HOL.                         *)
(* ------------------------------------------------------------------------- *)

let term_of_varpow =
  fun x k ->
    if k = 1 then Var x else Pow (Var x, k);;

let term_of_monomial =
  fun m -> if m = monomial_1 then Const num_1 else
           let m' = dest_monomial m in
           let vps = List.fold_right (fun (x,k) a -> term_of_varpow x k :: a) m' [] in
           end_itlist (fun s t -> Mul (s,t)) vps;;

let term_of_cmonomial =
  fun (m,c) ->
    if m = monomial_1 then Const c
    else if c =/ num_1 then term_of_monomial m
    else Mul (Const c,term_of_monomial m);;

let term_of_poly =
  fun p ->
    if p = poly_0 then Zero else
    let cms = List.map term_of_cmonomial
     (sort (fun (m1,_) (m2,_) -> monomial_order m1 m2) (graph p)) in
    end_itlist (fun t1 t2 -> Add (t1,t2)) cms;;

let term_of_sqterm (c,p) =
  Product(Rational_lt c,Square(term_of_poly p));;

let term_of_sos (pr,sqs) =
  if sqs = [] then pr
  else Product(pr,end_itlist (fun a b -> Sum(a,b)) (List.map term_of_sqterm sqs));;

(* ------------------------------------------------------------------------- *)
(* Some combinatorial helper functions.                                      *)
(* ------------------------------------------------------------------------- *)

let rec allpermutations l =
  if l = [] then [[]] else
  List.fold_right (fun h acc -> List.map (fun t -> h::t)
                (allpermutations (subtract l [h])) @ acc) l [];;

let changevariables_monomial zoln (m:monomial) =
  foldl (fun a x k -> (List.assoc x zoln |-> k) a) monomial_1 m;;

let changevariables zoln pol =
  foldl (fun a m c -> (changevariables_monomial zoln m |-> c) a)
        poly_0 pol;;

(* ------------------------------------------------------------------------- *)
(* Return to original non-block matrices.                                    *)
(* ------------------------------------------------------------------------- *)

let sdpa_of_vector (v:vector) =
  let n = dim v in
  let strs = List.map (o (decimalize 20) (element v)) (1--n) in
  String.concat " " strs ^ "\n";;

let sdpa_of_matrix k (m:matrix) =
  let pfx = string_of_int k ^ " 1 " in
  let ms = foldr (fun (i,j) c a -> if i > j then a else ((i,j),c)::a)
                 (snd m) [] in
  let mss = sort (increasing fst) ms in
  List.fold_right (fun ((i,j),c) a ->
     pfx ^ string_of_int i ^ " " ^ string_of_int j ^
     " " ^ decimalize 20 c ^ "\n" ^ a) mss "";;

let sdpa_of_problem comment obj mats =
  let m = List.length mats - 1
  and n,_ = dimensions (List.hd mats) in
  "\"" ^ comment ^ "\"\n" ^
  string_of_int m ^ "\n" ^
  "1\n" ^
  string_of_int n ^ "\n" ^
  sdpa_of_vector obj ^
  List.fold_right2 (fun k m a -> sdpa_of_matrix (k - 1) m ^ a)
          (1--List.length mats) mats "";;

let run_csdp dbg obj mats =
  let input_file = Filename.temp_file "sos" ".dat-s" in
  let output_file =
    String.sub input_file 0 (String.length input_file - 6) ^ ".out"
  and params_file = Filename.concat temp_path "param.csdp" in
  file_of_string input_file (sdpa_of_problem "" obj mats);
  file_of_string params_file csdp_params;
  let rv = Sys.command("cd "^temp_path^"; csdp "^input_file ^
                       " " ^ output_file ^
                       (if dbg then "" else "> /dev/null")) in
  let op = string_of_file output_file in
  let res = parse_csdpoutput op in
  ((if dbg then ()
    else (Sys.remove input_file; Sys.remove output_file));
    rv,res);;

let csdp obj mats =
  let rv,res = run_csdp (!debugging) obj mats in
  (if rv = 1 || rv = 2 then failwith "csdp: Problem is infeasible"
    else if rv = 3 then ()
(*    (Format.print_string "csdp warning: Reduced accuracy";
     Format.print_newline()) *)
   else if rv <> 0 then failwith("csdp: error "^string_of_int rv)
   else ());
  res;;

(* ------------------------------------------------------------------------- *)
(* Sum-of-squares function with some lowbrow symmetry reductions.            *)
(* ------------------------------------------------------------------------- *)

let sumofsquares_general_symmetry tool pol =
  let vars = poly_variables pol
  and lpps = newton_polytope pol in
  let n = List.length lpps in
  let sym_eqs =
    let invariants = List.filter
     (fun vars' ->
        is_undefined(poly_sub pol (changevariables (List.combine vars vars') pol)))
     (allpermutations vars) in
    let lpns = List.combine lpps (1--List.length lpps) in
    let lppcs =
      List.filter (fun (m,(n1,n2)) -> n1 <= n2)
             (allpairs
               (fun (m1,n1) (m2,n2) -> (m1,m2),(n1,n2)) lpns lpns) in
    let clppcs = end_itlist (@)
       (List.map (fun ((m1,m2),(n1,n2)) ->
                List.map (fun vars' ->
                        (changevariables_monomial (List.combine vars vars') m1,
                         changevariables_monomial (List.combine vars vars') m2),(n1,n2))
                    invariants)
            lppcs) in
    let clppcs_dom = setify(List.map fst clppcs) in
    let clppcs_cls = List.map (fun d -> List.filter (fun (e,_) -> e = d) clppcs)
                         clppcs_dom in
    let eqvcls = List.map (o setify (List.map snd)) clppcs_cls in
    let mk_eq cls acc =
      match cls with
        [] -> raise Sanity
      | [h] -> acc
      | h::t -> List.map (fun k -> (k |-> Int(-1)) (h |=> Int 1)) t @ acc in
    List.fold_right mk_eq eqvcls [] in
  let eqs = foldl (fun a x y -> y::a) []
   (itern 1 lpps (fun m1 n1 ->
        itern 1 lpps (fun m2 n2 f ->
                let m = monomial_mul m1 m2 in
                if n1 > n2 then f else
                let c = if n1 = n2 then Int 1 else Int 2 in
                (m |-> ((n1,n2) |-> c) (tryapplyd f m undefined)) f))
       (foldl (fun a m c -> (m |-> ((0,0)|=>c)) a)
              undefined pol)) @
    sym_eqs in
  let pvs,assig = eliminate_all_equations (0,0) eqs in
  let allassig = List.fold_right (fun v -> (v |-> (v |=> Int 1))) pvs assig in
  let qvars = (0,0)::pvs in
  let diagents =
    end_itlist equation_add (List.map (fun i -> apply allassig (i,i)) (1--n)) in
  let mk_matrix v =
   ((n,n),
    foldl (fun m (i,j) ass -> let c = tryapplyd ass v (Int 0) in
                              if c =/ Int 0 then m else
                              ((j,i) |-> c) (((i,j) |-> c) m))
          undefined allassig :matrix) in
  let mats = List.map mk_matrix qvars
  and obj = List.length pvs,
            itern 1 pvs (fun v i -> (i |--> tryapplyd diagents v (Int 0)))
                undefined in
  let raw_vec = if pvs = [] then vector_0 0 else tool obj mats in
  let find_rounding d =
   (if !debugging then
     (Format.print_string("Trying rounding with limit "^string_of_num d);
      Format.print_newline())
    else ());
    let vec = nice_vector d raw_vec in
    let mat = iter (1,dim vec)
     (fun i a -> matrix_add (matrix_cmul (element vec i) (List.nth mats i)) a)
     (matrix_neg (List.nth mats 0)) in
    deration(diag mat) in
  let rat,dia =
    if pvs = [] then
       let mat = matrix_neg (List.nth mats 0) in
       deration(diag mat)
    else
       tryfind find_rounding (List.map Num.num_of_int (1--31) @
                              List.map pow2 (5--66)) in
  let poly_of_lin(d,v) =
    d,foldl(fun a i c -> (List.nth lpps (i - 1) |-> c) a) undefined (snd v) in
  let lins = List.map poly_of_lin dia in
  let sqs = List.map (fun (d,l) -> poly_mul (poly_const d) (poly_pow l 2)) lins in
  let sos = poly_cmul rat (end_itlist poly_add sqs) in
  if is_undefined(poly_sub sos pol) then rat,lins else raise Sanity;;

let sumofsquares = sumofsquares_general_symmetry csdp;;

