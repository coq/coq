(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Constr
open Tactics
open Coqlib

open Num
open Utile

(***********************************************************************
 Operations on coefficients
*)

let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r')

module BigInt = struct
  open Big_int

  type t = big_int
  let of_int = big_int_of_int
  let coef0 = of_int 0
  let of_num = Num.big_int_of_num
  let to_num = Num.num_of_big_int
  let equal = eq_big_int
  let lt = lt_big_int
  let le = le_big_int
  let abs = abs_big_int
  let plus =add_big_int
  let mult = mult_big_int
  let sub = sub_big_int
  let opp = minus_big_int
  let div = div_big_int
  let modulo = mod_big_int
  let to_string = string_of_big_int
  let hash x =
    try (int_of_big_int x)
    with Failure _ -> 1
  let puis = power_big_int_positive_int

  (* a et b positifs, résultat positif *)
  let rec pgcd a b =
    if equal b coef0
    then a
    else if lt a b then pgcd b a else pgcd b (modulo a b)

end

(*
module Ent = struct
  type t = Entiers.entiers
  let of_int = Entiers.ent_of_int
  let of_num x = Entiers.ent_of_string(Num.string_of_num x)
  let to_num x = Num.num_of_string (Entiers.string_of_ent x)
  let equal = Entiers.eq_ent
  let lt = Entiers.lt_ent
  let le = Entiers.le_ent
  let abs = Entiers.abs_ent
  let plus =Entiers.add_ent
  let mult = Entiers.mult_ent
  let sub = Entiers.moins_ent
  let opp = Entiers.opp_ent
  let div = Entiers.div_ent
  let modulo = Entiers.mod_ent
  let coef0 = Entiers.ent0
  let coef1 = Entiers.ent1
  let to_string = Entiers.string_of_ent
  let to_int x = Entiers.int_of_ent x
  let hash x =Entiers.hash_ent x
  let signe = Entiers.signe_ent

  let rec puis p n = match n with
      0 -> coef1
    |_ -> (mult p (puis p (n-1)))

  (* a et b positifs, résultat positif *)
  let rec pgcd a b =
    if equal b coef0
    then a
    else if lt a b then pgcd b a else pgcd b (modulo a b)


  (* signe du pgcd = signe(a)*signe(b) si non nuls. *)
  let pgcd2 a b =
    if equal a coef0 then b
    else if equal b coef0 then a
    else let c = pgcd (abs a) (abs b) in
    if ((lt coef0 a)&&(lt b coef0))
      ||((lt coef0 b)&&(lt a coef0))
    then opp c else c
end
*)

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

type vname = string

type term =
  | Zero
  | Const of Num.num
  | Var of vname
  | Opp of term
  | Add of term * term
  | Sub of term * term
  | Mul of term * term
  | Pow of term * int

let const n =
  if eq_num n num_0 then Zero else Const n
let pow(p,i) = if Int.equal i 1 then p else Pow(p,i)
let add = function
    (Zero,q) -> q
  | (p,Zero) -> p
  | (p,q) -> Add(p,q)
let mul = function
    (Zero,_) -> Zero
  | (_,Zero) -> Zero
  | (p,Const n) when eq_num n num_1 -> p
  | (Const n,q) when eq_num n num_1 -> q
  | (p,q) -> Mul(p,q)

let gen_constant msg path s = UnivGen.constr_of_global @@
  coq_reference msg path s

let tpexpr  = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PExpr")
let ttconst = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEc")
let ttvar = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEX")
let ttadd = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEadd")
let ttsub = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEsub")
let ttmul = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEmul")
let ttopp = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEopp")
let ttpow = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEpow")

let datatypes = ["Init";"Datatypes"]
let binnums = ["Numbers";"BinNums"]

let tlist = lazy (gen_constant "CC" datatypes "list")
let lnil = lazy (gen_constant "CC" datatypes "nil")
let lcons = lazy (gen_constant "CC" datatypes "cons")

let tz = lazy (gen_constant "CC" binnums "Z")
let z0 = lazy (gen_constant "CC" binnums "Z0")
let zpos = lazy (gen_constant "CC" binnums "Zpos")
let zneg = lazy(gen_constant "CC" binnums "Zneg")

let pxI = lazy(gen_constant "CC" binnums "xI")
let pxO = lazy(gen_constant "CC" binnums "xO")
let pxH = lazy(gen_constant "CC" binnums "xH")

let nN0 = lazy (gen_constant "CC" binnums "N0")
let nNpos = lazy(gen_constant "CC" binnums "Npos")

let mkt_app name l =  mkApp (Lazy.force name, Array.of_list l)

let tlp () = mkt_app tlist [mkt_app tpexpr [Lazy.force tz]]
let tllp () = mkt_app tlist [tlp()]

let rec mkt_pos n =
  if n =/ num_1 then Lazy.force pxH
  else if mod_num n num_2 =/ num_0 then
    mkt_app pxO [mkt_pos (quo_num n num_2)]
  else
    mkt_app pxI [mkt_pos (quo_num n num_2)]

let mkt_n n =
  if Num.eq_num n num_0
  then Lazy.force nN0
  else mkt_app nNpos [mkt_pos n]

let mkt_z z  =
  if z =/ num_0 then  Lazy.force z0
  else if z >/ num_0 then
    mkt_app zpos [mkt_pos z]
  else
    mkt_app zneg [mkt_pos ((Int 0) -/ z)]

let rec mkt_term t  =  match t with
| Zero -> mkt_term (Const num_0)
| Const r -> let (n,d) = numdom r in
  mkt_app  ttconst [Lazy.force tz; mkt_z n]
| Var v -> mkt_app ttvar [Lazy.force tz; mkt_pos (num_of_string v)]
| Opp t1 -> mkt_app  ttopp [Lazy.force tz; mkt_term t1]
| Add (t1,t2) -> mkt_app  ttadd [Lazy.force tz; mkt_term t1; mkt_term t2]
| Sub (t1,t2) -> mkt_app  ttsub [Lazy.force tz; mkt_term t1; mkt_term t2]
| Mul (t1,t2) -> mkt_app  ttmul [Lazy.force tz; mkt_term t1; mkt_term t2]
| Pow (t1,n) ->  if Int.equal n 0 then
    mkt_app ttconst [Lazy.force tz; mkt_z num_1]
else
    mkt_app ttpow [Lazy.force tz; mkt_term t1; mkt_n (num_of_int n)]

let rec parse_pos p =
  match Constr.kind p with
| App (a,[|p2|]) ->
    if Constr.equal a (Lazy.force pxO) then num_2 */ (parse_pos p2)
    else num_1 +/ (num_2 */ (parse_pos p2))
| _ -> num_1

let parse_z z =
  match Constr.kind z with
| App (a,[|p2|]) ->
    if Constr.equal a (Lazy.force zpos) then parse_pos p2 else (num_0 -/ (parse_pos p2))
| _ -> num_0

let parse_n z =
  match Constr.kind z with
| App (a,[|p2|]) ->
    parse_pos p2
| _ -> num_0

let rec parse_term p =
  match Constr.kind p with
| App (a,[|_;p2|]) ->
    if Constr.equal a (Lazy.force ttvar) then Var (string_of_num (parse_pos p2))
    else if Constr.equal a (Lazy.force ttconst) then Const (parse_z p2)
    else if Constr.equal a (Lazy.force ttopp) then Opp (parse_term p2)
    else Zero
| App (a,[|_;p2;p3|]) ->
    if Constr.equal a (Lazy.force ttadd) then Add (parse_term p2, parse_term p3)
    else if Constr.equal a (Lazy.force ttsub) then Sub (parse_term p2, parse_term p3)
    else if Constr.equal a (Lazy.force ttmul) then Mul (parse_term p2, parse_term p3)
    else if Constr.equal a (Lazy.force ttpow) then
      Pow (parse_term p2, int_of_num (parse_n p3))
    else Zero
| _ -> Zero

let rec parse_request lp =
  match Constr.kind lp with
    | App (_,[|_|])  -> []
    | App (_,[|_;p;lp1|])  ->
	(parse_term p)::(parse_request lp1)
    |_-> assert false

let set_nvars_term nvars t =
  let rec aux t nvars =
    match t with
    | Zero -> nvars
    | Const r -> nvars
    | Var v -> let n = int_of_string v in
      max nvars n
    | Opp t1 -> aux t1 nvars
    | Add (t1,t2) -> aux t2 (aux t1 nvars)
    | Sub (t1,t2) -> aux t2 (aux t1 nvars)
    | Mul (t1,t2) -> aux t2 (aux t1 nvars)
    | Pow (t1,n) ->  aux t1 nvars
  in aux t nvars

(***********************************************************************
   Coefficients: recursive polynomials
 *)

module Coef = BigInt
(*module Coef = Ent*)
module Poly = Polynom.Make(Coef)
module PIdeal = Ideal.Make(Poly)
open PIdeal

(* term to sparse polynomial 
   varaibles <=np are in the coefficients
*)

let term_pol_sparse nvars np t=
  let d = nvars in
  let rec aux t =
(*    info ("conversion de: "^(string_of_term t)^"\n");*)
    let res =
    match t with
    | Zero -> zeroP
    | Const r ->
	if Num.eq_num r num_0
	then zeroP
	else polconst d (Poly.Pint (Coef.of_num r))
    | Var v ->
	let v = int_of_string v in
	if v <= np
	then polconst d (Poly.x v)
	else gen d v
    | Opp t1 ->  oppP (aux t1)
    | Add (t1,t2) -> plusP (aux t1) (aux t2)
    | Sub (t1,t2) -> plusP (aux t1) (oppP (aux t2))
    | Mul (t1,t2) -> multP (aux t1) (aux t2)
    | Pow (t1,n) ->  puisP (aux t1) n
    in 
(*       info ("donne: "^(stringP res)^"\n");*)
       res 
  in
  let res= aux t in
  res

(* sparse polynomial to term *)

let polrec_to_term p =
  let rec aux p =
  match p with
   |Poly.Pint n -> const (Coef.to_num n)
   |Poly.Prec (v,coefs) ->
    let fold i c res = add (res, mul (aux c, pow (Var (string_of_int v), i))) in
    Array.fold_right_i fold coefs Zero
  in aux p

(* approximation of the Horner form used in the tactic ring *)

let pol_sparse_to_term n2 p =
 (* info "pol_sparse_to_term ->\n";*)
  let p = PIdeal.repr p in
  let rec aux p =
    match p with
      [] -> const (num_of_string "0")
    | (a,m)::p1 ->
      let m = Ideal.Monomial.repr m in
      let n = (Array.length m)-1 in
      let (i0,e0) =
	List.fold_left (fun (r,d) (a,m) ->
              let m = Ideal.Monomial.repr m in
	      let i0= ref 0 in
	      for k=1 to n do
		if m.(k)>0
		then i0:=k
	      done;
	      if Int.equal !i0 0
	      then (r,d)
	      else if !i0 > r
	      then (!i0, m.(!i0))
	      else if Int.equal !i0 r && m.(!i0)<d
	      then (!i0, m.(!i0))
	      else (r,d))
	  (0,0)
	  p in
      if Int.equal i0 0
      then
	let mp = polrec_to_term a in
        if List.is_empty p1 then mp else add (mp, aux p1)
      else
        let fold (p1, p2) (a, m) =
          if (Ideal.Monomial.repr m).(i0) >= e0 then begin
            let m0 = Array.copy (Ideal.Monomial.repr m) in
            let () = m0.(i0) <- m0.(i0) - e0 in
            let m0 = Ideal.Monomial.make m0 in
            ((a, m0) :: p1, p2)
          end else
            (p1, (a, m) :: p2)
        in
        let (p1, p2) = List.fold_left fold ([], []) p in
	let vm =
	  if Int.equal e0 1
	  then Var (string_of_int (i0))
	  else pow (Var (string_of_int (i0)),e0) in
	add (mul(vm, aux (List.rev p1)), aux (List.rev p2))
  in   (*info "-> pol_sparse_to_term\n";*)
  aux p


(*
   lq = [cn+m+1 n+m ...cn+m+1 1]
   lci=[[cn+1 n,...,cn1 1]
   ...
   [cn+m n+m-1,...,cn+m 1]]

   removes intermediate polynomials not useful to compute the last one.
 *)

let remove_zeros lci =
  let m = List.length lci in
  let u = Array.make m false in
  let rec utiles k =
    (** TODO: Find a more reasonable implementation of this traversal. *)
    if k >= m || u.(k) then ()
    else
      let () = u.(k) <- true in
      let lc = List.nth lci k in
      let iter i c = if not (PIdeal.equal c zeroP) then utiles (i + k + 1) in
      List.iteri iter lc
  in
  let () = utiles 0 in
  let filter i l =
    let f j l = if m <= i + j + 1 then true else u.(i + j + 1) in
    if u.(i) then Some (List.filteri f l)
    else None
  in
  let lr = CList.map_filter_i filter lci in
  info (fun () -> Printf.sprintf "useless spolynomials: %i" (m-List.length lr));
  info (fun () -> Printf.sprintf "useful spolynomials: %i " (List.length lr));
  lr

let theoremedeszeros metadata nvars lpol p =
  let t1 = Unix.gettimeofday() in
  let m = nvars in
  let cert = in_ideal metadata m lpol p in
  info (fun () -> Printf.sprintf "time: @[%10.3f@]s" (Unix.gettimeofday ()-.t1));
  cert

open Ideal

(* Remove zero polynomials and duplicates from the list of polynomials lp
   Return (clp, lb)
   where clp is the reduced list and lb is a list of booleans
   that has the same size than lp and where true indicates an
   element that has been removed
 *)
let clean_pol lp =
  let t = Hashpol.create 12 in
  let find p = try Hashpol.find t p 
               with 
                 Not_found -> Hashpol.add t p true; false in
  let rec aux lp =
    match lp with
    | [] -> [], []
    | p :: lp1 -> 
      let clp, lb = aux lp1 in
      if equal p zeroP ||  find p then clp, true::lb 
       else
        (p :: clp, false::lb) in
     aux lp

(* Expand the list of polynomials lp putting zeros where the list of 
   booleans lb indicates there is a missing element 
   Warning:
   the expansion is relative to the end of the list in reversed order
   lp cannot have less elements than lb
*)
let expand_pol lb lp =
 let rec aux lb lp = 
   match lb with
   | [] -> lp
   | true :: lb1 ->  zeroP :: aux lb1 lp
   | false :: lb1 ->
     match lp with
     [] -> assert false
     | p :: lp1 -> p :: aux lb1 lp1 
  in List.rev (aux lb (List.rev lp))

let theoremedeszeros_termes lp =
  let nvars = List.fold_left set_nvars_term 0 lp in
  match lp with
  | Const (Int sugarparam)::Const (Int nparam)::lp ->
      ((match sugarparam with
      |0 -> sinfo "computation without sugar";
	  lexico:=false;
      |1 -> sinfo "computation with sugar";
	  lexico:=false;
      |2 -> sinfo "ordre lexico computation without sugar";
	  lexico:=true;
      |3 -> sinfo "ordre lexico computation with sugar";
	  lexico:=true;
      |4 -> sinfo "computation without sugar, division by pairs";
	  lexico:=false;
      |5 -> sinfo "computation with sugar, division by pairs";
	  lexico:=false;
      |6 -> sinfo "ordre lexico computation without sugar, division by pairs";
	  lexico:=true;
      |7 -> sinfo "ordre lexico computation with sugar, division by pairs";
	  lexico:=true;
      | _ -> user_err Pp.(str "nsatz: bad parameter")
       );
      let lvar = List.init nvars (fun i -> Printf.sprintf "x%i" (i + 1)) in
      let lvar = ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"] @ lvar in
      (* pour macaulay *)
      let metadata = { name_var = lvar } in
      let lp = List.map (term_pol_sparse nvars nparam) lp in
      match lp with
      | [] -> assert false
      | p::lp1 ->
	  let lpol = List.rev lp1 in
          (* preprocessing :
             we remove zero polynomials and duplicate that are not handled by in_ideal
             lb is kept in order to fix the certificate in the post-processing 
          *)
	  let lpol, lb  = clean_pol lpol in
	  let cert = theoremedeszeros metadata nvars lpol p in
          sinfo "cert ok";
	  let lc = cert.last_comb::List.rev cert.gb_comb in
	  match remove_zeros lc with
	  | [] -> assert false
	  | (lq::lci) ->
              (* post-processing : we apply the correction for the last line *)
              let lq = expand_pol lb lq in
	      (* lci commence par les nouveaux polynomes *)
	      let m = nvars in
	      let c = pol_sparse_to_term m (polconst m cert.coef) in
	      let r = Pow(Zero,cert.power) in
	      let lci = List.rev lci in
              (* post-processing we apply the correction for the other lines *)
	      let lci = List.map (expand_pol lb) lci in
	      let lci = List.map (List.map (pol_sparse_to_term m)) lci in
	      let lq = List.map (pol_sparse_to_term m) lq in
	      info (fun () -> Printf.sprintf "number of parameters: %i" nparam);
	      sinfo "term computed";
	      (c,r,lci,lq)
      )
  |_ -> assert false


(* version avec hash-consing du certificat:
let nsatz lpol =
  Hashtbl.clear Dansideal.hmon;
  Hashtbl.clear Dansideal.coefpoldep;
  Hashtbl.clear Dansideal.sugartbl;
  Hashtbl.clear Polynomesrec.hcontentP;
  init_constants ();
  let lp= parse_request lpol in
  let (_lp0,_p,c,r,_lci,_lq as rthz) = theoremedeszeros_termes lp in
  let certif = certificat_vers_polynome_creux rthz in
  let certif = hash_certif certif in
  let certif = certif_term certif in
  let c = mkt_term c in
  info "constr computed\n";
  (c, certif)
*)

let nsatz lpol =
  let lp= parse_request lpol in
  let (c,r,lci,lq) = theoremedeszeros_termes lp in
  let res = [c::r::lq]@lci in
  let res = List.map (fun lx -> List.map mkt_term lx) res in
  let res =
    List.fold_right
      (fun lt r ->
	 let ltterm =
	   List.fold_right
	     (fun t r ->
		mkt_app lcons [mkt_app tpexpr [Lazy.force tz];t;r])
	     lt
	     (mkt_app lnil [mkt_app tpexpr [Lazy.force tz]]) in
	 mkt_app lcons [tlp ();ltterm;r])
      res
      (mkt_app lnil [tlp ()]) in
  sinfo "term computed";
  res

let return_term t =
  let a =
    mkApp(gen_constant "CC" ["Init";"Logic"] "eq_refl",[|tllp ();t|]) in
  let a = EConstr.of_constr a in
  generalize [a]

let nsatz_compute t =
  let lpol =
    try nsatz t
    with Ideal.NotInIdeal ->
      user_err Pp.(str "nsatz cannot solve this problem") in
  return_term lpol
