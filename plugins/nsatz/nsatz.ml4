(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Errors
open Util
open Term
open Tactics
open Coqlib

open Num
open Utile

DECLARE PLUGIN "nsatz_plugin"

(***********************************************************************
 Operations on coefficients
*)

let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r')

module BigInt = struct
  open Big_int

  type t = big_int
  let of_int = big_int_of_int
  let coef0 = of_int 0
  let coef1 = of_int 1
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
  let to_int x = int_of_big_int x
  let hash x =
    try (int_of_big_int x)
    with Failure _ -> 1
  let puis = power_big_int_positive_int

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

let unconstr = mkRel 1

let tpexpr =
  lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PExpr")
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
  match kind_of_term p with
| App (a,[|p2|]) ->
    if eq_constr a (Lazy.force pxO) then num_2 */ (parse_pos p2)
    else num_1 +/ (num_2 */ (parse_pos p2))
| _ -> num_1

let parse_z z =
  match kind_of_term z with
| App (a,[|p2|]) ->
    if eq_constr a (Lazy.force zpos) then parse_pos p2 else (num_0 -/ (parse_pos p2))
| _ -> num_0

let parse_n z =
  match kind_of_term z with
| App (a,[|p2|]) ->
    parse_pos p2
| _ -> num_0

let rec parse_term p =
  match kind_of_term p with
| App (a,[|_;p2|]) ->
    if eq_constr a (Lazy.force ttvar) then Var (string_of_num (parse_pos p2))
    else if eq_constr a (Lazy.force ttconst) then Const (parse_z p2)
    else if eq_constr a (Lazy.force ttopp) then Opp (parse_term p2)
    else Zero
| App (a,[|_;p2;p3|]) ->
    if eq_constr a (Lazy.force ttadd) then Add (parse_term p2, parse_term p3)
    else if eq_constr a (Lazy.force ttsub) then Sub (parse_term p2, parse_term p3)
    else if eq_constr a (Lazy.force ttmul) then Mul (parse_term p2, parse_term p3)
    else if eq_constr a (Lazy.force ttpow) then
      Pow (parse_term p2, int_of_num (parse_n p3))
    else Zero
| _ -> Zero

let rec parse_request lp =
  match kind_of_term lp with
    | App (_,[|_|])  -> []
    | App (_,[|_;p;lp1|])  ->
	(parse_term p)::(parse_request lp1)
    |_-> assert false

let nvars = ref 0

let set_nvars_term t =
  let rec aux t =
    match t with
    | Zero -> ()
    | Const r -> ()
    | Var v -> let n = int_of_string v in
      nvars:= max (!nvars) n
    | Opp t1 -> aux t1
    | Add (t1,t2) -> aux t1; aux t2
    | Sub (t1,t2) -> aux t1; aux t2
    | Mul (t1,t2) -> aux t1; aux t2
    | Pow (t1,n) ->  aux t1
  in aux t

let string_of_term p =
  let rec aux p =
    match p with
    | Zero -> "0"
    | Const r -> string_of_num r
    | Var v -> "x"^v
    | Opp t1 -> "(-"^(aux t1)^")"
    | Add (t1,t2) -> "("^(aux t1)^"+"^(aux t2)^")"
    | Sub (t1,t2) ->  "("^(aux t1)^"-"^(aux t2)^")"
    | Mul (t1,t2) ->  "("^(aux t1)^"*"^(aux t2)^")"
    | Pow (t1,n) ->  (aux t1)^"^"^(string_of_int n)
  in aux p


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

let term_pol_sparse np t=
  let d = !nvars in
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
     let res = ref Zero in
     Array.iteri
      (fun i c ->
	 res:=add(!res, mul(aux c,
			    pow (Var (string_of_int v),
				 i))))
      coefs;
     !res
  in aux p

(* approximation of the Horner form used in the tactic ring *)

let pol_sparse_to_term n2 p =
 (* info "pol_sparse_to_term ->\n";*)
  let p = PIdeal.repr p in
  let rec aux p =
    match p with
      [] -> const (num_of_string "0")
    | (a,m)::p1 ->
      let n = (Array.length m)-1 in
      let (i0,e0) =
	List.fold_left (fun (r,d) (a,m) ->
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
	let mp = ref (polrec_to_term a) in
        if List.is_empty p1
	then !mp
	else add(!mp,aux p1)
      else (
	let p1=ref [] in
	let p2=ref [] in
	List.iter
	  (fun (a,m) ->
	     if m.(i0)>=e0
	     then (m.(i0)<-m.(i0)-e0;
		   p1:=(a,m)::(!p1))
	     else p2:=(a,m)::(!p2))
	  p;
	let vm =
	  if Int.equal e0 1
	  then Var (string_of_int (i0))
	  else pow (Var (string_of_int (i0)),e0) in
	add(mul(vm, aux (List.rev (!p1))), aux (List.rev (!p2))))
  in   (*info "-> pol_sparse_to_term\n";*)
  aux p


let remove_list_tail l i =
  let rec aux l i =
    if List.is_empty l
    then []
    else if i<0
    then l
    else if Int.equal i 0
    then List.tl l
    else
      match l with
      |(a::l1) ->
	  a::(aux l1 (i-1))
      |_ -> assert false
  in
  List.rev (aux (List.rev l) i)

(*
   lq = [cn+m+1 n+m ...cn+m+1 1]
   lci=[[cn+1 n,...,cn1 1]
   ...
   [cn+m n+m-1,...,cn+m 1]]

   removes intermediate polynomials not useful to compute the last one.
 *)

let remove_zeros zero lci =
  let n = List.length (List.hd lci) in
  let m=List.length lci in
  let u = Array.make m false in
  let rec utiles k =
    if k>=m
    then ()
    else (
      u.(k)<-true;
      let lc = List.nth lci k in
      for i=0 to List.length lc - 1 do
	if not (zero (List.nth lc i))
	then utiles (i+k+1);
      done)
  in utiles 0;
  let lr = ref [] in
  for i=0 to m-1 do
    if u.(i)
    then lr:=(List.nth lci i)::(!lr)
  done;
  let lr=List.rev !lr in
  let lr = List.map
      (fun lc ->
	let lcr=ref lc in
	for i=0 to m-1 do
	  if not u.(i)
	  then lcr:=remove_list_tail !lcr (m-i+(n-m))
	done;
	!lcr)
      lr in
  info ("useless spolynomials: "
	^string_of_int (m-List.length lr)^"\n");
  info ("useful spolynomials: "
	^string_of_int (List.length lr)^"\n");
  lr

let theoremedeszeros lpol p =
  let t1 = Unix.gettimeofday() in
  let m = !nvars in
  let (lp0,p,cert) = in_ideal m lpol p in
  let lpc = List.rev !poldepcontent in
  info ("time: "^Format.sprintf "@[%10.3f@]s\n" (Unix.gettimeofday ()-.t1));
  (cert,lp0,p,lpc)

open Ideal

let theoremedeszeros_termes lp =
  nvars:=0;(* mise a jour par term_pol_sparse *)
  List.iter set_nvars_term  lp;
  match lp with
  | Const (Int sugarparam)::Const (Int nparam)::lp ->
      ((match sugarparam with
      |0 -> info "computation without sugar\n";
	  lexico:=false;
	  sugar_flag := false;
	  divide_rem_with_critical_pair := false
      |1 -> info "computation with sugar\n";
	  lexico:=false;
	  sugar_flag := true;
	  divide_rem_with_critical_pair := false
      |2 -> info "ordre lexico computation without sugar\n";
	  lexico:=true;
	  sugar_flag := false;
	  divide_rem_with_critical_pair := false
      |3 -> info "ordre lexico computation with sugar\n";
	  lexico:=true;
	  sugar_flag := true;
	  divide_rem_with_critical_pair := false
      |4 -> info "computation without sugar, division by pairs\n";
	  lexico:=false;
	  sugar_flag := false;
	  divide_rem_with_critical_pair := true
      |5 -> info "computation with sugar, division by pairs\n";
	  lexico:=false;
	  sugar_flag := true;
	  divide_rem_with_critical_pair := true
      |6 -> info "ordre lexico computation without sugar, division by pairs\n";
	  lexico:=true;
	  sugar_flag := false;
	  divide_rem_with_critical_pair := true
      |7 -> info "ordre lexico computation with sugar, division by pairs\n";
	  lexico:=true;
	  sugar_flag := true;
	  divide_rem_with_critical_pair := true
      | _ -> error "nsatz: bad parameter"
       );
      let m= !nvars in
      let lvar=ref [] in
      for i=m downto 1 do lvar:=["x"^(string_of_int i)^""]@(!lvar); done;
      lvar:=["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"] @ (!lvar); (* pour macaulay *)
      name_var:=!lvar;
      let lp = List.map (term_pol_sparse nparam) lp in
      match lp with
      | [] -> assert false
      | p::lp1 ->
	  let lpol = List.rev lp1 in
	  let (cert,lp0,p,_lct) = theoremedeszeros lpol p in
          info "cert ok\n";
	  let lc = cert.last_comb::List.rev cert.gb_comb in
	  match remove_zeros (fun x -> equal x zeroP) lc with
	  | [] -> assert false
	  | (lq::lci) ->
	      (* lci commence par les nouveaux polynomes *)
	      let m= !nvars in
	      let c = pol_sparse_to_term m (polconst m cert.coef) in
	      let r = Pow(Zero,cert.power) in
	      let lci = List.rev lci in
	      let lci = List.map (List.map (pol_sparse_to_term m)) lci in
	      let lq = List.map (pol_sparse_to_term m) lq in
	      info ("number of parametres: "^string_of_int nparam^"\n");
	      info "term computed\n";
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
  info "term computed\n";
  res

let return_term t =
  let a =
    mkApp(gen_constant "CC" ["Init";"Logic"] "refl_equal",[|tllp ();t|]) in
  generalize [a]

let nsatz_compute t =
  let lpol =
    try nsatz t
    with Ideal.NotInIdeal ->
      error "nsatz cannot solve this problem" in
  return_term lpol

TACTIC EXTEND nsatz_compute
| [ "nsatz_compute"  constr(lt) ] -> [ Proofview.V82.tactic (nsatz_compute lt) ]
END


