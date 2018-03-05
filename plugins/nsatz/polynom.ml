(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Recursive polynomials: R[x1]...[xn]. *)
open Util
open Utile

(* 1. Coefficients: R *)

module type Coef = sig
  type t
  val equal : t -> t -> bool
  val lt : t -> t -> bool
  val le : t -> t -> bool
  val abs : t -> t
  val plus : t -> t -> t
  val mult : t -> t -> t
  val sub : t -> t -> t
  val opp : t -> t
  val div : t -> t -> t
  val modulo : t -> t -> t
  val puis : t -> int -> t
  val pgcd : t -> t -> t

  val hash : t -> int
  val of_num : Num.num -> t
  val to_string : t -> string
end

module type S = sig
  type coef
  type variable = int
  type t = Pint of coef | Prec of variable * t array

  val of_num : Num.num -> t
  val x : variable -> t
  val monome : variable -> int -> t
  val is_constantP : t -> bool
  val is_zero : t -> bool

  val max_var_pol : t -> variable
  val max_var_pol2 : t -> variable
  val max_var : t array -> variable
  val equal : t -> t -> bool
  val norm : t -> t
  val deg : variable -> t -> int
  val deg_total : t -> int
  val copyP : t -> t
  val coef : variable -> int -> t -> t

  val plusP : t -> t -> t
  val content : t -> coef
  val div_int : t -> coef -> t
  val vire_contenu : t -> t
  val vars : t -> variable list
  val int_of_Pint : t -> coef
  val multx : int -> variable -> t -> t
  val multP : t -> t -> t
  val deriv : variable -> t -> t
  val oppP : t -> t
  val moinsP : t -> t -> t
  val puisP : t -> int -> t
  val ( @@ ) : t -> t -> t
  val ( -- ) : t -> t -> t
  val ( ^^ ) : t -> int -> t
  val coefDom : variable -> t -> t
  val coefConst : variable -> t -> t
  val remP : variable -> t -> t
  val coef_int_tete : t -> coef
  val normc : t -> t
  val coef_constant : t -> coef
  val univ : bool ref
  val string_of_var : int -> string
  val nsP : int ref
  val to_string : t -> string
  val printP : t -> unit
  val print_tpoly : t array -> unit
  val print_lpoly : t list -> unit
  val quo_rem_pol : t -> t -> variable -> t * t
  val div_pol : t -> t -> variable -> t
  val divP : t -> t -> t
  val div_pol_rat : t -> t -> bool
  val pseudo_div : t -> t -> variable -> t * t * int * t
  val pgcdP : t -> t -> t
  val pgcd_pol : t -> t -> variable -> t
  val content_pol : t -> variable -> t
  val pgcd_coef_pol : t -> t -> variable -> t
  val pgcd_pol_rec : t -> t -> variable -> t
  val gcd_sub_res : t -> t -> variable -> t
  val gcd_sub_res_rec : t -> t -> t -> t -> int -> variable -> t
  val lazard_power : t -> t -> int -> variable -> t
  val hash : t -> int
  module Hashpol : Hashtbl.S with type key=t
end

(***********************************************************************
  2. Type of polynomials, operations.
*)
module Make (C:Coef) = struct

type coef = C.t
let coef_of_int i = C.of_num (Num.Int i)
let coef0 = coef_of_int 0
let coef1 = coef_of_int 1

type variable = int

type t =
    Pint of coef                    (* constant polynomial *)
  | Prec of variable * (t array)    (* coefficients, increasing degree *)

(* by default, operations work with normalized polynomials:
- variables are positive integers
- coefficients of a polynomial in x only use variables < x
- no zero coefficient at beginning
- no Prec(x,a) where a is constant in x
*)

(* constant polynomials *)
let of_num x = Pint (C.of_num x)
let cf0 = of_num (Num.Int 0)
let cf1 = of_num (Num.Int 1)

(* nth variable *)
let x n = Prec (n,[|cf0;cf1|])

(* create v^n *)
let monome v n =
  match n with
      0->Pint coef1;
    |_->let tmp = Array.make (n+1) (Pint coef0) in
        tmp.(n)<-(Pint coef1);
        Prec (v, tmp)

let is_constantP = function
    Pint _ -> true
  | Prec _ -> false

let int_of_Pint = function
    Pint x -> x
  | _ -> failwith "non"

let is_zero p =
  match p with Pint n -> if C.equal n coef0 then true else false |_-> false

let max_var_pol p =
  match p with
      Pint _ -> 0
    |Prec(x,_) -> x

(* p not normalized *)
let rec max_var_pol2 p =
  match p with
      Pint _ -> 0
    |Prec(v,c)-> Array.fold_right (fun q m -> max (max_var_pol2 q) m) c v

let max_var l = Array.fold_right (fun p m -> max (max_var_pol2 p) m) l 0

(* equality between polynomials *)

let rec equal p q =
  match (p,q) with
      (Pint a,Pint b) -> C.equal a b
    |(Prec(x,p1),Prec(y,q1)) -> (Int.equal x y) && Array.for_all2 equal p1 q1
    | (_,_) -> false

(* normalize polynomial: remove head zeros, coefficients are normalized
   if constant, returns the coefficient
*)

let norm p = match p with
    Pint _ -> p
  |Prec (x,a)->
     let d = (Array.length a -1) in
     let n = ref d in
       while !n>0 && (equal a.(!n) (Pint coef0)) do
	 n:=!n-1;
       done;
       if !n<0 then Pint coef0
       else if Int.equal !n 0 then a.(0)
       else if Int.equal !n d then p
       else (let b=Array.make (!n+1) (Pint coef0) in
               for i=0 to !n do b.(i)<-a.(i);done;
               Prec(x,b))


(* degree in v, v >= max var of p *)
let deg v p =
  match p with
      Prec(x,p1) when Int.equal x v -> Array.length p1 -1
    |_ -> 0


(* total degree *)
let rec deg_total p =
  match p with
      Prec (x,p1) -> let d = ref 0 in
        Array.iteri (fun i q -> d:= (max !d (i+(deg_total q)))) p1;
        !d
    |_ -> 0

let rec copyP p =
  match p with
      Pint i -> Pint i
    |Prec(x,q) -> Prec(x,Array.map copyP q)

(* coefficient of degree i in v, v >= max var of p *)
let coef v i p =
  match p with
      Prec (x,p1) when Int.equal x v  -> if i<(Array.length p1) then p1.(i) else Pint coef0
    |_ -> if Int.equal i 0 then p else Pint coef0

(* addition *)

let rec plusP p q =
  let res =
    (match (p,q) with
	 (Pint a,Pint b) -> Pint (C.plus a b)
       |(Pint a, Prec (y,q1)) -> let q2=Array.map copyP q1 in
           q2.(0)<- plusP p q1.(0);
           Prec (y,q2)
       |(Prec (x,p1),Pint b) -> let p2=Array.map copyP p1 in
           p2.(0)<- plusP p1.(0) q;
           Prec (x,p2)
       |(Prec (x,p1),Prec (y,q1)) ->
          if x<y then (let q2=Array.map copyP q1 in
                         q2.(0)<- plusP p q1.(0);
                         Prec (y,q2))
          else if x>y then (let p2=Array.map copyP p1 in
                              p2.(0)<- plusP p1.(0) q;
                              Prec (x,p2))
          else
            (let n=max (deg x p) (deg x q) in
             let r=Array.make (n+1) (Pint coef0) in
               for i=0 to n do
                 r.(i)<- plusP (coef x i p) (coef x i q);
               done;
               Prec(x,r)))
  in norm res


(* content, positive integer *)
let rec content p =
  match p with
      Pint a -> C.abs a
    | Prec (x ,p1) ->
       Array.fold_left C.pgcd coef0 (Array.map content p1)

let rec div_int p a=
  match p with
      Pint b -> Pint (C.div b a)
    | Prec(x,p1) -> Prec(x,Array.map (fun x -> div_int x a) p1)

let vire_contenu p =
  let c = content p in
    if C.equal c coef0 then p else div_int p c

(* sorted list of variables of a polynomial *)

let rec vars=function
    Pint _->[]
  | Prec (x,l)->(List.flatten ([x]::(List.map vars (Array.to_list l))))


(* multiply p by v^n, v >= max_var p *)
let multx n v p =
  match p with
      Prec (x,p1) when Int.equal x v -> let p2= Array.make ((Array.length p1)+n) (Pint coef0) in
        for i=0 to (Array.length p1)-1 do
          p2.(i+n)<-p1.(i);
        done;
        Prec (x,p2)
    |_ -> if equal p (Pint coef0) then (Pint coef0)
       else (let p2=Array.make (n+1) (Pint coef0) in
               p2.(n)<-p;
               Prec (v,p2))

(* product *)
let rec multP p q =
  match (p,q) with
      (Pint a,Pint b) -> Pint (C.mult a b)
    |(Pint a, Prec (y,q1)) ->
       if C.equal a coef0 then Pint coef0
       else let q2 = Array.map (fun z-> multP p z) q1 in
         Prec (y,q2)

    |(Prec (x,p1), Pint b) ->
       if C.equal b coef0 then Pint coef0
       else let p2 = Array.map (fun z-> multP z q) p1 in
         Prec (x,p2)
    |(Prec (x,p1), Prec(y,q1)) ->
       if x<y
       then (let q2 = Array.map (fun z-> multP p z) q1 in
               Prec (y,q2))
       else if x>y
       then (let p2 = Array.map (fun z-> multP z q) p1 in
               Prec (x,p2))
       else Array.fold_left plusP (Pint coef0)
         (Array.mapi (fun i z-> (multx i x (multP z q))) p1)



(* derive p with variable v, v >= max_var p *)
let deriv v p =
  match p with
      Pint a -> Pint coef0
    | Prec(x,p1) when Int.equal x v ->
       let d = Array.length p1 -1 in
         if Int.equal d 1 then p1.(1)
         else
           (let p2 = Array.make d (Pint coef0) in
              for i=0 to d-1 do
		p2.(i)<- multP (Pint (coef_of_int (i+1))) p1.(i+1);
              done;
              Prec (x,p2))
    | Prec(x,p1)-> Pint coef0


(* opposite *)
let rec oppP p =
  match p with
      Pint a -> Pint (C.opp a)
    |Prec(x,p1) -> Prec(x,Array.map oppP p1)

let moinsP p q=plusP p (oppP q)

let rec puisP p n = match n with
    0 -> cf1
  |_ -> (multP p (puisP p (n-1)))


(* infix notations *)
(*let (++) a b = plusP a b
*)
let (@@) a b = multP a b

let (--) a b = moinsP a b

let (^^) a b = puisP a b


(* leading coefficient in v,  v>= max_var p *)

let coefDom v p= coef v (deg v p) p

let coefConst v p = coef v 0 p

(* tail of a polynomial *)
let remP v p =
  moinsP p (multP (coefDom v p) (puisP (x v) (deg v p)))


(* first interger coefficient of p *)
let rec coef_int_tete p =
  let v = max_var_pol p in
    if v>0
    then coef_int_tete (coefDom v p)
    else (match p with | Pint a -> a |_ -> assert false)


(* divide by the content and make the head int coef positive *)
let normc p =
  let p = vire_contenu p in
  let a = coef_int_tete p in
    if C.le coef0 a then p else oppP p


(* constant coef of normalized polynomial *)
let rec coef_constant p =
  match p with
      Pint a->a
    |Prec(_,q)->coef_constant q.(0)


(***********************************************************************
  3. Printing polynomials.
*)

(* if univ = false, we use x,y,z,a,b,c,d... as variables, else x1,x2,...
*)
let univ=ref true

let string_of_var x=
  if !univ then
    "u"^(string_of_int x)
  else
    if x<=3 then String.make 1 (Char.chr(x+(Char.code 'w')))
    else String.make 1 (Char.chr(x-4+(Char.code 'a')))

let nsP = ref 0

let rec string_of_Pcut p =
  if (!nsP)<=0
  then "..."
  else
  match p with
  |Pint a-> nsP:=(!nsP)-1;
      if C.le coef0 a
      then C.to_string a
      else "("^(C.to_string a)^")"
  |Prec (x,t)->
      let v=string_of_var x
      and s=ref ""
      and sp=ref "" in
    let st0 = string_of_Pcut t.(0) in
      if not (String.equal st0 "0")
      then s:=st0;
    let fin = ref false in
    for i=(Array.length t)-1 downto 1 do
      if (!nsP)<0
      then (sp:="...";
	    if not (!fin) then s:=(!s)^"+"^(!sp);
	    fin:=true)
      else (
	let si=string_of_Pcut  t.(i) in
	sp:="";
	if Int.equal i 1
	then (
	  if not (String.equal si "0")
	  then (nsP:=(!nsP)-1;
		if String.equal si "1"
		then sp:=v
		else
		  (if (String.contains si '+')
		  then sp:="("^si^")*"^v
		  else sp:=si^"*"^v)))
	else (
	  if not (String.equal si "0")
	  then (nsP:=(!nsP)-1;
		if String.equal si "1"
		then sp:=v^"^"^(string_of_int i)
		else (if (String.contains si '+')
		then sp:="("^si^")*"^v^"^"^(string_of_int i)
		else  sp:=si^"*"^v^"^"^(string_of_int i))));
	if not (String.is_empty !sp) && not (!fin)
	then (nsP:=(!nsP)-1;
	      if String.is_empty !s
	      then s:=!sp
	      else s:=(!s)^"+"^(!sp)));
    done;
    if String.is_empty !s then (nsP:=(!nsP)-1;
		   (s:="0"));
    !s

let to_string p =
  nsP:=20;
  string_of_Pcut p

let printP p = Format.printf "@[%s@]" (to_string p)

let print_tpoly lp =
  let s = ref "\n{ " in
    Array.iter (fun p -> s:=(!s)^(to_string p)^"\n") lp;
    prt0 ((!s)^"}")

let print_lpoly lp = print_tpoly (Array.of_list lp)

(***********************************************************************
  4. Exact division of polynomials.
*)

(* return (s,r) s.t. p = s*q+r *)
let rec quo_rem_pol p q x =
  if Int.equal x 0
  then (match (p,q) with
          |(Pint a, Pint b) ->
	     if C.equal (C.modulo a b) coef0
             then (Pint (C.div a b), cf0)
             else failwith "div_pol1"
	  |_ -> assert false)
  else
    let m = deg x q in
    let b = coefDom x q in
    let q1 = remP x q in (* q = b*x^m+q1 *)
    let r = ref p in
    let s = ref cf0 in
    let continue =ref true in
      while (!continue) && (not (equal !r cf0)) do
	let n = deg x !r in
	  if n<m
	  then continue:=false
	  else (
            let a = coefDom x !r in
            let p1 = remP x !r in  (* r = a*x^n+p1 *)
            let c = div_pol a b (x-1) in  (* a = c*b *)
	    let s1 = c @@ ((monome x (n-m))) in
              s:= plusP (!s) s1;
              r:= p1 -- (s1 @@ q1);
          )
      done;
      (!s,!r)

(* returns quotient p/q if q divides p, else fails *)
and div_pol p q x =
  let (s,r) = quo_rem_pol p q x in
    if equal r cf0
    then s
    else  failwith ("div_pol:\n"
		   ^"p:"^(to_string p)^"\n"
		   ^"q:"^(to_string q)^"\n"
		   ^"r:"^(to_string r)^"\n"
		   ^"x:"^(string_of_int x)^"\n"
		   )
let divP p q=
  let x = max (max_var_pol p) (max_var_pol q) in
  div_pol p q x

let div_pol_rat p q=
  let x = max (max_var_pol p) (max_var_pol q) in
  try
    let r = puisP (Pint(coef_int_tete q)) (1+(deg x p)-(deg x q)) in
    let _ = div_pol (multP p r) q x in
    true
  with Failure _ -> false

(***********************************************************************
  5. Pseudo-division and gcd with subresultants.
*)

(* pseudo division :
   q = c*x^m+q1
   retruns (r,c,d,s) s.t. c^d*p = s*q + r.
*)

let pseudo_div p q x =
  match q with
      Pint _ -> (cf0, q,1, p)
    | Prec (v,q1) when not (Int.equal x v) -> (cf0, q,1, p)
    | Prec (v,q1) ->
	(
	  (*  pr "pseudo_division: c^d*p = s*q + r";*)
	  let delta = ref 0 in
	  let r = ref p in
	  let c = coefDom x q in
	  let q1 = remP x q in
	  let d' = deg x q in
	  let s = ref cf0 in
	    while (deg x !r)>=(deg x q) do
	      let d = deg x !r in
	      let a = coefDom x !r in
	      let r1=remP x !r in
	      let u = a @@ ((monome x (d-d'))) in
		r:=(c @@ r1) -- (u @@ q1);
		s:=plusP (c @@ (!s)) u;
		delta := (!delta) + 1;
	    done;
	    (*
	      pr ("deg d: "^(string_of_int (!delta))^", deg c: "^(string_of_int (deg_total c)));
	      pr ("deg r:"^(string_of_int (deg_total !r)));
	    *)
	    (!r,c,!delta, !s)
	)

(* gcd with subresultants *)

let rec pgcdP p q =
  let x = max (max_var_pol p) (max_var_pol q) in
    pgcd_pol p q x

and pgcd_pol p q x =
  pgcd_pol_rec p q x

and content_pol p x =
  match p with
      Prec(v,p1) when Int.equal v x ->
        Array.fold_left (fun a b -> pgcd_pol_rec a b (x-1)) cf0 p1
    | _ -> p

and pgcd_coef_pol c p x =
  match p with
      Prec(v,p1) when Int.equal x v ->
        Array.fold_left (fun a b -> pgcd_pol_rec a b (x-1)) c  p1
    |_ -> pgcd_pol_rec c p (x-1)

and pgcd_pol_rec p q x =
 match (p,q) with
	(Pint a,Pint b) -> Pint (C.pgcd (C.abs a) (C.abs b))
      |_ ->
	  if equal p cf0
	  then q
	  else if equal q cf0
	  then p
	  else if Int.equal (deg x q) 0
	  then pgcd_coef_pol q p x
	  else if Int.equal (deg x p) 0
	  then pgcd_coef_pol p q x
	  else (
	    let a = content_pol p x in
	    let b = content_pol q x in
	    let c = pgcd_pol_rec a b (x-1) in
	    pr (string_of_int x);
	    let p1 = div_pol p c x in
	    let q1 = div_pol q c x in
	    let r = gcd_sub_res p1 q1 x in
	    let cr = content_pol r x in
	    let res = c @@ (div_pol r cr x) in
	    res
	   )

(* Sub-résultants:

   ai*Ai = Qi*Ai+1 + bi*Ai+2

   deg Ai+2 < deg Ai+1

   Ai = ci*X^ni + ...
   di = ni - ni+1

   ai = (- ci+1)^(di + 1)
   b1 = 1
   bi = ci*si^di  si i>1

   s1 = 1
   si+1 = ((ci+1)^di*si)/si^di

*)
and gcd_sub_res p q x =
  if equal q cf0
  then p
  else
    let d = deg x p in
    let d' = deg x q in
      if d<d'
      then gcd_sub_res q p x
      else
	let delta = d-d' in
	let c' = coefDom x q in
	let r = snd (quo_rem_pol (((oppP c')^^(delta+1))@@p) (oppP q) x) in
	  gcd_sub_res_rec q r (c'^^delta) c' d' x

and gcd_sub_res_rec p q s c d x =
  if equal q cf0
  then p
  else (
    let d' = deg x q in
    let c' = coefDom x q in
    let delta = d-d' in
    let r = snd (quo_rem_pol (((oppP c')^^(delta+1))@@p) (oppP q) x) in
    let s'= lazard_power c' s delta x in
      gcd_sub_res_rec q (div_pol r (c @@ (s^^delta)) x) s' c' d' x
  )

and lazard_power c s d x =
  let res = ref c in
    for _i = 1 to d - 1 do
      res:= div_pol ((!res)@@c) s x;
    done;
    !res

(* memoizations *)

let rec hash = function
    Pint a -> (C.hash a)
  | Prec (v,p) ->
      Array.fold_right (fun q h -> h + hash q) p 0

module Hashpol = Hashtbl.Make(
  struct
    type poly = t
    type t = poly
    let equal = equal
    let hash = hash
  end)

end
