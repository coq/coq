(************************************************************************)

(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*
  Polynomes récursifs: Z[x1]...[xn].
*)
open Utile
open Util

(***********************************************************************
  1. Opérations sur les coefficients.
*)

open Big_int

type coef = big_int
let coef_of_int = big_int_of_int
let coef_of_num = Num.big_int_of_num
let num_of_coef = Num.num_of_big_int
let eq_coef = eq_big_int
let lt_coef = lt_big_int
let le_coef = le_big_int
let abs_coef = abs_big_int
let plus_coef =add_big_int
let mult_coef = mult_big_int
let sub_coef = sub_big_int
let opp_coef = minus_big_int
let div_coef = div_big_int
let mod_coef = mod_big_int
let coef0 = coef_of_int 0
let coef1 = coef_of_int 1
let string_of_coef = string_of_big_int
let int_of_coef x = int_of_big_int x
let hash_coef x =
  try (int_of_big_int x)
  with _-> 1
let puis_coef = power_big_int_positive_int 

(*
type coef = Entiers.entiers
let coef_of_int = Entiers.ent_of_int
let coef_of_num x = (* error if x is a ratio *)
  Entiers.ent_of_string
    (Big_int.string_of_big_int (Num.big_int_of_num x))
let num_of_coef x = Num.num_of_string (Entiers.string_of_ent x)
let eq_coef = Entiers.eq_ent
let lt_coef = Entiers.lt_ent
let le_coef = Entiers.le_ent
let abs_coef = Entiers.abs_ent
let plus_coef =Entiers.add_ent
let mult_coef = Entiers.mult_ent
let sub_coef = Entiers.moins_ent
let opp_coef = Entiers.opp_ent
let div_coef = Entiers.div_ent
let mod_coef = Entiers.mod_ent
let coef0 = Entiers.ent0
let coef1 = Entiers.ent1
let string_of_coef = Entiers.string_of_ent
let int_of_coef x = Entiers.int_of_ent x 
let hash_coef x =Entiers.hash_ent x
let signe_coef = Entiers.signe_ent

let rec puis_coef p n = match n with
    0 -> coef1
  |_ -> (mult_coef p (puis_coef p (n-1)))
*)

(* a et b positifs, résultat positif *)
let rec pgcd a b = 
  if eq_coef b coef0 
  then a
  else if lt_coef a b then pgcd b a else pgcd b (mod_coef a b)


(* signe du pgcd = signe(a)*signe(b) si non nuls. *)
let pgcd2 a b = 
  if eq_coef a coef0 then b
  else if eq_coef b coef0 then a
  else let c = pgcd (abs_coef a) (abs_coef b) in
    if ((lt_coef coef0 a)&&(lt_coef b coef0))
      ||((lt_coef coef0 b)&&(lt_coef a coef0))
    then opp_coef c else c

(***********************************************************************
  2. Le type des polynômes, operations.
*)

type variable = int

type poly = 
    Pint of coef                       (* polynome constant *)
  | Prec of variable * (poly array)    (* coefficients par degre croissant *)

(* sauf mention du contraire, les opérations ne concernent que des 
   polynomes normalisés:
   - les variables sont des entiers strictement positifs.
   - les coefficients d'un polynome en x ne font intervenir que des variables < x.
   - pas de coefficient nul en tête.
   - pas de Prec(x,a) ou a n'a qu'un element (constant en x).
*)

(* Polynômes constant *)
let cf x = Pint (coef_of_int x)
let cf0 = (cf 0)
let cf1 = (cf 1)
	    
(* la n-ième variable *)
let x n = Prec (n,[|cf0;cf1|])

(* variable max *)
let max_var_pol p = 
  match p with 
      Pint _ -> 0
    |Prec(x,_) -> x


(* p n'est pas forcément normalisé *)
let rec max_var_pol2 p =
  match p with 
      Pint _ -> 0
    |Prec(v,c)-> Array.fold_right (fun q m -> max (max_var_pol2 q) m) c v


(* variable max d'une liste de polynômes *)
let rec max_var l = Array.fold_right (fun p m -> max (max_var_pol2 p) m) l 0


(* Egalité de deux polynômes 
   On ne peut pas utiliser = car elle ne marche pas sur les Big_int.
*)
let rec eqP p q =
  match (p,q) with 
      (Pint a,Pint b) -> eq_coef a b
    |(Prec(x,p1),Prec(y,q1)) ->
       if x<>y then false
       else if (Array.length p1)<>(Array.length q1) then false
       else (try (Array.iteri (fun i a -> if not (eqP a q1.(i))
			       then failwith "raté")
		    p1;
		  true)
	     with _ -> false)
    | (_,_) -> false

(* vire les zéros de tête d'un polynôme non normalisé, dont les coefficients
   sont supposés normalisés.
   si constant, rend le coef constant.
*)
	
let rec norm p = match p with
    Pint _ -> p
  |Prec (x,a)->
     let d = (Array.length a -1) in
     let n = ref d in 
       while !n>0 && (eqP a.(!n) (Pint coef0)) do
	 n:=!n-1;
       done;
       if !n<0 then Pint coef0
       else if !n=0 then a.(0) 
       else if !n=d then p
       else (let b=Array.create (!n+1) (Pint coef0) in
               for i=0 to !n do b.(i)<-a.(i);done;
               Prec(x,b))


(* degré en la variable v du polynome p, v >= max var de p *)
let rec deg v p =
  match p with 
      Prec(x,p1) when x=v -> Array.length p1 -1
    |_ -> 0


(* degré total *)
let rec deg_total p =
  match p with 
      Prec (x,p1) -> let d = ref 0 in
        Array.iteri (fun i q -> d:= (max !d (i+(deg_total q)))) p1;
        !d
    |_ -> 0


(* copie le polynome *)
let rec copyP p =
  match p with
      Pint i -> Pint i
    |Prec(x,q) -> Prec(x,Array.map copyP q)


(* coefficient de degre i en v, v >= max var de p *)
let coef v i p =
  match p with 
      Prec (x,p1) when x=v  -> if i<(Array.length p1) then p1.(i) else Pint coef0
    |_ -> if i=0 then p else Pint coef0


let rec plusP p q =
  let res =
    (match (p,q) with
	 (Pint a,Pint b) -> Pint (plus_coef a b)
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
             let r=Array.create (n+1) (Pint coef0) in
               for i=0 to n do
                 r.(i)<- plusP (coef x i p) (coef x i q);
               done;
               Prec(x,r))) 
  in norm res


(* contenu entier positif *)
let rec content p =
  match p with
      Pint a -> abs_coef a
    | Prec (x ,p1) ->
       Array.fold_left pgcd coef0 (Array.map content p1)


(* divise tous les coefficients de p par l'entier a*)
let rec div_int p a=
  match p with
      Pint b -> Pint (div_coef b a)
    | Prec(x,p1) -> Prec(x,Array.map (fun x -> div_int x a) p1)

(* divise p par son contenu entier positif. *)
let vire_contenu p =
  let c = content p in
    if eq_coef c coef0 then p else div_int p c


(* liste triee des variables impliquees dans un poly *)
let rec vars=function
    Pint _->[]
  | Prec (x,l)->(List.flatten ([x]::(List.map vars (Array.to_list l))))


(* conversion d'un poly cst en entier*)
let int_of_Pint=function 
    (Pint x)->x
  |_->failwith "non"


(* multiplie p par v^n, v >= max_var p *)
let rec multx n v p =
  match p with
      Prec (x,p1) when x=v -> let p2= Array.create ((Array.length p1)+n) (Pint coef0) in
        for i=0 to (Array.length p1)-1 do
          p2.(i+n)<-p1.(i);
        done;
        Prec (x,p2)
    |_ -> if p = (Pint coef0) then (Pint coef0) 
       else (let p2=Array.create (n+1) (Pint coef0) in 
               p2.(n)<-p;
               Prec (v,p2))


(* produit de 2 polynomes *)
let rec multP p q =
  match (p,q) with
      (Pint a,Pint b) -> Pint (mult_coef a b)
    |(Pint a, Prec (y,q1)) ->
       if eq_coef a coef0 then Pint coef0
       else let q2 = Array.map (fun z-> multP p z) q1 in
         Prec (y,q2)
           
    |(Prec (x,p1), Pint b) ->
       if eq_coef b coef0 then Pint coef0
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



(* derive p par rapport a la variable v, v >= max_var p *)
let rec deriv v p =
  match p with 
      Pint a -> Pint coef0
    |Prec(x,p1) when x=v ->
       let d = Array.length p1 -1 in
         if d=1 then p1.(1)
         else
           (let p2 = Array.create d (Pint coef0) in
              for i=0 to d-1 do
		p2.(i)<- multP (Pint (coef_of_int (i+1))) p1.(i+1);
              done;
              Prec (x,p2))
    |Prec(x,p1)-> Pint coef0


(* opposé de p *)
let rec oppP p =
  match p with 
      Pint a -> Pint (opp_coef a)
    |Prec(x,p1) -> Prec(x,Array.map oppP p1)


(* différence de deux polynômes. *)
let moinsP p q=plusP p (oppP q)

let rec puisP p n = match n with
    0 -> cf1
  |_ -> (multP p (puisP p (n-1)))


(* notations infixes...*)
(*let (++) a b = plusP a b
*)
let (@@) a b = multP a b

let (--) a b = moinsP a b

let (^^) a b = puisP a b


(* coefficient dominant de p,  v>= max_var p *)

let coefDom v p= coef v (deg v p) p


let coefConst v p = coef v 0 p

(* queue d'un polynôme *)
let remP v p =
  moinsP p (multP (coefDom v p) (puisP (x v) (deg v p)))


(* premier coef entier de p *)
let rec coef_int_tete p =
  let v = max_var_pol p in
    if v>0
    then coef_int_tete (coefDom v p)
    else (match p with | Pint a -> a |_ -> assert false)


(* divise par le contenu, et rend positif le premier coefficient entier *)
let normc p =
  let p = vire_contenu p in
  let a = coef_int_tete p in
    if le_coef coef0 a then p else oppP p


(* teste si un polynome est constant *)
let is_constantP p = match p with
    Pint _ -> true
  |Prec (_,_) -> false


(* teste si un poly est identiquement nul *)
let is_zero p =
  match p with Pint n -> if eq_coef n coef0 then true else false |_-> false

(* crée rapidement v^n *)
let monome v n = 
  match n with
      0->Pint coef1;
    |_->let tmp = Array.create (n+1) (Pint coef0) in
        tmp.(n)<-(Pint coef1);
        Prec (v, tmp)


(*coef constant d'un polynome normalise*)
let rec coef_constant p =
  match p with
      Pint a->a
    |Prec(_,q)->coef_constant q.(0)
       

(***********************************************************************
  3. Affichage des polynômes.
*)

(* si univ=false, on utilise x,y,z,a,b,c,d... comme noms de variables,
   sinon, x1,x2,...
*)
let univ=ref true 

(* joli jusqu'a trois variables -- sinon changer le 'w' *)
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
      if le_coef coef0 a
      then string_of_coef a
      else "("^(string_of_coef a)^")"
  |Prec (x,t)->
      let v=string_of_var x
      and s=ref ""
      and sp=ref "" in
    let st0 = string_of_Pcut t.(0) in
      if st0<>"0"
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
	if i=1
	then (
	  if si<>"0"
	  then (nsP:=(!nsP)-1;
		if si="1"
		then sp:=v
		else
		  (if (String.contains si '+')
		  then sp:="("^si^")*"^v
		  else sp:=si^"*"^v)))
	else (
	  if si<>"0"
	  then (nsP:=(!nsP)-1;
		if si="1"
		then sp:=v^"^"^(string_of_int i)
		else (if (String.contains si '+')
		then sp:="("^si^")*"^v^"^"^(string_of_int i)
		else  sp:=si^"*"^v^"^"^(string_of_int i))));
	if !sp<>"" && not (!fin)
	then (nsP:=(!nsP)-1;
	      if !s=""
	      then s:=!sp
	      else s:=(!s)^"+"^(!sp)));
    done;
    if !s="" then (nsP:=(!nsP)-1;
		   (s:="0"));
    !s
      
let string_of_P p =
  nsP:=20;
  string_of_Pcut p 

let printP p = Format.printf "@[%s@]" (string_of_P p)


let print_tpoly lp =
  let s = ref "\n{ " in
    Array.iter (fun p -> s:=(!s)^(string_of_P p)^"\n") lp;
    prt0 ((!s)^"}")


let print_lpoly lp = print_tpoly (Array.of_list lp)

(* #install_printer printP *)

(***********************************************************************
  4. Division exacte de polynômes.
*)

(* rend (s,r) tel que p = s*q+r *)
let rec quo_rem_pol p q x =
  if x=0
  then (match (p,q) with 
          |(Pint a, Pint b) ->
	     if eq_coef (mod_coef a b) coef0 
             then (Pint (div_coef a b), cf 0)
             else failwith "div_pol1"
	  |_ -> assert false)
  else 
    let m = deg x q in
    let b = coefDom x q in
    let q1 = remP x q in (* q = b*x^m+q1 *)
    let r = ref p in
    let s = ref cf0 in
    let continue =ref true in
      while (!continue) && (not (eqP !r cf0)) do
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

(* echoue si q ne divise pas p, rend le quotient sinon *)
and div_pol p q x =
  let (s,r) = quo_rem_pol p q x in
    if eqP r cf0
    then s
    else  failwith ("div_pol:\n"
		   ^"p:"^(string_of_P p)^"\n"
		   ^"q:"^(string_of_P q)^"\n"
		   ^"r:"^(string_of_P r)^"\n"
		   ^"x:"^(string_of_int x)^"\n"
		   )


(* test de division exacte  de p par q mais constantes rationnels 
   à vérifier *)
let divP p q=
  let x = max (max_var_pol p) (max_var_pol q) in
  div_pol p q x

(* test de division exacte  de p par q mais constantes rationnels 
   à vérifier *)
let div_pol_rat p q=
  let x = max (max_var_pol p) (max_var_pol q) in
    try (let s = div_pol (multP p (puisP (Pint(coef_int_tete q))
				     (1+(deg x p) - (deg x q))))
		   q x in
         (*degueulasse, mais c 'est pour enlever un warning *)
         if s==s then true else true)
    with _ -> false




(***********************************************************************
  5. Pseudo-division et pgcd par les sous-résultants.
*)

(* pseudo division :
   q = c*x^m+q1
   rend (r,c,d,s) tels que c^d*p = s*q + r.
*)

let pseudo_div p q x =
  match q with
      Pint _ -> (cf0, q,1, p)
    | Prec (v,q1) when x<>v -> (cf0, q,1, p)
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


(* pgcd de polynômes par les sous-résultants *)


let rec pgcdP p q =
  let x = max (max_var_pol p) (max_var_pol q) in
    pgcd_pol p q x

and pgcd_pol p q x =
  pgcd_pol_rec p q x

and content_pol p x = 
  match p with
      Prec(v,p1) when v=x ->
        Array.fold_left (fun a b -> pgcd_pol_rec a b (x-1)) cf0 p1
    | _ -> p

and pgcd_coef_pol c p x =
  match p with
      Prec(v,p1) when x=v ->
        Array.fold_left (fun a b -> pgcd_pol_rec a b (x-1)) c  p1
    |_ -> pgcd_pol_rec c p (x-1)
    
  
and pgcd_pol_rec p q x =
 match (p,q) with
	(Pint a,Pint b) -> Pint (pgcd (abs_coef a) (abs_coef b))
      |_ ->
	  if eqP p cf0
	  then q
	  else if eqP q cf0
	  then p
	  else if (deg x q) = 0
	  then pgcd_coef_pol q p x
	  else if (deg x p) = 0
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

(* version avec memo*)
(*
and htblpgcd = Hashtbl.create 1000 

and pgcd_pol_rec p q x =
  try
    (let c = Hashtbl.find htblpgcd (p,q,x) in
    (*info "*";*)
    c)
  with _ ->
    (let c =  
      (match (p,q) with
	(Pint a,Pint b) -> Pint (pgcd (abs_coef a) (abs_coef b))
      |_ ->
	  if eqP p cf0
	  then q
	  else if eqP q cf0
	  then p
	  else if (deg x q) = 0
	  then pgcd_coef_pol q p x
	  else if (deg x p) = 0
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
      )
    in
    (*info "-";*)
    Hashtbl.add htblpgcd (p,q,x) c;
    c)
*)
(* Sous-résultants:

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
  if eqP q cf0
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
  if eqP q cf0 
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
    for i=1 to d-1 do
      res:= div_pol ((!res)@@c) s x;
    done;
    !res



(***********************************************************************
  6. Décomposition sans carré, factorisation.
*)

(*
  p = f1 f2^2 ... fn^r 
  p/\p'= f2 f3^2...fn^(r-1)
  sans_carré(p)= p/p/\p '= f1 f2 ... fn
*)

let sans_carre p x =
  if (deg x p) <= 1 then p
  else
    let p' = deriv x p in
      div_pol p (pgcd_pol p p' x) x


(* liste [f1;...;fn] *)
let facteurs p x =
  let rec facteurs_rec p q =
    if (deg x p)=0 then []
    else
      let p2 = div_pol p q x in
      let q2 = sans_carre p2 x in
        (div_pol q q2 x)::(facteurs_rec p2 q2)
  in facteurs_rec p (sans_carre p x)


(* liste [f1;f3;...] *)
let facteurs_impairs p x =
  let lf = Array.of_list (facteurs p x) in
  let r = ref [] in
    Array.iteri (fun i f ->
		   if ((i+1) mod 2)=1
                   then r:=(!r)@[f])
      lf;
    !r


(* décomposition sans carrés en toutes les variables *)


let hcontentP = Hashtbl.create 51

let prcontentP () =
  Hashtbl.iter (fun s c ->
                  prn (s^" -> "^(string_of_P c)))
    hcontentP


let contentP =
  memos "c" hcontentP (fun (p,x) -> ((string_of_P p)^":"^(string_of_int x)))
    (fun (p,x) -> content_pol p x)


(* Tables de hash et polynômes, mémo *)

(* dans le mli on écrit:
   module Hashpol:Hashtbl.S with type t = poly
*)

(* fonction de hachage des polynômes *)
let hashP p =
  let rec hP p =
    match p with
	Pint a -> (hash_coef a)
      |Prec (v,p) ->
         (Array.fold_right (fun q h -> h+(hP q)) p 0)
  in (* Hashtbl.hash *) (hP p) 


module Hashpol = Hashtbl.Make(
  struct
    type t = poly
    let equal = eqP
    let hash = hashP
  end)


let memoP s memoire fonction x =
  try (let v = Hashpol.find memoire x in pr s;v)
  with _ -> (pr "#";
	     let v = fonction x in
	       Hashpol.add memoire x v;
	       v)


let hfactorise = Hashpol.create 51

let prfactorise () =
  Hashpol.iter (fun p c ->
                  prn ((string_of_P p)^" -> ");
		  print_lpoly (List.flatten c))
    hfactorise

let factorise = 
  memoP "f" hfactorise 
    (fun p -> 
       let rec fact p x =
         if x=0
         then []
         else
           let c = contentP (p,x) in
           let q = div_pol p c x in
             (facteurs q x)::(fact c (x-1))
       in  fact p (max_var_pol p))


(* liste des facteurs sans carré non constants,
   avec coef entier de tête positif *)
let facteurs2 p =
  List.map normc
    (List.filter (fun q -> deg_total q >0)
       (List.flatten (factorise (normc p))))


(* produit des facteurs non constants d'une décomposition sans carré *)
let pol_de_factorisation lf =
  let p = ref cf1 in
    List.iter (fun lq ->
		 Array.iteri (fun i q ->  if (deg_total q)>0 then p:=(!p)@@(q^^(i+1)))
                 (Array.of_list lq))
      lf;
    !p


let set_of_array_facteurs tf =
  let h = Hashpol.create 51 in
    Array.iter (fun lf ->
		  List.iter (fun p -> if not (Hashpol.mem h p)
		             then Hashpol.add h p true)
		  lf)
      tf;
    let res = ref [] in
      Hashpol.iter (fun p _ -> res:=p::(!res)) h;
      !res


(* Factorise un tableau de polynômes f, et rend:
   - un tableau p de facteurs (degré>0, contenu entier 1, 
   coefficient de tête >0) obtenu par décomposition sans carrés 
   puis par division mutuelle
   - un tableau l de couples (constante, listes d'indices l)
   tels que f.(i) = l.(i)_1*Produit(p.(j), j dans l.(i)_2)
*)

(* on donne le tableau des facteurs de chaque poly de f *)
let factorise_tableauP2 f l1 =
  let x = max_var f in
    (* liste des facteurs sans carré des polynômes de f *)
    pr"<";
    let l1 = set_of_array_facteurs l1 in
      (* on les divise entre eux pour éventuellement trouver
	 de nouveaux facteurs *)
      pr "~";
      let l1 = Sort.list (fun p q -> (deg_total p)<(deg_total q)) l1 in
      let l1 = Array.of_list (facteurs_liste (fun a b -> div_pol a b x)
				(fun p -> (deg_total p)<1)
				l1) in
	(* puis on décompose les polynômes de f avec ces facteurs *)
	pr "-";
	let res = factorise_tableau (fun a b -> div_pol a b x)
                    (fun p -> eqP p cf0)
                    cf0
                    f l1 in
	  pr ">";
	  res
	    
let factorise_tableauP f =
  factorise_tableauP2 f (Array.map facteurs2 f)


(***********************************************************************
  7. Pseudo-division avec reste de même signe,
  en utilisant des polynômes non nuls pour diviser le reste.
*)

(* polynôme pair et coefficients positifs *)
let rec is_positif p =

  let res =
    match p with 
	Pint a -> le_coef coef0 a
      |Prec(x,p1) -> 
         (array_for_all is_positif p1)
	 && (try (Array.iteri (fun i c -> if (i mod 2)<>0 && not (eqP c cf0)
                               then failwith "pas pair")
		    p1;
                  true)
             with _ -> false)
  in
    res



let is_negatif p = is_positif (oppP p)


(* rend r tel que deg r < deg q et r a le signe de p en les racines de q.
   le coefficient dominant de q est non nul 
   quand les polynômes de coef_non_nuls le sont.
   (rs,cs,ds,ss,crs,lpos,lpol)= pseudo_euclide coef_non_nuls vect.(s-1) res.(s-1) v
*)
let pseudo_euclide coef_non_nuls p q x =
  let (r,c,d,s) = pseudo_div p q x in
    (*
      c^d * p = s*q + r, c = coef dominant de q
    *)
    (* vérification de la pseudo-division:
       let verif = ((c^^d)@@p)--(plusP (s@@q) r) in
       if not (eqP verif cf0)
       then (prn ("p:"^(string_of_P p));
       prn ("q:"^(string_of_P q));
       prn ("c:"^(string_of_P c));
       prn ("r:"^(string_of_P r));
       prn ("d:"^(string_of_int d));
       failwith "erreur dans la pseudo-division");
    *)

    (* pour autoriser des c pas positifs, il faut modifier algo14 et preuve3*)
      let r = if d mod 2 = 1 then c@@r else r in
      let s = if d mod 2 = 1 then c@@s else s in
      let d = if d mod 2 = 1 then d+1 else d in
    
    (* on encore  c^d * p = s*q + r, mais d pair *)
    if eqP r cf0
    then ((*pr "reste nul"; *) (r,c,d,s,cf1,[],[]))
    else (
      let r1 = vire_contenu r in
      let cr = div_pol r r1 x in
      let r = ref r1 in
	(* r a maintenant le même signe que p en les racines de q.*)
	(* on tente de diviser r par les polynômes de coef_non_nuls *)
      let lf = ref [] in (* liste de (facteur, puissance) *)
	List.iter (fun f ->
		     if (deg_total f)>0 && (max_var_pol f) < x
		     then (
                       let k = ref 0 in
			 (try (while true do
 				 let rd = div_pol !r f x in
				   (* verification de la division 
				      if not (eqP cf0 ((!r)--(f@@rd)))
				      then failwith "erreur dans la division";
				   *)
	   			   k:=(!k)+1;
				   r:=rd;
				   (*pr "+";*)
	 		       done)
			  with _ -> ());
	 		 lf:=(f,!k)::(!lf)))
          coef_non_nuls;
	(* il faut éventuellement remultiplier pour garder le signe de r *)
	let lpos = ref [] in 
	let lpol = ref [] in
	  List.iter (fun (f,k) ->
		       if k>0
		       then (
			 if (is_positif f)
			   (* f est positif, tout va bien *)
			 then lpos:=(f,k)::(!lpos)
			 else if (is_negatif f)
			   (* f est négatif *)
			 then (if k mod 2  = 1
				 (* k est impair *)
			       then (lpos:=(oppP f,k)::(!lpos);
				     r:=oppP (!r))
			       else lpos:=(f,k)::(!lpos))
			   (* on ne connaît pas le signe de f *)
			 else if k mod 2 = 0
			   (* k est pair, tout va bien *)
			 then lpol:=(f,k)::(!lpol)
			   (* k est impair *)
			 else  (lpol:=(f,k-1)::(!lpol);
				r:=multP (!r) f)))
            !lf;
	  (*
            pr ((* "------reste de même signe: "
	    ^(string_of_P c)
	    ^" variable: "^(string_of_int x)
	    ^" c:"^(string_of_int (deg_total c))
	    ^" d:"^(string_of_int d)
	    ^" deg(r)-deg(r0):"
	    ^*)(string_of_int ((deg_total !r)-(deg_total r0))));
	  *)
	  (* lpos = liste de (f,k) ou f est non nul positif, et f^k divise r0
	     lpol = liste de (f,k) ou f non nul, k est pair et f^k divise r0
	     on c^d * p = s*q + r0 
	     avec d pair
	     r0 = cr * r * PI_lpos f^k * PI_lpol g^k
	     cr non nul positif
	  *)
	  (!r,c,d,s,cr,!lpos,!lpol))



(* teste si la non-nullité des polynômes de lp entraîne celle de p:
   chacun des facteurs de la décomposition sans carrés de p 
   divise un des polynômes de lp (dans Q[x1...xn]) *)

let implique_non_nul lp p =
  if eqP p cf0 then false
  else(
    pr "[";
    let lf = facteurs2 p in 
    let r =(
      try (List.iter (fun f ->
			if (try (List.iter (fun q ->
	                                      if div_pol_rat q f
					      then failwith "divise")
                                   lp;
          	                 true)
                            with _ -> false)
			then failwith "raté")
	     lf;
	   true)
      with _ -> false)
    in pr "]";r)


let ajoute_non_nul p lp =
  if (deg_total p) >0
  then(
    let p = normc p in
    let lf = facteurs2 p in
    let r = set_of_list_eq eqP (lp@lf@[p]) in
      r)
  else lp

