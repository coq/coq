(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Méthode d'élimination de Fourier *)
(* Référence:
Auteur(s) : Fourier, Jean-Baptiste-Joseph

Titre(s) : Oeuvres de Fourier [Document électronique]. Tome second. Mémoires publiés dans divers recueils / publ. par les soins de M. Gaston Darboux,...

Publication : Numérisation BnF de l'édition de Paris : Gauthier-Villars, 1890

Pages: 326-327

http://gallica.bnf.fr/
*)

(* Un peu de calcul sur les rationnels...
Les opérations rendent des rationnels normalisés,
i.e. le numérateur et le dénominateur sont premiers entre eux.
*)
type rational = {num:int;
                 den:int}
;;
let print_rational x =
        print_int x.num;
        print_string "/";
        print_int x.den
;;

let rec pgcd x y = if y = 0 then x else pgcd y (x mod y);;


let r0 = {num=0;den=1};;
let r1 = {num=1;den=1};;

let rnorm x = let x = (if x.den<0 then {num=(-x.num);den=(-x.den)} else x) in
              if x.num=0 then r0
              else (let d=pgcd x.num x.den in
		    let d= (if d<0 then -d else d) in
                    {num=(x.num)/d;den=(x.den)/d});;

let rop x = rnorm {num=(-x.num);den=x.den};;

let rplus x y = rnorm {num=x.num*y.den + y.num*x.den;den=x.den*y.den};;

let rminus x y = rnorm {num=x.num*y.den - y.num*x.den;den=x.den*y.den};;

let rmult x y = rnorm {num=x.num*y.num;den=x.den*y.den};;

let rinv x = rnorm {num=x.den;den=x.num};;

let rdiv x y = rnorm {num=x.num*y.den;den=x.den*y.num};;

let rinf x y = x.num*y.den < y.num*x.den;;
let rinfeq x y = x.num*y.den <= y.num*x.den;;

(* {coef;hist;strict}, où coef=[c1; ...; cn; d], représente l'inéquation
c1x1+...+cnxn < d si strict=true, <= sinon,
hist donnant les coefficients (positifs) d'une combinaison linéaire qui permet d'obtenir l'inéquation à partir de celles du départ.
*)

type ineq = {coef:rational list;
             hist:rational list;
             strict:bool};;

let pop x l = l:=x::(!l);;

(* sépare la liste d'inéquations s selon que leur premier coefficient est
négatif, nul ou positif. *)
let partitionne s =
   let lpos=ref [] in
   let lneg=ref [] in
   let lnul=ref [] in
   List.iter (fun ie -> match ie.coef with
                        [] ->  raise (Failure "empty ineq")
                       |(c::r) -> if rinf c r0
           	                  then pop ie lneg
                                  else if rinf r0 c then pop ie lpos
                                              else pop ie lnul)
             s;
   [!lneg;!lnul;!lpos]
;;
(* initialise les histoires d'une liste d'inéquations données par leurs listes de coefficients et leurs strictitudes (!):
(add_hist [(equation 1, s1);...;(équation n, sn)])
=
[{équation 1, [1;0;...;0], s1};
 {équation 2, [0;1;...;0], s2};
 ...
 {équation n, [0;0;...;1], sn}]
*)
let add_hist le =
   let n = List.length le in
   let i = ref 0 in
   List.map (fun (ie,s) ->
              let h = ref [] in
              for _k = 1 to (n - (!i) - 1) do pop r0 h; done;
              pop r1 h;
              for _k = 1 to !i do pop r0 h; done;
              i:=!i+1;
              {coef=ie;hist=(!h);strict=s})
             le
;;
(* additionne deux inéquations *)
let ie_add ie1 ie2 = {coef=List.map2 rplus ie1.coef ie2.coef;
                      hist=List.map2 rplus ie1.hist ie2.hist;
		      strict=ie1.strict || ie2.strict}
;;
(* multiplication d'une inéquation par un rationnel (positif) *)
let ie_emult a ie = {coef=List.map (fun x -> rmult a x) ie.coef;
                     hist=List.map (fun x -> rmult a x) ie.hist;
		     strict= ie.strict}
;;
(* on enlève le premier coefficient *)
let ie_tl ie = {coef=List.tl ie.coef;hist=ie.hist;strict=ie.strict}
;;
(* le premier coefficient: "tête" de l'inéquation *)
let hd_coef ie = List.hd ie.coef
;;

(* calcule toutes les combinaisons entre inéquations de tête négative et inéquations de tête positive qui annulent le premier coefficient.
*)
let deduce_add lneg lpos =
   let res=ref [] in
   List.iter (fun i1 ->
		 List.iter (fun i2 ->
				let a = rop (hd_coef i1) in
				let b = hd_coef i2 in
				pop (ie_tl (ie_add (ie_emult b i1)
						   (ie_emult a i2))) res)
		           lpos)
             lneg;
   !res
;;
(* élimination de la première variable à partir d'une liste d'inéquations:
opération qu'on itère dans l'algorithme de Fourier.
*)
let deduce1 s =
    match (partitionne s) with
      [lneg;lnul;lpos] ->
    let lnew = deduce_add lneg lpos in
    (List.map ie_tl lnul)@lnew
     |_->assert false
;;
(* algorithme de Fourier: on élimine successivement toutes les variables.
*)
let deduce lie =
   let n = List.length (fst (List.hd lie)) in
   let lie=ref (add_hist lie) in
   for _i = 1 to n - 1 do
      lie:= deduce1 !lie;
   done;
   !lie
;;

(* donne [] si le système a des solutions,
sinon donne [c,s,lc]
où lc est la combinaison linéaire des inéquations de départ
qui donne 0 < c si s=true
       ou 0 <= c sinon
cette inéquation étant absurde.
*)

exception Contradiction of (rational * bool * rational list) list

let unsolvable lie =
   let lr = deduce lie in
   let check = function
     | {coef=[c];hist=lc;strict=s} ->
       if (rinf c r0 && (not s)) || (rinfeq c r0 && s)
       then raise (Contradiction [c,s,lc])
     |_->assert false
   in
   try List.iter check lr; []
   with Contradiction l -> l

(* Exemples:

let test1=[[r1;r1;r0],true;[rop r1;r1;r1],false;[r0;rop r1;rop r1],false];;
deduce test1;;
unsolvable test1;;

let test2=[
[r1;r1;r0;r0;r0],false;
[r0;r1;r1;r0;r0],false;
[r0;r0;r1;r1;r0],false;
[r0;r0;r0;r1;r1],false;
[r1;r0;r0;r0;r1],false;
[rop r1;rop r1;r0;r0;r0],false;
[r0;rop r1;rop r1;r0;r0],false;
[r0;r0;rop r1;rop r1;r0],false;
[r0;r0;r0;rop r1;rop r1],false;
[rop r1;r0;r0;r0;rop r1],false
];;
deduce test2;;
unsolvable test2;;

*)
