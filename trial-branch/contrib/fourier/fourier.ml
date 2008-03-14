(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* M�thode d'�limination de Fourier *)
(* R�f�rence:
Auteur(s) : Fourier, Jean-Baptiste-Joseph
 
Titre(s) : Oeuvres de Fourier [Document �lectronique]. Tome second. M�moires publi�s dans divers recueils / publ. par les soins de M. Gaston Darboux,...
 
Publication : Num�risation BnF de l'�dition de Paris : Gauthier-Villars, 1890
 
Pages: 326-327

http://gallica.bnf.fr/
*)

(* Un peu de calcul sur les rationnels... 
Les op�rations rendent des rationnels normalis�s,
i.e. le num�rateur et le d�nominateur sont premiers entre eux.
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

(* {coef;hist;strict}, o� coef=[c1; ...; cn; d], repr�sente l'in�quation
c1x1+...+cnxn < d si strict=true, <= sinon,
hist donnant les coefficients (positifs) d'une combinaison lin�aire qui permet d'obtenir l'in�quation � partir de celles du d�part.
*)

type ineq = {coef:rational list;
             hist:rational list;
             strict:bool};;

let pop x l = l:=x::(!l);;

(* s�pare la liste d'in�quations s selon que leur premier coefficient est 
n�gatif, nul ou positif. *)
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
(* initialise les histoires d'une liste d'in�quations donn�es par leurs listes de coefficients et leurs strictitudes (!):
(add_hist [(equation 1, s1);...;(�quation n, sn)])
=
[{�quation 1, [1;0;...;0], s1};
 {�quation 2, [0;1;...;0], s2};
 ...
 {�quation n, [0;0;...;1], sn}]
*)
let add_hist le =
   let n = List.length le in
   let i=ref 0 in
   List.map (fun (ie,s) -> 
              let h =ref [] in
              for k=1 to (n-(!i)-1) do pop r0 h; done;
              pop r1 h;
              for k=1 to !i do pop r0 h; done;
              i:=!i+1;
              {coef=ie;hist=(!h);strict=s})
             le
;;
(* additionne deux in�quations *)      
let ie_add ie1 ie2 = {coef=List.map2 rplus ie1.coef ie2.coef;
                      hist=List.map2 rplus ie1.hist ie2.hist;
		      strict=ie1.strict || ie2.strict}
;;
(* multiplication d'une in�quation par un rationnel (positif) *)
let ie_emult a ie = {coef=List.map (fun x -> rmult a x) ie.coef;
                     hist=List.map (fun x -> rmult a x) ie.hist;
		     strict= ie.strict}
;;
(* on enl�ve le premier coefficient *)
let ie_tl ie = {coef=List.tl ie.coef;hist=ie.hist;strict=ie.strict}
;;
(* le premier coefficient: "t�te" de l'in�quation *)
let hd_coef ie = List.hd ie.coef
;;

(* calcule toutes les combinaisons entre in�quations de t�te n�gative et in�quations de t�te positive qui annulent le premier coefficient.
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
(* �limination de la premi�re variable � partir d'une liste d'in�quations:
op�ration qu'on it�re dans l'algorithme de Fourier.
*)
let deduce1 s =
    match (partitionne s) with 
      [lneg;lnul;lpos] ->
    let lnew = deduce_add lneg lpos in
    (List.map ie_tl lnul)@lnew
     |_->assert false
;;
(* algorithme de Fourier: on �limine successivement toutes les variables.
*)
let deduce lie =
   let n = List.length (fst (List.hd lie)) in
   let lie=ref (add_hist lie) in
   for i=1 to n-1 do
      lie:= deduce1 !lie;
   done;
   !lie
;;

(* donne [] si le syst�me a des solutions,
sinon donne [c,s,lc]
o� lc est la combinaison lin�aire des in�quations de d�part
qui donne 0 < c si s=true
       ou 0 <= c sinon
cette in�quation �tant absurde.
*)
let unsolvable lie =
   let lr = deduce lie in
   let res = ref [] in
   (try (List.iter (fun e ->
         match e with
           {coef=[c];hist=lc;strict=s} ->
		  if (rinf c r0 && (not s)) || (rinfeq c r0 && s) 
                  then (res := [c,s,lc];
			raise (Failure "contradiction found"))
          |_->assert false)
			     lr)
   with _ -> ());
   !res
;;

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