(***************************************************************************

  This module provides a function for solving systems of linear equations
  over the integers.

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Solve

type identifications_for_unification = 
     Without_identifications of (int array array) * (int array array)
   | With_identifications of (int array array) * (int array array)
   | No_sol

type etat =
    {         
      e   : (int * int) list; (* correspond a pe.edge *)
      vt  : int array;        (* vecteur de type des vars (inst. ou pas) *)
      nv  : int;              (* nombre de variables de depart           *)
      nc  : int;              (* nombre total de variables instanciees   *)
      mutable  ne  : int;     (* nombre d'equations courant              *)
      mutable  nvc  : int;    (* nombre de variables courant             *)
      mutable  a   : int array; (* a et b representent les eqs courantes *)
      mutable  b   : int array; (* aX+b=0 vis-a-vis desquelles on transforme *)
      mutable  grand_a   : int array array;
      mutable  grand_b   : int array array;
      mutable  grand_c   : int array array;
      mutable  grand_d   : int array array
    }

exception Matrice_Nulle
exception Systeme_Sans_Solution

(*
  show imprime l'etat e
*)
(*
let show e =
printf "show\n";
printf "vt =";
for i=0 to pred (Array.length e.vt) do 
    printf " %d" e.vt.(i)
done;
printf "\n";
printf "nv = %d\n" e.nv;
printf "nc = %d\n" e.nc;
printf "ne = %d\n" e.ne;
printf "nvc = %d\n" e.nvc;
printf " A | B \n";
for i=0 to (pred e.ne) do
    for j=0 to (pred e.nvc) do
        printf "%d " e.grand_a.(i).(j)
    done;
    printf " | ";
    for j=0 to (pred e.nc) do
        printf "%d " e.grand_b.(i).(j)
    done
done;
printf " C | D\n";
for i=0 to (pred e.nv) do
    for j=0 to (pred e.nvc) do
        printf "%d " e.grand_c.(i).(j)
    done;
    printf " | ";
    for j=0 to (pred e.nc) do
        printf "%d " e.grand_d.(i).(j)
    done
done;
flush stdout
*)

(*
  Careful extension of the functions [/] and [mod], quotient and reminder of
  the integer division over the negative and positive integers in such a 
  way that
  \[
  p = (p \mathop{zquo} q) * q + (p \mathop{zmod} q),
  \]
  where $0 <= (p \mathop{zmod} q) < \mathop{abs}(q)$.
*)

let zquo p q =
  if q = 0
  then raise Division_by_zero
  else 
    if p >= 0
    then 
      begin
        if q > 0
        then (p / q)
        else -(p / (-q))
      end
    else 
      begin
        if q > 0
        then 
	  if ((-p) mod q) = 0
	  then -((-p) / q)
          else -(((-p) / q) +1)
        else 
	  if ((-p) mod (-q)) = 0
	  then ((-p) / (-q))
	  else ((-p) / (-q)) +1
      end

let zmod p q =
   if q = 0
   then raise Division_by_zero
   else 
     if p >= 0
     then 
       begin
         if q > 0
         then p mod q
         else p mod (-q)
       end
     else
       begin
         if q > 0
         then 
	   if ((-p) mod q) = 0
           then 0
           else q - ((-p) mod q)
         else 
	   if ((-p) mod (-q)) = 0
           then 0
           else (-q) - ((-p) mod (-q))
       end


(* 

   [(divides c n v)] checks whether the integer [c] divides the [n]th
   first elements of the array of integers [v].

*)

let divides c n v =
  if c = 0
  then raise Division_by_zero
  else 
    let d = abs c in
      begin
        try
	  let _ =
	    Array.iter
	      (function vi ->
		 if ((abs vi) mod d) <> 0
		 then raise Exit)
	      v in
	    true
	with Exit -> false
      end
 


let init mat vect_type pe_edge = 
  let nb_eq = Array.length mat
  and nb_var = vect_type.(0)
  and nb_cst = vect_type.(pred (Array.length vect_type)) - vect_type.(0) in
  if (nb_var + nb_cst) = (Array.length mat.(0))
  then 
    let grand_o = Array.create_matrix nb_var nb_cst 0
    and grand_id = Array.create_matrix nb_var nb_var 0 
    and grand_aa = Array.create_matrix nb_eq nb_var 0 
    and grand_bb = Array.create_matrix nb_eq nb_cst 0 in 
      begin
	for j=0 to (pred nb_var) do
          grand_id.(j).(j) <- 1
	done;
	for i=0 to (pred nb_eq) do
          for j=0 to (pred nb_var) do
	    grand_aa.(i).(j) <- mat.(i).(j)
	  done;
	  for j=0 to (pred nb_cst) do
	    grand_bb.(i).(j) <- mat.(i).(nb_var + j)
	  done
	done;

	let e =  {
	  e = pe_edge;
          vt = vect_type;
          nv = nb_var;
	  nc = nb_cst;
          ne = nb_eq;
          nvc = nb_var;
          a = Array.create nb_var 0;
          b = Array.create nb_cst 0;
          grand_a = grand_aa;
          grand_b = grand_bb;
          grand_c = grand_id;
          grand_d = grand_o
	} in 
       (* show e; *) 
	  e 
      end
  else failwith "A et v_type ont des dimensions incompatibles"

(* recherche des positions du plus petit coefficient non nul en valeur
 absolue dans une matrice d'entiers : ppc dimx dimy mat retourne (i,j)
 tel que mat(i,j) est la valeur desiree. Si la matrice est nulle,
 l'exception Matrice_Nulle est levee. Seules les dimx premieres lignes
 et les dimy premieres colonnes sont considerees.  *)

let ppc dimx dimy mat = 
  let list_pos_min = ref []
  and min = ref 0 in
    for i=0 to (pred dimx) do
      for j=0 to (pred dimy) do
	if (!min = 0) & (mat.(i).(j) <> 0)
	then 
	  begin 
            min := abs mat.(i).(j);
            list_pos_min := [(i,j)]
          end
	else 
	  if (((abs mat.(i).(j)) < !min) & (mat.(i).(j) <> 0))
          then 
	    begin
              min := abs mat.(i).(j);
              list_pos_min := [(i,j)]
            end
          else 
	    if (((abs mat.(i).(j)) = !min) & (mat.(i).(j) <> 0))
            then list_pos_min := (i,j)::(!list_pos_min)                   
      done
    done;
    if !min = 0
    then raise Matrice_Nulle
    else !list_pos_min

let rec selection e = function
    [] -> raise Not_found
  | (i,j)::ll -> 
      if (List.exists 
            (function (l,k) -> 
               let l'= l - e.nv in
                 ((e.grand_d.(k).(l') - 
		   e.grand_a.(i).(j)*e.grand_c.(k).(j)*e.grand_b.(i).(l')) 
		  <> 0))
            e.e)
      then selection e ll
      else (i,j)


let etape1 i0 j0 e = 
(*
  elimination de la variable j0 dans le systeme grace a l'equation i0
  ou elle apparait avec un coefficent c egal a +/- 1.
*)
  let nb_var = e.nvc
  and nb_var_dep = e.nv
  and nb_cst = e.nc
  and nb_eq = e.ne
  and c = e.grand_a.(i0).(j0) in
(*
  on met dans a et b les coefficients de l'equation i0
*)
    for j=0 to (pred nb_var) do
      e.a.(j) <- e.grand_a.(i0).(j)
    done;
    for j=0 to (pred nb_cst) do
      e.b.(j) <- e.grand_b.(i0).(j)
    done;
(*
  mise a jour de C et D. La colonne j0 vaut 0 dans C, car la variable
  j0 a ete eliminee, et les variables de depart ne s'expriment plus
  en fonction d'elle.
*)
    for i=0 to (pred nb_var_dep) do
      for j=0 to (pred nb_cst) do
	e.grand_d.(i).(j) <- 
	e.grand_d.(i).(j) - (c * (e.grand_c.(i).(j0) * e.b.(j)))
      done;
      for j=0 to (pred j0) do
        e.grand_c.(i).(j) <- 
	e.grand_c.(i).(j) - (c * (e.grand_c.(i).(j0) * e.a.(j)))
      done;
      for j = (succ j0) to (pred nb_var) do
        e.grand_c.(i).(j) <- 
	e.grand_c.(i).(j) - (c * (e.grand_c.(i).(j0) * e.a.(j)))
      done
    done;

(*
  mise a jour de la matrice A et de la matrice de constantes B
  la ligne i0 (dans A et B)correspond a l'equation utilisee, 
  et l'information sera conservee dans la partie X = CYn + D,
  la colonne j0 (dans A) correspond a la variable eliminee,
  et vaut 0. 
*)
    for i=0 to (pred i0) do
      for j=0 to (pred nb_cst) do
	e.grand_b.(i).(j) <- 
	e.grand_b.(i).(j) - (c * (e.grand_a.(i).(j0) * e.b.(j)))
      done;
      for j=0 to (pred j0) do
        e.grand_a.(i).(j) <- 
	e.grand_a.(i).(j) - (c * (e.grand_a.(i).(j0) * e.a.(j)))
      done;
      for j = (succ j0) to (pred nb_var) do
        e.grand_a.(i).(j) <- 
	e.grand_a.(i).(j) - (c * (e.grand_a.(i).(j0) * e.a.(j)))
      done
    done;

    for i=(succ i0) to (pred nb_eq) do
      for j=0 to (pred nb_cst) do
	e.grand_b.(i).(j) <- 
	e.grand_b.(i).(j) - (c * (e.grand_a.(i).(j0) * e.b.(j)))
      done;
      for j=0 to (pred j0) do
        e.grand_a.(i).(j) <-
	e.grand_a.(i).(j) - (c * (e.grand_a.(i).(j0) * e.a.(j)))
      done;
      for j = (succ j0) to (pred nb_var) do
        e.grand_a.(i).(j) <- 
	e.grand_a.(i).(j) - (c * (e.grand_a.(i).(j0) * e.a.(j)))
      done
    done;
(*
  A, B, C, D ont ete mis a jour, mais il reste a eliminer effectivement
  la ligne i0 (correspondant a l'equation eliminee) dans A et B, et
  la colonne j0 (correspondant a la variable eliminee) dans A et C.
  Ce sera fait par des decalages.
*)
    for i=i0 to (nb_eq - 2) do
      for j=0 to (pred nb_cst) do
	e.grand_b.(i).(j) <- e.grand_b.(i+1).(j)
      done;
      for j=0 to (pred nb_var) do
        e.grand_a.(i).(j) <- e.grand_a.(i+1).(j)
      done
    done;

    for j=j0 to (nb_var -2) do
      for i=0 to (nb_eq - 2) do
        e.grand_a.(i).(j) <- e.grand_a.(i).(j+1)
      done;
      for i=0 to (pred e.nv) do
        e.grand_c.(i).(j) <- e.grand_c.(i).(j+1)
      done
    done;

(*
  mise a jour du nombre de variables et d'equations courants
*)
    e.nvc <- (pred e.nvc);
    e.ne <- (pred e.ne);
    e


let etape2 i0 j0 e = 
(*
  elimination de la variable j0 dans le systeme grace a l'equation i0
  ou elle apparait avec un coefficent dont la valeur absolue est >1
*)
  let nb_var = e.nvc
  and nb_var_dep = e.nv
  and nb_cst = e.nc
  and nb_eq = e.ne
  and c = e.grand_a.(i0).(j0) in
(*
  on met dans a et b les coefficients de l'equation i0
*)
    for j=0 to (pred nb_var) do
      e.a.(j) <- e.grand_a.(i0).(j)
    done;
    for j=0 to (pred nb_cst) do
      e.b.(j) <- e.grand_b.(i0).(j)
    done;
(*
  Premier test : si tous les coefficients variables de l'equation i0
  sont des multiples de ai0j0, et les coefficients constants aussi,
  il faut diviser tous les coefficients de l'equation i0 par ai0j0
  et appliquer l'etape1. Si tous les coefficents variables sont des
  multiples de ai0j0 et pas les coefficients constants, il faut echouer.
*)
    if divides c nb_var e.a
    then 
      begin
	if divides c nb_cst e.b
	then 
	  begin
            for j=0 to (pred nb_var) do
              e.grand_a.(i0).(j) <- zquo e.a.(j) c
            done;
	    for j=0 to (pred nb_cst) do
              e.grand_b.(i0).(j) <- zquo e.b.(j) c
            done;
            etape1 i0 j0 e
          end
	else raise Systeme_Sans_Solution
      end
    else 
      begin
(*
  Sinon yj0 est eliminee au profit de d'une nouvelle variable y'j0 telle que
  y'j0 = [ai01/ai0j0] y1 + ...+ [ai0j0/ai0j0] yj0 + ... + [ai0n/ai0j0] yn
  [a/b] est defini comme le produit du signe de a/b et du quotient 
  entier des valeurs absolues de a et b. 
  Nota : l'equation i0 est toujours presente.
*)

(*
  mise a jour de C. Le matrice de constantes D ne change pas. 
*)
	for i=0 to (pred nb_var_dep) do
	  for j=0 to (pred j0) do
            e.grand_c.(i).(j) <- 
	    e.grand_c.(i).(j) - (e.grand_c.(i).(j0) * (zquo e.a.(j) c))
	  done;
	  for j = (succ j0) to (pred nb_var) do
            e.grand_c.(i).(j) <- 
	    e.grand_c.(i).(j) - (e.grand_c.(i).(j0) * (zquo e.a.(j) c))
	  done
	done;

(*
  mise a jour de la matrice A, la colonne j0 correspond a la nouvelle 
  variable, mais ne change pas. La matrice de constantes B ne change pas. 
*)
	for i=0 to (pred nb_eq) do
	  for j=0 to (pred j0) do
            e.grand_a.(i).(j) <- 
	    e.grand_a.(i).(j) - (e.grand_a.(i).(j0) * (zquo e.a.(j) c))
	  done;
	  for j = (succ j0) to (pred nb_var) do
            e.grand_a.(i).(j) <- 
	    e.grand_a.(i).(j) - (e.grand_a.(i).(j0) * (zquo e.a.(j) c))
	  done
	done;

(*
  le nombre d'equations a resoudre et le nombre de variables courant
  n'ont pas change. 
*)
	e
      end

let appliquer_etape e =
  (* show e; *)
  let l = ppc e.ne e.nvc e.grand_a in 
  let (i0,j0) = List.hd l in
    if (abs e.grand_a.(i0).(j0)) = 1
    then 
      begin
        try 
	  let (i1,j1) = selection e l in
            etape1 i1 j1 e
        with Not_found -> etape1 i0 j0 e
      end
    else etape2 i0 j0 e

let rec repeter_etape e = 
  try 
    repeter_etape (appliquer_etape e)
  with 
      Matrice_Nulle -> e
    | Systeme_Sans_Solution -> raise Systeme_Sans_Solution

let grand_b_est_nul e = 
  let nb_cst = e.nc 
  and nb_eq = e.ne in
    try 
      for i=0 to (pred nb_eq) do
        for j=0 to (pred nb_cst) do
          if (e.grand_b.(i).(j) <> 0)
          then raise Exit
        done
      done;
      true
    with Exit -> false


let i_solve vect_type mat pe_edge = 
  let e = init mat vect_type pe_edge in 
  try ignore (try repeter_etape e with x -> print_string "trouve\n";raise x);
    if (grand_b_est_nul e)
    then 
      begin
        let solutions_homogenes = Array.create_matrix e.nvc (e.nv + e.nc) 0 
        and solutions_particulieres = 
	  Array.create_matrix e.nc (e.nv + e.nc) 0 in
	  
          for j=0 to (pred e.nvc) do
            for i=0 to (pred e.nv) do
              solutions_homogenes.(j).(i) <- e.grand_c.(i).(j)
            done
          done;

          for j=0 to (pred e.nc) do
            for i=0 to (pred e.nv) do
              solutions_particulieres.(j).(i) <- e.grand_d.(i).(j)
            done;
            solutions_particulieres.(j).(e.nv + j) <- 1
          done;

          Without_identifications (solutions_homogenes,solutions_particulieres)
           
      end
      
    else 
      begin (* il faut faire des identifications sur les var. inst. *)
        let mat = Array.create_matrix e.ne e.nc 0 in
          for i=0 to (pred e.ne) do
            for j=0 to (pred e.nc) do
              mat.(i).(j) <- e.grand_b.(i).(j)
            done
          done;
          let cst_vect_type = Array.copy vect_type in
            for i=0 to (pred (Array.length vect_type)) do
              cst_vect_type.(i) <- vect_type.(i) - vect_type.(0)
            done;
            let identifications = dioph_solve cst_vect_type mat in
            let solutions_homogenes = 
	      Array.create_matrix e.nvc (e.nv + e.nc) 0 
            and solutions_particulieres = 
	      Array.create_matrix (Array.length identifications) 
		(e.nv + e.nc) 0 in

              for j=0 to (pred e.nvc) do
		for i=0 to (pred e.nv) do
                  solutions_homogenes.(j).(i) <- e.grand_c.(i).(j)
		done
              done;
              
              for j=0 to (pred (Array.length identifications)) do
		for i=0 to (pred e.nv) do
	          for k=0 to (pred e.nc) do
	            solutions_particulieres.(j).(i) <- 
                    solutions_particulieres.(j).(i) + 
                    (e.grand_d.(i).(k) * identifications.(j).(k))
	          done
		done;
		for i=e.nv to (pred (e.nv + e.nc)) do
	          solutions_particulieres.(j).(i) <- 
                  identifications.(j).(i - e.nv)
		done
              done; 
	      
              With_identifications 
		(solutions_homogenes,solutions_particulieres)
		
      end
      
  with Systeme_Sans_Solution -> No_sol


