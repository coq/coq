(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Piles;;
open Type_de_donnees_dioph;;
open Init;;
open Solprocess;;
open Notsolprocess;;
open Printf;;
(*i
open Args;;
i*)

let show_state s =
  printf "ne = %d\n" s.ne;
  printf "nv = %d\n" s.nv;
  printf "v_type = ";
  for i=0 to (pred (Array.length s.vt)) do
      printf "%d " s.vt.(i)
  done;
  printf "\n";
  printf "Le systeme est egal a\n";
  for i=0 to (pred s.ne) do
      for j=0 to (pred s.nv) do
          printf "%d " s.syst.(i).(j)
      done;
      printf "\n"
  done; 
  printf "La pile est egale a \n";
  for i=0 to (pred s.st.h) do
      printf "n_uplet = ";
      for j=0 to (pred s.nv) do
          printf "%s(%d) " (if s.st.v.(i).n_uplet.(j).frozen then " G"
                                                             else "NG")
                           s.st.v.(i).n_uplet.(j).valeur
      done;
      printf "\n";
      printf "defaut = ";
      for j=0 to (pred s.ne) do
          printf "%d " s.st.v.(i).defaut.(j)
      done;
      printf "\n";
      printf "contraint = ";
      List.iter (function c -> printf "[";
                             for k=0 to (pred s.nv) do
                                 printf "%d " c.(k)
                             done;
                             printf "] ")
              s.st.v.(i).contraint;
      printf "\n"
  done;
  printf "\n\n"
;;

let show_pile s = 
  printf "La pile est egale a \n";
  for i=(pred s.st.h) downto 0 do
      printf "n_uplet = ";
      for j=0 to (pred s.nv) do
          printf "%d " s.st.v.(i).n_uplet.(j).valeur
      done;
      printf "\n"
(*
      printf "defaut = ";
      for j=0 to (pred s.ne) do
          printf "%d " s.st.v.(i).defaut.(j)
      done;
      printf "\n";
      printf "contraint = ";
      List.iter (function c -> printf "[";
                             for k=0 to (pred s.nv) do
                                 printf "%d " c.(k)
                             done;
                             printf "] ")
              s.st.v.(i).contraint;
      printf "\n";
*)
  done;
  printf "\n\n";
  flush stdout
;;

let process my_state = 

  (* recuperation des donnees utiles sur le systeme a resoudre *)

  let nb_eq = my_state.ne
  and nb_var = my_state.nv
  and v_type = my_state.vt
  and tab_defaut = my_state.tab_def

  (* on depile le noeud que l'on va tenter de developper       *)

  and elem_cour = sommet my_state.st in 
  if (is_solution nb_eq elem_cour)
  
  then 

  (* si le noeud courant est solution, on le met dans la liste
     et on met a jour les contraintes                           *)

       begin
       let s = extract_solution elem_cour in
       add_solution s my_state;
       add_contraint s my_state
       end 

  else 

  (* sinon, on tente de developper le noeud et on empile ses fils *)

       let ti = increm_index_list nb_var v_type tab_defaut elem_cour in
       List.iter (function increm -> 
                        push_a_stack_elem my_state elem_cour increm;
                        elem_cour.n_uplet.(increm).frozen <- true)
               ti
;;

let dioph_solve v_type system =

  let nb_eq = Array.length system 
  and nb_var = v_type.(pred (Array.length v_type)) in
  let my_state  = init_state nb_eq v_type system in
(*i
  let f = options_courantes.dioph_output in
  if options_courantes.print_dioph >=2
  then
    begin
      Printf.fprintf f "vecteur de contraintes : ";
      for i=0 to pred (Array.length v_type) do
        Printf.fprintf f "%d " v_type.(i)
      done;
      Printf.fprintf f "\n"
    end;
  if options_courantes.print_dioph >= 1
  then 
    begin
      Printf.fprintf f "%d\n" nb_eq;
      Printf.fprintf f "%d\n" nb_var;
      for i=0 to (pred nb_eq) do
      	for j=0 to (pred nb_var) do
	  Printf.fprintf f "%d " system.(i).(j)
      	done;
      	Printf.fprintf f "\n"
      done;
      Printf.fprintf f "\n";
      flush f
    end;
i*)
(*
  show_state my_state;
  flush stdout;
*)
  while ((hauteur my_state.st) > 0) do
(*
        show_state my_state;
        flush stdout;
*)
        process my_state
  done;
  let vect_of_sols = Array.of_list my_state.sol in
(*
  printf "\n nombre de vraies variables = %d\n" v_type.(0);
  printf "Les solutions sont egales a \n";
  for i=0 to (pred (Array.length vect_of_sols)) do
      for j=0 to (pred (Array.length vect_of_sols.(i))) do
          printf "%d " vect_of_sols.(i).(j)
      done;
      printf "\n"

  done;
*)
  vect_of_sols
;;

(*
let dioph_solve = Time_profiler.profile2 "dioph_solve" dioph_solve
;;
*)
