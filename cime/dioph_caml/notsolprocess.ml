(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


open Type_de_donnees_dioph;;
open Piles;;


let produit_scalaire v w =
  let p = ref 0
  in
  for i=0 to (pred (Array.length v)) do
      p:= !p + (v.(i) * w.(i))
  done;
  !p
;;

let increm_index_list nb_var v_type tab_defaut n = 
  let ti = ref []
  in
  for i = (pred nb_var) downto v_type.(0) do
      if ((n.n_uplet.(i).frozen = false) &
          (n.n_uplet.(i).valeur = 0))
      then if ((produit_scalaire n.defaut tab_defaut.(i)) < 0)
           then ti:= i::!ti
  done;
  for i=(pred v_type.(0)) downto 0 do
      if (n.n_uplet.(i).frozen = false)
      then if ((produit_scalaire n.defaut tab_defaut.(i)) < 0)
           then ti:= i::!ti
  done;
  !ti
;;

let vect_is_nul_from n c =
   try for i=n to (pred (Array.length c)) do
           if (c.(i) <> 0)
           then raise Not_found
       done;
       true
   with Not_found -> false
;;
  
let copy_vect_entier v = 
  let v' = Array.create (Array.length v) {frozen=true; valeur=0} in
  for i=0 to (pred (Array.length v)) do
    v'.(i) <- {frozen = v.(i).frozen; valeur = v.(i).valeur}
  done;
  v'
;;

let push_a_stack_elem my_state n increm =

  let n_copy = {n_uplet = copy_vect_entier n.n_uplet;
                defaut = Array.copy n.defaut;
                contraint = []}
  and nb_var = my_state.nv
  and v_type = my_state.vt
  and nb_eq = my_state.ne
  and tab_defaut = my_state.tab_def
  in 
  (* mise a jour de la valeur associee au noeud *)
  n_copy.n_uplet.(increm).valeur <- succ n_copy.n_uplet.(increm).valeur;

  (* mise a jour des contraintes associees au noeud, avec test de minimalite *)
  let est_minimal = ref true
  in 
  let rec mise_a_jour_contraint = function
    [] -> []
  | c::l -> if (!est_minimal)
            then let c'=Array.copy c in
      	       	 begin
                 if (c'.(increm) > 0) & (increm >= 0)
                 then begin
                      c'.(increm) <- pred c'.(increm);
                      if (vect_is_nul_from 0 c')
                      then begin
                           est_minimal := false;
                           []
                           end
                      else c'::(mise_a_jour_contraint l)
                      end
                 else c'::(mise_a_jour_contraint l)
                 end
            else []
  in 
  let nouv_contraint = mise_a_jour_contraint n.contraint
  in
  if (!est_minimal)
  then begin 
       n_copy.contraint <- nouv_contraint;

  (* gel si la composante correspond a une constante *)
       if (v_type.(0) <= increm)
       then begin
            n_copy.n_uplet.(increm).frozen <- true;
            for i=1 to (pred (pred (Array.length v_type))) do
            if ((v_type.(i) > increm) or (v_type.(i+1) <= increm))
            then for j=v_type.(i) to (pred (v_type.(i+1))) do
                 n_copy.n_uplet.(j).frozen <- true
                 done
            done
            end;

  (* mise a jour du defaut *)
       for i=0 to (pred nb_eq) do
           n_copy.defaut.(i) <- n_copy.defaut.(i) + tab_defaut.(increm).(i)
       done; 

   (* ajout du noeud modifie sur la pile *)
       empile n_copy my_state.st      

       end
;;
              
  
