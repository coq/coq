(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


type entier = 
{ 
  mutable  frozen : bool;
  mutable  valeur : int
};;

type noeud = 
{
 mutable  n_uplet   : entier array;
          defaut    : int array;
 mutable  contraint : int array list
}
;;

type pile =                    (* pile implemente le type "pile bornee" *)
{
          hmax  : int;         (* hauteur maximale de la pile              *)
  mutable h	: int; 	       (* hauteur courante de la pile              *)
  mutable v     : noeud array   (* contenu de la pile sous forme de vecteur *)
}
;;

type state =
{
    ne               : int;           (* nombre d'equations                 *)
    nv               : int;           (* nombre de variables                *)
    vt               : int array;      (* nombre de variables de chaque type *)
    mutable aci_syst : (int array *int array) array; (* pour unif ACI          *)
    syst             : int array array; (* le systeme ligne par ligne         *)
    tab_def          : int array array; (* le systeme colonne par colonne     *)
    st               : pile;          (* pile qui contient l'etat courant   *)
    mutable sol      : int array list  (* liste des solutions deja trouvees  *)
}                                        
;;
 


