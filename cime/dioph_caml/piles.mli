(***************************************************************************

(This sentence has been added automatically, it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

open Type_de_donnees_dioph

val pile_vide : int -> pile

val empile : noeud -> pile -> unit

val sommet : pile -> noeud

val hauteur : pile -> int

val do_pile : (noeud -> unit) -> pile -> unit
