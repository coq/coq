(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)

type position =
    Top
  | Pos of int * position



val string_of_position : position -> string

val build_pos : position -> int -> position
