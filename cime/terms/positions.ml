(***************************************************************************

(This sentence has been added automatically,
it should be replaced by a description of the module)

CiME Project - Démons research team - LRI - Université Paris XI

$Id$

***************************************************************************)


type position =
    Top
  | Pos of int * position

let string_of_position =
  let rec strp = function
      Top -> ""
    | Pos(i,p) -> "." ^   (string_of_int i) ^ (strp p) in
    function
	Top -> "^"
      | Pos(i,p) -> (string_of_int i) ^ (strp p)
    

let rec build_pos p i = match p with
    Top -> Pos (i,Top)
  | Pos (j,q) -> Pos (j, (build_pos q i))
