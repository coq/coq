
(* $Id$ *)

open Names
open Term
open Declare

let nat_path = make_path ["Coq";"Init";"Datatypes"] (id_of_string "nat") CCI
let myvar_path =
  make_path ["Coq";"Arith";"Arith"] (id_of_string "My_special_variable") CCI

let glob_nat = IndRef (nat_path,0)

let glob_O = ConstructRef ((nat_path,0),1)
let glob_S = ConstructRef ((nat_path,0),2)

let glob_My_special_variable_nat = ConstRef myvar_path
