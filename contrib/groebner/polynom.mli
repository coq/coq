type coef (*= Entiers.entiers*)
val coef_of_num : Num.num -> coef
val num_of_coef : coef -> Num.num
val eq_coef : coef -> coef -> bool
val lt_coef : coef -> coef -> bool
val le_coef : coef -> coef -> bool
val abs_coef : coef -> coef
val plus_coef : coef -> coef -> coef
val mult_coef : coef -> coef -> coef
val sub_coef : coef -> coef -> coef
val opp_coef : coef -> coef
val div_coef : coef -> coef -> coef
val mod_coef : coef -> coef -> coef
val coef0 : coef
val coef1 : coef
val string_of_coef : coef -> string
val int_of_coef : coef -> int
val hash_coef : coef -> int
val puis_coef : coef -> int -> coef
val pgcd : coef -> coef -> coef
val pgcd2 : coef -> coef -> coef

type variable = int
type poly = Pint of coef | Prec of variable * poly array

val cf : int -> poly
val cf0 : poly
val cf1 : poly
val x : variable -> poly
val max_var_pol : poly -> variable
val max_var_pol2 : poly -> variable
val max_var : poly array -> variable
val eqP : poly -> poly -> bool
val norm : poly -> poly
val deg : variable -> poly -> int
val deg_total : poly -> int
val copyP : poly -> poly
val coef : variable -> int -> poly -> poly
val plusP : poly -> poly -> poly
val content : poly -> coef
val div_int : poly -> coef -> poly
val vire_contenu : poly -> poly
val vars : poly -> variable list
val int_of_Pint : poly -> coef
val multx : int -> variable -> poly -> poly
val multP : poly -> poly -> poly
val deriv : variable -> poly -> poly
val oppP : poly -> poly
val moinsP : poly -> poly -> poly
val puisP : poly -> int -> poly
val ( @@ ) : poly -> poly -> poly
val ( -- ) : poly -> poly -> poly
val ( ^^ ) : poly -> int -> poly
val coefDom : variable -> poly -> poly
val coefConst : variable -> poly -> poly
val remP : variable -> poly -> poly
val coef_int_tete : poly -> coef
val normc : poly -> poly
val is_constantP : poly -> bool
val is_zero : poly -> bool
val monome : variable -> int -> poly
val coef_constant : poly -> coef
val univ : bool ref
val string_of_var : int -> string
val nsP : int ref
val string_of_Pcut : poly -> string
val string_of_P : poly -> string
val printP : poly -> unit
val print_tpoly : poly array -> unit
val print_lpoly : poly list -> unit
val quo_rem_pol : poly -> poly -> variable -> poly * poly
val div_pol : poly -> poly -> variable -> poly
val divP : poly -> poly -> poly
val div_pol_rat : poly -> poly -> bool
val pseudo_div : poly -> poly -> variable -> poly * poly * int * poly
val pgcdP : poly -> poly -> poly
val pgcd_pol : poly -> poly -> variable -> poly
val content_pol : poly -> variable -> poly
val pgcd_coef_pol : poly -> poly -> variable -> poly
val pgcd_pol_rec : poly -> poly -> variable -> poly
val gcd_sub_res : poly -> poly -> variable -> poly
val gcd_sub_res_rec : poly -> poly -> poly -> poly -> int -> variable -> poly
val lazard_power : poly -> poly -> int -> variable -> poly
val sans_carre : poly -> variable -> poly
val facteurs : poly -> variable -> poly list
val facteurs_impairs : poly -> variable -> poly list
val hcontentP : (string, poly) Hashtbl.t
val prcontentP : unit -> unit
val contentP : poly * variable -> poly
val hashP : poly -> int
module Hashpol : Hashtbl.S with type key=poly
val memoP :
  string -> 'a Hashpol.t -> (poly -> 'a) -> poly -> 'a
val hfactorise : poly list list Hashpol.t
val prfactorise : unit -> unit
val factorise : poly -> poly list list
val facteurs2 : poly -> poly list
val pol_de_factorisation : poly list list -> poly
val set_of_array_facteurs : poly list array -> poly list
val factorise_tableauP2 :
  poly array ->
  poly list array -> poly array * (poly * int list) array
val factorise_tableauP :
  poly array -> poly array * (poly * int list) array
val is_positif : poly -> bool
val is_negatif : poly -> bool
val pseudo_euclide :
  poly list -> poly -> poly -> variable ->
  poly * poly * int * poly * poly * (poly * int) list * (poly * int) list
val implique_non_nul : poly list -> poly -> bool
val ajoute_non_nul : poly -> poly list -> poly list
