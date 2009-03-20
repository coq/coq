(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type coef = Polynom.poly
val coef_of_int : int -> coef
val eq_coef : coef -> coef -> bool
val plus_coef : coef -> coef -> coef
val mult_coef : coef -> coef -> coef
val sub_coef : coef -> coef -> coef
val opp_coef : coef -> coef
val div_coef : coef -> coef -> coef
val coef0 : coef
val coef1 : coef
val string_of_coef : coef -> string
val pgcd : coef -> coef -> coef

type mon = int array
type poly = (coef * mon) list

val eq_poly : poly -> poly -> bool
val mult_mon : int -> mon -> mon -> mon
val deg : mon -> int
val compare_mon : int -> mon -> mon -> int
val div_mon : int -> mon -> mon -> mon
val div_pol_coef : poly -> coef -> poly
val div_mon_test : int -> mon -> mon -> bool
val set_deg : int -> mon -> mon
val ppcm_mon : int -> mon -> mon -> mon

val name_var : string list ref
val getvar : string list -> int -> string
val stringP : poly -> string
val stringPcut : poly -> string
val lstringP : poly list -> string
val printP : poly -> unit
val lprintP : poly list -> unit

val polconst : int -> coef -> poly
val zeroP : poly
val plusP : int -> poly -> poly -> poly
val mult_t_pol : int -> coef -> mon -> poly -> poly
val selectdiv : int -> mon -> poly list -> poly
val gen : int -> int -> poly
val oppP : poly -> poly
val emultP : coef -> poly -> poly
val multP : int -> poly -> poly -> poly
val puisP : int -> poly -> int -> poly
val contentP : poly -> coef
val contentPlist : poly list -> coef
val pgcdpos : coef -> coef -> coef
val div_pol : int -> poly -> poly -> coef -> coef -> mon -> poly
val reduce2 : int -> poly -> poly list -> coef * poly

val poldepcontent : coef list ref
val coefpoldep_find : poly -> poly -> poly
val coefpoldep_set : poly -> poly -> poly -> unit
val initcoefpoldep : int -> poly list -> unit
val reduce2_trace :
  int -> poly -> poly list -> poly list -> poly list * poly
val homogeneous : bool ref
val spol : int -> poly -> poly -> poly
val etrangers : int -> ('a * mon) list -> ('b * mon) list -> bool
val div_ppcm : int -> poly -> poly -> poly -> bool

type 'a cpRes = Keep of 'a list | DontKeep of 'a list
val list_rec : 'a -> ('b -> 'b list -> 'a -> 'a) -> 'b list -> 'a
val addRes : 'a -> 'a cpRes -> 'a cpRes
val slice : int -> poly -> poly -> poly list -> poly cpRes
val addS : 'a -> 'a list -> 'a list
val genPcPf : int -> poly -> poly list -> poly list -> poly list
val genOCPf : int -> poly list -> poly list

val is_homogeneous : poly -> bool

val in_ideal :
  int -> poly list -> poly ->
  coef * poly list * poly * poly list list * poly list
