(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

exception NotInIdeal
val lexico : bool ref
val use_hmon : bool ref

module type S = sig

(* Monomials *)
type mon = int array

val mult_mon : int -> mon -> mon -> mon
val deg : mon -> int
val compare_mon : int -> mon -> mon -> int
val div_mon : int -> mon -> mon -> mon
val div_mon_test : int -> mon -> mon -> bool
val ppcm_mon : int -> mon -> mon -> mon

(* Polynomials *)

type deg = int
type coef
type poly
val repr : poly -> (coef * mon) list
val polconst : deg -> coef -> poly
val zeroP : poly
val gen : deg -> int -> poly

val equal : poly -> poly -> bool
val name_var : string list ref
val getvar : string list -> int -> string
val lstringP : poly list -> string
val printP : poly -> unit
val lprintP : poly list -> unit

val div_pol_coef : poly -> coef -> poly
val plusP : deg -> poly -> poly -> poly
val mult_t_pol : deg -> coef -> mon -> poly -> poly
val selectdiv : deg -> mon -> poly list -> poly
val oppP : poly -> poly
val emultP : coef -> poly -> poly
val multP : deg -> poly -> poly -> poly
val puisP : deg -> poly -> int -> poly
val contentP : poly -> coef
val contentPlist : poly list -> coef
val pgcdpos : coef -> coef -> coef
val div_pol : deg -> poly -> poly -> coef -> coef -> mon -> poly
val reduce2 : deg -> poly -> poly list -> coef * poly

val poldepcontent : coef list ref
val coefpoldep_find : poly -> poly -> poly
val coefpoldep_set : poly -> poly -> poly -> unit
val initcoefpoldep : deg -> poly list -> unit
val reduce2_trace : deg -> poly -> poly list -> poly list -> poly list * poly
val spol : deg -> poly -> poly -> poly
val etrangers : deg -> poly -> poly -> bool
val div_ppcm : deg -> poly -> poly -> poly -> bool

val genPcPf : deg -> poly -> poly list -> poly list -> poly list
val genOCPf : deg -> poly list -> poly list

val is_homogeneous : poly -> bool

type certificate =
    { coef : coef; power : int;
      gb_comb : poly list list; last_comb : poly list }
val test_dans_ideal : deg -> poly -> poly list -> poly list ->
  poly list * poly * certificate

val in_ideal : deg -> poly list -> poly -> poly list * poly * certificate

end

module Make (P:Polynom.S) : S with type coef = P.t
