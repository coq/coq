(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Building recursive polynom operations from a type of coefficients *)

module type Coef = sig
  type t
  val equal : t -> t -> bool
  val lt : t -> t -> bool
  val le : t -> t -> bool
  val abs : t -> t
  val plus : t -> t -> t
  val mult : t -> t -> t
  val sub : t -> t -> t
  val opp : t -> t
  val div : t -> t -> t
  val modulo : t -> t -> t
  val puis : t -> int -> t
  val pgcd : t -> t -> t

  val hash : t -> int
  val of_num : Num.num -> t
  val to_string : t -> string
end

module type S = sig
  type coef
  type variable = int
  type t = Pint of coef | Prec of variable * t array

  val of_num : Num.num -> t
  val x : variable -> t
  val monome : variable -> int -> t
  val is_constantP : t -> bool
  val is_zero : t -> bool

  val max_var_pol : t -> variable
  val max_var_pol2 : t -> variable
  val max_var : t array -> variable
  val equal : t -> t -> bool
  val norm : t -> t
  val deg : variable -> t -> int
  val deg_total : t -> int
  val copyP : t -> t
  val coef : variable -> int -> t -> t

  val plusP : t -> t -> t
  val content : t -> coef
  val div_int : t -> coef -> t
  val vire_contenu : t -> t
  val vars : t -> variable list
  val int_of_Pint : t -> coef
  val multx : int -> variable -> t -> t
  val multP : t -> t -> t
  val deriv : variable -> t -> t
  val oppP : t -> t
  val moinsP : t -> t -> t
  val puisP : t -> int -> t
  val ( @@ ) : t -> t -> t
  val ( -- ) : t -> t -> t
  val ( ^^ ) : t -> int -> t
  val coefDom : variable -> t -> t
  val coefConst : variable -> t -> t
  val remP : variable -> t -> t
  val coef_int_tete : t -> coef
  val normc : t -> t
  val coef_constant : t -> coef
  val univ : bool ref
  val string_of_var : int -> string
  val nsP : int ref
  val to_string : t -> string
  val printP : t -> unit
  val print_tpoly : t array -> unit
  val print_lpoly : t list -> unit
  val quo_rem_pol : t -> t -> variable -> t * t
  val div_pol : t -> t -> variable -> t
  val divP : t -> t -> t
  val div_pol_rat : t -> t -> bool
  val pseudo_div : t -> t -> variable -> t * t * int * t
  val pgcdP : t -> t -> t
  val pgcd_pol : t -> t -> variable -> t
  val content_pol : t -> variable -> t
  val pgcd_coef_pol : t -> t -> variable -> t
  val pgcd_pol_rec : t -> t -> variable -> t
  val gcd_sub_res : t -> t -> variable -> t
  val gcd_sub_res_rec : t -> t -> t -> t -> int -> variable -> t
  val lazard_power : t -> t -> int -> variable -> t
  val hash : t -> int
  module Hashpol : Hashtbl.S with type key=t
end

module Make (C:Coef) : S with type coef = C.t
