(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Arnaud Spiwack, May 2007 *)
(* Addition of native Head (nb of heading 0) and Tail (nb of trailing 0) by
   Benjamin Grégoire, Jun 2007 *)

(* This file defines the knowledge that the kernel is able to optimize. *)

open Names

type retroknowledge = {
    retro_int63 : Constant.t option;
    retro_float64 : Constant.t option;
    retro_string : Constant.t option;
    retro_array : Constant.t option;
    retro_bool : (constructor * constructor) option; (* true, false *)
    retro_carry : (constructor * constructor) option; (* C0, C1 *)
    retro_pair : constructor option;
    retro_cmp : (constructor * constructor * constructor) option;
                    (* Eq, Lt, Gt *)
    retro_f_cmp : (constructor * constructor * constructor * constructor)
                  option;
                  (* FEq, FLt, FGt, FNotComparable *)
    retro_f_class : (constructor * constructor * constructor * constructor
                     * constructor * constructor * constructor * constructor
                     * constructor)
                      option;
                    (* PNormal, NNormal, PSubn, NSubn,
                       PZero, NZero, PInf, NInf,
                       NaN *)
}

let empty = {
    retro_int63 = None;
    retro_float64 = None;
    retro_string = None;
    retro_array = None;
    retro_bool = None;
    retro_carry = None;
    retro_pair = None;
    retro_cmp = None;
    retro_f_cmp = None;
    retro_f_class = None;
}

type action =
  | Register_ind : 'a CPrimitives.prim_ind * inductive -> action
  | Register_type : 'a CPrimitives.prim_type * Constant.t -> action
