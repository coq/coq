(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Names

(* Priority for the expansion of constant in the conversion test.
 * Higher levels means that the expansion is less prioritary.
 * (And Expand stands for -oo, and Opaque +oo.)
 * The default value is [Level 100].
 *)
type level = Expand | Level of int | Opaque
let default = Level 0
let transparent = default

type oracle = level Idmap.t * level Cmap.t

let var_opacity = ref Idmap.empty
let cst_opacity = ref Cmap.empty

let get_strategy = function
  | VarKey id ->
      (try Idmap.find id !var_opacity
      with Not_found -> default)
  | ConstKey c ->
      (try Cmap.find c !cst_opacity
      with Not_found -> default)
  | RelKey _ -> Expand

let set_strategy k l =
  match k with
  | VarKey id ->
      var_opacity :=
      if l=default then Idmap.remove id !var_opacity
      else Idmap.add id l !var_opacity
  | ConstKey c ->
      cst_opacity :=
      if l=default then Cmap.remove c !cst_opacity
      else Cmap.add c l !cst_opacity
  | RelKey _ -> Util.error "set_strategy: RelKey"

let get_transp_state () =
  (Idmap.fold
    (fun id l ts -> if  l=Opaque then Idpred.remove id ts else ts)
    !var_opacity Idpred.full,
   Cmap.fold
    (fun c l ts -> if  l=Opaque then Cpred.remove c ts else ts)
    !cst_opacity Cpred.full)

(* Unfold the first constant only if it is "more transparent" than the
   second one. In case of tie, expand the second one. *)
let oracle_order k1 k2 =
  match get_strategy k1, get_strategy k2 with
    | Expand, _ -> true
    | Level n1, Opaque -> true
    | Level n1, Level n2 -> n1 < n2
    | _ -> false (* expand k2 *)

(* summary operations *)
let init() = (cst_opacity := Cmap.empty; var_opacity := Idmap.empty)
let freeze () = (!var_opacity, !cst_opacity)
let unfreeze (vo,co) = (cst_opacity := co; var_opacity := vo)
