(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Names
open Mod_subst

let eq_scheme_map = ref Indmap.empty

let cache_scheme (_,(ind,const)) =
    eq_scheme_map := Indmap.add ind const (!eq_scheme_map)



let _ = Summary.declare_summary "eqscheme"
    { Summary.freeze_function = (fun () -> !eq_scheme_map);
      Summary.unfreeze_function = (fun fs -> eq_scheme_map := fs);
      Summary.init_function = (fun () -> eq_scheme_map := Indmap.empty) }

let find_eq_scheme ind =
  Indmap.find ind !eq_scheme_map

let check_eq_scheme ind =
  Indmap.mem ind !eq_scheme_map

let bl_map = ref Indmap.empty
let lb_map = ref Indmap.empty
let dec_map = ref Indmap.empty


let cache_bl (_,(ind,const)) =
    bl_map := Indmap.add ind const (!bl_map)

let cache_lb (_,(ind,const)) =
    lb_map := Indmap.add ind const (!lb_map)

let cache_dec (_,(ind,const)) =
    dec_map := Indmap.add ind const (!dec_map)



let _ = Summary.declare_summary "bl_proof"
    { Summary.freeze_function = (fun () -> !bl_map);
      Summary.unfreeze_function = (fun fs -> bl_map := fs);
      Summary.init_function = (fun () -> bl_map := Indmap.empty) }

let find_bl_proof ind =
  Indmap.find ind !bl_map

let check_bl_proof ind =
  Indmap.mem ind !bl_map

let _ = Summary.declare_summary "lb_proof"
    { Summary.freeze_function = (fun () -> !lb_map);
      Summary.unfreeze_function = (fun fs -> lb_map := fs);
      Summary.init_function = (fun () -> lb_map := Indmap.empty) }

let find_lb_proof ind =
  Indmap.find ind !lb_map

let check_lb_proof ind =
  Indmap.mem ind !lb_map

let _ = Summary.declare_summary "eq_dec_proof"
    { Summary.freeze_function = (fun () -> !dec_map);
      Summary.unfreeze_function = (fun fs -> dec_map := fs);
      Summary.init_function = (fun () -> dec_map := Indmap.empty) }

let find_eq_dec_proof ind =
  Indmap.find ind !dec_map

let check_dec_proof ind =
  Indmap.mem ind !dec_map



