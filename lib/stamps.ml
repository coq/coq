(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

let new_stamp = 
  let stamp_ctr = ref 0 in
  fun () -> incr stamp_ctr; !stamp_ctr

type 'a timestamped = { stamp : int; ed : 'a }

let ts_stamp st = st.stamp
let ts_mod f st = { stamp = new_stamp(); ed = f st.ed }
let ts_it st = st.ed
let ts_mk v = { stamp = new_stamp(); ed = v}
let ts_eq st1 st2 = st1.stamp = st2.stamp

type 'a idstamped = 'a timestamped

let ids_mod f st = { stamp = st.stamp; ed = f st.ed}
let ids_it = ts_it
let ids_mk = ts_mk
let ids_eq = ts_eq
