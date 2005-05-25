open Evd
open Libnames
open Coqlib
open Natural
open Term
open Names

let init_constant dir s = gen_constant "Subtac" dir s

let build_sig () = 
  { proj1 = init_constant ["Init"; "Specif"] "proj1_sig";
    proj2 = init_constant ["Init"; "Specif"] "proj2_sig";
    elim = init_constant ["Init"; "Specif"] "sig_rec";
    intro = init_constant ["Init"; "Specif"] "exist";
    typ = init_constant ["Init"; "Specif"] "sig" }

let sig_ = lazy (build_sig ())

let boolind = lazy (gen_constant "subtac" ["Init"; "Datatypes"] "bool")
let sumboolind = lazy (gen_constant "subtac" ["Init"; "Specif"] "sumbool")
let natind = lazy (gen_constant "subtac" ["Init"; "Datatypes"] "nat")
let intind = lazy (gen_constant "subtac" ["ZArith"; "binint"] "Z")
let existSind = lazy (gen_constant "subtac" ["Init"; "Specif"] "sigS")
  
let existS = lazy (build_sigma_set ())

(* orders *)
let lt = lazy (gen_constant "subtac" ["Init"; "Peano"] "lt")
let lt_wf = lazy (gen_constant "subtac" ["Arith"; "Wf_nat"] "lt_wf")

let fix = lazy (gen_constant "subtac" ["Init"; "Wf"] "Fix")

let extconstr = Constrextern.extern_constr true (Global.env ())
let extsort s = Constrextern.extern_constr true (Global.env ()) (mkSort s)

open Pp

let mknewexist = 
  let exist_counter = ref 0 in
    fun () -> let i = exist_counter in
      incr exist_counter;
      !i


let debug_level = ref 0

let debug n s = 
  if n >= !debug_level then
    msgnl s
  else ()

let debug_msg n s = 
  if n >= !debug_level then s
  else mt ()

let trace s = 
  if !debug_level < 2 then msgnl s
  else ()
