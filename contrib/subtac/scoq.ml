open Evd
open Libnames
open Coqlib
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

let eqind = lazy (gen_constant "subtac" ["Init"; "Logic"] "eq")

let boolind = lazy (gen_constant "subtac" ["Init"; "Datatypes"] "bool")
let sumboolind = lazy (gen_constant "subtac" ["Init"; "Specif"] "sumbool")
let natind = lazy (gen_constant "subtac" ["Init"; "Datatypes"] "nat")
let intind = lazy (gen_constant "subtac" ["ZArith"; "binint"] "Z")
let existSind = lazy (gen_constant "subtac" ["Init"; "Specif"] "sigS")
  
let existS = lazy (build_sigma_set ())

(* orders *)
let well_founded = lazy (gen_constant "subtac" ["Init"; "Wf"] "well_founded")
let fix = lazy (gen_constant "subtac" ["Init"; "Wf"] "Fix")

let extconstr = Constrextern.extern_constr true (Global.env ())
let extsort s = Constrextern.extern_constr true (Global.env ()) (mkSort s)

open Pp

let my_print_constr = Termops.print_constr_env
let my_print_context = Termops.print_rel_context
let my_print_rawconstr = Printer.pr_rawconstr_env

let mknewexist = 
  let exist_counter = ref 0 in
    fun () -> let i = exist_counter in
      incr exist_counter;
      !i

let debug_level = ref 0

let debug n s = 
  if n >= !debug_level then (
    msgnl s;
    msg_warning s;
  ) else ()

let debug_msg n s = 
  if n >= !debug_level then s
  else mt ()

let trace s = 
  if !debug_level < 2 then (msgnl s)
  else ()

let wf_relations = Hashtbl.create 10

let std_relations () = 
  let add k v = Hashtbl.add wf_relations k v in
    add (gen_constant "subtac" ["Init"; "Peano"] "lt")
      (lazy (gen_constant "subtac" ["Arith"; "Wf_nat"] "lt_wf"))
      
let std_relations = Lazy.lazy_from_fun std_relations

type wf_proof_type = 
    AutoProof 
  | ManualProof of Topconstr.constr_expr
  | ExistentialProof

let app_opt c e = 
  match c with
      Some constr -> constr e
    | None -> e	

let make_existential loc env nonimplicit isevars c =
  let key = mknewexist () in
  let args = Sign.instance_from_named_context (Environ.named_context env) in
    isevars :=
      Evd.evar_declare (Environ.named_context_val env) key c ~src:(loc, InternalHole) !isevars;
    nonimplicit := Gset.add key !nonimplicit;
    mkEvar(key, args)

let non_instanciated_map env nonimplicit evd =
  let evm = evars_of !evd in
    List.fold_left 
      (fun evm (key, evi) -> 
	 if Gset.mem key !nonimplicit then
	   Evd.add evm key evi
	 else
	   let (loc,k) = evar_source key !evd in
	     Pretype_errors.error_unsolvable_implicit loc env evm k)
      Evd.empty (Evarutil.non_instantiated evm)
