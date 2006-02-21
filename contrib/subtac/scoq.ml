open Evd
open Libnames
open Coqlib
open Term
open Names
open Util

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

type recursion_order =
  | StructRec of name located
  | WfRec of Topconstr.constr_expr * name located

type binders = Topconstr.local_binder list

let app_opt c e = 
  match c with
      Some constr -> constr e
    | None -> e	

let make_existential loc env nonimplicit isevars c =
  let evar = Evarutil.e_new_evar isevars env ~src:(loc, QuestionMark) c in
  let (key, args) = destEvar evar in
    debug 2 (str "Constructed evar " ++ int key ++ str " applied to args: " ++
	     Array.fold_right (fun a acc -> my_print_constr env a ++ spc () ++ acc) args (str ""));
    nonimplicit := Gset.add key !nonimplicit;
    evar

let string_of_hole_kind = function
  | ImplicitArg _ -> "ImplicitArg"
  | BinderType _ -> "BinderType"
  | QuestionMark -> "QuestionMark"
  | CasesType -> "CasesType"
  | InternalHole -> "InternalHole"
  | TomatchTypeParameter _ -> "TomatchTypeParameter"
      
let non_instanciated_map env nonimplicit evd =
  let evm = evars_of !evd in
    List.fold_left 
      (fun evm (key, evi) -> 
	 let (loc,k) = evar_source key !evd in
	   debug 2 (str "evar " ++ int key ++ str " has kind " ++ 
		    str (string_of_hole_kind k));
	   if Gset.mem key !nonimplicit then
	     begin
	       debug 2 (str " and is not an implicit");
	       Evd.add evm key evi
	     end
	   else
	     let (loc,k) = evar_source key !evd in
	       debug 2 (str " and is an implicit");
	       Pretype_errors.error_unsolvable_implicit loc env evm k)
      Evd.empty (Evarutil.non_instantiated evm)

