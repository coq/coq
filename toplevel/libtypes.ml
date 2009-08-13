(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Term
open Summary
open Libobject

(* 
 * Module construction
 *)
  
let reduce c = Reductionops.head_unfold_under_prod 
  (Auto.Hint_db.transparent_state (Auto.searchtable_map "typeclass_instances"))
  (Global.env()) Evd.empty c

module TypeDnet = Term_dnet.Make(struct 
				   type t = Libnames.global_reference
				   let compare = Pervasives.compare
				   let subst s gr = fst (Libnames.subst_global s gr)
				   let constr_of = Global.type_of_global
				 end)
  (struct let reduce = reduce 
	  let direction = false end)

type result = Libnames.global_reference * (constr*existential_key) * Termops.subst

let all_types = ref TypeDnet.empty
let defined_types = ref TypeDnet.empty

(*
 * Bookeeping & States
 *)

let freeze () = 
  (!all_types,!defined_types)

let unfreeze (lt,dt) = 
  all_types := lt; 
  defined_types := dt

let init () = 
  all_types := TypeDnet.empty; 
  defined_types := TypeDnet.empty

let _ = 
  declare_summary "type-library-state"
    { freeze_function = freeze;
      unfreeze_function = unfreeze;
      init_function = init }

let load (_,d) =
(*  Profile.print_logical_stats !all_types;
  Profile.print_logical_stats d;*)
  all_types := TypeDnet.union d !all_types 

let subst s t = TypeDnet.subst s t
(*
let subst_key = Profile.declare_profile "subst"
let subst a b = Profile.profile2 subst_key TypeDnet.subst a b

let load_key = Profile.declare_profile "load"
let load a = Profile.profile1 load_key load a
*)
let (input,output) = 
  declare_object
    { (default_object "LIBTYPES") with
	load_function = (fun _ -> load);
	subst_function = (fun (_,s,t) -> subst s t);
	export_function = (fun x -> Some x);
	classify_function = (fun x -> Substitute x) 
    }

let update () = Lib.add_anonymous_leaf (input !defined_types)

(* 
 * Search interface
 *)

let search_pattern pat = TypeDnet.search_pattern !all_types pat
let search_concl pat = TypeDnet.search_concl !all_types pat
let search_head_concl pat = TypeDnet.search_head_concl !all_types pat
let search_eq_concl eq pat = TypeDnet.search_eq_concl !all_types eq pat

let add typ gr =
  defined_types := TypeDnet.add typ gr !defined_types;
  all_types := TypeDnet.add typ gr !all_types
(*
let add_key = Profile.declare_profile "add"
let add a b = Profile.profile1 add_key add a b
*)
    
(* 
 * Hooks declaration 
 *)

let _ = Declare.add_cache_hook 
  ( fun sp ->
      let gr = Nametab.global_of_path sp in
      let ty = Global.type_of_global gr in
      add ty gr )

let _ = Declaremods.set_end_library_hook update
