(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

open Pmisc
open Past
open Ptype
open Names
open Nameops
open Libobject
open Library
open Term

(* Environments for imperative programs.
 *
 * An environment of programs is an association tables
 * from identifiers (Names.identifier) to types of values with effects
 * (ProgAst.ml_type_v), together with a list of these associations, since
 * the order is relevant (we have dependent types e.g. [x:nat; t:(array x T)])
 *)

module Env = struct
  type 'a t = ('a Idmap.t)
	    * ((identifier * 'a) list)
	    * ((identifier * (identifier * variant)) list)
  let empty = Idmap.empty, [], []
  let add id v (m,l,r) = (Idmap.add id v m, (id,v)::l, r)
  let find id (m,_,_) = Idmap.find id m
  let fold f (_,l,_) x0 = List.fold_right f l x0
  let add_rec (id,var) (m,l,r) = (m,l,(id,var)::r)
  let find_rec id (_,_,r) = List.assoc id r
end

(* Local environments *)

type type_info = Set | TypeV of type_v

type local_env = type_info Env.t

let empty = (Env.empty : local_env)

let add (id,v) = Env.add id (TypeV v)

let add_set id = Env.add id Set

let find id env =
  match Env.find id env with TypeV v -> v | Set -> raise Not_found

let is_local env id =
  try
    match Env.find id env with TypeV _ -> true | Set -> false
  with
      Not_found -> false

let is_local_set env id =
  try
    match Env.find id env with TypeV _ -> false | Set -> true
  with
      Not_found -> false


(* typed programs *)

type typing_info = {
  env : local_env;
  kappa : constr ml_type_c
}
  
type typed_program = (typing_info, constr) t


(* The global environment.
 *
 * We have a global typing environment env
 * We also keep a table of programs for extraction purposes
 * and a table of initializations (still for extraction)
 *)

let (env : type_info Env.t ref) = ref Env.empty

let (pgm_table : (typed_program option) Idmap.t ref) = ref Idmap.empty

let (init_table : constr Idmap.t ref) = ref Idmap.empty

let freeze () = (!env, !pgm_table, !init_table)
let unfreeze (e,p,i) = env := e; pgm_table := p; init_table := i
let init () = 
  env := Env.empty; pgm_table := Idmap.empty; init_table := Idmap.empty
;;

Summary.declare_summary "programs-environment"
  { Summary.freeze_function = freeze;
    Summary.unfreeze_function = unfreeze;
    Summary.init_function = init;
    Summary.survive_module = false;
    Summary.survive_section = false }
;;

(* Operations on the global environment. *)

let add_pgm id p = pgm_table := Idmap.add id p !pgm_table

let cache_global (_,(id,v,p)) =
  env := Env.add id v !env; add_pgm id p

let type_info_app f = function Set -> Set | TypeV v -> TypeV (f v)

let subst_global (_,s,(id,v,p)) = (id, type_info_app (type_v_knsubst s) v, p)

let (inProg,outProg) =
  declare_object { object_name = "programs-objects";
                   cache_function = cache_global;
                   load_function = (fun _ -> cache_global);
                   open_function = (fun _ _ -> ());
		   classify_function = (fun (_,x) -> Substitute x);
		   subst_function = subst_global;
		   export_function = (fun x -> Some x) }

let is_mutable = function Ref _ | Array _ -> true | _ -> false

let add_global id v p =
  try
    let _ = Env.find id !env in
    Perror.clash id None
  with
    Not_found -> begin
      let id' =
	if is_mutable v then id 
        else id_of_string ("prog_" ^ (string_of_id id)) 
      in
      Lib.add_leaf id' (inProg (id,TypeV v,p))
    end

let add_global_set id =
  try
    let _ = Env.find id !env in
    Perror.clash id None
  with
    Not_found -> Lib.add_leaf id (inProg (id,Set,None))

let is_global id =
  try
    match Env.find id !env with TypeV _ -> true | Set -> false
  with
    Not_found -> false

let is_global_set id =
  try
    match Env.find id !env with TypeV _ -> false | Set -> true
  with
    Not_found -> false


let lookup_global id =
  match Env.find id !env with TypeV v -> v | Set -> raise Not_found

let find_pgm id = Idmap.find id !pgm_table

let all_vars () =
  Env.fold
    (fun (id,v) l -> match v with TypeV (Arrow _|TypePure _) -> id::l | _ -> l)
    !env []

let all_refs () =
  Env.fold
    (fun (id,v) l -> match v with TypeV (Ref _ | Array _) -> id::l | _ -> l)
    !env []

(* initializations *)

let cache_init (_,(id,c)) =
  init_table := Idmap.add id c !init_table

let subst_init (_,s,(id,c)) = (id, subst_mps s c)

let (inInit,outInit) =
  declare_object { object_name = "programs-objects-init";
                   cache_function = cache_init;
                   load_function = (fun _ -> cache_init);
		   open_function = (fun _ _-> ());
		   classify_function = (fun (_,x) -> Substitute x);
		   subst_function = subst_init;
                   export_function = (fun x -> Some x) }

let initialize id c = Lib.add_anonymous_leaf (inInit (id,c))

let find_init id = Idmap.find id !init_table


(* access in env, local then global *)

let type_in_env env id =
  try find id env with Not_found -> lookup_global id

let is_in_env env id =
  (is_global id) or (is_local env id)

let fold_all f lenv x0 =
  let x1 = Env.fold f !env x0 in
  Env.fold f lenv x1


(* recursions *)

let add_recursion = Env.add_rec

let find_recursion = Env.find_rec


(* We also maintain a table of the currently edited proofs of programs
 * in order to add them in the environnement when the user does Save *)

open Pp
open Himsg

let (edited : (type_v * typed_program) Idmap.t ref) = ref Idmap.empty

let new_edited id v =
  edited := Idmap.add id v !edited

let is_edited id =
  try let _ = Idmap.find id !edited in true with Not_found -> false

let register id id' =
  try
    let (v,p) = Idmap.find id !edited in
    let _ = add_global id' v (Some p) in
    Flags.if_verbose 
      msgnl (hov 0 (str"Program " ++ pr_id id' ++ spc () ++ str"is defined"));
    edited := Idmap.remove id !edited
  with Not_found -> ()

