
(* $Id$ *)

open Typing
open Summary

(* We introduce here the global environment of the system, and we declare it
   as a synchronized table. *)

let global_env = ref empty_environment

let _ = 
  declare_summary "Global environment"
    { freeze_function = (fun () -> !global_env);
      unfreeze_function = (fun fr -> global_env := fr);
      init_function = (fun () -> global_env := empty_environment) }

(* Then we export the functions of [Typing] on that environment. *)

let evar_map () = evar_map !global_env
let universes () = universes !global_env
let metamap () = metamap !global_env
let context () = context !global_env

let push_var idc = global_env := push_var idc !global_env
let push_rel nac = global_env := push_rel nac !global_env
let add_constant sp ce = global_env := add_constant sp ce !global_env
let add_parameter sp c = global_env := add_parameter sp c !global_env
let add_mind sp mie = global_env := add_mind sp mie !global_env

let lookup_var id = lookup_var id !global_env
let lookup_rel n = lookup_rel n !global_env
let lookup_constant sp = lookup_constant sp !global_env
let lookup_mind sp = lookup_mind sp !global_env
let lookup_mind_specif c = lookup_mind_specif c !global_env
let lookup_meta n = lookup_meta n !global_env

let export s = export !global_env s
let import cenv = global_env := import cenv !global_env
