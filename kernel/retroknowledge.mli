(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

type retroknowledge

(** aliased type for clarity purpose*)
type entry = Constr.t

(** the following types correspond to the different "things"
   the kernel can learn about.*)
type int31_field =
  | Int31Bits
  | Int31Type
  | Int31Constructor
  | Int31Twice
  | Int31TwicePlusOne
  | Int31Phi
  | Int31PhiInv
  | Int31Plus
  | Int31PlusC
  | Int31PlusCarryC
  | Int31Minus
  | Int31MinusC
  | Int31MinusCarryC
  | Int31Times
  | Int31TimesC
  | Int31Div21
  | Int31Div
  | Int31Diveucl
  | Int31AddMulDiv
  | Int31Compare
  | Int31Head0
  | Int31Tail0
  | Int31Lor
  | Int31Land
  | Int31Lxor

type field =
  | KInt31 of string*int31_field

(** This type represent an atomic action of the retroknowledge. It
   is stored in the compiled libraries 
   As per now, there is only the possibility of registering things
   the possibility of unregistering or changing the flag is under study *)
type action =
    | RKRegister of field*entry


(** initial value for retroknowledge *)
val initial_retroknowledge : retroknowledge


(** Given an identifier id (usually Const _)
   and the continuation cont of the bytecode compilation
   returns the compilation of id in cont if it has a specific treatment
   or raises Not_found if id should be compiled as usual *)
val get_vm_compiling_info  : retroknowledge -> entry ->
                             Cinstr.lambda array -> Cinstr.lambda
(*Given an identifier id (usually Construct _)
   and its argument array, returns a function that tries an ad-hoc optimisated
   compilation (in the case of the 31-bit integers it means compiling them
   directly into an integer)
   raises Not_found if id should be compiled as usual, and expectingly
   CBytecodes.NotClosed if the term is not a closed constructor pattern
   (a constant for the compiler) *)
val get_vm_constant_static_info : retroknowledge -> entry ->
                                   constr array -> Cinstr.lambda

(*Given an identifier id (usually Construct _ )
   its argument array and a continuation, returns the compiled version
   of id+args+cont when id has a specific treatment (in the case of
   31-bit integers, that would be the dynamic compilation into integers)
   or raises Not_found if id should be compiled as usual *)
val get_vm_constant_dynamic_info : retroknowledge -> entry ->
                                   Cinstr.lambda array -> Cinstr.lambda

(** Given a type identifier, this function is used before compiling a match
   over this type. In the case of 31-bit integers for instance, it is used
   to add the instruction sequence which would perform a dynamic decompilation
   in case the argument of the match is not in coq representation *)
val get_vm_before_match_info : retroknowledge -> entry -> Cinstr.lambda
                                                       -> Cinstr.lambda

(** Given a type identifier, this function is used by pretyping/vnorm.ml to
   recover the elements of that type from their compiled form if it's non
   standard (it is used (and can be used) only when the compiled form
   is not a block *)
val get_vm_decompile_constant_info : retroknowledge -> entry -> int -> constr


val get_native_compiling_info  : retroknowledge -> entry -> Nativeinstr.prefix ->
				 Nativeinstr.lambda array -> Nativeinstr.lambda

val get_native_constant_static_info : retroknowledge -> entry ->
                                      constr array -> Nativeinstr.lambda

val get_native_constant_dynamic_info : retroknowledge -> entry ->
                                       Nativeinstr.prefix -> constructor ->
				       Nativeinstr.lambda array ->
				       Nativeinstr.lambda

val get_native_before_match_info : retroknowledge -> entry ->
				   Nativeinstr.prefix -> constructor ->
				   Nativeinstr.lambda -> Nativeinstr.lambda


(** the following functions are solely used in Environ and Safe_typing to implement
   the functions  register and unregister (and mem) of Environ *)
val add_field : retroknowledge -> field -> entry -> retroknowledge
val mem : retroknowledge -> field -> bool
(* val remove : retroknowledge -> field -> retroknowledge *)
val find : retroknowledge -> field -> entry


(** Dispatching type for the above [get_*] functions. *)
type reactive_info = {(*information required by the compiler of the VM *)
  vm_compiling :
      (*fastcomputation flag -> continuation -> result *)
      (bool -> Cinstr.lambda array -> Cinstr.lambda)
      option;
  vm_constant_static :
      (*fastcomputation flag -> constructor -> args -> result*)
      (bool -> constr array -> Cinstr.lambda)
      option;
  vm_constant_dynamic :
      (*fastcomputation flag -> constructor -> reloc -> args -> sz -> cont -> result *)
      (bool -> Cinstr.lambda array -> Cinstr.lambda)
      option;
  (* fastcomputation flag -> cont -> result *)
  vm_before_match : (bool -> Cinstr.lambda -> Cinstr.lambda) option;
  (* tag (= compiled int for instance) -> result *)
  vm_decompile_const : (int -> constr) option;

  native_compiling :
      (bool -> Nativeinstr.prefix -> Nativeinstr.lambda array ->
       Nativeinstr.lambda) option;

  native_constant_static :
      (bool -> constr array -> Nativeinstr.lambda) option;

  native_constant_dynamic :
      (bool -> Nativeinstr.prefix -> constructor ->
       Nativeinstr.lambda array -> Nativeinstr.lambda) option;

  native_before_match : (bool -> Nativeinstr.prefix -> constructor ->
			 Nativeinstr.lambda -> Nativeinstr.lambda) option

}

val empty_reactive_info : reactive_info

(** Hook to be set after the compiler are installed to dispatch fields
    into the above [get_*] functions. *)
val dispatch_hook : (retroknowledge -> entry -> field -> reactive_info) Hook.t
