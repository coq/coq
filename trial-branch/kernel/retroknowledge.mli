(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: retroknowledge.mli ??? 2006-??-?? ??:??:??Z spiwack $ i*)

(*i*)
open Names
open Term
(*i*)

type retroknowledge

(* aliased type for clarity purpose*)
type entry =  (constr, types) kind_of_term

(* the following types correspond to the different "things"
   the kernel can learn about.*)
type nat_field =
  | NatType
  | NatPlus
  | NatTimes
  
type n_field = 
  | NPositive
  | NType
  | NTwice
  | NTwicePlusOne
  | NPhi
  | NPhiInv
  | NPlus
  | NTimes

type int31_field = 
  | Int31Bits
  | Int31Type
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
  | Int31AddMulDiv
  | Int31Compare
  | Int31Head0
  | Int31Tail0

type field =
(*  | KEq
  | KNat of nat_field
  | KN of n_field *)
  | KInt31 of string*int31_field


(* This type represent an atomic action of the retroknowledge. It
   is stored in the compiled libraries *)
(* As per now, there is only the possibility of registering things
   the possibility of unregistering or changing the flag is under study *)
type action =
    | RKRegister of field*entry


(* initial value for retroknowledge *)
val initial_retroknowledge : retroknowledge


(* Given an identifier id (usually Const _)
   and the continuation cont of the bytecode compilation
   returns the compilation of id in cont if it has a specific treatment
   or raises Not_found if id should be compiled as usual *)
val get_vm_compiling_info  : retroknowledge -> entry -> Cbytecodes.comp_env ->
                             constr array -> 
                             int -> Cbytecodes.bytecodes-> Cbytecodes.bytecodes
(*Given an identifier id (usually Construct _)
   and its argument array, returns a function that tries an ad-hoc optimisated
   compilation (in the case of the 31-bit integers it means compiling them
   directly into an integer)
   raises Not_found if id should be compiled as usual, and expectingly
   CBytecodes.NotClosed if the term is not a closed constructor pattern 
   (a constant for the compiler) *)
val get_vm_constant_static_info : retroknowledge -> entry ->
                                   constr array ->
                                   Cbytecodes.structured_constant

(*Given an identifier id (usually Construct _ )
   its argument array and a continuation, returns the compiled version
   of id+args+cont when id has a specific treatment (in the case of
   31-bit integers, that would be the dynamic compilation into integers)
   or raises Not_found if id should be compiled as usual *)
val get_vm_constant_dynamic_info : retroknowledge -> entry -> 
                                Cbytecodes.comp_env -> 
                                Cbytecodes.block array -> 
                                int -> Cbytecodes.bytecodes -> Cbytecodes.bytecodes
(* Given a type identifier, this function is used before compiling a match 
   over this type. In the case of 31-bit integers for instance, it is used 
   to add the instruction sequence which would perform a dynamic decompilation
   in case the argument of the match is not in coq representation *)
val get_vm_before_match_info : retroknowledge -> entry -> Cbytecodes.bytecodes
                                                       -> Cbytecodes.bytecodes

(* Given a type identifier, this function is used by pretyping/vnorm.ml to 
   recover the elements of that type from their compiled form if it's non 
   standard (it is used (and can be used) only when the compiled form
   is not a block *)
val get_vm_decompile_constant_info : retroknowledge -> entry -> int -> Term.constr


(* the following functions are solely used in Pre_env and Environ to implement
   the functions  register and unregister (and mem) of Environ *)
val add_field : retroknowledge -> field -> entry -> retroknowledge
val mem : retroknowledge -> field -> bool
val remove : retroknowledge -> field -> retroknowledge
val find : retroknowledge -> field -> entry

(* the following function manipulate the reactive information of values
   they are only used by the functions of Pre_env, and Environ to implement
   the functions register and unregister of Environ *)
val add_vm_compiling_info : retroknowledge-> entry -> 
                            (bool -> Cbytecodes.comp_env -> constr array -> int ->
                            Cbytecodes.bytecodes -> Cbytecodes.bytecodes) ->
                            retroknowledge
val add_vm_constant_static_info : retroknowledge-> entry -> 
                                  (bool->constr array->
                                      Cbytecodes.structured_constant) ->
                                  retroknowledge
val add_vm_constant_dynamic_info : retroknowledge-> entry -> 
                                   (bool -> Cbytecodes.comp_env -> 
                                   Cbytecodes.block array -> int -> 
                                   Cbytecodes.bytecodes -> Cbytecodes.bytecodes) ->
                                   retroknowledge
val add_vm_before_match_info : retroknowledge -> entry ->
                              (bool->Cbytecodes.bytecodes->Cbytecodes.bytecodes) ->
                              retroknowledge

val add_vm_decompile_constant_info : retroknowledge -> entry -> 
                                    (int -> constr) -> retroknowledge
                                      

val clear_info : retroknowledge-> entry -> retroknowledge



