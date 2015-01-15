open Names
open Cbytecodes
open Cemitcodes
open Term
open Declarations
open Pre_env


val compile : env -> constr -> bytecodes * bytecodes * fv
                              (** init, fun, fv *)

val compile_constant_body : env -> constant_def -> body_code

(** Shortcut of the previous function used during module strengthening *)

val compile_alias : pconstant -> body_code

(** spiwack: this function contains the information needed to perform
            the static compilation of int31 (trying and obtaining
            a 31-bit integer in processor representation at compile time) *)
val compile_structured_int31 : bool -> constr array ->
                               structured_constant

(** this function contains the information needed to perform
        the dynamic compilation of int31 (trying and obtaining a
        31-bit integer in processor representation at runtime when
        it failed at compile time *)
val dynamic_int31_compilation : bool -> comp_env ->
                                block array ->
                                int -> bytecodes -> bytecodes

(*spiwack: template for the compilation n-ary operation, invariant: n>=1.
           works as follow: checks if all the arguments are non-pointers
           if they are applies the operation (second argument) if not
           all of them are, returns to a coq definition (third argument) *)
val op_compilation : int -> instruction -> pconstant -> bool -> comp_env ->
                             constr array -> int -> bytecodes-> bytecodes

(*spiwack: compiling function to insert dynamic decompilation before
           matching integers (in case they are in processor representation) *)
val int31_escape_before_match : bool -> bytecodes -> bytecodes
