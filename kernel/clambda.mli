open Names
open Cinstr

exception TooLargeInductive of Pp.t

val lambda_of_constr : optimize:bool -> Pre_env.env -> Constr.t -> lambda

val decompose_Llam : lambda -> Name.t array * lambda

val get_alias : Pre_env.env -> Constant.t -> Constant.t

val compile_prim : int -> Cbytecodes.instruction -> Constr.pconstant -> bool -> lambda array -> lambda

(** spiwack: this function contains the information needed to perform
            the static compilation of int31 (trying and obtaining
            a 31-bit integer in processor representation at compile time) *)
val compile_structured_int31 : bool -> Constr.t array -> lambda

(** this function contains the information needed to perform
        the dynamic compilation of int31 (trying and obtaining a
        31-bit integer in processor representation at runtime when
        it failed at compile time *)
val dynamic_int31_compilation : bool -> lambda array -> lambda

(*spiwack: compiling function to insert dynamic decompilation before
           matching integers (in case they are in processor representation) *)
val int31_escape_before_match : bool -> lambda -> lambda
