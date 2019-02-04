open Names
open Environ

(** {5 Reduction of primitives} *)
val add_retroknowledge : env -> Retroknowledge.action -> env

val get_int_type : env -> Constant.t
val get_bool_constructors : env -> constructor * constructor
val get_carry_constructors : env -> constructor * constructor
val get_pair_constructor : env -> constructor
val get_cmp_constructors : env -> constructor * constructor * constructor

exception NativeDestKO (* Should be raised by get_* functions on failure *)

module type RedNativeEntries =
  sig
    type elem
    type args
    type evd (* will be unit in kernel, evar_map outside *)

    val get : args -> int -> elem
    val get_int : evd -> elem -> Uint63.t
    val mkInt : env -> Uint63.t -> elem
    val mkBool : env -> bool -> elem
    val mkCarry : env -> bool -> elem -> elem (* true if carry *)
    val mkIntPair : env -> elem -> elem -> elem
    val mkLt : env -> elem
    val mkEq : env -> elem
    val mkGt : env -> elem
  end

module type RedNative =
 sig
   type elem
   type args
   type evd
   val red_prim : env -> evd -> CPrimitives.t -> args -> elem option
 end

module RedNative :
  functor (E:RedNativeEntries) ->
    RedNative with type elem = E.elem
    with type args = E.args
    with type evd = E.evd
