open Names
open Environ

(** {5 Reduction of primitives} *)
type _ action_kind =
  | IncompatTypes : _ CPrimitives.prim_type -> Constant.t action_kind
  | IncompatInd : _ CPrimitives.prim_ind -> inductive action_kind

type exn += IncompatibleDeclarations : 'a action_kind * 'a * 'a -> exn

(** May raise [IncomtibleDeclarations] *)
val add_retroknowledge : env -> Retroknowledge.action -> env

val get_int_type : env -> Constant.t
val get_float_type : env -> Constant.t
val get_string_type : env -> Constant.t
val get_cmp_type : env -> Constant.t
val get_bool_constructors : env -> constructor * constructor
val get_carry_constructors : env -> constructor * constructor
val get_pair_constructor : env -> constructor
val get_cmp_constructors : env -> constructor * constructor * constructor
val get_f_cmp_constructors : env -> constructor * constructor * constructor * constructor
val get_f_class_constructors :
  env -> constructor * constructor * constructor * constructor
         * constructor * constructor * constructor * constructor
         * constructor

exception NativeDestKO (* Should be raised by get_* functions on failure *)

module type RedNativeEntries =
  sig
    type elem
    type args
    type evd (* will be unit in kernel, evar_map outside *)
    type uinstance

    val get : args -> int -> elem
    val get_int : evd -> elem -> Uint63.t
    val get_float : evd -> elem -> Float64.t
    val get_string : evd -> elem -> Pstring.t
    val get_parray : evd -> elem -> elem Parray.t
    val mkInt : env -> Uint63.t -> elem
    val mkFloat : env -> Float64.t -> elem
    val mkString : env -> Pstring.t -> elem
    val mkBool : env -> bool -> elem
    val mkCarry : env -> bool -> elem -> elem (* true if carry *)
    val mkIntPair : env -> elem -> elem -> elem
    val mkFloatIntPair : env -> elem -> elem -> elem
    val mkLt : env -> elem
    val mkEq : env -> elem
    val mkGt : env -> elem
    val mkFLt : env -> elem
    val mkFEq : env -> elem
    val mkFGt : env -> elem
    val mkFNotComparable : env -> elem
    val mkPNormal : env -> elem
    val mkNNormal : env -> elem
    val mkPSubn : env -> elem
    val mkNSubn : env -> elem
    val mkPZero : env -> elem
    val mkNZero : env -> elem
    val mkPInf : env -> elem
    val mkNInf : env -> elem
    val mkNaN : env -> elem
    val mkArray : env -> uinstance -> elem Parray.t -> elem -> elem
  end

module type RedNative =
 sig
   type elem
   type args
   type evd
   type uinstance
   val red_prim : env -> evd -> CPrimitives.t -> uinstance -> args -> elem option
 end

module RedNative :
  functor (E:RedNativeEntries) ->
    RedNative with type elem = E.elem
    with type args = E.args
    with type evd = E.evd
    with type uinstance = E.uinstance
