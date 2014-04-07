(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Created by Arnaud Spiwack, May 2007 *)
(* Addition of native Head (nb of heading 0) and Tail (nb of trailing 0) by
   Benjamin Grégoire, Jun 2007 *)

(* This file defines the knowledge that the kernel is able to optimize
   for evaluation in the bytecode virtual machine *)

open Names
open Term

(* Type declarations, these types shouldn't be exported they are accessed
   through specific functions. As being mutable and all it is wiser *)
(* These types are put into two distinct categories: proactive and reactive.
   Proactive information allows to find the name of a combinator, constructor
   or inductive type handling a specific function.
   Reactive information is, on the other hand, everything you need to know
   about a specific name.*)

(* aliased type for clarity purpose*)
type entry = Constr.t

(* the following types correspond to the different "things"
   the kernel can learn about. These are the fields of the proactive knowledge*)
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
  | Int31Lor
  | Int31Land
  | Int31Lxor

type field =
 (* | KEq
  | KNat of nat_field
  | KN of n_field *)
  | KInt31 of string*int31_field


(* record representing all the flags of the internal state of the kernel *)
type flags = {fastcomputation : bool}





(*A definition of maps from strings to pro_int31, to be able
  to have any amount of coq representation for the 31bits integers *)

module Proactive =
  Map.Make (struct type t = field let compare = compare end)

type proactive = entry Proactive.t

(* the reactive knowledge is represented as a functionaly map
   from the type of terms (actually it is the terms whose outermost
   layer is unfolded (typically by Term.kind_of_term)) to the
   type reactive_end which is a record containing all the kind of reactive
   information needed *)
(* todo: because of the bug with output state, reactive_end should eventually
   contain no function. A forseen possibility is to make it a map from
   a finite type describing the fields to the field of proactive retroknowledge
   (and then to make as many functions as needed in environ.ml) *)

module EntryOrd =
struct
  type t = entry
  let compare = Constr.compare
end

module Reactive = Map.Make (EntryOrd)

type reactive_end = {(*information required by the compiler of the VM *)
  vm_compiling :
      (*fastcomputation flag -> continuation -> result *)
      (bool->Cbytecodes.comp_env->constr array ->
       int->Cbytecodes.bytecodes->Cbytecodes.bytecodes)
      option;
  vm_constant_static :
      (*fastcomputation flag -> constructor -> args -> result*)
      (bool->constr array->Cbytecodes.structured_constant)
      option;
  vm_constant_dynamic :
      (*fastcomputation flag -> constructor -> reloc -> args -> sz -> cont -> result *)
      (bool->Cbytecodes.comp_env->Cbytecodes.block array->int->
         Cbytecodes.bytecodes->Cbytecodes.bytecodes)
      option;
  (* fastcomputation flag -> cont -> result *)
  vm_before_match : (bool -> Cbytecodes.bytecodes -> Cbytecodes.bytecodes) option;
  (* tag (= compiled int for instance) -> result *)
  vm_decompile_const : (int -> Term.constr) option;

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



and reactive = reactive_end Reactive.t

and retroknowledge = {flags : flags; proactive : proactive; reactive : reactive}

(* This type represent an atomic action of the retroknowledge. It
   is stored in the compiled libraries *)
(* As per now, there is only the possibility of registering things
   the possibility of unregistering or changing the flag is under study *)
type action =
    | RKRegister of field*entry


(*initialisation*)
let initial_flags =
      {fastcomputation = true;}

let initial_proactive =
  (Proactive.empty:proactive)

let initial_reactive =
  (Reactive.empty:reactive)

let initial_retroknowledge =
  {flags = initial_flags;
   proactive = initial_proactive;
   reactive = initial_reactive }

let empty_reactive_end =
  { vm_compiling = None ;
    vm_constant_static = None;
    vm_constant_dynamic = None;
    vm_before_match = None;
    vm_decompile_const = None;
    native_compiling = None;
    native_constant_static = None;
    native_constant_dynamic = None;
    native_before_match = None;
  }




(* acces functions for proactive retroknowledge *)
let add_field knowledge field value =
  {knowledge with proactive = Proactive.add field value knowledge.proactive}

let mem knowledge field =
  Proactive.mem field knowledge.proactive

let remove knowledge field =
  {knowledge with proactive = Proactive.remove field knowledge.proactive}

let find knowledge field =
  Proactive.find field knowledge.proactive





(*access functions for reactive retroknowledge*)

(* used for compiling of functions (add, mult, etc..) *)
let get_vm_compiling_info knowledge key =
  match (Reactive.find key knowledge.reactive).vm_compiling
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of fully applied constructors *)
let get_vm_constant_static_info knowledge key =
  match (Reactive.find key knowledge.reactive).vm_constant_static
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of partially applied constructors *)
let get_vm_constant_dynamic_info knowledge key =
  match (Reactive.find key knowledge.reactive).vm_constant_dynamic
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

let get_vm_before_match_info knowledge key =
  match (Reactive.find key knowledge.reactive).vm_before_match
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

let get_vm_decompile_constant_info knowledge key =
  match (Reactive.find key knowledge.reactive).vm_decompile_const
  with
    | None -> raise Not_found
    | Some f -> f

let get_native_compiling_info knowledge key =
  match (Reactive.find key knowledge.reactive).native_compiling
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of fully applied constructors *)
let get_native_constant_static_info knowledge key =
  match (Reactive.find key knowledge.reactive).native_constant_static
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of partially applied constructors *)
let get_native_constant_dynamic_info knowledge key =
  match (Reactive.find key knowledge.reactive).native_constant_dynamic
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

let get_native_before_match_info knowledge key =
  match (Reactive.find key knowledge.reactive).native_before_match
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* functions manipulating reactive knowledge *)
let add_vm_compiling_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with vm_compiling = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with vm_compiling = Some nfo}
       knowledge.reactive
  }

let add_vm_constant_static_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with vm_constant_static = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with vm_constant_static = Some nfo}
       knowledge.reactive
  }

let add_vm_constant_dynamic_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with vm_constant_dynamic = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with vm_constant_dynamic = Some nfo}
       knowledge.reactive
  }

let add_vm_before_match_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with vm_before_match = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with vm_before_match = Some nfo}
       knowledge.reactive
  }

let add_vm_decompile_constant_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with vm_decompile_const = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with vm_decompile_const = Some nfo}
       knowledge.reactive
  }

let add_native_compiling_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with native_compiling = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with native_compiling = Some nfo}
       knowledge.reactive
  }

let add_native_constant_static_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with native_constant_static = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with native_constant_static = Some nfo}
       knowledge.reactive
  }

let add_native_constant_dynamic_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with native_constant_dynamic = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with native_constant_dynamic = Some nfo}
       knowledge.reactive
  }

let add_native_before_match_info knowledge value nfo =
  {knowledge with reactive =
   try
     Reactive.add value
       {(Reactive.find value (knowledge.reactive)) with native_before_match = Some nfo}
       knowledge.reactive
   with Not_found ->
     Reactive.add value {empty_reactive_end with native_before_match = Some nfo}
       knowledge.reactive
  }

let clear_info knowledge value =
  {knowledge with reactive = Reactive.remove value knowledge.reactive}
