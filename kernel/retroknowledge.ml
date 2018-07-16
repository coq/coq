(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Arnaud Spiwack, May 2007 *)
(* Addition of native Head (nb of heading 0) and Tail (nb of trailing 0) by
   Benjamin Grégoire, Jun 2007 *)

(* This file defines the knowledge that the kernel is able to optimize
   for evaluation in the bytecode virtual machine *)

open Names
open Constr

(* The retroknowledge defines a bijective correspondance between some
   [entry]-s (which are, in fact, merely terms) and [field]-s which
   are roles assigned to these entries. *)

(* aliased type for clarity purpose*)
type entry = Constr.t

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


(* record representing all the flags of the internal state of the kernel *)
type flags = {fastcomputation : bool}





(* The [proactive] knowledge contains the mapping [field->entry]. *)

module Proactive =
  Map.Make (struct type t = field let compare = Pervasives.compare end)

type proactive = entry Proactive.t

(* The [reactive] knowledge contains the mapping
   [entry->field]. Fields are later to be interpreted as a
   [reactive_info]. *)

module EntryOrd =
struct
  type t = entry
  let compare = Constr.compare
end

module Reactive = Map.Make (EntryOrd)

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



and reactive = field Reactive.t

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

let empty_reactive_info =
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



(* adds a binding [entry<->field]. *)
let add_field knowledge field entry =
  {knowledge with
    proactive = Proactive.add field entry knowledge.proactive;
    reactive = Reactive.add entry field knowledge.reactive}

(* acces functions for proactive retroknowledge *)
let mem knowledge field =
  Proactive.mem field knowledge.proactive

let find knowledge field =
  Proactive.find field knowledge.proactive


let (dispatch,dispatch_hook) = Hook.make ()

let dispatch_reactive entry retroknowledge =
  Hook.get dispatch retroknowledge entry (Reactive.find entry retroknowledge.reactive)

(*access functions for reactive retroknowledge*)

(* used for compiling of functions (add, mult, etc..) *)
let get_vm_compiling_info knowledge key =
  match (dispatch_reactive key knowledge).vm_compiling
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of fully applied constructors *)
let get_vm_constant_static_info knowledge key =
  match (dispatch_reactive key knowledge).vm_constant_static
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of partially applied constructors *)
let get_vm_constant_dynamic_info knowledge key =
  match (dispatch_reactive key knowledge).vm_constant_dynamic
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

let get_vm_before_match_info knowledge key =
  match (dispatch_reactive key knowledge).vm_before_match
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

let get_vm_decompile_constant_info knowledge key =
  match (dispatch_reactive key knowledge).vm_decompile_const
  with
    | None -> raise Not_found
    | Some f -> f

let get_native_compiling_info knowledge key =
  match (dispatch_reactive key knowledge).native_compiling
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of fully applied constructors *)
let get_native_constant_static_info knowledge key =
  match (dispatch_reactive key knowledge).native_constant_static
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

(* used for compilation of partially applied constructors *)
let get_native_constant_dynamic_info knowledge key =
  match (dispatch_reactive key knowledge).native_constant_dynamic
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation

let get_native_before_match_info knowledge key =
  match (dispatch_reactive key knowledge).native_before_match
  with
    | None -> raise Not_found
    | Some f -> f knowledge.flags.fastcomputation
