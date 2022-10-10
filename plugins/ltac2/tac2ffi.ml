(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Proofview.Notations

type ('a, _) arity0 =
| OneAty : ('a, 'a -> 'a Proofview.tactic) arity0
| AddAty : ('a, 'b) arity0 -> ('a, 'a -> 'b) arity0

type valexpr = Obj.t

type closure = MLTactic : (valexpr, 'v) arity0 * 'v -> closure

let arity_one = OneAty
let arity_suc a = AddAty a

type 'a arity = (valexpr, 'a) arity0

let mk_closure arity f = MLTactic (arity, f)

module Valexpr =
struct

type t = valexpr

let is_int = Obj.is_int

let tag = Obj.tag

let field = Obj.field

let fields v = Array.init (Obj.size v) (fun i -> Obj.field v i)

let set_field = Obj.set_field

let make_block tag v =
  let o = Obj.new_block tag (Array.length v) in
  Array.iteri (fun i v -> Obj.set_field o i v) v;
  o

let make_int n = Obj.repr (n:int)

end

type 'a repr =
  | Id : valexpr repr
  | Functions of {
      r_of : 'a -> valexpr;
      r_to : valexpr -> 'a;
    }

let repr_of (type a) (r:a repr) (x:a) : valexpr = match r with
  | Id -> x
  | Functions { r_of } -> r_of x
let repr_to (type a) (r:a repr) (x:valexpr) : a = match r with
  | Id -> x
  | Functions { r_to } -> r_to x

let make_repr r_of r_to = Functions { r_of; r_to; }

let magic_repr () : _ repr = Obj.magic Id

let map_repr f g r = Functions {
  r_of = (fun x -> repr_of r (g x));
  r_to = (fun x -> f (repr_to r x));
}

(** Dynamic tags *)

let constr = magic_repr ()
let ident = magic_repr ()
let pattern = magic_repr ()
let preterm = magic_repr ()
let matching_context = magic_repr ()
let pp = magic_repr ()
let evar = magic_repr ()
let sort = magic_repr ()
let cast = magic_repr ()
let inductive = magic_repr ()
let constant = magic_repr ()
let constructor = magic_repr ()
let projection = magic_repr ()
let case = magic_repr ()
let binder = magic_repr ()
let univ = magic_repr ()
let free : Names.Id.Set.t repr = magic_repr ()
let ltac1 : Geninterp.Val.t repr = magic_repr ()
let ind_data : (Names.Ind.t * Declarations.mutual_inductive_body) repr = magic_repr ()

(** Exception *)

exception LtacError of KerName.t * valexpr array

(** Conversion functions *)

let valexpr = Id

let unit : unit repr = magic_repr ()
let of_unit = repr_of unit
let to_unit = repr_to unit

let int : int repr = magic_repr ()
let of_int = repr_of int
let to_int = repr_to int

let bool : bool repr = magic_repr ()
let of_bool = repr_of bool
let to_bool = repr_to bool

let char : char repr = magic_repr ()
let of_char = repr_of char
let to_char = repr_to char

let bytes : Bytes.t repr = magic_repr ()
let of_bytes = repr_of bytes
let to_bytes = repr_to bytes

let string = map_repr String.of_bytes String.to_bytes bytes
let of_string = repr_of string
let to_string = repr_to string

let of_list (f:_ -> valexpr) l = Obj.repr (List.map f l)
let to_list (f:valexpr -> _) l = List.map f (Obj.magic l : valexpr list)

let list (type a) (r:a repr) : a list repr = match r with
  | Id -> magic_repr ()
  | Functions { r_of; r_to } ->
    Functions { r_of = (fun l -> of_list r_of l);
                r_to = (fun l -> to_list r_to l);
              }

let closure : closure repr = magic_repr ()
let of_closure = repr_of closure
let to_closure = repr_to closure

let of_constr c = repr_of constr c
let to_constr c = repr_to constr c

let of_ident c = repr_of ident c
let to_ident c = repr_to ident c

let of_pattern c = repr_of pattern c
let to_pattern c = repr_to pattern c

let of_evar ev = repr_of evar ev
let to_evar ev = repr_to evar ev

let open_ : (KerName.t * valexpr array) repr = magic_repr ()
let of_open = repr_of open_
let to_open = repr_to open_

let internal_err =
  let open Names in
  let coq_prefix =
    MPfile (DirPath.make (List.map Id.of_string ["Init"; "Ltac2"]))
  in
  KerName.make coq_prefix (Label.of_id (Id.of_string "Internal"))

(** FIXME: handle backtrace in Ltac2 exceptions *)
let of_exn c = match fst c with
| LtacError (kn, c) -> of_open (kn, c)
| _ -> of_open (internal_err, [|Obj.magic c|])

let to_exn c =
  let (kn, c) = to_open c in
  if Names.KerName.equal kn internal_err then
    Obj.magic c.(0)
  else
    (LtacError (kn, c), Exninfo.null)

let exn = make_repr of_exn to_exn

let of_option f o = Obj.repr (Option.map f o)
let to_option f o = Option.map f (Obj.magic o : valexpr option)

let option (type a) (r:a repr) : a option repr = match r with
  | Id -> magic_repr ()
  | Functions { r_of; r_to } ->
    Functions { r_of = (fun l -> of_option r_of l);
                r_to = (fun l -> to_option r_to l);
              }

let of_pp c = repr_of pp c
let to_pp c = repr_to pp c

let of_tuple cl = Valexpr.make_block 0 cl
let to_tuple v = Valexpr.fields v

let of_pair f g (x, y) = Obj.repr (f x, g y)
let to_pair f g p =
  let (x, y : valexpr * valexpr) = Obj.magic p in
  f x, g y

let pair (type a b) (r0:a repr) (r1:b repr) : (a * b) repr = match r0, r1 with
  | Id, Id -> magic_repr ()
  | _ -> make_repr (of_pair (repr_of r0) (repr_of r1)) (to_pair (repr_to r0) (repr_to r1))

let of_triple f g h (x, y, z) = Obj.repr (f x, g y, h z)
let to_triple f g h p =
  let (x, y, z : valexpr * valexpr * valexpr) = Obj.magic p in
  f x, g y, h z

let triple (type a b c) (r0:a repr) (r1:b repr) (r2:c repr) : (a * b * c) repr = match r0, r1, r2 with
  | Id, Id, Id -> magic_repr ()
  | _ -> make_repr (of_triple (repr_of r0) (repr_of r1) (repr_of r2))
           (to_triple (repr_to r0) (repr_to r1) (repr_to r2))

let of_array (f:_ -> valexpr) l = Obj.repr (Array.map f l)
let to_array (f:valexpr -> _) l = Array.map f (Obj.magic l : valexpr array)

let array (type a) (r:a repr) : a array repr = match r with
  | Id -> magic_repr ()
  | Functions { r_of; r_to } ->
    Functions { r_of = (fun l -> of_array r_of l);
                r_to = (fun l -> to_array r_to l);
              }

let of_block (n, args) = Valexpr.make_block n args
let to_block v = Obj.tag v, Valexpr.fields v

let block = Functions {
  r_of = of_block;
  r_to = to_block;
}

let uint63 : Uint63.t repr = magic_repr ()
let of_uint63 = repr_of uint63
let to_uint63 = repr_to uint63

let float : Float64.t repr = magic_repr ()
let of_float = repr_of float
let to_float = repr_to float

let of_constant c = repr_of constant c
let to_constant c = repr_to constant c

let reference : GlobRef.t repr = magic_repr ()
let of_reference = repr_of reference
let to_reference = repr_to reference

type ('a, 'b) fun1 = closure

let fun1 (r0 : 'a repr) (r1 : 'b repr) : ('a, 'b) fun1 repr = closure
let to_fun1 r0 r1 f = to_closure f

let rec apply : type a. a arity -> a -> valexpr list -> valexpr Proofview.tactic =
  fun arity f args -> match args, arity with
  | [], arity -> Proofview.tclUNIT (of_closure (MLTactic (arity, f)))
  (* A few hardcoded cases for efficiency *)
  | [a0], OneAty -> f a0
  | [a0; a1], AddAty OneAty -> f a0 a1
  | [a0; a1; a2], AddAty (AddAty OneAty) -> f a0 a1 a2
  | [a0; a1; a2; a3], AddAty (AddAty (AddAty OneAty)) -> f a0 a1 a2 a3
  (* Generic cases *)
  | a :: args, OneAty ->
    f a >>= fun f ->
    let MLTactic (arity, f) = to_closure f in
    apply arity f args
  | a :: args, AddAty arity ->
    apply arity (f a) args

let apply (MLTactic (arity, f)) args = apply arity f args

type n_closure =
| NClosure : 'a arity * (valexpr list -> 'a) -> n_closure

let rec abstract n f =
  if Int.equal n 1 then NClosure (OneAty, fun accu v -> f (List.rev (v :: accu)))
  else
    let NClosure (arity, fe) = abstract (n - 1) f in
    NClosure (AddAty arity, fun accu v -> fe (v :: accu))

let abstract n f =
  let () = assert (n > 0) in
  let NClosure (arity, f) = abstract n f in
  MLTactic (arity, f [])

let app_fun1 cls r0 r1 x =
  apply cls [repr_of r0 x] >>= fun v -> Proofview.tclUNIT (repr_to r1 v)
