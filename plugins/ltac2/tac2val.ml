(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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

type tag = int

type valexpr =
| ValInt of int
  (** Immediate integers *)
| ValBlk of tag * valexpr array
  (** Structured blocks *)
| ValStr of Bytes.t
  (** Strings *)
| ValCls of closure
  (** Closures *)
| ValOpn of KerName.t * valexpr array
  (** Open constructors *)
| ValExt : 'a Tac2dyn.Val.tag * 'a -> valexpr
  (** Arbitrary data *)

and closure = MLTactic : (valexpr, 'v) arity0 * Tac2expr.frame option * 'v -> closure

let arity_one = OneAty
let arity_suc a = AddAty a

type 'a arity = (valexpr, 'a) arity0

let mk_closure arity f = MLTactic (arity, None, f)

let mk_closure_val arity f = ValCls (mk_closure arity f)

module Valexpr =
struct

type t = valexpr

let is_int = function
| ValInt _ -> true
| ValBlk _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ -> false

let tag v = match v with
| ValBlk (n, _) -> n
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let field v n = match v with
| ValBlk (_, v) -> v.(n)
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let set_field v n w = match v with
| ValBlk (_, v) -> v.(n) <- w
| ValInt _ | ValStr _ | ValCls _ | ValOpn _ | ValExt _ ->
  CErrors.anomaly (Pp.str "Unexpected value shape")

let make_block tag v = ValBlk (tag, v)
let make_int n = ValInt n

end

let to_closure = function
| ValCls cls -> cls
| ValExt _ | ValInt _ | ValBlk _ | ValStr _ | ValOpn _ -> assert false

let wrap fr tac = match fr with
  | None -> tac
  | Some fr -> Tac2bt.with_frame fr tac

let rec apply : type a. a arity -> _ -> a -> valexpr list -> valexpr Proofview.tactic =
  fun arity fr f args -> match args, arity with
  | [], arity -> Proofview.tclUNIT (ValCls (MLTactic (arity, fr, f)))
  (* A few hardcoded cases for efficiency *)
  | [a0], OneAty -> wrap fr (f a0)
  | [a0; a1], AddAty OneAty -> wrap fr (f a0 a1)
  | [a0; a1; a2], AddAty (AddAty OneAty) -> wrap fr (f a0 a1 a2)
  | [a0; a1; a2; a3], AddAty (AddAty (AddAty OneAty)) -> wrap fr (f a0 a1 a2 a3)
  (* Generic cases *)
  | a :: args, OneAty ->
    wrap fr (f a) >>= fun f ->
    let MLTactic (arity, fr, f) = to_closure f in
    apply arity fr f args
  | a :: args, AddAty arity ->
    apply arity fr (f a) args

let apply (MLTactic (arity, wrap, f)) args = apply arity wrap f args

let apply_val v args = apply (to_closure v) args

type n_closure =
| NClosure : 'a arity * (valexpr list -> 'a) -> n_closure

let rec abstract n f =
  if Int.equal n 1 then NClosure (OneAty, fun accu v -> f (List.rev (v :: accu)))
  else
    let NClosure (arity, fe) = abstract (n - 1) f in
    NClosure (AddAty arity, fun accu v -> fe (v :: accu))

let abstract n f =
  match n with
  | 1 -> MLTactic (OneAty, None, fun a -> f [a])
  | 2 -> MLTactic (AddAty OneAty, None, fun a b -> f [a;b])
  | 3 -> MLTactic (AddAty (AddAty OneAty), None, fun a b c -> f [a;b;c])
  | 4 -> MLTactic (AddAty (AddAty (AddAty OneAty)), None, fun a b c d -> f [a;b;c;d])
  | _ ->
    let () = assert (n > 0) in
    let NClosure (arity, f) = abstract n f in
    MLTactic (arity, None, f [])

let annotate_closure fr (MLTactic (arity, fr0, f)) =
  assert (Option.is_empty fr0);
  MLTactic (arity, Some fr, f)

let rec purify_closure : type a. a arity -> (unit -> a) -> a = fun arity f ->
  match arity with
  | OneAty -> (fun x -> Proofview.tclUNIT () >>= fun () -> f () x)
  | AddAty a -> (fun x -> purify_closure a (fun () -> f () x))

let purify_closure ar f = purify_closure ar (fun () -> f)
