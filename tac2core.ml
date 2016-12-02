(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CSig
open Pp
open CErrors
open Names
open Genarg
open Geninterp
open Tac2env
open Tac2expr
open Proofview.Notations

(** Standard values *)

let coq_prefix = DirPath.make (List.map Id.of_string ["Ltac2"; "ltac2"; "Coq"])
let coq_core n = KerName.make2 (MPfile coq_prefix) (Label.of_id (Id.of_string_soft n))

module Core =
struct

let t_int = coq_core "int"
let t_string = coq_core "string"
let t_array = coq_core "array"
let t_unit = coq_core "unit"
let t_list = coq_core "list"
let t_constr = coq_core "constr"

let c_nil = coq_core "[]"
let c_cons = coq_core "::"

end

open Core

let v_unit = ValInt 0
let v_nil = ValInt 0
let v_cons v vl = ValBlk (0, [|v; vl|])

module Value =
struct

let of_unit () = v_unit

let to_unit = function
| ValInt 0 -> ()
| _ -> assert false

let rec of_list = function
| [] -> v_nil
| x :: l -> v_cons x (of_list l)

let rec to_list = function
| ValInt 0 -> []
| ValBlk (0, [|v; vl|]) -> v :: to_list vl
| _ -> assert false

end

let extract_val (type a) (tag : a Val.typ) (Val.Dyn (tag', v)) : a =
match Val.eq tag tag' with
| None -> assert false
| Some Refl -> v

let val_pp = Val.create "ltac2:pp"
let get_pp v = extract_val val_pp v

let val_valexpr = Val.create "ltac2:valexpr"

(** Helper functions *)

let return x = Proofview.tclUNIT x
let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let wrap f =
  return () >>= fun () -> return (f ())

let wrap_unit f =
  return () >>= fun () -> f (); return v_unit

(** Primitives *)

let prm_print : ml_tactic = function
| [ValExt pp] -> wrap_unit (fun () -> Feedback.msg_notice (get_pp pp))
| _ -> assert false

let prm_message_of_int : ml_tactic = function
| [ValInt s] -> return (ValExt (Val.Dyn (val_pp, int s)))
| _ -> assert false

let prm_message_of_string : ml_tactic = function
| [ValStr s] -> return (ValExt (Val.Dyn (val_pp, str s)))
| _ -> assert false

let prm_array_make : ml_tactic = function
| [ValInt n; x] -> wrap (fun () -> ValBlk (0, Array.make n x))
| _ -> assert false

let prm_array_length : ml_tactic = function
| [ValBlk (_, v)] -> return (ValInt (Array.length v))
| _ -> assert false

let prm_array_set : ml_tactic = function
| [ValBlk (_, v); ValInt n; x] -> wrap_unit (fun () -> v.(n) <- x)
| _ -> assert false

let prm_array_get : ml_tactic = function
| [ValBlk (_, v); ValInt n] -> wrap (fun () -> v.(n))
| _ -> assert false

(** Registering *)

let () = Tac2env.define_primitive (pname "print") prm_print
let () = Tac2env.define_primitive (pname "message_of_string") prm_message_of_string
let () = Tac2env.define_primitive (pname "message_of_int") prm_message_of_int

let () = Tac2env.define_primitive (pname "array_make") prm_array_make
let () = Tac2env.define_primitive (pname "array_length") prm_array_length
let () = Tac2env.define_primitive (pname "array_get") prm_array_get
let () = Tac2env.define_primitive (pname "array_set") prm_array_set

(** ML types *)

let val_tag t = match val_tag t with
| Val.Base t -> t
| _ -> assert false

let tag_constr = val_tag (topwit Stdarg.wit_constr)

let constr_flags () =
  let open Pretyping in
  {
    use_typeclasses = true;
    solve_unification_constraints = true;
    use_hook = Pfedit.solve_by_implicit_tactic ();
    fail_evar = true;
    expand_evars = true
  }

(** In Ltac2, the notion of "current environment" only makes sense when there is
    at most one goal under focus. Contrarily to Ltac1, instead of dynamically
    focussing when we need it, we raise a non-backtracking error when it does
    not make sense. *)
exception NonFocussedGoal

let () = register_handler begin function
| NonFocussedGoal -> str "Several goals under focus"
| _ -> raise Unhandled
end

let pf_apply f =
  Proofview.Goal.goals >>= function
  | [] ->
    Proofview.tclENV >>= fun env ->
    Proofview.tclEVARMAP >>= fun sigma ->
    f env sigma
  | [gl] ->
    gl >>= fun gl ->
    f (Proofview.Goal.env gl) (Tacmach.New.project gl)
  | _ :: _ :: _ ->
    Proofview.tclLIFT (Proofview.NonLogical.raise NonFocussedGoal)

(** Embed all Ltac2 data into Values *)
let to_lvar ist =
  let open Pretyping in
  let map e = Val.Dyn (val_valexpr, e) in
  let lfun = Id.Map.map map ist in
  { empty_lvar with ltac_genargs = lfun }

let () =
  let open Pretyping in
  let interp ist (c, _) = pf_apply begin fun env sigma ->
    let ist = to_lvar ist in
    let (sigma, c) = understand_ltac (constr_flags ()) env sigma ist WithoutTypeConstraint c in
    let c = Val.Dyn (tag_constr, c) in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT c
  end in
  let obj = {
    ml_type = t_constr;
    ml_interp = interp;
  } in
  define_ml_object Stdarg.wit_constr obj
