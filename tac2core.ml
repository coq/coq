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
open Tac2interp
open Proofview.Notations

(** Standard values *)

let coq_core n = KerName.make2 Tac2env.coq_prefix (Label.of_id (Id.of_string_soft n))
let stdlib_prefix md =
  MPfile (DirPath.make (List.map Id.of_string [md; "ltac2"; "Coq"]))
let coq_stdlib md n =
  KerName.make2 (stdlib_prefix md) (Label.of_id (Id.of_string n))

let val_tag t = match val_tag t with
| Val.Base t -> t
| _ -> assert false

let val_constr = val_tag (topwit Stdarg.wit_constr)
let val_ident = val_tag (topwit Stdarg.wit_ident)
let val_pp = Val.create "ltac2:pp"

let extract_val (type a) (tag : a Val.typ) (Val.Dyn (tag', v)) : a =
match Val.eq tag tag' with
| None -> assert false
| Some Refl -> v

module Core =
struct

let t_int = coq_core "int"
let t_string = coq_core "string"
let t_array = coq_core "array"
let t_unit = coq_core "unit"
let t_list = coq_core "list"
let t_constr = coq_core "constr"
let t_ident = coq_core "ident"

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

let of_int n = ValInt n
let to_int = function
| ValInt n -> n
| _ -> assert false

let of_bool b = if b then ValInt 0 else ValInt 1

let to_bool = function
| ValInt 0 -> true
| ValInt 1 -> false
| _ -> assert false

let of_char n = ValInt (Char.code n)
let to_char = function
| ValInt n -> Char.chr n
| _ -> assert false

let of_string s = ValStr s
let to_string = function
| ValStr s -> s
| _ -> assert false

let rec of_list = function
| [] -> v_nil
| x :: l -> v_cons x (of_list l)

let rec to_list = function
| ValInt 0 -> []
| ValBlk (0, [|v; vl|]) -> v :: to_list vl
| _ -> assert false

let of_ext tag c =
  ValExt (Val.Dyn (tag, c))

let to_ext tag = function
| ValExt e -> extract_val tag e
| _ -> assert false

let of_constr c = of_ext val_constr c
let to_constr c = to_ext val_constr c

let of_ident c = of_ext val_ident c
let to_ident c = to_ext val_ident c

(** FIXME: handle backtrace in Ltac2 exceptions *)
let of_exn c = match fst c with
| LtacError (kn, c) -> ValOpn (kn, c)
| _ -> of_ext val_exn c

let to_exn c = match c with
| ValOpn (kn, c) -> (LtacError (kn, c), Exninfo.null)
| _ -> to_ext val_exn c

let of_pp c = of_ext val_pp c
let to_pp c = to_ext val_pp c

end

let val_valexpr = Val.create "ltac2:valexpr"

(** Stdlib exceptions *)

let err_notfocussed =
  LtacError (coq_core "Not_focussed", [||])

let err_outofbounds =
  LtacError (coq_core "Out_of_bounds", [||])

let err_notfound =
  LtacError (coq_core "Not_found", [||])

(** Helper functions *)

let thaw f = interp_app f [v_unit]
let throw e = Proofview.tclLIFT (Proofview.NonLogical.raise e)

let return x = Proofview.tclUNIT x
let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let wrap f =
  return () >>= fun () -> return (f ())

let wrap_unit f =
  return () >>= fun () -> f (); return v_unit

let wrap_exn f err =
  return () >>= fun () ->
    try return (f ()) with e when CErrors.noncritical e -> err

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
    throw err_notfocussed

(** Primitives *)

(** Printing *)

let prm_print : ml_tactic = function
| [pp] -> wrap_unit (fun () -> Feedback.msg_notice (Value.to_pp pp))
| _ -> assert false

let prm_message_of_int : ml_tactic = function
| [ValInt s] -> return (ValExt (Val.Dyn (val_pp, int s)))
| _ -> assert false

let prm_message_of_string : ml_tactic = function
| [ValStr s] -> return (ValExt (Val.Dyn (val_pp, str (Bytes.to_string s))))
| _ -> assert false

let prm_message_of_constr : ml_tactic = function
| [c] ->
  pf_apply begin fun env sigma ->
    let c = Value.to_constr c in
    let pp = Printer.pr_econstr_env env sigma c in
    return (ValExt (Val.Dyn (val_pp, pp)))
  end
| _ -> assert false

let prm_message_concat : ml_tactic = function
| [m1; m2] ->
  let m1 = Value.to_pp m1 in
  let m2 = Value.to_pp m2 in
  return (Value.of_pp (Pp.app m1 m2))
| _ -> assert false

(** Array *)

let prm_array_make : ml_tactic = function
| [ValInt n; x] ->
  if n < 0 || n > Sys.max_array_length then throw err_outofbounds
  else wrap (fun () -> ValBlk (0, Array.make n x))
| _ -> assert false

let prm_array_length : ml_tactic = function
| [ValBlk (_, v)] -> return (ValInt (Array.length v))
| _ -> assert false

let prm_array_set : ml_tactic = function
| [ValBlk (_, v); ValInt n; x] ->
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap_unit (fun () -> v.(n) <- x)
| _ -> assert false

let prm_array_get : ml_tactic = function
| [ValBlk (_, v); ValInt n] ->
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap (fun () -> v.(n))
| _ -> assert false

(** Int *)

let prm_int_equal : ml_tactic = function
| [m; n] ->
  return (Value.of_bool (Value.to_int m == Value.to_int n))
| _ -> assert false

let binop f : ml_tactic = function
| [m; n] -> return (Value.of_int (f (Value.to_int m) (Value.to_int n)))
| _ -> assert false

let prm_int_compare args = binop Int.compare args
let prm_int_add args = binop (+) args
let prm_int_sub args = binop (-) args
let prm_int_mul args = binop ( * ) args

let prm_int_neg : ml_tactic = function
| [m] -> return (Value.of_int (~- (Value.to_int m)))
| _ -> assert false

(** String *)

let prm_string_make : ml_tactic = function
| [n; c] ->
  let n = Value.to_int n in
  let c = Value.to_char c in
  if n < 0 || n > Sys.max_string_length then throw err_outofbounds
  else wrap (fun () -> Value.of_string (Bytes.make n c))
| _ -> assert false

let prm_string_length : ml_tactic = function
| [s] ->
  return (Value.of_int (Bytes.length (Value.to_string s)))
| _ -> assert false

let prm_string_set : ml_tactic = function
| [s; n; c] ->
  let s = Value.to_string s in
  let n = Value.to_int n in
  let c = Value.to_char c in
  if n < 0 || n >= Bytes.length s then throw err_outofbounds
  else wrap_unit (fun () -> Bytes.set s n c)
| _ -> assert false

let prm_string_get : ml_tactic = function
| [s; n] ->
  let s = Value.to_string s in
  let n = Value.to_int n in
  if n < 0 || n >= Bytes.length s then throw err_outofbounds
  else wrap (fun () -> Value.of_char (Bytes.get s n))
| _ -> assert false

(** Error *)

let prm_throw : ml_tactic = function
| [e] ->
  let (e, info) = Value.to_exn e in
  Proofview.tclLIFT (Proofview.NonLogical.raise ~info e)
| _ -> assert false

(** Control *)

(** exn -> 'a *)
let prm_zero : ml_tactic = function
| [e] ->
  let (e, info) = Value.to_exn e in
  Proofview.tclZERO ~info e
| _ -> assert false

(** exn -> 'a *)
let prm_plus : ml_tactic = function
| [x; k] ->
  Proofview.tclOR (thaw x) (fun e -> interp_app k [Value.of_exn e])
| _ -> assert false

(** (unit -> 'a) -> 'a *)
let prm_once : ml_tactic = function
| [f] -> Proofview.tclONCE (thaw f)
| _ -> assert false

(** (unit -> unit) list -> unit *)
let prm_dispatch : ml_tactic = function
| [l] ->
  let l = Value.to_list l in
  let l = List.map (fun f -> Proofview.tclIGNORE (thaw f)) l in
  Proofview.tclDISPATCH l >>= fun () -> return v_unit
| _ -> assert false

(** (unit -> unit) list -> (unit -> unit) -> (unit -> unit) list -> unit *)
let prm_extend : ml_tactic = function
| [lft; tac; rgt] ->
  let lft = Value.to_list lft in
  let lft = List.map (fun f -> Proofview.tclIGNORE (thaw f)) lft in
  let tac = Proofview.tclIGNORE (thaw tac) in
  let rgt = Value.to_list rgt in
  let rgt = List.map (fun f -> Proofview.tclIGNORE (thaw f)) rgt in
  Proofview.tclEXTEND lft tac rgt >>= fun () -> return v_unit
| _ -> assert false

(** (unit -> unit) -> unit *)
let prm_enter : ml_tactic = function
| [f] ->
  let f = Proofview.tclIGNORE (thaw f) in
  Proofview.tclINDEPENDENT f >>= fun () -> return v_unit
| _ -> assert false

(** int -> int -> (unit -> 'a) -> 'a *)
let prm_focus : ml_tactic = function
| [i; j; tac] ->
  let i = Value.to_int i in
  let j = Value.to_int j in
  Proofview.tclFOCUS i j (thaw tac)
| _ -> assert false

(** unit -> unit *)
let prm_shelve : ml_tactic = function
| [_] -> Proofview.shelve >>= fun () -> return v_unit
| _ -> assert false

(** unit -> unit *)
let prm_shelve_unifiable : ml_tactic = function
| [_] -> Proofview.shelve_unifiable >>= fun () -> return v_unit
| _ -> assert false

(** unit -> constr *)
let prm_goal : ml_tactic = function
| [_] ->
  Proofview.Goal.enter_one { enter = fun gl ->
    let concl = Tacmach.New.pf_nf_concl gl in
    return (Value.of_constr concl)
  }
| _ -> assert false

(** ident -> constr *)
let prm_hyp : ml_tactic = function
| [id] ->
  let id = Value.to_ident id in
  pf_apply begin fun env _ ->
    let mem = try ignore (Environ.lookup_named id env); true with Not_found -> false in
    if mem then return (Value.of_constr (EConstr.mkVar id))
    else Tacticals.New.tclZEROMSG
      (str "Hypothesis " ++ quote (Id.print id) ++ str " not found") (** FIXME: Do something more sensible *)
  end
| _ -> assert false

(** (unit -> constr) -> unit *)
let prm_refine : ml_tactic = function
| [c] ->
  let c = thaw c >>= fun c -> Proofview.tclUNIT ((), Value.to_constr c) in
  Proofview.Goal.nf_enter { enter = fun gl ->
    Refine.generic_refine ~unsafe:false c gl
  } >>= fun () -> return v_unit
| _ -> assert false


(** Registering *)

let () = Tac2env.define_primitive (pname "print") prm_print
let () = Tac2env.define_primitive (pname "message_of_string") prm_message_of_string
let () = Tac2env.define_primitive (pname "message_of_int") prm_message_of_int
let () = Tac2env.define_primitive (pname "message_of_constr") prm_message_of_constr
let () = Tac2env.define_primitive (pname "message_concat") prm_message_concat

let () = Tac2env.define_primitive (pname "array_make") prm_array_make
let () = Tac2env.define_primitive (pname "array_length") prm_array_length
let () = Tac2env.define_primitive (pname "array_get") prm_array_get
let () = Tac2env.define_primitive (pname "array_set") prm_array_set

let () = Tac2env.define_primitive (pname "string_make") prm_string_make
let () = Tac2env.define_primitive (pname "string_length") prm_string_length
let () = Tac2env.define_primitive (pname "string_get") prm_string_get
let () = Tac2env.define_primitive (pname "string_set") prm_string_set

let () = Tac2env.define_primitive (pname "int_equal") prm_int_equal
let () = Tac2env.define_primitive (pname "int_compare") prm_int_compare
let () = Tac2env.define_primitive (pname "int_neg") prm_int_neg
let () = Tac2env.define_primitive (pname "int_add") prm_int_add
let () = Tac2env.define_primitive (pname "int_sub") prm_int_sub
let () = Tac2env.define_primitive (pname "int_mul") prm_int_mul

let () = Tac2env.define_primitive (pname "throw") prm_throw

let () = Tac2env.define_primitive (pname "zero") prm_zero
let () = Tac2env.define_primitive (pname "plus") prm_plus
let () = Tac2env.define_primitive (pname "once") prm_once
let () = Tac2env.define_primitive (pname "dispatch") prm_dispatch
let () = Tac2env.define_primitive (pname "extend") prm_extend
let () = Tac2env.define_primitive (pname "enter") prm_enter

let () = Tac2env.define_primitive (pname "focus") prm_focus
let () = Tac2env.define_primitive (pname "shelve") prm_shelve
let () = Tac2env.define_primitive (pname "shelve_unifiable") prm_shelve_unifiable
let () = Tac2env.define_primitive (pname "goal") prm_goal
let () = Tac2env.define_primitive (pname "hyp") prm_hyp
let () = Tac2env.define_primitive (pname "refine") prm_refine

(** ML types *)

let constr_flags () =
  let open Pretyping in
  {
    use_typeclasses = true;
    solve_unification_constraints = true;
    use_hook = Pfedit.solve_by_implicit_tactic ();
    fail_evar = true;
    expand_evars = true
  }

let open_constr_no_classes_flags () =
  let open Pretyping in
  {
  use_typeclasses = false;
  solve_unification_constraints = true;
  use_hook = Pfedit.solve_by_implicit_tactic ();
  fail_evar = false;
  expand_evars = true
  }

(** Embed all Ltac2 data into Values *)
let to_lvar ist =
  let open Pretyping in
  let map e = Val.Dyn (val_valexpr, e) in
  let lfun = Id.Map.map map ist in
  { empty_lvar with ltac_genargs = lfun }

let interp_constr flags ist (c, _) =
  let open Pretyping in
  pf_apply begin fun env sigma ->
  Proofview.V82.wrap_exceptions begin fun () ->
    let ist = to_lvar ist in
    let (sigma, c) = understand_ltac flags env sigma ist WithoutTypeConstraint c in
    let c = Val.Dyn (val_constr, c) in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT c
  end
  end

let () =
  let open Pretyping in
  let interp ist c = interp_constr (constr_flags ()) ist c in
  let obj = {
    ml_type = t_constr;
    ml_interp = interp;
  } in
  define_ml_object Stdarg.wit_constr obj

let () =
  let open Pretyping in
  let interp ist c = interp_constr (open_constr_no_classes_flags ()) ist c in
  let obj = {
    ml_type = t_constr;
    ml_interp = interp;
  } in
  define_ml_object Stdarg.wit_open_constr obj

let () =
  let interp _ id = return (Val.Dyn (val_ident, id)) in
  let obj = {
    ml_type = t_ident;
    ml_interp = interp;
  } in
  define_ml_object Stdarg.wit_ident obj

let () =
  let interp ist env sigma concl tac =
    let fold id (Val.Dyn (tag, v)) (accu : environment) : environment =
      match Val.eq tag val_valexpr with
      | None -> accu
      | Some Refl -> Id.Map.add id v accu
    in
    let ist = Id.Map.fold fold ist Id.Map.empty in
    let tac = Proofview.tclIGNORE (interp ist tac) in
    let c, sigma = Pfedit.refine_by_tactic env sigma concl tac in
    (EConstr.of_constr c, sigma)
  in
  Pretyping.register_constr_interp0 wit_ltac2 interp
