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
open Pp
open Names
open Genarg
open Tac2val
open Tac2ffi
open Tac2env
open Tac2expr
open Tac2entries.Pltac
open Proofview.Notations

module GT = Tac2globals.Types

let ltac2_plugin = "coq-core.plugins.ltac2"

let constr_flags =
  let open Pretyping in
  {
    use_coercions = true;
    use_typeclasses = Pretyping.UseTC;
    solve_unification_constraints = true;
    fail_evar = true;
    expand_evars = true;
    program_mode = false;
    polymorphic = false;
  }

let open_constr_use_classes_flags =
  let open Pretyping in
  {
  use_coercions = true;
  use_typeclasses = Pretyping.UseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = true;
  program_mode = false;
  polymorphic = false;
  }

let open_constr_no_classes_flags =
  let open Pretyping in
  {
  use_coercions = true;
  use_typeclasses = Pretyping.NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = false;
  program_mode = false;
  polymorphic = false;
  }

let preterm_flags =
  let open Pretyping in
  {
  use_coercions = true;
  use_typeclasses = Pretyping.NoUseTC;
  solve_unification_constraints = true;
  fail_evar = false;
  expand_evars = false;
  program_mode = false;
  polymorphic = false;
  }

(** Standard values *)

let val_format = Tac2print.val_format
let format_ = repr_ext val_format
let format t1 t2 t3 t4 =
  typed format_
    Types.(! GT.format [t1; t2; t3; t4])

let core_prefix path n = KerName.make path (Label.of_id (Id.of_string_soft n))

let std_core n = core_prefix Tac2env.std_prefix n
let coq_core n = core_prefix Tac2env.coq_prefix n

module Core =
struct

let t_unit = coq_core "unit"
let v_unit = Tac2ffi.of_unit ()

let t_int = coq_core "int"
let t_string = coq_core "string"
let t_array = coq_core "array"
let t_list = coq_core "list"
let t_constr = coq_core "constr"
let t_preterm = coq_core "preterm"
let t_pattern = coq_core "pattern"
let t_ident = coq_core "ident"
let t_option = coq_core "option"
let t_exn = coq_core "exn"
let t_reference = std_core "reference"

let c_nil = coq_core "[]"
let c_cons = coq_core "::"

let c_none = coq_core "None"
let c_some = coq_core "Some"

let c_true = coq_core "true"
let c_false = coq_core "false"

end

open Core

let v_blk = Valexpr.make_block

let of_relevance = function
  | Sorts.Relevant -> ValInt 0
  | Sorts.Irrelevant -> ValInt 1
  | Sorts.RelevanceVar q -> ValBlk (0, [|of_ext val_qvar q|])

let to_relevance = function
  | ValInt 0 -> Sorts.Relevant
  | ValInt 1 -> Sorts.Irrelevant
  | ValBlk (0, [|qvar|]) ->
    let qvar = to_ext val_qvar qvar in
    Sorts.RelevanceVar qvar
  | _ -> assert false

let relevance_ = make_repr of_relevance to_relevance
let relevance = typed relevance_ Types.(!! GT.relevance)

let of_binder b =
  Tac2ffi.of_ext Tac2ffi.val_binder b

let to_binder b =
  Tac2ffi.to_ext Tac2ffi.val_binder b

let of_instance u =
  let u = UVars.Instance.to_array (EConstr.Unsafe.to_instance u) in
  let toqs = Tac2ffi.of_array (fun v -> Tac2ffi.of_ext Tac2ffi.val_quality v) in
  let tous = Tac2ffi.of_array (fun v -> Tac2ffi.of_ext Tac2ffi.val_univ v) in
  Tac2ffi.of_pair toqs tous u

let to_instance u =
  let toqs = Tac2ffi.to_array (fun v -> Tac2ffi.to_ext Tac2ffi.val_quality v) in
  let tous = Tac2ffi.to_array (fun v -> Tac2ffi.to_ext Tac2ffi.val_univ v) in
  let u = Tac2ffi.to_pair toqs tous u in
  EConstr.EInstance.make (UVars.Instance.of_array u)

let of_rec_declaration (nas, ts, cs) =
  let binders = Array.map2 (fun na t -> (na, t)) nas ts in
  (Tac2ffi.of_array of_binder binders,
  Tac2ffi.of_array Tac2ffi.of_constr cs)

let to_rec_declaration (nas, cs) =
  let nas = Tac2ffi.to_array to_binder nas in
  (Array.map fst nas,
  Array.map snd nas,
  Tac2ffi.to_array Tac2ffi.to_constr cs)

let of_case_invert = let open Constr in function
  | NoInvert -> ValInt 0
  | CaseInvert {indices} ->
    v_blk 0 [|of_array of_constr indices|]

let to_case_invert = let open Constr in function
  | ValInt 0 -> NoInvert
  | ValBlk (0, [|indices|]) ->
    let indices = to_array to_constr indices in
    CaseInvert {indices}
  | _ -> CErrors.anomaly Pp.(str "unexpected value shape")

let inductive_ = repr_ext val_inductive
let inductive = typed inductive_ Types.(!! GT.inductive)

let projection_ = repr_ext val_projection
let projection = typed projection_ Types.(!! GT.projection)

(** Stdlib exceptions *)

let err_notfocussed =
  Tac2interp.LtacError (coq_core "Not_focussed", [||])

let err_outofbounds =
  Tac2interp.LtacError (coq_core "Out_of_bounds", [||])

let err_notfound =
  Tac2interp.LtacError (coq_core "Not_found", [||])

let err_matchfailure =
  Tac2interp.LtacError (coq_core "Match_failure", [||])

let err_division_by_zero =
  Tac2interp.LtacError (coq_core "Division_by_zero", [||])

(** Helper functions *)

let fatal_flag : unit Exninfo.t = Exninfo.make "fatal_flag"

let has_fatal_flag info = match Exninfo.get info fatal_flag with
  | None -> false
  | Some () -> true

let set_bt info =
  if !Tac2bt.print_ltac2_backtrace then
    Tac2bt.get_backtrace >>= fun bt ->
    Proofview.tclUNIT (Exninfo.add info Tac2bt.backtrace bt)
  else Proofview.tclUNIT info

let throw ?(info = Exninfo.null) e =
  set_bt info >>= fun info ->
  let info = Exninfo.add info fatal_flag () in
  Proofview.tclLIFT (Proofview.NonLogical.raise (e, info))

let fail ?(info = Exninfo.null) e =
  set_bt info >>= fun info ->
  Proofview.tclZERO ~info e

let return x = Proofview.tclUNIT x
let pname ?(plugin=ltac2_plugin) s = { mltac_plugin = plugin; mltac_tactic = s }

let catchable_exception = function
  | Logic_monad.Exception _ -> false
  | e -> CErrors.noncritical e

(* Adds ltac2 backtrace
   With [passthrough:false], acts like [Proofview.wrap_exceptions] + Ltac2 backtrace handling
*)
let wrap_exceptions ?(passthrough=false) f =
  try f ()
  with e ->
    let e, info = Exninfo.capture e in
    set_bt info >>= fun info ->
    if not passthrough && catchable_exception e
    then begin if has_fatal_flag info
      then Proofview.tclLIFT (Proofview.NonLogical.raise (e, info))
      else Proofview.tclZERO ~info e
    end
    else Exninfo.iraise (e, info)

let assert_focussed =
  Proofview.Goal.goals >>= fun gls ->
  match gls with
  | [_] -> Proofview.tclUNIT ()
  | [] | _ :: _ :: _ -> throw err_notfocussed

let pf_apply ?(catch_exceptions=false) f =
  let f env sigma = wrap_exceptions ~passthrough:(not catch_exceptions) (fun () -> f env sigma) in
  Proofview.Goal.goals >>= function
  | [] ->
    Proofview.tclENV >>= fun env ->
    Proofview.tclEVARMAP >>= fun sigma ->
    f env sigma
  | [gl] ->
    gl >>= fun gl ->
    f (Proofview.Goal.env gl) (Tacmach.project gl)
  | _ :: _ :: _ ->
    throw err_notfocussed

open Tac2externals

let define ?plugin s = define (pname ?plugin s)

(** Printing *)

let () = define "print" (pp @-> ret unit) Feedback.msg_notice

let () = define "message_of_int" (int @-> ret pp) Pp.int

let () = define "message_of_string" (string @-> ret pp) Pp.str

let () = define "message_to_string" (pp @-> ret string) Pp.string_of_ppcmds

let () =
  define "message_of_constr" (constr @-> tac pp) @@ fun c ->
  pf_apply @@ fun env sigma -> return (Printer.pr_econstr_env env sigma c)

let () = define "message_of_ident" (ident @-> ret pp) Id.print

let () =
  define "message_of_exn" (valexpr_0 @-> eret pp) @@ fun v env sigma ->
  Tac2print.pr_valexpr env sigma v (GTypRef (Other Core.t_exn, []))

let () = define "message_concat" (pp @-> pp @-> ret pp) Pp.app

let () = define "format_stop" (ret Types.(format any any any any)) []

let format_linear_spec =
  Types.(format (var 0) (var 1) (var 2) (var 3))

let format_one_arg_spec argty =
  format_linear_spec
  @-> ret Types.(format (argty @-> var 0) (var 1) (var 2) (var 3))

let () =
  define "format_string" (format_one_arg_spec Types.(!! GT.string)) @@ fun s ->
  Tac2print.FmtString :: s

let () =
  define "format_int" (format_one_arg_spec Types.(!! GT.int)) @@ fun s ->
  Tac2print.FmtInt :: s

let () =
  define "format_constr" (format_one_arg_spec Types.(!! GT.constr)) @@ fun s ->
  Tac2print.FmtConstr :: s

let () =
  define "format_ident" (format_one_arg_spec Types.(!! GT.ident)) @@ fun s ->
  Tac2print.FmtIdent :: s

let () =
  define "format_literal" (string @-> format_linear_spec @-> ret format_linear_spec) @@ fun lit s ->
  Tac2print.FmtLiteral lit :: s

let () =
  define "format_alpha"
    (format_linear_spec
     @-> ret Types.(format ((var 1 @-> var 4 @-> var 2) @-> var 4 @-> var 0) (var 1) (var 2) (var 3))) @@ fun s ->
  Tac2print.FmtAlpha :: s

let arity_of_format fmt =
  let open Tac2print in
  let fold accu = function
    | FmtLiteral _ -> accu
    | FmtString | FmtInt | FmtConstr | FmtIdent -> 1 + accu
    | FmtAlpha -> 2 + accu
  in
  List.fold_left fold 0 fmt

let () =
  define "format_kfprintf"
    (fun1 pp (typed valexpr (Types.var 1))
     @-> Types.(format (var 0) (!! GT.unit) (!! GT.message) (var 1))
     @-> tac valexpr_0) @@ fun k fmt ->
  let open Tac2print in
  let pop1 l = match l with [] -> assert false | x :: l -> (x, l) in
  let pop2 l = match l with [] | [_] -> assert false | x :: y :: l -> (x, y, l) in
  let arity = arity_of_format fmt in
  let rec eval accu args fmt = match fmt with
  | [] -> k accu
  | tag :: fmt ->
    match tag with
    | FmtLiteral s ->
      eval (Pp.app accu (Pp.str s)) args fmt
    | FmtString ->
      let (s, args) = pop1 args in
      let pp = Pp.str (to_string s) in
      eval (Pp.app accu pp) args fmt
    | FmtInt ->
      let (i, args) = pop1 args in
      let pp = Pp.int (to_int i) in
      eval (Pp.app accu pp) args fmt
    | FmtConstr ->
      let (c, args) = pop1 args in
      let c = to_constr c in
      pf_apply begin fun env sigma ->
        let pp = Printer.pr_econstr_env env sigma c in
        eval (Pp.app accu pp) args fmt
      end
    | FmtIdent ->
      let (i, args) = pop1 args in
      let pp = Id.print (to_ident i) in
      eval (Pp.app accu pp) args fmt
    | FmtAlpha ->
      let (f, x, args) = pop2 args in
      Tac2val.apply_val f [of_unit (); x] >>= fun pp ->
      eval (Pp.app accu (to_pp pp)) args fmt
  in
  let eval v = eval (Pp.mt ()) v fmt in
  if Int.equal arity 0 then eval []
  else return (Tac2ffi.of_closure (Tac2val.abstract arity eval))

let () =
  define "format_ikfprintf"
    (typed closure Types.(var 1 @-> var 2)
     @-> typed valexpr (Types.var 1)
     @-> Types.(format (var 0) (!! GT.unit) (var 1) (var 2))
     @-> tac valexpr_0) @@ fun k v fmt ->
  let arity = arity_of_format fmt in
  let eval _args = apply k [v] in
  if Int.equal arity 0 then eval []
  else return (Tac2ffi.of_closure (Tac2val.abstract arity eval))

(** Array *)

(* avoid using "array valexpr_0" to avoid useless Array.map in readers
   and to avoid making writers write to a copied array *)
let array_ty_0 = Types.(! GT.array [var 0])

let () = define "array_empty" (ret (typed valexpr array_ty_0)) (v_blk 0 [||])

let () =
  define "array_make" (int @-> valexpr_0 @-> tac (typed valexpr array_ty_0)) @@ fun n x ->
  try return (v_blk 0 (Array.make n x)) with Invalid_argument _ -> throw err_outofbounds

let () =
  define "array_length" (typed block array_ty_0 @-> ret int) @@ fun (_, v) -> Array.length v

let () =
  define "array_set" (typed block array_ty_0 @-> int @-> valexpr_0 @-> tac unit) @@ fun (_, v) n x ->
  try Array.set v n x; return () with Invalid_argument _ -> throw err_outofbounds

let () =
  define "array_get" (typed block array_ty_0 @-> int @-> tac @@ valexpr_0) @@ fun (_, v) n ->
  try return (Array.get v n) with Invalid_argument _ -> throw err_outofbounds

let () =
  define "array_blit"
    (typed block array_ty_0 @-> int @-> typed block array_ty_0 @-> int @-> int @-> tac unit)
    @@ fun (_, v0) s0 (_, v1) s1 l ->
  try Array.blit v0 s0 v1 s1 l; return () with Invalid_argument _ ->
  throw err_outofbounds

let () =
  define "array_fill" (typed block array_ty_0 @-> int @-> int @-> valexpr_0 @-> tac unit) @@ fun (_, d) s l v ->
  try Array.fill d s l v; return () with Invalid_argument _ -> throw err_outofbounds

let () =
  define "array_concat" (list (typed block array_ty_0) @-> ret (typed valexpr array_ty_0)) @@ fun l ->
  v_blk 0 (Array.concat (List.map snd l))

(** Ident *)

let () = define "ident_equal" (ident @-> ident @-> ret bool) Id.equal

let () = define "ident_to_string" (ident @-> ret string) Id.to_string

let () =
  define "ident_of_string" (string @-> ret (option ident)) @@ fun s ->
  try Some (Id.of_string s) with e when CErrors.noncritical e -> None

(** Int *)

let () = define "int_equal" (int @-> int @-> ret bool) (==)

let () = define "int_neg" (int @-> ret int) (~-)
let () = define "int_abs" (int @-> ret int) abs

let () = define "int_compare" (int @-> int @-> ret int) Int.compare
let () = define "int_add" (int @-> int @-> ret int) (+)
let () = define "int_sub" (int @-> int @-> ret int) (-)
let () = define "int_mul" (int @-> int @-> ret int) ( * )

let () = define "int_div" (int @-> int @-> tac int) @@ fun m n ->
  if n == 0 then throw err_division_by_zero else return (m / n)
let () = define "int_mod" (int @-> int @-> tac int) @@ fun m n ->
  if n == 0 then throw err_division_by_zero else return (m mod n)

let () = define "int_asr" (int @-> int @-> ret int) (asr)
let () = define "int_lsl" (int @-> int @-> ret int) (lsl)
let () = define "int_lsr" (int @-> int @-> ret int) (lsr)
let () = define "int_land" (int @-> int @-> ret int) (land)
let () = define "int_lor" (int @-> int @-> ret int) (lor)
let () = define "int_lxor" (int @-> int @-> ret int) (lxor)
let () = define "int_lnot" (int @-> ret int) lnot

(** Char *)

let () = define "char_of_int" (int @-> tac char) @@ fun i ->
  try return (Char.chr i)
  with Invalid_argument _ as e ->
    let e, info = Exninfo.capture e in
    throw ~info e

let () = define "char_to_int" (char @-> ret int) Char.code

(** String *)

let () =
  define "string_make" (int @-> char @-> tac bytes) @@ fun n c ->
  try return (Bytes.make n c) with Invalid_argument _ -> throw err_outofbounds

let () = define "string_length" (bytes @-> ret int) Bytes.length

let () =
  define "string_set" (bytes @-> int @-> char @-> tac unit) @@ fun s n c ->
  try Bytes.set s n c; return () with Invalid_argument _ -> throw err_outofbounds

let () =
  define "string_get" (bytes @-> int @-> tac char) @@ fun s n ->
  try return (Bytes.get s n) with Invalid_argument _ -> throw err_outofbounds

let () = define "string_concat" (bytes @-> list bytes @-> ret bytes) Bytes.concat

let () =
  define "string_app" (bytes @-> bytes @-> ret bytes) @@ fun a b ->
  Bytes.concat Bytes.empty [a; b]

let () = define "string_equal" (bytes @-> bytes @-> ret bool) Bytes.equal

let () = define "string_compare" (bytes @-> bytes @-> ret int) Bytes.compare

(** Terms *)

(** constr -> constr *)
let () =
  define "constr_type" (constr @-> tac constr) @@ fun c ->
  let get_type env sigma =
    let (sigma, t) = Typing.type_of env sigma c in
    Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
  in
  pf_apply ~catch_exceptions:true get_type

(** constr -> constr *)
let () =
  define "constr_equal" (constr @-> constr @-> tac bool) @@ fun c1 c2 ->
  Proofview.tclEVARMAP >>= fun sigma -> return (EConstr.eq_constr sigma c1 c2)

let () =
  define "constr_kind" (constr @-> eret (typed valexpr Types.(!! GT.constr_kind))) @@ fun c env sigma ->
  let open Constr in
  match EConstr.kind sigma c with
  | Rel n ->
    v_blk 0 [|Tac2ffi.of_int n|]
  | Var id ->
    v_blk 1 [|Tac2ffi.of_ident id|]
  | Meta n ->
    v_blk 2 [|Tac2ffi.of_int n|]
  | Evar (evk, args) ->
    let args = Evd.expand_existential sigma (evk, args) in
    v_blk 3 [|
      Tac2ffi.of_evar evk;
      Tac2ffi.of_array Tac2ffi.of_constr (Array.of_list args);
    |]
  | Sort s ->
    v_blk 4 [|Tac2ffi.of_ext Tac2ffi.val_sort s|]
  | Cast (c, k, t) ->
    v_blk 5 [|
      Tac2ffi.of_constr c;
      Tac2ffi.of_ext Tac2ffi.val_cast k;
      Tac2ffi.of_constr t;
    |]
  | Prod (na, t, u) ->
    v_blk 6 [|
      of_binder (na, t);
      Tac2ffi.of_constr u;
    |]
  | Lambda (na, t, c) ->
    v_blk 7 [|
      of_binder (na, t);
      Tac2ffi.of_constr c;
    |]
  | LetIn (na, b, t, c) ->
    v_blk 8 [|
      of_binder (na, t);
      Tac2ffi.of_constr b;
      Tac2ffi.of_constr c;
    |]
  | App (c, cl) ->
    v_blk 9 [|
      Tac2ffi.of_constr c;
      Tac2ffi.of_array Tac2ffi.of_constr cl;
    |]
  | Const (cst, u) ->
    v_blk 10 [|
      Tac2ffi.of_constant cst;
      of_instance u;
    |]
  | Ind (ind, u) ->
    v_blk 11 [|
      Tac2ffi.of_ext Tac2ffi.val_inductive ind;
      of_instance u;
    |]
  | Construct (cstr, u) ->
    v_blk 12 [|
      Tac2ffi.of_ext Tac2ffi.val_constructor cstr;
      of_instance u;
    |]
  | Case (ci, u, pms, c, iv, t, bl) ->
    (* FIXME: also change representation Ltac2-side? *)
    let (ci, c, iv, t, bl) = EConstr.expand_case env sigma (ci, u, pms, c, iv, t, bl) in
    v_blk 13 [|
      Tac2ffi.of_ext Tac2ffi.val_case ci;
      Tac2ffi.(of_pair of_constr of_relevance c);
      of_case_invert iv;
      Tac2ffi.of_constr t;
      Tac2ffi.of_array Tac2ffi.of_constr bl;
    |]
  | Fix ((recs, i), def) ->
    let (nas, cs) = of_rec_declaration def in
    v_blk 14 [|
      Tac2ffi.of_array Tac2ffi.of_int recs;
      Tac2ffi.of_int i;
      nas;
      cs;
    |]
  | CoFix (i, def) ->
    let (nas, cs) = of_rec_declaration def in
    v_blk 15 [|
      Tac2ffi.of_int i;
      nas;
      cs;
    |]
  | Proj (p, r, c) ->
    v_blk 16 [|
      Tac2ffi.of_ext Tac2ffi.val_projection p;
      of_relevance r;
      Tac2ffi.of_constr c;
    |]
  | Int n ->
    v_blk 17 [|Tac2ffi.of_uint63 n|]
  | Float f ->
    v_blk 18 [|Tac2ffi.of_float f|]
  | Array(u,t,def,ty) ->
    v_blk 19 [|
      of_instance u;
      Tac2ffi.of_array Tac2ffi.of_constr t;
      Tac2ffi.of_constr def;
      Tac2ffi.of_constr ty;
    |]

let () =
  define "constr_make" (typed valexpr Types.(!! GT.constr_kind) @-> eret constr) @@ fun knd env sigma ->
  match Tac2ffi.to_block knd with
  | (0, [|n|]) ->
    let n = Tac2ffi.to_int n in
    EConstr.mkRel n
  | (1, [|id|]) ->
    let id = Tac2ffi.to_ident id in
    EConstr.mkVar id
  | (2, [|n|]) ->
    let n = Tac2ffi.to_int n in
    EConstr.mkMeta n
  | (3, [|evk; args|]) ->
    let evk = to_evar evk in
    let args = Tac2ffi.to_array Tac2ffi.to_constr args in
    EConstr.mkLEvar sigma (evk, Array.to_list args)
  | (4, [|s|]) ->
    let s = Tac2ffi.to_ext Tac2ffi.val_sort s in
    EConstr.mkSort s
  | (5, [|c; k; t|]) ->
    let c = Tac2ffi.to_constr c in
    let k = Tac2ffi.to_ext Tac2ffi.val_cast k in
    let t = Tac2ffi.to_constr t in
    EConstr.mkCast (c, k, t)
  | (6, [|na; u|]) ->
    let (na, t) = to_binder na in
    let u = Tac2ffi.to_constr u in
    EConstr.mkProd (na, t, u)
  | (7, [|na; c|]) ->
    let (na, t) = to_binder na in
    let u = Tac2ffi.to_constr c in
    EConstr.mkLambda (na, t, u)
  | (8, [|na; b; c|]) ->
    let (na, t) = to_binder na in
    let b = Tac2ffi.to_constr b in
    let c = Tac2ffi.to_constr c in
    EConstr.mkLetIn (na, b, t, c)
  | (9, [|c; cl|]) ->
    let c = Tac2ffi.to_constr c in
    let cl = Tac2ffi.to_array Tac2ffi.to_constr cl in
    EConstr.mkApp (c, cl)
  | (10, [|cst; u|]) ->
    let cst = Tac2ffi.to_constant cst in
    let u = to_instance u in
    EConstr.mkConstU (cst, u)
  | (11, [|ind; u|]) ->
    let ind = Tac2ffi.to_ext Tac2ffi.val_inductive ind in
    let u = to_instance u in
    EConstr.mkIndU (ind, u)
  | (12, [|cstr; u|]) ->
    let cstr = Tac2ffi.to_ext Tac2ffi.val_constructor cstr in
    let u = to_instance u in
    EConstr.mkConstructU (cstr, u)
  | (13, [|ci; c; iv; t; bl|]) ->
    let ci = Tac2ffi.to_ext Tac2ffi.val_case ci in
    let c = Tac2ffi.(to_pair to_constr to_relevance c) in
    let iv = to_case_invert iv in
    let t = Tac2ffi.to_constr t in
    let bl = Tac2ffi.to_array Tac2ffi.to_constr bl in
    EConstr.mkCase (EConstr.contract_case env sigma (ci, c, iv, t, bl))
  | (14, [|recs; i; nas; cs|]) ->
    let recs = Tac2ffi.to_array Tac2ffi.to_int recs in
    let i = Tac2ffi.to_int i in
    let def = to_rec_declaration (nas, cs) in
    EConstr.mkFix ((recs, i), def)
  | (15, [|i; nas; cs|]) ->
    let i = Tac2ffi.to_int i in
    let def = to_rec_declaration (nas, cs) in
    EConstr.mkCoFix (i, def)
  | (16, [|p; r; c|]) ->
    let p = Tac2ffi.to_ext Tac2ffi.val_projection p in
    let r = to_relevance r in
    let c = Tac2ffi.to_constr c in
    EConstr.mkProj (p, r, c)
  | (17, [|n|]) ->
    let n = Tac2ffi.to_uint63 n in
    EConstr.mkInt n
  | (18, [|f|]) ->
    let f = Tac2ffi.to_float f in
    EConstr.mkFloat f
  | (19, [|u;t;def;ty|]) ->
    let t = Tac2ffi.to_array Tac2ffi.to_constr t in
    let def = Tac2ffi.to_constr def in
    let ty = Tac2ffi.to_constr ty in
    let u = to_instance u in
    EConstr.mkArray(u,t,def,ty)
  | _ -> assert false

let () =
  define "constr_check" (constr @-> tac @@ result constr) @@ fun c ->
  pf_apply @@ fun env sigma ->
  try
    let (sigma, _) = Typing.type_of env sigma c in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    return (Ok c)
  with e when CErrors.noncritical e ->
    let e = Exninfo.capture e in
    return (Error e)

let () =
  define "constr_liftn" (int @-> int @-> constr @-> ret constr)
    EConstr.Vars.liftn

let () =
  define "constr_substnl" (list constr @-> int @-> constr @-> ret constr)
    EConstr.Vars.substnl

let () =
  define "constr_closenl" (list ident @-> int @-> constr @-> tac constr)
    @@ fun ids k c ->
  Proofview.tclEVARMAP >>= fun sigma ->
  return (EConstr.Vars.substn_vars sigma k ids c)

let () =
  define "constr_closedn" (int @-> constr @-> tac bool) @@ fun n c ->
  Proofview.tclEVARMAP >>= fun sigma ->
  return (EConstr.Vars.closedn sigma n c)

let () =
  define "constr_occur_between" (int @-> int @-> constr @-> tac bool) @@ fun n m c ->
  Proofview.tclEVARMAP >>= fun sigma ->
  return (EConstr.Vars.noccur_between sigma n m c)

let constr_case_ = repr_ext val_case
let constr_case = typed constr_case_ Types.(!! GT.constr_case)

let () =
  define "constr_case" (inductive @-> tac constr_case) @@ fun ind ->
  Proofview.tclENV >>= fun env ->
  try
    let ans = Inductiveops.make_case_info env ind Constr.RegularStyle in
    return ans
  with e when CErrors.noncritical e ->
    throw err_notfound

let () = define "constr_cast_default" (ret cast) DEFAULTcast
let () = define "constr_cast_vm" (ret cast) VMcast
let () = define "constr_cast_native" (ret cast) NATIVEcast

let () =
  define "constr_in_context" (ident @-> constr @-> thunk unit @-> tac constr) @@ fun id t c ->
  Proofview.Goal.goals >>= function
  | [gl] ->
    gl >>= fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let has_var =
      try
        let _ = Environ.lookup_named id env in
        true
      with Not_found -> false
    in
    if has_var then
      Tacticals.tclZEROMSG (str "Variable already exists")
    else
      let open Context.Named.Declaration in
      let sigma, t_rel =
        let t_ty = Retyping.get_type_of env sigma t in
        (* If the user passed eg ['_] for the type we force it to indeed be a type *)
        let sigma, j = Typing.type_judgment env sigma {uj_val=t; uj_type=t_ty} in
        sigma, EConstr.ESorts.relevance_of_sort sigma j.utj_type
      in
      let nenv = EConstr.push_named (LocalAssum (Context.make_annot id t_rel, t)) env in
      let (sigma, (evt, _)) = Evarutil.new_type_evar nenv sigma Evd.univ_flexible in
      let (sigma, evk) = Evarutil.new_pure_evar (Environ.named_context_val nenv) sigma evt in
      Proofview.Unsafe.tclEVARS sigma >>= fun () ->
      Proofview.Unsafe.tclSETGOALS [Proofview.with_empty_state evk] >>= fun () ->
      thaw c >>= fun _ ->
      Proofview.Unsafe.tclSETGOALS [Proofview.with_empty_state (Proofview.Goal.goal gl)] >>= fun () ->
      let args = EConstr.identity_subst_val (Environ.named_context_val env) in
      let args = SList.cons (EConstr.mkRel 1) args in
      let ans = EConstr.mkEvar (evk, args) in
      return (EConstr.mkLambda (Context.make_annot (Name id) t_rel, t, ans))
  | _ ->
    throw err_notfocussed

(** preterm -> constr *)
let pretype_flags_ = repr_ext val_pretype_flags
let pretype_flags = typed pretype_flags_ Types.(!! GT.pretype_flags)

let () = define "constr_flags" (ret pretype_flags) constr_flags

let () = define "open_constr_flags" (ret pretype_flags) open_constr_use_classes_flags

let expected_type_ = repr_ext val_expected_type
let expected_type = typed expected_type_ Types.(!! GT.pretype_expected_type)

let () = define "expected_istype" (ret expected_type) IsType

let () = define "expected_oftype" (constr @-> ret expected_type) @@ fun c ->
  OfType c

let () = define "expected_without_type_constraint" (ret expected_type) WithoutTypeConstraint

let () =
  define "constr_pretype" (pretype_flags @-> expected_type @-> preterm @-> tac constr) @@ fun flags expected_type c ->
  let pretype env sigma =
    let sigma, t = Pretyping.understand_uconstr ~flags ~expected_type env sigma c in
    Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
  in
  pf_apply ~catch_exceptions:true pretype

let binder_ = repr_ext val_binder
let binder = typed binder_ Types.(!! GT.binder)

let () =
  define "constr_binder_make" (option ident @-> constr @-> tac binder) @@ fun na ty ->
  pf_apply @@ fun env sigma ->
  match Retyping.relevance_of_type env sigma ty with
  | rel ->
    let na = match na with None -> Anonymous | Some id -> Name id in
    return (Context.make_annot na rel, ty)
  | exception (Retyping.RetypeError _ as e) ->
    let e, info = Exninfo.capture e in
    fail ~info (CErrors.UserError Pp.(str "Not a type."))

let () =
  define "constr_binder_unsafe_make"
    (option ident @-> relevance @-> constr @-> ret binder)
    @@ fun na rel ty ->
  let na = match na with None -> Anonymous | Some id -> Name id in
  (Context.make_annot na rel, ty)

let () =
  define "constr_binder_name" (binder @-> ret (option ident)) @@ fun (bnd, _) ->
  match bnd.Context.binder_name with Anonymous -> None | Name id -> Some id

let () =
  define "constr_binder_type" (binder @-> ret constr) @@ fun (_, ty) -> ty

let () =
  define "constr_has_evar" (constr @-> tac bool) @@ fun c ->
  Proofview.tclEVARMAP >>= fun sigma ->
  return (Evarutil.has_undefined_evars sigma c)

(** Extra equalities *)

let meta = typed int_ Types.(!! GT.meta)

let () = define "evar_equal" (evar @-> evar @-> ret bool) Evar.equal
let () = define "float_equal" (float @-> float @-> ret bool) Float64.equal
let () = define "uint63_equal" (uint63 @-> uint63 @-> ret bool) Uint63.equal
let () = define "meta_equal" (meta @-> meta @-> ret bool) Int.equal
let () = define "constr_cast_equal" (cast @-> cast @-> ret bool) Glob_ops.cast_kind_eq

let () =
  define "constant_equal"
    (constant @-> constant @-> ret bool)
    Constant.UserOrd.equal
let () =
  define "constr_case_equal" (constr_case @-> constr_case @-> ret bool) @@ fun x y ->
  Ind.UserOrd.equal x.ci_ind y.ci_ind
let () =
  let ty = typed (repr_ext val_constructor) Types.(!! GT.constructor) in
  define "constructor_equal" (ty @-> ty @-> ret bool) Construct.UserOrd.equal
let () =
  define "projection_equal" (projection @-> projection @-> ret bool) Projection.UserOrd.equal

(** Patterns *)

let matching_context_ = repr_ext val_matching_context
let matching_context = typed matching_context_ Types.(!! GT.matching_context)

let () =
  define "pattern_empty_context"
    (ret matching_context)
    Constr_matching.empty_context

let () =
  define "pattern_matches" (pattern @-> constr @-> tac (list (pair ident constr))) @@ fun pat c ->
  pf_apply @@ fun env sigma ->
  let ans =
    try Some (Constr_matching.matches env sigma pat c)
    with Constr_matching.PatternMatchingFailure -> None
  in
  begin match ans with
  | None -> fail err_matchfailure
  | Some ans ->
    let ans = Id.Map.bindings ans in
    return ans
  end

let () =
  define "pattern_matches_subterm" (pattern @-> constr @-> tac (pair matching_context (list (pair ident constr)))) @@ fun pat c ->
  let open Constr_matching in
  let rec multireturn s = match IStream.peek s with
  | IStream.Nil -> fail err_matchfailure
  | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
    let ans = Id.Map.bindings sub in
    Proofview.tclOR (return (m_ctx,ans)) (fun _ -> multireturn s)
  in
  pf_apply @@ fun env sigma ->
  let pat = Constr_matching.instantiate_pattern env sigma Id.Map.empty pat in
  let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
  multireturn ans

let () =
  define "pattern_matches_vect" (pattern @-> constr @-> tac (array constr)) @@ fun pat c ->
  pf_apply @@ fun env sigma ->
  let ans =
    try Some (Constr_matching.matches env sigma pat c)
    with Constr_matching.PatternMatchingFailure -> None
  in
  match ans with
  | None -> fail err_matchfailure
  | Some ans ->
    let ans = Id.Map.bindings ans in
    let ans = Array.map_of_list snd ans in
    return ans

let () =
  define "pattern_matches_subterm_vect" (pattern @-> constr @-> tac (pair matching_context (array constr))) @@ fun pat c ->
  let open Constr_matching in
  let rec multireturn s = match IStream.peek s with
  | IStream.Nil -> fail err_matchfailure
  | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
    let ans = Id.Map.bindings sub in
    let ans = Array.map_of_list snd ans in
    Proofview.tclOR (return (m_ctx, ans)) (fun _ -> multireturn s)
  in
  pf_apply @@ fun env sigma ->
  let pat = Constr_matching.instantiate_pattern env sigma Id.Map.empty pat in
  let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
  multireturn ans

let match_pattern_ = map_repr
    (fun (b,pat) -> if b then Tac2match.MatchPattern pat else Tac2match.MatchContext pat)
    (function Tac2match.MatchPattern pat -> (true, pat) | MatchContext pat -> (false, pat))
    (pair_ bool_ pattern_)

let match_pattern = typed match_pattern_ Types.(tuple [!! GT.match_kind; !! GT.pattern])

let pattern_matches_goal_return_ty =
  let open Types in
  let open GT in
  tuple [! array [!! ident];
         ! array [!! matching_context];
         ! array [!! matching_context];
         ! array [!! constr];
         !! matching_context]

let () =
  define "pattern_matches_goal"
    (bool @-> list (pair (option match_pattern) match_pattern) @-> match_pattern
     @-> tac (typed valexpr pattern_matches_goal_return_ty))
    @@ fun rev hp cp ->
  assert_focussed >>= fun () ->
  Proofview.Goal.enter_one @@ fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  Tac2match.match_goal env sigma concl ~rev (hp, cp) >>= fun (hyps, ctx, subst) ->
  let empty_context = Constr_matching.empty_context in
  let of_ctxopt ctx = Tac2ffi.of_ext val_matching_context (Option.default empty_context ctx) in
  let hids = Tac2ffi.of_array Tac2ffi.of_ident (Array.map_of_list pi1 hyps) in
  let hbctx = Tac2ffi.of_array of_ctxopt
      (Array.of_list (CList.filter_map (fun (_,bctx,_) -> bctx) hyps))
  in
  let hctx = Tac2ffi.of_array of_ctxopt (Array.map_of_list pi3 hyps) in
  let subs = Tac2ffi.of_array Tac2ffi.of_constr (Array.map_of_list snd (Id.Map.bindings subst)) in
  let cctx = of_ctxopt ctx in
  let ans = Tac2ffi.of_tuple [| hids; hbctx; hctx; subs; cctx |] in
  Proofview.tclUNIT ans

let () =
  define "pattern_instantiate"
    (matching_context @-> constr @-> ret constr)
    Constr_matching.instantiate_context

(** Error *)

let () =
  define "throw" (exn @-> tac valexpr_0) @@ fun (e, info) -> throw ~info e

let () =
  define "throw_bt" (exn @-> exninfo @-> tac valexpr_0) @@ fun (e,_) info ->
    Proofview.tclLIFT (Proofview.NonLogical.raise (e, info))

let () =
  define "clear_err_info" (err @-> ret err) @@ fun (e,_) -> (e, Exninfo.null)

(** Control *)

(** exn -> 'a *)
let () =
  define "zero" (exn @-> tac valexpr_0) @@ fun (e, info) -> fail ~info e

let () =
  define "zero_bt" (exn @-> exninfo @-> tac valexpr_0) @@ fun (e,_) info ->
    Proofview.tclZERO ~info e

(** (unit -> 'a) -> (exn -> 'a) -> 'a *)
let () =
  define "plus"
    (thunk valexpr_0
     @-> fun1 exn valexpr_0
     @-> tac valexpr_0) @@ fun x k ->
  Proofview.tclOR (thaw x) k

let () =
  define "plus_bt"
    (thunk valexpr_0 @-> fun2 exn exninfo valexpr_0 @-> tac valexpr_0) @@ fun run handle ->
  Proofview.tclOR (thaw run)
    (fun e -> handle e (snd e))

(** (unit -> 'a) -> 'a *)
let () =
  define "once" (thunk valexpr_0 @-> tac valexpr_0) @@ fun f ->
  Proofview.tclONCE (thaw f)

(** (unit -> unit) list -> unit *)
let () =
  define "dispatch" (list (thunk unit) @-> tac unit) @@ fun l ->
  let l = List.map (fun f -> thaw f) l in
  Proofview.tclDISPATCH l

(** (unit -> unit) list -> (unit -> unit) -> (unit -> unit) list -> unit *)
let () =
  define "extend" (list (thunk unit) @-> thunk unit @-> list (thunk unit) @-> tac unit) @@ fun lft tac rgt ->
  let lft = List.map thaw lft in
  let tac = thaw tac in
  let rgt = List.map thaw rgt in
  Proofview.tclEXTEND lft tac rgt

(** (unit -> unit) -> unit *)
let () =
  define "enter" (thunk unit  @-> tac unit) @@ fun f ->
  Proofview.tclINDEPENDENT (thaw f)

(** (unit -> 'a) -> ('a * ('exn -> 'a)) result *)
let () =
  define "case" (thunk valexpr_0 @-> tac (result (pair valexpr_0 (fun1 exn valexpr_0)))) @@ fun f ->
  Proofview.tclCASE (thaw f) >>= begin function
  | Proofview.Next (x, k) ->
    let k (e,info) =
      set_bt info >>= fun info ->
      k (e, info)
    in
    return (Ok (x, k))
  | Proofview.Fail e -> return (Error e)
  end

(** int -> int -> (unit -> 'a) -> 'a *)
let () =
  define "focus" (int @-> int @-> thunk valexpr_0 @-> tac valexpr_0) @@ fun i j tac ->
  Proofview.tclFOCUS i j (thaw tac)

(** unit -> unit *)
let () = define "shelve" (unit @-> tac unit) @@ fun _ -> Proofview.shelve

(** unit -> unit *)
let () =
  define "shelve_unifiable" (unit @-> tac unit) @@ fun _ ->
  Proofview.shelve_unifiable

let () =
  define "new_goal" (evar @-> tac unit) @@ fun ev ->
  Proofview.tclEVARMAP >>= fun sigma ->
  if Evd.mem sigma ev then
    Proofview.Unsafe.tclNEWGOALS [Proofview.with_empty_state ev] <*>
    Proofview.tclUNIT ()
  else throw err_notfound

(** unit -> constr *)
let () =
  define "goal" (unit @-> tac constr) @@ fun _ ->
  assert_focussed >>= fun () ->
  Proofview.Goal.enter_one @@ fun gl -> return (Tacmach.pf_nf_concl gl)

(** ident -> constr *)
let () =
  define "hyp" (ident @-> tac constr) @@ fun id ->
  pf_apply @@ fun env _ ->
  let mem = try ignore (Environ.lookup_named id env); true with Not_found -> false in
  if mem then return (EConstr.mkVar id)
  else Tacticals.tclZEROMSG
    (str "Hypothesis " ++ quote (Id.print id) ++ str " not found") (* FIXME: Do something more sensible *)

let () =
  define "hyps" (unit @-> tac (list (triple ident (option constr) constr))) @@ fun _ ->
  pf_apply @@ fun env _ ->
  let open Context in
  let open Named.Declaration in
  let map = function
  | LocalAssum (id, t) ->
    let t = EConstr.of_constr t in
    (id.binder_name, None, t)
  | LocalDef (id, c, t) ->
    let c = EConstr.of_constr c in
    let t = EConstr.of_constr t in
    (id.binder_name, Some c, t)
  in
  let hyps = List.rev_map map (Environ.named_context env) in
  return hyps

(** (unit -> constr) -> unit *)
let () =
  define "refine" (thunk constr @-> tac unit) @@ fun c ->
  let c = thaw c >>= fun c -> Proofview.tclUNIT ((), c) in
  Proofview.Goal.enter @@ fun gl ->
  Refine.generic_refine ~typecheck:true c gl

let () =
  define "with_holes"
    (thunk valexpr_0 @-> fun1 valexpr_0 (typed valexpr (Types.var 1))
     @-> tac (typed valexpr (Types.var 1))) @@ fun x f ->
  Proofview.tclEVARMAP >>= fun sigma0 ->
  thaw x >>= fun ans ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclEVARS sigma0 >>= fun () ->
  Tacticals.tclWITHHOLES false (f ans) sigma

let () =
  define "progress" (thunk valexpr_0 @-> tac valexpr_0) @@ fun f ->
  Proofview.tclPROGRESS (thaw f)

let () =
  define "abstract" (option ident @-> thunk unit @-> tac unit) @@ fun id f ->
  Abstract.tclABSTRACT id (thaw f)

let () =
  define "time" (option string @-> thunk valexpr_0 @-> tac valexpr_0) @@ fun s f ->
  Proofview.tclTIME s (thaw f)

let () =
  define "timeout" (int @-> thunk valexpr_0 @-> tac valexpr_0) @@ fun i f ->
    Proofview.tclTIMEOUT i (thaw f)

let () =
  define "timeoutf" (float @-> thunk valexpr_0 @-> tac valexpr_0) @@ fun f64 f ->
    Proofview.tclTIMEOUTF (Float64.to_float f64) (f())

let () =
  define "check_interrupt" (unit @-> tac unit) @@ fun _ ->
  Proofview.tclCHECKINTERRUPT

(** Fresh *)

let free_ = repr_ext val_free
let free = typed free_ Types.(!! GT.free)

let () =
  define "fresh_free_union" (free @-> free @-> ret free) Id.Set.union

let () =
  define "fresh_free_of_ids" (list ident @-> ret free) @@ fun ids ->
  List.fold_right Id.Set.add ids Id.Set.empty

let () =
  define "fresh_free_of_constr" (constr @-> tac free) @@ fun c ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let rec fold accu c =
    match EConstr.kind sigma c with
    | Constr.Var id -> Id.Set.add id accu
    | _ -> EConstr.fold sigma fold accu c
  in
  return (fold Id.Set.empty c)

let () =
  define "fresh_fresh" (free @-> ident @-> ret ident) @@ fun avoid id ->
  Namegen.next_ident_away_from id (fun id -> Id.Set.mem id avoid)

(** Env *)

let () =
  define "env_get" (list ident @-> ret (option reference)) @@ fun ids ->
  match ids with
  | [] -> None
  | _ :: _ as ids ->
    let (id, path) = List.sep_last ids in
    let path = DirPath.make (List.rev path) in
    let fp = Libnames.make_path path id in
    try Some (Nametab.global_of_path fp) with Not_found -> None

let () =
  define "env_expand" (list ident @-> ret (list reference)) @@ fun ids ->
  match ids with
  | [] -> []
  | _ :: _ as ids ->
    let (id, path) = List.sep_last ids in
    let path = DirPath.make (List.rev path) in
    let qid = Libnames.make_qualid path id in
    Nametab.locate_all qid

let () =
  define "env_path" (reference @-> tac (list ident)) @@ fun r ->
  match Nametab.path_of_global r with
  | fp ->
    let (path, id) = Libnames.repr_path fp in
    let path = DirPath.repr path in
    return (List.rev_append path [id])
  | exception Not_found ->
    throw err_notfound

let () =
  define "env_instantiate" (reference @-> tac constr) @@ fun r ->
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let (sigma, c) = Evd.fresh_global env sigma r in
  Proofview.Unsafe.tclEVARS sigma >>= fun () ->
  return c

(** Ind *)

let ind_data_ = repr_ext val_ind_data
let ind_data = typed ind_data_ Types.(!! GT.ind_data)

let () =
  define "ind_equal" (inductive @-> inductive @-> ret bool) Ind.UserOrd.equal

let () =
  define "ind_data"
    (inductive @-> tac ind_data)
    @@ fun ind ->
  Proofview.tclENV >>= fun env ->
  if Environ.mem_mind (fst ind) env then
    return (ind, Environ.lookup_mind (fst ind) env)
  else
    throw err_notfound

let () = define "ind_repr" (ind_data @-> ret inductive) fst
let () = define "ind_index" (inductive @-> ret int) snd

let () =
  define "ind_nblocks" (ind_data @-> ret int) @@ fun (_, mib) ->
  Array.length mib.Declarations.mind_packets

let () =
  define "ind_nconstructors" (ind_data @-> ret int) @@ fun ((_, n), mib) ->
  Array.length Declarations.(mib.mind_packets.(n).mind_consnames)

let () =
  define "ind_get_block"
    (ind_data @-> int @-> tac ind_data)
    @@ fun (ind, mib) n ->
  if 0 <= n && n < Array.length mib.Declarations.mind_packets then
    return ((fst ind, n), mib)
  else throw err_notfound

let constructor_ = repr_ext val_constructor
let constructor = typed constructor_ Types.(!! GT.constructor)

let () =
  define "ind_get_constructor"
    (ind_data @-> int @-> tac constructor)
    @@ fun ((mind, n), mib) i ->
  let open Declarations in
  let ncons = Array.length mib.mind_packets.(n).mind_consnames in
  if 0 <= i && i < ncons then
    (* WARNING: In the ML API constructors are indexed from 1 for historical
       reasons, but Ltac2 uses 0-indexing instead. *)
    return ((mind, n), i + 1)
  else throw err_notfound

let () =
  define "constructor_inductive"
    (constructor @-> ret inductive)
  @@ fun (ind, _) -> ind

let () =
  define "constructor_index"
    (constructor @-> ret int)
  @@ fun (_, i) ->
  (* WARNING: ML constructors are 1-indexed but Ltac2 constructors are 0-indexed *)
  i-1

let () =
  define "ind_get_projections" (ind_data @-> ret (option (array projection)))
  @@ fun (ind,mib) ->
  Declareops.inductive_make_projections ind mib
  |> Option.map (Array.map (fun (p,_) -> Projection.make p false))

(** Proj *)

let () =
  define "projection_ind" (projection @-> ret inductive) Projection.inductive

let () =
  define "projection_index" (projection @-> ret int) Projection.arg

let () =
  define "projection_unfolded" (projection @-> ret bool) Projection.unfolded

let () =
  define "projection_set_unfolded" (projection @-> bool @-> ret projection) @@ fun p b ->
  Projection.make (Projection.repr p) b

let () =
  define "projection_of_constant" (constant @-> ret (option projection)) @@ fun c ->
  Structures.PrimitiveProjections.find_opt c |> Option.map (fun p -> Projection.make p false)

let () =
  define "projection_to_constant" (projection @-> ret (option constant)) @@ fun p ->
  Some (Projection.constant p)

module MapTagDyn = Dyn.Make()

type ('a,'set,'map) map_tag = ('a * 'set * 'map) MapTagDyn.tag

type any_map_tag = Any : _ map_tag -> any_map_tag
type tagged_set = TaggedSet : (_,'set,_) map_tag * 'set -> tagged_set
type tagged_map = TaggedMap : (_,_,'map) map_tag * 'map -> tagged_map

let map_tag_ext : any_map_tag Tac2dyn.Val.tag = Tac2dyn.Val.create "fmap_tag"
let map_tag_repr = Tac2ffi.repr_ext map_tag_ext

let map_tag_ty t = Types.(! GT.map_tag [t])

let map_tag_0 = typed map_tag_repr (map_tag_ty (Types.var 0))

let set_ext : tagged_set Tac2dyn.Val.tag = Tac2dyn.Val.create "fset"
let set_repr = Tac2ffi.repr_ext set_ext
let tag_set tag s = TaggedSet (tag,s)

let map_ext : tagged_map Tac2dyn.Val.tag = Tac2dyn.Val.create "fmap"
let map_repr = Tac2ffi.repr_ext map_ext
let tag_map tag m = TaggedMap (tag,m)

module type MapType = sig
  (* to have less boilerplate we use S.elt rather than declaring a toplevel type t *)
  module S : CSig.SetS
  module M : CMap.ExtS with type key = S.elt and module Set := S
  type valmap
  val valmap_eq : (valmap, valexpr M.t) Util.eq
  val repr : S.elt repr
  val typ : Types.t option
end

type ('t,'set,'map) maptype = (module MapType with type S.elt = 't and type S.t = 'set and type valmap = 'map)

module MapTypeV = struct
  type _ t = Map : ('t,'set,'map) maptype
    -> ('t * 'set * 'map) t
end

module MapMap = MapTagDyn.Map(MapTypeV)

let maps = ref MapMap.empty

let register_map (type t set map) ?(plugin=ltac2_plugin) ~tag_name (x:(t,set,map) maptype)
  : (t * set * map) MapTagDyn.tag =
  let tag = MapTagDyn.create (plugin^":"^tag_name) in
  let () = maps := MapMap.add tag (Map x) !maps in
  let module X = (val x) in
  let ty = map_tag_ty (Types.default X.typ) in
  let () = define ~plugin tag_name (ret (typed map_tag_repr ty)) (Any tag) in
  tag

let get_map (type t s m) (tag:(t,s,m) map_tag)
  : (module MapType with type S.elt = t and type S.t = s and type valmap = m) =
  let Map v = MapMap.find tag !maps in
  v

let map_tag_eq (type a b c a' b' c') (t1:(a,b,c) map_tag) (t2:(a',b',c') map_tag)
  : (a*b*c,a'*b'*c') Util.eq option
  = MapTagDyn.eq t1 t2

let assert_map_tag_eq t1 t2 = match map_tag_eq t1 t2 with
  | Some v -> v
  | None -> assert false

let ident_map_tag : _ map_tag = register_map ~tag_name:"fmap_ident_tag" (module struct
    module S = Id.Set
    module M = Id.Map
    let repr, typ = Tac2ffi.ident
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let int_map_tag : _ map_tag = register_map ~tag_name:"fmap_int_tag" (module struct
    module S = Int.Set
    module M = Int.Map
    let repr, typ = Tac2ffi.int
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let string_map_tag : _ map_tag = register_map ~tag_name:"fmap_string_tag" (module struct
    module S = String.Set
    module M = String.Map
    let repr, typ = Tac2ffi.string
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let inductive_map_tag : _ map_tag = register_map ~tag_name:"fmap_inductive_tag" (module struct
    module S = Indset_env
    module M = Indmap_env
    let repr, typ = inductive
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let constructor_map_tag : _ map_tag = register_map ~tag_name:"fmap_constructor_tag" (module struct
    module S = Constrset_env
    module M = Constrmap_env
    let repr, typ = constructor
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let constant_map_tag : _ map_tag = register_map ~tag_name:"fmap_constant_tag" (module struct
    module S = Cset_env
    module M = Cmap_env
    let repr, typ = constant
    type valmap = valexpr M.t
    let valmap_eq = Refl
  end)

let fset_0 = typed set_repr Types.(! GT.fset [var 0])

let () =
  define "fset_empty" (map_tag_0 @-> ret fset_0) @@ fun (Any tag) ->
  let (module V) = get_map tag in
  tag_set tag V.S.empty

let () =
  define "fset_is_empty" (fset_0 @-> ret bool) @@ fun (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  V.S.is_empty s

let () =
  define "fset_mem" (valexpr_0 @-> fset_0 @-> ret bool) @@ fun x (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  V.S.mem (repr_to V.repr x) s

let () =
  define "fset_add" (valexpr_0 @-> fset_0 @-> ret fset_0) @@ fun x (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  tag_set tag (V.S.add (repr_to V.repr x) s)

let () =
  define "fset_remove" (valexpr_0 @-> fset_0 @-> ret fset_0) @@ fun x (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  tag_set tag (V.S.remove (repr_to V.repr x) s)

let () =
  define "fset_union" (fset_0 @-> fset_0 @-> ret fset_0)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  tag_set tag (V.S.union s1 s2)

let () =
  define "fset_inter" (fset_0 @-> fset_0 @-> ret fset_0)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  tag_set tag (V.S.inter s1 s2)

let () =
  define "fset_diff" (fset_0 @-> fset_0 @-> ret fset_0)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  tag_set tag (V.S.diff s1 s2)

let () =
  define "fset_equal" (fset_0 @-> fset_0 @-> ret bool)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  V.S.equal s1 s2

let () =
  define "fset_subset" (fset_0 @-> fset_0 @-> ret bool)
    @@ fun (TaggedSet (tag,s1)) (TaggedSet (tag',s2)) ->
  let Refl = assert_map_tag_eq tag tag' in
  let (module V) = get_map tag in
  V.S.subset s1 s2

let () =
  define "fset_cardinal" (fset_0 @-> ret int) @@ fun (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  V.S.cardinal s

let () =
  define "fset_elements" (fset_0 @-> ret (list valexpr_0)) @@ fun (TaggedSet (tag,s)) ->
  let (module V) = get_map tag in
  List.map (repr_of V.repr) (V.S.elements s)

let fmap_0_1 = typed map_repr Types.(! GT.fmap [var 0; var 1])

let () =
  define "fmap_empty" (map_tag_0 @-> ret fmap_0_1) @@ fun (Any (tag)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_map tag V.M.empty

let () =
  define "fmap_is_empty" (fmap_0_1 @-> ret bool) @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.is_empty m

let () =
  define "fmap_mem" (valexpr_0 @-> fmap_0_1 @-> ret bool) @@ fun x (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.mem (repr_to V.repr x) m

let () =
  define "fmap_add" (valexpr_0 @-> typed valexpr (Types.var 1) @-> fmap_0_1 @-> ret fmap_0_1)
    @@ fun x v (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_map tag (V.M.add (repr_to V.repr x) v m)

let () =
  define "fmap_remove" (valexpr_0 @-> fmap_0_1 @-> ret fmap_0_1)
    @@ fun x (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_map tag (V.M.remove (repr_to V.repr x) m)

let () =
  define "fmap_find_opt" (valexpr_0 @-> fmap_0_1 @-> ret (option (typed valexpr (Types.var 1))))
    @@ fun x (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.find_opt (repr_to V.repr x) m

let () =
  define "fmap_mapi"
    (fun2 valexpr_0 (typed valexpr (Types.var 1)) (typed valexpr (Types.var 2))
     @-> fmap_0_1 @-> tac (typed map_repr Types.(! GT.fmap [var 0; var 2])))
    @@ fun f (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  let module Monadic = V.M.Monad(Proofview.Monad) in
  Monadic.mapi (fun k v -> f (repr_of V.repr k) v) m >>= fun m ->
  return (tag_map tag m)

let () =
  define "fmap_fold"
    (fun3 valexpr_0 (typed valexpr (Types.var 1)) (typed valexpr (Types.var 2))
       (typed valexpr (Types.var 2))
     @-> fmap_0_1 @-> typed valexpr (Types.var 2) @-> tac (typed valexpr (Types.var 2)))
    @@ fun f (TaggedMap (tag,m)) acc ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  let module Monadic = V.M.Monad(Proofview.Monad) in
  Monadic.fold (fun k v acc -> f (repr_of V.repr k) v acc) m acc

let () =
  define "fmap_cardinal" (fmap_0_1 @-> ret int) @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  V.M.cardinal m

let () =
  define "fmap_bindings"
    (fmap_0_1 @->
     ret (list (pair (typed valexpr (Types.var 0)) (typed valexpr (Types.var 1)))))
  @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  List.map (fun (k,v) -> repr_of V.repr k, v) (V.M.bindings m)

let () =
  define "fmap_domain" (fmap_0_1 @-> ret fset_0) @@ fun (TaggedMap (tag,m)) ->
  let (module V) = get_map tag in
  let Refl = V.valmap_eq in
  tag_set tag (V.M.domain m)

(** ML types *)

(** Embed all Ltac2 data into Values *)
let to_lvar ist =
  let open Glob_ops in
  let lfun = Tac2interp.set_env ist Id.Map.empty in
  { empty_lvar with Ltac_pretype.ltac_genargs = lfun }

let gtypref kn = GTypRef (Other kn, [])

let intern_constr self ist c =
  let (_, (c, _)) = Genintern.intern Stdarg.wit_constr ist c in
  let v = match DAst.get c with
    | GGenarg (GenArg (Glbwit tag, v)) ->
      begin match genarg_type_eq tag wit_ltac2_var_quotation with
      | Some Refl ->
        begin match (fst v) with
        | ConstrVar -> GlbTacexpr (GTacVar (snd v))
        | _ -> GlbVal c
        end
      | None -> GlbVal c
      end
    | _ -> GlbVal c
  in
  (v, gtypref t_constr)

let interp_constr flags ist c =
  let open Pretyping in
  let ist = to_lvar ist in
  pf_apply ~catch_exceptions:true begin fun env sigma ->
    let (sigma, c) = understand_ltac flags env sigma ist WithoutTypeConstraint c in
    let c = Tac2ffi.of_constr c in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT c
  end

let () =
  let intern = intern_constr in
  let interp ist c = interp_constr constr_flags ist c in
  let print env sigma c = str "constr:(" ++ Printer.pr_lglob_constr_env env sigma c ++ str ")" in
  let raw_print env sigma c = str "constr:(" ++ Ppconstr.pr_constr_expr env sigma c ++ str ")" in
  let subst subst c = Detyping.subst_glob_constr (Global.env()) subst c in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_constr obj

let () =
  let intern = intern_constr in
  let interp ist c = interp_constr open_constr_no_classes_flags ist c in
  let print env sigma c = str "open_constr:(" ++ Printer.pr_lglob_constr_env env sigma c ++ str ")" in
  let raw_print env sigma c = str "open_constr:(" ++ Ppconstr.pr_constr_expr env sigma c ++ str ")" in
  let subst subst c = Detyping.subst_glob_constr (Global.env()) subst c in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_open_constr obj

let () =
  let interp _ id = return (Tac2ffi.of_ident id) in
  let print _ _ id = str "ident:(" ++ Id.print id ++ str ")" in
  let obj = {
    ml_intern = (fun _ _ id -> GlbVal id, gtypref t_ident);
    ml_interp = interp;
    ml_subst = (fun _ id -> id);
    ml_print = print;
    ml_raw_print = print;
  } in
  define_ml_object Tac2quote.wit_ident obj

let () =
  let intern self {Genintern.ltacvars=lfun; genv=env; extra; intern_sign=_; strict_check} c =
    let sigma = Evd.from_env env in
    let ltacvars = {
      Constrintern.ltac_vars = lfun;
      ltac_bound = Id.Set.empty;
      ltac_extra = extra;
    }
    in
    let _, pat = Constrintern.intern_uninstantiated_constr_pattern env sigma ~strict_check ~as_type:false ~ltacvars c in
    GlbVal pat, gtypref t_pattern
  in
  let subst subst c =
    let env = Global.env () in
    let sigma = Evd.from_env env in
    Patternops.subst_pattern env sigma subst c
  in
  let print env sigma pat = str "pat:(" ++ Printer.pr_lconstr_pattern_env env sigma pat ++ str ")" in
  let raw_print env sigma pat = str "pat:(" ++ Ppconstr.pr_constr_pattern_expr env sigma pat ++ str ")" in
  let interp env c =
    let ist = to_lvar env in
    pf_apply ~catch_exceptions:true begin fun env sigma ->
      let c = Patternops.interp_pattern env sigma ist c in
      return (Tac2ffi.of_pattern c)
    end
  in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = subst;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_pattern obj

let () =
  let intern self ist c =
    let (_, (c, _)) = Genintern.intern Stdarg.wit_constr ist c in
    (GlbVal (Id.Set.empty,c), gtypref t_preterm)
  in
  let interp env (ids,c) =
    let open Ltac_pretype in
    let get_preterm id = match Id.Map.find_opt id env.env_ist with
      | Some (ValExt (tag, v)) ->
        begin match Tac2dyn.Val.eq tag val_preterm with
          | Some Refl -> (v:closed_glob_constr)
          | None -> assert false
        end
      | _ -> assert false
    in
    let closure = {
      idents = Id.Map.empty;
      typed = Id.Map.empty;
      untyped = Id.Map.bind get_preterm ids;
      genargs = Tac2interp.set_env env Id.Map.empty;
    } in
    let c = { closure; term = c } in
    return (Tac2ffi.of_preterm c)
  in
  let subst subst (ids,c) = ids, Detyping.subst_glob_constr (Global.env()) subst c in
  let print env sigma (ids,c) =
    let ppids = if Id.Set.is_empty ids then mt()
      else prlist_with_sep spc Id.print (Id.Set.elements ids) ++ spc() ++ str "|-" ++ spc()
    in
    str "preterm:(" ++ ppids ++ Printer.pr_lglob_constr_env env sigma c ++ str ")"
  in
  let raw_print env sigma c = str "preterm:(" ++ Ppconstr.pr_constr_expr env sigma c ++ str ")" in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = subst;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_preterm obj

let () =
  let intern self ist ref = match ref.CAst.v with
  | Tac2qexpr.QHypothesis id ->
    GlbVal (GlobRef.VarRef id), gtypref t_reference
  | Tac2qexpr.QReference qid ->
    let gr =
      try Nametab.locate qid
      with Not_found as exn ->
        let _, info = Exninfo.capture exn in
        Nametab.error_global_not_found ~info qid
    in
    GlbVal gr, gtypref t_reference
  in
  let subst s c = Globnames.subst_global_reference s c in
  let interp _ gr = return (Tac2ffi.of_reference gr) in
  let print _ _ = function
  | GlobRef.VarRef id -> str "reference:(" ++ str "&" ++ Id.print id ++ str ")"
  | r -> str "reference:(" ++ Printer.pr_global r ++ str ")"
  in
  let raw_print _ _ r = match r.CAst.v with
    | Tac2qexpr.QReference qid -> str "reference:(" ++ Libnames.pr_qualid qid ++ str ")"
    | Tac2qexpr.QHypothesis id -> str "reference:(&" ++ Id.print id ++ str ")"
  in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
    ml_raw_print = raw_print;
  } in
  define_ml_object Tac2quote.wit_reference obj

(** Ltac2 in terms *)

let () =
  let interp ?loc ~poly env sigma tycon (ids, tac) =
    (* Syntax prevents bound notation variables in constr quotations *)
    let () = assert (Id.Set.is_empty ids) in
    let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
    let tac = Proofview.tclIGNORE (Tac2interp.interp ist tac) in
    let name, poly = Id.of_string "ltac2", poly in
    let sigma, concl = match tycon with
    | Some ty -> sigma, ty
    | None -> GlobEnv.new_type_evar env sigma ~src:(loc,Evar_kinds.InternalHole)
    in
    let c, sigma = Proof.refine_by_tactic ~name ~poly (GlobEnv.renamed_env env) sigma concl tac in
    let j = { Environ.uj_val = EConstr.of_constr c; Environ.uj_type = concl } in
    (j, sigma)
  in
  GlobEnv.register_constr_interp0 wit_ltac2_constr interp

let interp_constr_var_as_constr ?loc env sigma tycon id =
  let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
  let env = GlobEnv.renamed_env env in
  let c = Id.Map.find id ist.env_ist in
  let c = Tac2ffi.to_constr c in
  let t = Retyping.get_type_of env sigma c in
  let j = { Environ.uj_val = c; uj_type = t } in
  match tycon with
  | None ->
    j, sigma
  | Some ty ->
    let sigma =
      try Evarconv.unify_leq_delay env sigma t ty
      with Evarconv.UnableToUnify (sigma,e) ->
        Pretype_errors.error_actual_type ?loc env sigma j ty e
    in
    {j with Environ.uj_type = ty}, sigma

let interp_preterm_var_as_constr ?loc env sigma tycon id =
  let open Ltac_pretype in
  let ist = Tac2interp.get_env @@ GlobEnv.lfun env in
  let env = GlobEnv.renamed_env env in
  let c = Id.Map.find id ist.env_ist in
  let {closure; term} = Tac2ffi.to_preterm c in
  let vars = {
    ltac_constrs = closure.typed;
    ltac_uconstrs = closure.untyped;
    ltac_idents = closure.idents;
    ltac_genargs = closure.genargs;
  }
  in
  let flags = preterm_flags in
  let tycon = let open Pretyping in match tycon with
    | Some ty -> OfType ty
    | None -> WithoutTypeConstraint
  in
  let sigma, t, ty = Pretyping.understand_ltac_ty flags env sigma vars tycon term in
  Environ.make_judge t ty, sigma

let () =
  let interp ?loc ~poly env sigma tycon (kind,id) =
    let f = match kind with
      | ConstrVar -> interp_constr_var_as_constr
      | PretermVar -> interp_preterm_var_as_constr
      | PatternVar -> assert false
    in
    f ?loc env sigma tycon id
  in
  GlobEnv.register_constr_interp0 wit_ltac2_var_quotation interp

let () =
  let interp env sigma ist (kind,id) =
    let () = match kind with
      | ConstrVar -> assert false (* checked at intern time *)
      | PretermVar -> assert false
      | PatternVar -> ()
    in
    let ist = Tac2interp.get_env ist.Ltac_pretype.ltac_genargs in
    let c = Id.Map.find id ist.env_ist in
    let c = Tac2ffi.to_pattern c in
    c
  in
  Patternops.register_interp_pat wit_ltac2_var_quotation interp

let () =
  let pr_raw (kind,id) = Genprint.PrinterBasic (fun _env _sigma ->
      let ppkind =
      match kind with
        | None -> mt()
        | Some kind -> Id.print kind.CAst.v ++ str ":"
      in
      str "$" ++ ppkind ++ Id.print id.CAst.v)
  in
  let pr_glb (kind,id) = Genprint.PrinterBasic (fun _env _sigma ->
      let ppkind = match kind with
        | ConstrVar -> mt()
        | PretermVar -> str "preterm:"
        | PatternVar -> str "pattern:"
      in
      str "$" ++ ppkind ++ Id.print id) in
  let pr_top x = Util.Empty.abort x in
  Genprint.register_print0 wit_ltac2_var_quotation pr_raw pr_glb pr_top

let warn_missing_notation_variable =
  CWarnings.create ~name:"ltac2-missing-notation-var" ~category:CWarnings.CoreCategories.ltac2
    Pp.(fun rem ->
        let plural = if Id.Set.cardinal rem <= 1 then " " else "s " in
        str "Missing notation term for variable" ++ str plural ++
        pr_sequence Id.print (Id.Set.elements rem) ++
        str ", if used in Ltac2 code in the notation an error will be produced.")

let () =
  let subs avoid globs (ids, tac) =
    (* Let-bind the notation terms inside the tactic *)
    let fold id c (rem, accu) =
      let c = GTacExt (Tac2quote.wit_preterm, (avoid, c)) in
      let rem = Id.Set.remove id rem in
      rem, (Name id, c) :: accu
    in
    let rem, bnd = Id.Map.fold fold globs (ids, []) in
    (* FIXME: provide a reasonable middle-ground with the behaviour
       introduced by 8d9b66b. We should be able to pass mere syntax to
       term notation without facing the wrath of the internalization. *)
    let () = if not @@ Id.Set.is_empty rem then warn_missing_notation_variable rem in
    let bnd = Id.Set.fold (fun id bnd ->
        let c =
          DAst.make
            (Glob_term.GVar
               (Id.of_string_soft ("Notation variable " ^ Id.to_string id ^ " is not available")))
        in
        let c = GTacExt (Tac2quote.wit_preterm, (Id.Set.empty, c)) in
        (Name id, c) :: bnd)
        rem bnd
    in
    let tac = if List.is_empty bnd then tac else GTacLet (false, bnd, tac) in
    (avoid, tac)
  in
  Genintern.register_ntn_subst0 wit_ltac2_constr subs

let () =
  let pr_raw _ = Genprint.PrinterBasic (fun _env _sigma -> assert false) in
  let pr_glb (ids, e) =
    let ids =
      if List.is_empty ids then mt ()
      else pr_sequence Id.print ids ++ str " |- "
    in
    Genprint.PrinterBasic Pp.(fun _env _sigma -> ids ++ Tac2print.pr_glbexpr ~avoid:Id.Set.empty e)
  in
  let pr_top x = Util.Empty.abort x in
  Genprint.register_print0 wit_ltac2in1 pr_raw pr_glb pr_top

let () =
  let pr_raw e = Genprint.PrinterBasic (fun _env _sigma ->
      let avoid = Id.Set.empty in
      (* FIXME avoid set, same as pr_glb *)
      let e = Tac2intern.debug_globalize_allow_ext avoid e in
      Tac2print.pr_rawexpr_gen ~avoid E5 e) in
  let pr_glb (ids, e) =
    let ids =
      let ids = Id.Set.elements ids in
      if List.is_empty ids then mt ()
      else pr_sequence Id.print ids ++ str " |- "
    in
    (* FIXME avoid set
       eg "Ltac2 bla foo := constr:(ltac2:(foo X.foo))"
       gets incorrectly printed as "fun foo => constr:(ltac2:(foo foo))"
       NB: can't pass through evar map store as the evar map we get is a dummy,
       see Ppconstr.pr_genarg
    *)
    Genprint.PrinterBasic Pp.(fun _env _sigma -> ids ++ Tac2print.pr_glbexpr ~avoid:Id.Set.empty e)
  in
  let pr_top e = Util.Empty.abort e in
  Genprint.register_print0 wit_ltac2_constr pr_raw pr_glb pr_top

(** Built-in notation scopes *)

let add_scope s f =
  Tac2entries.register_scope (Id.of_string s) f

let rec pr_scope = let open CAst in function
| SexprStr {v=s} -> qstring s
| SexprInt {v=n} -> Pp.int n
| SexprRec (_, {v=na}, args) ->
  let na = match na with
  | None -> str "_"
  | Some id -> Id.print id
  in
  na ++ str "(" ++ prlist_with_sep (fun () -> str ", ") pr_scope args ++ str ")"

let scope_fail s args =
  let args = str "(" ++ prlist_with_sep (fun () -> str ", ") pr_scope args ++ str ")" in
  CErrors.user_err (str "Invalid arguments " ++ args ++ str " in scope " ++ str s)

let q_unit = CAst.make @@ CTacCst (AbsKn (Tuple 0))

let add_generic_scope s entry arg =
  let parse = function
  | [] ->
    let scope = Pcoq.Symbol.nterm entry in
    let act x = CAst.make @@ CTacExt (arg, x) in
    Tac2entries.ScopeRule (scope, act)
  | arg -> scope_fail s arg
  in
  add_scope s parse

open CAst

let () = add_scope "keyword" begin function
| [SexprStr {loc;v=s}] ->
  let scope = Pcoq.Symbol.token (Tok.PKEYWORD s) in
  Tac2entries.ScopeRule (scope, (fun _ -> q_unit))
| arg -> scope_fail "keyword" arg
end

let () = add_scope "terminal" begin function
| [SexprStr {loc;v=s}] ->
  let scope = Pcoq.Symbol.token (Pcoq.terminal s) in
  Tac2entries.ScopeRule (scope, (fun _ -> q_unit))
| arg -> scope_fail "terminal" arg
end

let () = add_scope "list0" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let scope = Pcoq.Symbol.list0 scope in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| [tok; SexprStr {v=str}] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let sep = Pcoq.Symbol.tokens [Pcoq.TPattern (Pcoq.terminal str)] in
  let scope = Pcoq.Symbol.list0sep scope sep false in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "list0" arg
end

let () = add_scope "list1" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let scope = Pcoq.Symbol.list1 scope in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| [tok; SexprStr {v=str}] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let sep = Pcoq.Symbol.tokens [Pcoq.TPattern (Pcoq.terminal str)] in
  let scope = Pcoq.Symbol.list1sep scope sep false in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "list1" arg
end

let () = add_scope "opt" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let scope = Pcoq.Symbol.opt scope in
  let act opt = match opt with
  | None ->
    CAst.make @@ CTacCst (AbsKn (Other Core.c_none))
  | Some x ->
    CAst.make @@ CTacApp (CAst.make @@ CTacCst (AbsKn (Other Core.c_some)), [act x])
  in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "opt" arg
end

let () = add_scope "self" begin function
| [] ->
  let scope = Pcoq.Symbol.self in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "self" arg
end

let () = add_scope "next" begin function
| [] ->
  let scope = Pcoq.Symbol.next in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "next" arg
end

let () = add_scope "tactic" begin function
| [] ->
  (* Default to level 5 parsing *)
  let scope = Pcoq.Symbol.nterml ltac2_expr "5" in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| [SexprInt {loc;v=n}] as arg ->
  let () = if n < 0 || n > 6 then scope_fail "tactic" arg in
  let scope = Pcoq.Symbol.nterml ltac2_expr (string_of_int n) in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "tactic" arg
end

let () = add_scope "thunk" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let act e = Tac2quote.thunk (act e) in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "thunk" arg
end

let () = add_scope "constr" (fun arg ->
    let delimiters = List.map (function
        | SexprRec (_, { v = Some s }, []) -> s
        | _ -> scope_fail "constr" arg)
        arg
    in
    let act e = Tac2quote.of_constr ~delimiters e in
    Tac2entries.ScopeRule (Pcoq.Symbol.nterm Pcoq.Constr.constr, act)
  )

let () = add_scope "open_constr" (fun arg ->
    let delimiters = List.map (function
        | SexprRec (_, { v = Some s }, []) -> s
        | _ -> scope_fail "open_constr" arg)
        arg
    in
    let act e = Tac2quote.of_open_constr ~delimiters e in
    Tac2entries.ScopeRule (Pcoq.Symbol.nterm Pcoq.Constr.constr, act)
  )

let () = add_scope "preterm" (fun arg ->
    let delimiters = List.map (function
        | SexprRec (_, { v = Some s }, []) -> s
        | _ -> scope_fail "preterm" arg)
        arg
    in
    let act e = Tac2quote.of_preterm ~delimiters e in
    Tac2entries.ScopeRule (Pcoq.Symbol.nterm Pcoq.Constr.constr, act)
  )

let add_expr_scope name entry f =
  add_scope name begin function
  | [] -> Tac2entries.ScopeRule (Pcoq.Symbol.nterm entry, f)
  | arg -> scope_fail name arg
  end

let () = add_expr_scope "ident" q_ident (fun id -> Tac2quote.of_anti Tac2quote.of_ident id)
let () = add_expr_scope "bindings" q_bindings Tac2quote.of_bindings
let () = add_expr_scope "with_bindings" q_with_bindings Tac2quote.of_bindings
let () = add_expr_scope "intropattern" q_intropattern Tac2quote.of_intro_pattern
let () = add_expr_scope "intropatterns" q_intropatterns Tac2quote.of_intro_patterns
let () = add_expr_scope "destruction_arg" q_destruction_arg Tac2quote.of_destruction_arg
let () = add_expr_scope "induction_clause" q_induction_clause Tac2quote.of_induction_clause
let () = add_expr_scope "conversion" q_conversion Tac2quote.of_conversion
let () = add_expr_scope "orient" q_orient Tac2quote.of_orient
let () = add_expr_scope "rewriting" q_rewriting Tac2quote.of_rewriting
let () = add_expr_scope "clause" q_clause Tac2quote.of_clause
let () = add_expr_scope "hintdb" q_hintdb Tac2quote.of_hintdb
let () = add_expr_scope "occurrences" q_occurrences Tac2quote.of_occurrences
let () = add_expr_scope "dispatch" q_dispatch Tac2quote.of_dispatch
let () = add_expr_scope "strategy" q_strategy_flag Tac2quote.of_strategy_flag
let () = add_expr_scope "reference" q_reference Tac2quote.of_reference
let () = add_expr_scope "move_location" q_move_location Tac2quote.of_move_location
let () = add_expr_scope "pose" q_pose Tac2quote.of_pose
let () = add_expr_scope "assert" q_assert Tac2quote.of_assertion
let () = add_expr_scope "constr_matching" q_constr_matching Tac2quote.of_constr_matching
let () = add_expr_scope "goal_matching" q_goal_matching Tac2quote.of_goal_matching
let () = add_expr_scope "format" Pcoq.Prim.lstring Tac2quote.of_format

let () = add_generic_scope "pattern" Pcoq.Constr.constr Tac2quote.wit_pattern

(** seq scope, a bit hairy *)

open Pcoq

type _ converter =
| CvNil : (Loc.t -> raw_tacexpr) converter
| CvCns : 'act converter * ('a -> raw_tacexpr) option -> ('a -> 'act) converter

let rec apply : type a. a converter -> raw_tacexpr list -> a = function
| CvNil -> fun accu loc -> Tac2quote.of_tuple ~loc accu
| CvCns (c, None) -> fun accu x -> apply c accu
| CvCns (c, Some f) -> fun accu x -> apply c (f x :: accu)

type seqrule =
| Seqrule : (Tac2expr.raw_tacexpr, Gramlib.Grammar.norec, 'act, Loc.t -> raw_tacexpr) Rule.t * 'act converter -> seqrule

let rec make_seq_rule = function
| [] ->
  Seqrule (Pcoq.Rule.stop, CvNil)
| tok :: rem ->
  let Tac2entries.ScopeRule (scope, f) = Tac2entries.parse_scope tok in
  let scope =
    match Pcoq.generalize_symbol scope with
    | None ->
      CErrors.user_err (str "Recursive symbols (self / next) are not allowed in local rules")
    | Some scope -> scope
  in
  let Seqrule (r, c) = make_seq_rule rem in
  let r = Pcoq.Rule.next_norec r scope in
  let f = match tok with
  | SexprStr _ -> None (* Leave out mere strings *)
  | _ -> Some f
  in
  Seqrule (r, CvCns (c, f))

let () = add_scope "seq" begin fun toks ->
  let scope =
    let Seqrule (r, c) = make_seq_rule (List.rev toks) in
    Pcoq.(Symbol.rules [Rules.make r (apply c [])])
  in
  Tac2entries.ScopeRule (scope, (fun e -> e))
end
