(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CSig
open Pp
open Names
open Genarg
open Tac2env
open Tac2dyn
open Tac2expr
open Tac2interp
open Tac2entries.Pltac
open Proofview.Notations

(** Standard values *)

module Value = Tac2ffi

let std_core n = KerName.make2 Tac2env.std_prefix (Label.of_id (Id.of_string_soft n))
let coq_core n = KerName.make2 Tac2env.coq_prefix (Label.of_id (Id.of_string_soft n))

module Core =
struct

let t_int = coq_core "int"
let t_string = coq_core "string"
let t_array = coq_core "array"
let t_unit = coq_core "unit"
let t_list = coq_core "list"
let t_constr = coq_core "constr"
let t_pattern = coq_core "pattern"
let t_ident = coq_core "ident"
let t_option = coq_core "option"
let t_reference = std_core "reference"

let c_nil = coq_core "[]"
let c_cons = coq_core "::"

let c_none = coq_core "None"
let c_some = coq_core "Some"

let c_true = coq_core "true"
let c_false = coq_core "false"

end

open Core

let v_unit = ValInt 0

let to_block = function
| ValBlk (_, v) -> v
| _ -> assert false

let of_name c = match c with
| Anonymous -> Value.of_option Value.of_ident None
| Name id -> Value.of_option Value.of_ident (Some id)

let to_name c = match Value.to_option Value.to_ident c with
| None -> Anonymous
| Some id -> Name id

let of_instance u =
  let u = Univ.Instance.to_array (EConstr.Unsafe.to_instance u) in
  Value.of_array (fun v -> Value.of_ext Value.val_univ v) u

let to_instance u =
  let u = Value.to_array (fun v -> Value.to_ext Value.val_univ v) u in
  EConstr.EInstance.make (Univ.Instance.of_array u)

let of_rec_declaration (nas, ts, cs) =
  (Value.of_array of_name nas,
  Value.of_array Value.of_constr ts,
  Value.of_array Value.of_constr cs)

let to_rec_declaration (nas, ts, cs) =
  (Value.to_array to_name nas,
  Value.to_array Value.to_constr ts,
  Value.to_array Value.to_constr cs)

let of_result f = function
| Inl c -> ValBlk (0, [|f c|])
| Inr e -> ValBlk (1, [|Value.of_exn e|])

(** Stdlib exceptions *)

let err_notfocussed =
  LtacError (coq_core "Not_focussed", [||])

let err_outofbounds =
  LtacError (coq_core "Out_of_bounds", [||])

let err_notfound =
  LtacError (coq_core "Not_found", [||])

let err_matchfailure =
  LtacError (coq_core "Match_failure", [||])

(** Helper functions *)

let thaw f = interp_app f [v_unit]
let throw e = Proofview.tclLIFT (Proofview.NonLogical.raise e)

let return x = Proofview.tclUNIT x
let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let wrap f =
  return () >>= fun () -> return (f ())

let wrap_unit f =
  return () >>= fun () -> f (); return v_unit

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

let define0 name f = Tac2env.define_primitive (pname name) begin function
| [_] -> f
| _ -> assert false
end

let define1 name f = Tac2env.define_primitive (pname name) begin function
| [x] -> f x
| _ -> assert false
end

let define2 name f = Tac2env.define_primitive (pname name) begin function
| [x; y] -> f x y
| _ -> assert false
end

let define3 name f = Tac2env.define_primitive (pname name) begin function
| [x; y; z] -> f x y z
| _ -> assert false
end

(** Printing *)

let () = define1 "print" begin fun pp ->
  wrap_unit (fun () -> Feedback.msg_notice (Value.to_pp pp))
end

let () = define1 "message_of_int" begin fun n ->
  let n = Value.to_int n in
  return (Value.of_pp (int n))
end

let () = define1 "message_of_string" begin fun s ->
  let s = Value.to_string s in
  return (Value.of_pp (str (Bytes.to_string s)))
end

let () = define1 "message_of_constr" begin fun c ->
  pf_apply begin fun env sigma ->
    let c = Value.to_constr c in
    let pp = Printer.pr_econstr_env env sigma c in
    return (Value.of_pp pp)
  end
end

let () = define1 "message_of_ident" begin fun c ->
  let c = Value.to_ident c in
  let pp = Id.print c in
  return (Value.of_pp pp)
end

let () = define2 "message_concat" begin fun m1 m2 ->
  let m1 = Value.to_pp m1 in
  let m2 = Value.to_pp m2 in
  return (Value.of_pp (Pp.app m1 m2))
end

(** Array *)

let () = define2 "array_make" begin fun n x ->
  let n = Value.to_int n in
  if n < 0 || n > Sys.max_array_length then throw err_outofbounds
  else wrap (fun () -> ValBlk (0, Array.make n x))
end

let () = define1 "array_length" begin fun v ->
  let v = to_block v in
  return (ValInt (Array.length v))
end

let () = define3 "array_set" begin fun v n x ->
  let v = to_block v in
  let n = Value.to_int n in
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap_unit (fun () -> v.(n) <- x)
end

let () = define2 "array_get" begin fun v n ->
  let v = to_block v in
  let n = Value.to_int n in
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap (fun () -> v.(n))
end

(** Ident *)

let () = define2 "ident_equal" begin fun id1 id2 ->
  let id1 = Value.to_ident id1 in
  let id2 = Value.to_ident id2 in
  return (Value.of_bool (Id.equal id1 id2))
end

let () = define1 "ident_to_string" begin fun id ->
  let id = Value.to_ident id in
  return (Value.of_string (Id.to_string id))
end

let () = define1 "ident_of_string" begin fun s ->
  let s = Value.to_string s in
  let id = try Some (Id.of_string s) with _ -> None in
  return (Value.of_option Value.of_ident id)
end

(** Int *)

let () = define2 "int_equal" begin fun m n ->
  return (Value.of_bool (Value.to_int m == Value.to_int n))
end

let binop n f = define2 n begin fun m n ->
  return (Value.of_int (f (Value.to_int m) (Value.to_int n)))
end

let () = binop "int_compare" Int.compare
let () = binop "int_add" (+)
let () = binop "int_sub" (-)
let () = binop "int_mul" ( * )

let () = define1 "int_neg" begin fun m ->
  return (Value.of_int (~- (Value.to_int m)))
end

(** String *)

let () = define2 "string_make" begin fun n c ->
  let n = Value.to_int n in
  let c = Value.to_char c in
  if n < 0 || n > Sys.max_string_length then throw err_outofbounds
  else wrap (fun () -> Value.of_string (Bytes.make n c))
end

let () = define1 "string_length" begin fun s ->
  return (Value.of_int (Bytes.length (Value.to_string s)))
end

let () = define3 "string_set" begin fun s n c ->
  let s = Value.to_string s in
  let n = Value.to_int n in
  let c = Value.to_char c in
  if n < 0 || n >= Bytes.length s then throw err_outofbounds
  else wrap_unit (fun () -> Bytes.set s n c)
end

let () = define2 "string_get" begin fun s n ->
  let s = Value.to_string s in
  let n = Value.to_int n in
  if n < 0 || n >= Bytes.length s then throw err_outofbounds
  else wrap (fun () -> Value.of_char (Bytes.get s n))
end

(** Terms *)

(** constr -> constr *)
let () = define1 "constr_type" begin fun c ->
  let c = Value.to_constr c in
  let get_type env sigma =
  Proofview.V82.wrap_exceptions begin fun () ->
    let (sigma, t) = Typing.type_of env sigma c in
    let t = Value.of_constr t in
    Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
  end in
  pf_apply get_type
end

(** constr -> constr *)
let () = define2 "constr_equal" begin fun c1 c2 ->
  let c1 = Value.to_constr c1 in
  let c2 = Value.to_constr c2 in
  Proofview.tclEVARMAP >>= fun sigma ->
  let b = EConstr.eq_constr sigma c1 c2 in
  Proofview.tclUNIT (Value.of_bool b)
end

let () = define1 "constr_kind" begin fun c ->
  let open Constr in
  Proofview.tclEVARMAP >>= fun sigma ->
  let c = Value.to_constr c in
  return begin match EConstr.kind sigma c with
  | Rel n ->
    ValBlk (0, [|Value.of_int n|])
  | Var id ->
    ValBlk (1, [|Value.of_ident id|])
  | Meta n ->
    ValBlk (2, [|Value.of_int n|])
  | Evar (evk, args) ->
    ValBlk (3, [|
      Value.of_int (Evar.repr evk);
      Value.of_array Value.of_constr args;
    |])
  | Sort s ->
    ValBlk (4, [|Value.of_ext Value.val_sort s|])
  | Cast (c, k, t) ->
    ValBlk (5, [|
      Value.of_constr c;
      Value.of_ext Value.val_cast k;
      Value.of_constr t;
    |])
  | Prod (na, t, u) ->
    ValBlk (6, [|
      of_name na;
      Value.of_constr t;
      Value.of_constr u;
    |])
  | Lambda (na, t, c) ->
    ValBlk (7, [|
      of_name na;
      Value.of_constr t;
      Value.of_constr c;
    |])
  | LetIn (na, b, t, c) ->
    ValBlk (8, [|
      of_name na;
      Value.of_constr b;
      Value.of_constr t;
      Value.of_constr c;
    |])
  | App (c, cl) ->
    ValBlk (9, [|
      Value.of_constr c;
      Value.of_array Value.of_constr cl;
    |])
  | Const (cst, u) ->
    ValBlk (10, [|
      Value.of_constant cst;
      of_instance u;
    |])
  | Ind (ind, u) ->
    ValBlk (11, [|
      Value.of_ext Value.val_inductive ind;
      of_instance u;
    |])
  | Construct (cstr, u) ->
    ValBlk (12, [|
      Value.of_ext Value.val_constructor cstr;
      of_instance u;
    |])
  | Case (ci, c, t, bl) ->
    ValBlk (13, [|
      Value.of_ext Value.val_case ci;
      Value.of_constr c;
      Value.of_constr t;
      Value.of_array Value.of_constr bl;
    |])
  | Fix ((recs, i), def) ->
    let (nas, ts, cs) = of_rec_declaration def in
    ValBlk (14, [|
      Value.of_array Value.of_int recs;
      Value.of_int i;
      nas;
      ts;
      cs;
    |])
  | CoFix (i, def) ->
    let (nas, ts, cs) = of_rec_declaration def in
    ValBlk (15, [|
      Value.of_int i;
      nas;
      ts;
      cs;
    |])
  | Proj (p, c) ->
    ValBlk (16, [|
      Value.of_ext Value.val_projection p;
      Value.of_constr c;
    |])
  end
end

let () = define1 "constr_make" begin fun knd ->
  let open Constr in
  let c = match knd with
  | ValBlk (0, [|n|]) ->
    let n = Value.to_int n in
    EConstr.mkRel n
  | ValBlk (1, [|id|]) ->
    let id = Value.to_ident id in
    EConstr.mkVar id
  | ValBlk (2, [|n|]) ->
    let n = Value.to_int n in
    EConstr.mkMeta n
  | ValBlk (3, [|evk; args|]) ->
    let evk = Evar.unsafe_of_int (Value.to_int evk) in
    let args = Value.to_array Value.to_constr args in
    EConstr.mkEvar (evk, args)
  | ValBlk (4, [|s|]) ->
    let s = Value.to_ext Value.val_sort s in
    EConstr.mkSort (EConstr.Unsafe.to_sorts s)
  | ValBlk (5, [|c; k; t|]) ->
    let c = Value.to_constr c in
    let k = Value.to_ext Value.val_cast k in
    let t = Value.to_constr t in
    EConstr.mkCast (c, k, t)
  | ValBlk (6, [|na; t; u|]) ->
    let na = to_name na in
    let t = Value.to_constr t in
    let u = Value.to_constr u in
    EConstr.mkProd (na, t, u)
  | ValBlk (7, [|na; t; c|]) ->
    let na = to_name na in
    let t = Value.to_constr t in
    let u = Value.to_constr c in
    EConstr.mkLambda (na, t, u)
  | ValBlk (8, [|na; b; t; c|]) ->
    let na = to_name na in
    let b = Value.to_constr b in
    let t = Value.to_constr t in
    let c = Value.to_constr c in
    EConstr.mkLetIn (na, b, t, c)
  | ValBlk (9, [|c; cl|]) ->
    let c = Value.to_constr c in
    let cl = Value.to_array Value.to_constr cl in
    EConstr.mkApp (c, cl)
  | ValBlk (10, [|cst; u|]) ->
    let cst = Value.to_constant cst in
    let u = to_instance u in
    EConstr.mkConstU (cst, u)
  | ValBlk (11, [|ind; u|]) ->
    let ind = Value.to_ext Value.val_inductive ind in
    let u = to_instance u in
    EConstr.mkIndU (ind, u)
  | ValBlk (12, [|cstr; u|]) ->
    let cstr = Value.to_ext Value.val_constructor cstr in
    let u = to_instance u in
    EConstr.mkConstructU (cstr, u)
  | ValBlk (13, [|ci; c; t; bl|]) ->
    let ci = Value.to_ext Value.val_case ci in
    let c = Value.to_constr c in
    let t = Value.to_constr t in
    let bl = Value.to_array Value.to_constr bl in
    EConstr.mkCase (ci, c, t, bl)
  | ValBlk (14, [|recs; i; nas; ts; cs|]) ->
    let recs = Value.to_array Value.to_int recs in
    let i = Value.to_int i in
    let def = to_rec_declaration (nas, ts, cs) in
    EConstr.mkFix ((recs, i), def)
  | ValBlk (15, [|i; nas; ts; cs|]) ->
    let i = Value.to_int i in
    let def = to_rec_declaration (nas, ts, cs) in
    EConstr.mkCoFix (i, def)
  | ValBlk (16, [|p; c|]) ->
    let p = Value.to_ext Value.val_projection p in
    let c = Value.to_constr c in
    EConstr.mkProj (p, c)
  | _ -> assert false
  in
  return (Value.of_constr c)
end

let () = define1 "constr_check" begin fun c ->
  let c = Value.to_constr c in
  pf_apply begin fun env sigma ->
    try
      let (sigma, _) = Typing.type_of env sigma c in
      Proofview.Unsafe.tclEVARS sigma >>= fun () ->
      return (of_result Value.of_constr (Inl c))
    with e when CErrors.noncritical e ->
      let e = CErrors.push e in
      return (of_result Value.of_constr (Inr e))
  end
end

let () = define3 "constr_substnl" begin fun subst k c ->
  let subst = Value.to_list Value.to_constr subst in
  let k = Value.to_int k in
  let c = Value.to_constr c in
  let ans = EConstr.Vars.substnl subst k c in
  return (Value.of_constr ans)
end

let () = define3 "constr_closenl" begin fun ids k c ->
  let ids = Value.to_list Value.to_ident ids in
  let k = Value.to_int k in
  let c = Value.to_constr c in
  let ans = EConstr.Vars.substn_vars k ids c in
  return (Value.of_constr ans)
end

(** Patterns *)

let () = define2 "pattern_matches" begin fun pat c ->
  let pat = Value.to_pattern pat in
  let c = Value.to_constr c in
  pf_apply begin fun env sigma ->
    let ans =
      try Some (Constr_matching.matches env sigma pat c)
      with Constr_matching.PatternMatchingFailure -> None
    in
    begin match ans with
    | None -> Proofview.tclZERO err_matchfailure
    | Some ans ->
      let ans = Id.Map.bindings ans in
      let of_pair (id, c) = Value.of_tuple [| Value.of_ident id; Value.of_constr c |] in
      return (Value.of_list of_pair ans)
    end
  end
end

let () = define2 "pattern_matches_subterm" begin fun pat c ->
  let pat = Value.to_pattern pat in
  let c = Value.to_constr c in
  let open Constr_matching in
  let rec of_ans s = match IStream.peek s with
  | IStream.Nil -> Proofview.tclZERO err_matchfailure
  | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
    let ans = Id.Map.bindings sub in
    let of_pair (id, c) = Value.of_tuple [| Value.of_ident id; Value.of_constr c |] in
    let ans = Value.of_tuple [| Value.of_constr m_ctx; Value.of_list of_pair ans |] in
    Proofview.tclOR (return ans) (fun _ -> of_ans s)
  in
  pf_apply begin fun env sigma ->
    let ans = Constr_matching.match_appsubterm env sigma pat c in
    of_ans ans
  end
end

let () = define2 "pattern_instantiate" begin fun ctx c ->
  let ctx = EConstr.Unsafe.to_constr (Value.to_constr ctx) in
  let c = EConstr.Unsafe.to_constr (Value.to_constr c) in
  let ans = Termops.subst_meta [Constr_matching.special_meta, c] ctx in
  return (Value.of_constr (EConstr.of_constr ans))
end

(** Error *)

let () = define1 "throw" begin fun e ->
  let (e, info) = Value.to_exn e in
  Proofview.tclLIFT (Proofview.NonLogical.raise ~info e)
end

(** Control *)

(** exn -> 'a *)
let () = define1 "zero" begin fun e ->
  let (e, info) = Value.to_exn e in
  Proofview.tclZERO ~info e
end

(** (unit -> 'a) -> (exn -> 'a) -> 'a *)
let () = define2 "plus" begin fun x k ->
  Proofview.tclOR (thaw x) (fun e -> interp_app k [Value.of_exn e])
end

(** (unit -> 'a) -> 'a *)
let () = define1 "once" begin fun f ->
  Proofview.tclONCE (thaw f)
end

(** (unit -> unit) list -> unit *)
let () = define1 "dispatch" begin fun l ->
  let l = Value.to_list (fun f -> Proofview.tclIGNORE (thaw f)) l in
  Proofview.tclDISPATCH l >>= fun () -> return v_unit
end

(** (unit -> unit) list -> (unit -> unit) -> (unit -> unit) list -> unit *)
let () = define3 "extend" begin fun lft tac rgt ->
  let lft = Value.to_list (fun f -> Proofview.tclIGNORE (thaw f)) lft in
  let tac = Proofview.tclIGNORE (thaw tac) in
  let rgt = Value.to_list (fun f -> Proofview.tclIGNORE (thaw f)) rgt in
  Proofview.tclEXTEND lft tac rgt >>= fun () -> return v_unit
end

(** (unit -> unit) -> unit *)
let () = define1 "enter" begin fun f ->
  let f = Proofview.tclIGNORE (thaw f) in
  Proofview.tclINDEPENDENT f >>= fun () -> return v_unit
end

let k_var = Id.of_string "k"
let e_var = Id.of_string "e"
let prm_apply_kont_h = pname "apply_kont"

(** (unit -> 'a) -> ('a * ('exn -> 'a)) result *)
let () = define1 "case" begin fun f ->
  Proofview.tclCASE (thaw f) >>= begin function
  | Proofview.Next (x, k) ->
    let k = {
      clos_env = Id.Map.singleton k_var (Value.of_ext Value.val_kont k);
      clos_var = [Name e_var];
      clos_exp = GTacPrm (prm_apply_kont_h, [GTacVar k_var; GTacVar e_var]);
    } in
    return (ValBlk (0, [| Value.of_tuple [| x; ValCls k |] |]))
  | Proofview.Fail e -> return (ValBlk (1, [| Value.of_exn e |]))
  end
end

(** 'a kont -> exn -> 'a *)
let () = define2 "apply_kont" begin fun k e ->
  (Value.to_ext Value.val_kont k) (Value.to_exn e)
end

(** int -> int -> (unit -> 'a) -> 'a *)
let () = define3 "focus" begin fun i j tac ->
  let i = Value.to_int i in
  let j = Value.to_int j in
  Proofview.tclFOCUS i j (thaw tac)
end

(** unit -> unit *)
let () = define0 "shelve" begin
  Proofview.shelve >>= fun () -> return v_unit
end

(** unit -> unit *)
let () = define0 "shelve_unifiable" begin
  Proofview.shelve_unifiable >>= fun () -> return v_unit
end

let () = define1 "new_goal" begin fun ev ->
  let ev = Evar.unsafe_of_int (Value.to_int ev) in
  Proofview.tclEVARMAP >>= fun sigma ->
  if Evd.mem sigma ev then
    Proofview.Unsafe.tclNEWGOALS [ev] <*> Proofview.tclUNIT v_unit
  else throw err_notfound
end

(** unit -> constr *)
let () = define0 "goal" begin
  Proofview.Goal.enter_one begin fun gl ->
    let concl = Tacmach.New.pf_nf_concl gl in
    return (Value.of_constr concl)
  end
end

(** ident -> constr *)
let () = define1 "hyp" begin fun id ->
  let id = Value.to_ident id in
  pf_apply begin fun env _ ->
    let mem = try ignore (Environ.lookup_named id env); true with Not_found -> false in
    if mem then return (Value.of_constr (EConstr.mkVar id))
    else Tacticals.New.tclZEROMSG
      (str "Hypothesis " ++ quote (Id.print id) ++ str " not found") (** FIXME: Do something more sensible *)
  end
end

let () = define0 "hyps" begin
  pf_apply begin fun env _ ->
    let open Context.Named.Declaration in
    let hyps = List.rev (Environ.named_context env) in
    let map = function
    | LocalAssum (id, t) ->
      let t = EConstr.of_constr t in
      Value.of_tuple [|Value.of_ident id; Value.of_option Value.of_constr None; Value.of_constr t|]
    | LocalDef (id, c, t) ->
      let c = EConstr.of_constr c in
      let t = EConstr.of_constr t in
      Value.of_tuple [|Value.of_ident id; Value.of_option Value.of_constr (Some c); Value.of_constr t|]
    in
    return (Value.of_list map hyps)
  end
end

(** (unit -> constr) -> unit *)
let () = define1 "refine" begin fun c ->
  let c = thaw c >>= fun c -> Proofview.tclUNIT ((), Value.to_constr c) in
  Proofview.Goal.nf_enter begin fun gl ->
    Refine.generic_refine ~typecheck:true c gl
  end >>= fun () -> return v_unit
end

let () = define2 "with_holes" begin fun x f ->
  Proofview.tclEVARMAP >>= fun sigma0 ->
  thaw x >>= fun ans ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclEVARS sigma0 >>= fun () ->
  Tacticals.New.tclWITHHOLES false (interp_app f [ans]) sigma
end

let () = define1 "progress" begin fun f ->
  Proofview.tclPROGRESS (thaw f)
end

let () = define2 "abstract" begin fun id f ->
  let id = Value.to_option Value.to_ident id in
  Tactics.tclABSTRACT id (Proofview.tclIGNORE (thaw f)) >>= fun () ->
  return v_unit
end

let () = define2 "time" begin fun s f ->
  let s = Value.to_option Value.to_string s in
  Proofview.tclTIME s (thaw f)
end

let () = define0 "check_interrupt" begin
  Proofview.tclCHECKINTERRUPT >>= fun () -> return v_unit
end

(** Fresh *)

let () = define2 "fresh_free_union" begin fun set1 set2 ->
  let set1 = Value.to_ext Value.val_free set1 in
  let set2 = Value.to_ext Value.val_free set2 in
  let ans = Id.Set.union set1 set2 in
  return (Value.of_ext Value.val_free ans)
end

let () = define1 "fresh_free_of_ids" begin fun ids ->
  let ids = Value.to_list Value.to_ident ids in
  let free = List.fold_right Id.Set.add ids Id.Set.empty in
  return (Value.of_ext Value.val_free free)
end

let () = define1 "fresh_free_of_constr" begin fun c ->
  let c = Value.to_constr c in
  Proofview.tclEVARMAP >>= fun sigma ->
  let rec fold accu c = match EConstr.kind sigma c with
  | Constr.Var id -> Id.Set.add id accu
  | _ -> EConstr.fold sigma fold accu c
  in
  let ans = fold Id.Set.empty c in
  return (Value.of_ext Value.val_free ans)
end

let () = define2 "fresh_fresh" begin fun avoid id ->
  let avoid = Value.to_ext Value.val_free avoid in
  let id = Value.to_ident id in
  let nid = Namegen.next_ident_away_from id (fun id -> Id.Set.mem id avoid) in
  return (Value.of_ident nid)
end

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
  let open Glob_ops in
  let lfun = Tac2interp.set_env ist Id.Map.empty in
  { empty_lvar with Glob_term.ltac_genargs = lfun }

let gtypref kn = GTypRef (Other kn, [])

let intern_constr self ist c =
  let (_, (c, _)) = Genintern.intern Stdarg.wit_constr ist c in
  (GlbVal c, gtypref t_constr)

let interp_constr flags ist c =
  let open Pretyping in
  pf_apply begin fun env sigma ->
  Proofview.V82.wrap_exceptions begin fun () ->
    let ist = to_lvar ist in
    let (sigma, c) = understand_ltac flags env sigma ist WithoutTypeConstraint c in
    let c = ValExt (Value.val_constr, c) in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT c
  end
  end

let () =
  let intern = intern_constr in
  let interp ist c = interp_constr (constr_flags ()) ist c in
  let print env c = str "constr:(" ++ Printer.pr_lglob_constr_env env c ++ str ")" in
  let obj = {
    ml_intern = intern;
    ml_subst = Detyping.subst_glob_constr;
    ml_interp = interp;
    ml_print = print;
  } in
  define_ml_object Tac2env.wit_constr obj

let () =
  let intern = intern_constr in
  let interp ist c = interp_constr (open_constr_no_classes_flags ()) ist c in
  let print env c = str "open_constr:(" ++ Printer.pr_lglob_constr_env env c ++ str ")" in
  let obj = {
    ml_intern = intern;
    ml_subst = Detyping.subst_glob_constr;
    ml_interp = interp;
    ml_print = print;
  } in
  define_ml_object Tac2env.wit_open_constr obj

let () =
  let interp _ id = return (ValExt (Value.val_ident, id)) in
  let print _ id = str "ident:(" ++ Id.print id ++ str ")" in
  let obj = {
    ml_intern = (fun _ _ id -> GlbVal id, gtypref t_ident);
    ml_interp = interp;
    ml_subst = (fun _ id -> id);
    ml_print = print;
  } in
  define_ml_object Tac2env.wit_ident obj

let () =
  let intern self ist c =
    let _, pat = Constrintern.intern_constr_pattern ist.Genintern.genv ~as_type:false c in
    GlbVal pat, gtypref t_pattern
  in
  let print env pat = str "pattern:(" ++ Printer.pr_lconstr_pattern_env env Evd.empty pat ++ str ")" in
  let interp _ c = return (ValExt (Value.val_pattern, c)) in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = Patternops.subst_pattern;
    ml_print = print;
  } in
  define_ml_object Tac2env.wit_pattern obj

let () =
  let intern self ist qid = match qid with
  | Libnames.Ident (_, id) ->
    GlbVal (Globnames.VarRef id), gtypref t_reference
  | Libnames.Qualid (loc, qid) ->
    let gr =
      try Nametab.locate qid
      with Not_found ->
        Nametab.error_global_not_found ?loc qid
    in
    GlbVal gr, gtypref t_reference
  in
  let subst s c = Globnames.subst_global_reference s c in
  let interp _ gr = return (Value.of_reference gr) in
  let print _ = function
  | Globnames.VarRef id -> str "reference:(" ++ str "&" ++ Id.print id ++ str ")"
  | r -> str "reference:(" ++ Printer.pr_global r ++ str ")"
  in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
  } in
  define_ml_object Tac2env.wit_reference obj

let () =
  let intern self ist tac =
    (** Prevent inner calls to Ltac2 values *)
    let extra = Tac2intern.drop_ltac2_env ist.Genintern.extra in
    let ist = { ist with Genintern.extra } in
    let _, tac = Genintern.intern Ltac_plugin.Tacarg.wit_tactic ist tac in
    GlbVal tac, gtypref t_unit
  in
  let interp _ tac =
    (** FUCK YOU API *)
    (Obj.magic Ltac_plugin.Tacinterp.eval_tactic tac : unit Proofview.tactic) >>= fun () ->
    return v_unit
  in
  let subst s tac = Genintern.substitute Ltac_plugin.Tacarg.wit_tactic s tac in
  let print env tac =
    str "ltac1:(" ++ Ltac_plugin.Pptactic.pr_glob_tactic (Obj.magic env) tac ++ str ")"
  in
  let obj = {
    ml_intern = intern;
    ml_subst = subst;
    ml_interp = interp;
    ml_print = print;
  } in
  define_ml_object Tac2env.wit_ltac1 obj

(** Ltac2 in terms *)

let () =
  let interp ist env sigma concl tac =
    let ist = Tac2interp.get_env ist in
    let tac = Proofview.tclIGNORE (interp ist tac) in
    let c, sigma = Pfedit.refine_by_tactic env sigma concl tac in
    (EConstr.of_constr c, sigma)
  in
  Pretyping.register_constr_interp0 wit_ltac2 interp

(** Ltac2 in Ltac1 *)

let () =
  (** FUCK YOU API *)
  let e = (Obj.magic Tac2entries.Pltac.tac2expr : _ API.Pcoq.Gram.entry) in
  let inject (loc, v) = Tacexpr.TacGeneric (in_gen (rawwit wit_ltac2) v) in
  Ltac_plugin.Tacentries.create_ltac_quotation "ltac2" inject (e, None)

let () =
  let open Ltac_plugin in
  let open Tacinterp in
  let idtac = Value.of_closure (default_ist ()) (Tacexpr.TacId []) in
  (** FUCK YOU API *)
  let idtac = (Obj.magic idtac : Geninterp.Val.t) in
  let interp ist tac =
    Tac2interp.interp Tac2interp.empty_environment tac >>= fun _ ->
    Ftactic.return idtac
  in
  Geninterp.register_interp0 wit_ltac2 interp

let () =
  let pr_raw _ = mt () in
  let pr_glb e = Tac2print.pr_glbexpr e in
  let pr_top _ = mt () in
  Genprint.register_print0 wit_ltac2 pr_raw pr_glb pr_top

(** Built-in notation scopes *)

let add_scope s f =
  Tac2entries.register_scope (Id.of_string s) f

let scope_fail () = CErrors.user_err (str "Invalid parsing token")

let q_unit = Loc.tag @@ CTacCst (AbsKn (Tuple 0))

let rthunk e =
  let loc = Tac2intern.loc_of_tacexpr e in
  let var = [Loc.tag ?loc @@ CPatVar Anonymous, Some (Loc.tag ?loc @@ CTypRef (AbsKn (Other Core.t_unit), []))] in
  Loc.tag ?loc @@ CTacFun (var, e)

let add_generic_scope s entry arg =
  let parse = function
  | [] ->
    let scope = Extend.Aentry entry in
    let act x = Loc.tag @@ CTacExt (arg, x) in
    Tac2entries.ScopeRule (scope, act)
  | _ -> scope_fail ()
  in
  add_scope s parse

let () = add_scope "keyword" begin function
| [SexprStr (loc, s)] ->
  let scope = Extend.Atoken (Tok.KEYWORD s) in
  Tac2entries.ScopeRule (scope, (fun _ -> q_unit))
| _ -> scope_fail ()
end

let () = add_scope "terminal" begin function
| [SexprStr (loc, s)] ->
  let scope = Extend.Atoken (CLexer.terminal s) in
  Tac2entries.ScopeRule (scope, (fun _ -> q_unit))
| _ -> scope_fail ()
end

let () = add_scope "list0" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let scope = Extend.Alist0 scope in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| [tok; SexprStr (_, str)] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let sep = Extend.Atoken (CLexer.terminal str) in
  let scope = Extend.Alist0sep (scope, sep) in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| _ -> scope_fail ()
end

let () = add_scope "list1" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let scope = Extend.Alist1 scope in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| [tok; SexprStr (_, str)] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let sep = Extend.Atoken (CLexer.terminal str) in
  let scope = Extend.Alist1sep (scope, sep) in
  let act l = Tac2quote.of_list act l in
  Tac2entries.ScopeRule (scope, act)
| _ -> scope_fail ()
end

let () = add_scope "opt" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let scope = Extend.Aopt scope in
  let act opt = match opt with
  | None ->
    Loc.tag @@ CTacCst (AbsKn (Other Core.c_none))
  | Some x ->
    Loc.tag @@ CTacApp (Loc.tag @@ CTacCst (AbsKn (Other Core.c_some)), [act x])
  in
  Tac2entries.ScopeRule (scope, act)
| _ -> scope_fail ()
end

let () = add_scope "self" begin function
| [] ->
  let scope = Extend.Aself in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| _ -> scope_fail ()
end

let () = add_scope "next" begin function
| [] ->
  let scope = Extend.Anext in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| _ -> scope_fail ()
end

let () = add_scope "tactic" begin function
| [] ->
  (** Default to level 5 parsing *)
  let scope = Extend.Aentryl (tac2expr, 5) in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| [SexprInt (loc, n)] ->
  let () = if n < 0 || n > 6 then scope_fail () in
  let scope = Extend.Aentryl (tac2expr, n) in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| _ -> scope_fail ()
end

let () = add_scope "thunk" begin function
| [tok] ->
  let Tac2entries.ScopeRule (scope, act) = Tac2entries.parse_scope tok in
  let act e = rthunk (act e) in
  Tac2entries.ScopeRule (scope, act)
| _ -> scope_fail ()
end

let add_expr_scope name entry f =
  add_scope name begin function
  | [] -> Tac2entries.ScopeRule (Extend.Aentry entry, f)
  | _ -> scope_fail ()
  end

let () = add_expr_scope "ident" q_ident (fun id -> Tac2quote.of_anti Tac2quote.of_ident id)
let () = add_expr_scope "bindings" q_bindings Tac2quote.of_bindings
let () = add_expr_scope "with_bindings" q_with_bindings Tac2quote.of_bindings
let () = add_expr_scope "intropattern" q_intropattern Tac2quote.of_intro_pattern
let () = add_expr_scope "intropatterns" q_intropatterns Tac2quote.of_intro_patterns
let () = add_expr_scope "induction_clause" q_induction_clause Tac2quote.of_induction_clause
let () = add_expr_scope "rewriting" q_rewriting Tac2quote.of_rewriting
let () = add_expr_scope "clause" q_clause Tac2quote.of_clause
let () = add_expr_scope "occurrences" q_occurrences Tac2quote.of_occurrences
let () = add_expr_scope "dispatch" q_dispatch Tac2quote.of_dispatch
let () = add_expr_scope "strategy" q_strategy_flag Tac2quote.of_strategy_flag
let () = add_expr_scope "reference" q_reference Tac2quote.of_reference

let () = add_generic_scope "constr" Pcoq.Constr.constr wit_constr
let () = add_generic_scope "open_constr" Pcoq.Constr.constr wit_open_constr
let () = add_generic_scope "pattern" Pcoq.Constr.constr wit_pattern

(** seq scope, a bit hairy *)

open Extend
exception SelfSymbol

type 'a any_symbol = { any_symbol : 'r. ('r, 'a) symbol }

let rec generalize_symbol :
  type a s. (s, a) Extend.symbol -> a any_symbol = function
| Atoken tok ->
  { any_symbol = Atoken tok }
| Alist1 e ->
  let e = generalize_symbol e in
  { any_symbol = Alist1 e.any_symbol }
| Alist1sep (e, sep) ->
  let e = generalize_symbol e in
  let sep = generalize_symbol sep in
  { any_symbol = Alist1sep (e.any_symbol, sep.any_symbol) }
| Alist0 e ->
  let e = generalize_symbol e in
  { any_symbol = Alist0 e.any_symbol }
| Alist0sep (e, sep) ->
  let e = generalize_symbol e in
  let sep = generalize_symbol sep in
  { any_symbol = Alist0sep (e.any_symbol, sep.any_symbol) }
| Aopt e ->
  let e = generalize_symbol e in
  { any_symbol = Aopt e.any_symbol }
| Aself -> raise SelfSymbol
| Anext -> raise SelfSymbol
| Aentry e -> { any_symbol = Aentry e }
| Aentryl (e, l) -> { any_symbol = Aentryl (e, l) }
| Arules r -> { any_symbol = Arules r }

type _ converter =
| CvNil : (Loc.t -> raw_tacexpr) converter
| CvCns : 'act converter * ('a -> raw_tacexpr) option -> ('a -> 'act) converter

let rec apply : type a. a converter -> raw_tacexpr list -> a = function
| CvNil -> fun accu loc -> Tac2quote.of_tuple ~loc accu
| CvCns (c, None) -> fun accu x -> apply c accu
| CvCns (c, Some f) -> fun accu x -> apply c (f x :: accu)

type seqrule =
| Seqrule : ('act, Loc.t -> raw_tacexpr) norec_rule * 'act converter -> seqrule

let rec make_seq_rule = function
| [] ->
  let r = { norec_rule = Stop } in
  Seqrule (r, CvNil)
| tok :: rem ->
  let Tac2entries.ScopeRule (scope, f) = Tac2entries.parse_scope tok in
  let scope = generalize_symbol scope in
  let Seqrule (r, c) = make_seq_rule rem in
  let r = { norec_rule = Next (r.norec_rule, scope.any_symbol) } in
  let f = match tok with
  | SexprStr _ -> None (** Leave out mere strings *)
  | _ -> Some f
  in
  Seqrule (r, CvCns (c, f))

let () = add_scope "seq" begin fun toks ->
  let scope =
    try
      let Seqrule (r, c) = make_seq_rule (List.rev toks) in
      Arules [Rules (r, apply c [])]
    with SelfSymbol ->
      CErrors.user_err (str "Recursive symbols (self / next) are not allowed in local rules")
  in
  Tac2entries.ScopeRule (scope, (fun e -> e))
end
