(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Util
open Pp
open Names
open Genarg
open Tac2env
open Tac2expr
open Tac2entries.Pltac
open Proofview.Notations

(** Standard values *)

module Value = Tac2ffi
open Value

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

let v_unit = Value.of_unit ()
let v_blk = Valexpr.make_block

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
| Inl c -> v_blk 0 [|f c|]
| Inr e -> v_blk 1 [|Value.of_exn e|]

(** Stdlib exceptions *)

let err_notfocussed =
  Tac2interp.LtacError (coq_core "Not_focussed", [||])

let err_outofbounds =
  Tac2interp.LtacError (coq_core "Out_of_bounds", [||])

let err_notfound =
  Tac2interp.LtacError (coq_core "Not_found", [||])

let err_matchfailure =
  Tac2interp.LtacError (coq_core "Match_failure", [||])

(** Helper functions *)

let thaw f = Tac2ffi.apply f [v_unit]

let fatal_flag : unit Exninfo.t = Exninfo.make ()

let set_bt info =
  if !Tac2interp.print_ltac2_backtrace then
    Tac2interp.get_backtrace >>= fun bt ->
    Proofview.tclUNIT (Exninfo.add info Tac2entries.backtrace bt)
  else Proofview.tclUNIT info

let throw ?(info = Exninfo.null) e =
  set_bt info >>= fun info ->
  let info = Exninfo.add info fatal_flag () in
  Proofview.tclLIFT (Proofview.NonLogical.raise ~info e)

let fail ?(info = Exninfo.null) e =
  set_bt info >>= fun info ->
  Proofview.tclZERO ~info e

let return x = Proofview.tclUNIT x
let pname s = { mltac_plugin = "ltac2"; mltac_tactic = s }

let wrap f =
  return () >>= fun () -> return (f ())

let wrap_unit f =
  return () >>= fun () -> f (); return v_unit

let assert_focussed =
  Proofview.Goal.goals >>= fun gls ->
  match gls with
  | [_] -> Proofview.tclUNIT ()
  | [] | _ :: _ :: _ -> throw err_notfocussed

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

let define_primitive name arity f =
  Tac2env.define_primitive (pname name) (mk_closure arity f)

let define0 name f = define_primitive name arity_one (fun _ -> f)

let define1 name r0 f = define_primitive name arity_one begin fun x ->
  f (Value.repr_to r0 x)
end

let define2 name r0 r1 f = define_primitive name (arity_suc arity_one) begin fun x y ->
  f (Value.repr_to r0 x) (Value.repr_to r1 y)
end

let define3 name r0 r1 r2 f = define_primitive name (arity_suc (arity_suc arity_one)) begin fun x y z ->
  f (Value.repr_to r0 x) (Value.repr_to r1 y) (Value.repr_to r2 z)
end

(** Printing *)

let () = define1 "print" pp begin fun pp ->
  wrap_unit (fun () -> Feedback.msg_notice pp)
end

let () = define1 "message_of_int" int begin fun n ->
  return (Value.of_pp (Pp.int n))
end

let () = define1 "message_of_string" string begin fun s ->
  return (Value.of_pp (str (Bytes.to_string s)))
end

let () = define1 "message_of_constr" constr begin fun c ->
  pf_apply begin fun env sigma ->
    let pp = Printer.pr_econstr_env env sigma c in
    return (Value.of_pp pp)
  end
end

let () = define1 "message_of_ident" ident begin fun c ->
  let pp = Id.print c in
  return (Value.of_pp pp)
end

let () = define1 "message_of_exn" valexpr begin fun v ->
  Proofview.tclENV >>= fun env ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let pp = Tac2print.pr_valexpr env sigma v (GTypRef (Other Core.t_exn, [])) in
  return (Value.of_pp pp)
end


let () = define2 "message_concat" pp pp begin fun m1 m2 ->
  return (Value.of_pp (Pp.app m1 m2))
end

(** Array *)

let () = define2 "array_make" int valexpr begin fun n x ->
  if n < 0 || n > Sys.max_array_length then throw err_outofbounds
  else wrap (fun () -> v_blk 0 (Array.make n x))
end

let () = define1 "array_length" block begin fun (_, v) ->
  return (Value.of_int (Array.length v))
end

let () = define3 "array_set" block int valexpr begin fun (_, v) n x ->
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap_unit (fun () -> v.(n) <- x)
end

let () = define2 "array_get" block int begin fun (_, v) n ->
  if n < 0 || n >= Array.length v then throw err_outofbounds
  else wrap (fun () -> v.(n))
end

(** Ident *)

let () = define2 "ident_equal" ident ident begin fun id1 id2 ->
  return (Value.of_bool (Id.equal id1 id2))
end

let () = define1 "ident_to_string" ident begin fun id ->
  return (Value.of_string (Bytes.of_string (Id.to_string id)))
end

let () = define1 "ident_of_string" string begin fun s ->
  let id = try Some (Id.of_string (Bytes.to_string s)) with _ -> None in
  return (Value.of_option Value.of_ident id)
end

(** Int *)

let () = define2 "int_equal" int int begin fun m n ->
  return (Value.of_bool (m == n))
end

let binop n f = define2 n int int begin fun m n ->
  return (Value.of_int (f m n))
end

let () = binop "int_compare" Int.compare
let () = binop "int_add" (+)
let () = binop "int_sub" (-)
let () = binop "int_mul" ( * )

let () = define1 "int_neg" int begin fun m ->
  return (Value.of_int (~- m))
end

(** String *)

let () = define2 "string_make" int char begin fun n c ->
  if n < 0 || n > Sys.max_string_length then throw err_outofbounds
  else wrap (fun () -> Value.of_string (Bytes.make n c))
end

let () = define1 "string_length" string begin fun s ->
  return (Value.of_int (Bytes.length s))
end

let () = define3 "string_set" string int char begin fun s n c ->
  if n < 0 || n >= Bytes.length s then throw err_outofbounds
  else wrap_unit (fun () -> Bytes.set s n c)
end

let () = define2 "string_get" string int begin fun s n ->
  if n < 0 || n >= Bytes.length s then throw err_outofbounds
  else wrap (fun () -> Value.of_char (Bytes.get s n))
end

(** Terms *)

(** constr -> constr *)
let () = define1 "constr_type" constr begin fun c ->
  let get_type env sigma =
  Proofview.V82.wrap_exceptions begin fun () ->
    let (sigma, t) = Typing.type_of env sigma c in
    let t = Value.of_constr t in
    Proofview.Unsafe.tclEVARS sigma <*> Proofview.tclUNIT t
  end in
  pf_apply get_type
end

(** constr -> constr *)
let () = define2 "constr_equal" constr constr begin fun c1 c2 ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let b = EConstr.eq_constr sigma c1 c2 in
  Proofview.tclUNIT (Value.of_bool b)
end

let () = define1 "constr_kind" constr begin fun c ->
  let open Constr in
  Proofview.tclEVARMAP >>= fun sigma ->
  return begin match EConstr.kind sigma c with
  | Rel n ->
    v_blk 0 [|Value.of_int n|]
  | Var id ->
    v_blk 1 [|Value.of_ident id|]
  | Meta n ->
    v_blk 2 [|Value.of_int n|]
  | Evar (evk, args) ->
    v_blk 3 [|
      Value.of_int (Evar.repr evk);
      Value.of_array Value.of_constr args;
    |]
  | Sort s ->
    v_blk 4 [|Value.of_ext Value.val_sort s|]
  | Cast (c, k, t) ->
    v_blk 5 [|
      Value.of_constr c;
      Value.of_ext Value.val_cast k;
      Value.of_constr t;
    |]
  | Prod (na, t, u) ->
    v_blk 6 [|
      of_name na;
      Value.of_constr t;
      Value.of_constr u;
    |]
  | Lambda (na, t, c) ->
    v_blk 7 [|
      of_name na;
      Value.of_constr t;
      Value.of_constr c;
    |]
  | LetIn (na, b, t, c) ->
    v_blk 8 [|
      of_name na;
      Value.of_constr b;
      Value.of_constr t;
      Value.of_constr c;
    |]
  | App (c, cl) ->
    v_blk 9 [|
      Value.of_constr c;
      Value.of_array Value.of_constr cl;
    |]
  | Const (cst, u) ->
    v_blk 10 [|
      Value.of_constant cst;
      of_instance u;
    |]
  | Ind (ind, u) ->
    v_blk 11 [|
      Value.of_ext Value.val_inductive ind;
      of_instance u;
    |]
  | Construct (cstr, u) ->
    v_blk 12 [|
      Value.of_ext Value.val_constructor cstr;
      of_instance u;
    |]
  | Case (ci, c, t, bl) ->
    v_blk 13 [|
      Value.of_ext Value.val_case ci;
      Value.of_constr c;
      Value.of_constr t;
      Value.of_array Value.of_constr bl;
    |]
  | Fix ((recs, i), def) ->
    let (nas, ts, cs) = of_rec_declaration def in
    v_blk 14 [|
      Value.of_array Value.of_int recs;
      Value.of_int i;
      nas;
      ts;
      cs;
    |]
  | CoFix (i, def) ->
    let (nas, ts, cs) = of_rec_declaration def in
    v_blk 15 [|
      Value.of_int i;
      nas;
      ts;
      cs;
    |]
  | Proj (p, c) ->
    v_blk 16 [|
      Value.of_ext Value.val_projection p;
      Value.of_constr c;
    |]
  end
end

let () = define1 "constr_make" valexpr begin fun knd ->
  let c = match Tac2ffi.to_block knd with
  | (0, [|n|]) ->
    let n = Value.to_int n in
    EConstr.mkRel n
  | (1, [|id|]) ->
    let id = Value.to_ident id in
    EConstr.mkVar id
  | (2, [|n|]) ->
    let n = Value.to_int n in
    EConstr.mkMeta n
  | (3, [|evk; args|]) ->
    let evk = Evar.unsafe_of_int (Value.to_int evk) in
    let args = Value.to_array Value.to_constr args in
    EConstr.mkEvar (evk, args)
  | (4, [|s|]) ->
    let s = Value.to_ext Value.val_sort s in
    EConstr.mkSort (EConstr.Unsafe.to_sorts s)
  | (5, [|c; k; t|]) ->
    let c = Value.to_constr c in
    let k = Value.to_ext Value.val_cast k in
    let t = Value.to_constr t in
    EConstr.mkCast (c, k, t)
  | (6, [|na; t; u|]) ->
    let na = to_name na in
    let t = Value.to_constr t in
    let u = Value.to_constr u in
    EConstr.mkProd (na, t, u)
  | (7, [|na; t; c|]) ->
    let na = to_name na in
    let t = Value.to_constr t in
    let u = Value.to_constr c in
    EConstr.mkLambda (na, t, u)
  | (8, [|na; b; t; c|]) ->
    let na = to_name na in
    let b = Value.to_constr b in
    let t = Value.to_constr t in
    let c = Value.to_constr c in
    EConstr.mkLetIn (na, b, t, c)
  | (9, [|c; cl|]) ->
    let c = Value.to_constr c in
    let cl = Value.to_array Value.to_constr cl in
    EConstr.mkApp (c, cl)
  | (10, [|cst; u|]) ->
    let cst = Value.to_constant cst in
    let u = to_instance u in
    EConstr.mkConstU (cst, u)
  | (11, [|ind; u|]) ->
    let ind = Value.to_ext Value.val_inductive ind in
    let u = to_instance u in
    EConstr.mkIndU (ind, u)
  | (12, [|cstr; u|]) ->
    let cstr = Value.to_ext Value.val_constructor cstr in
    let u = to_instance u in
    EConstr.mkConstructU (cstr, u)
  | (13, [|ci; c; t; bl|]) ->
    let ci = Value.to_ext Value.val_case ci in
    let c = Value.to_constr c in
    let t = Value.to_constr t in
    let bl = Value.to_array Value.to_constr bl in
    EConstr.mkCase (ci, c, t, bl)
  | (14, [|recs; i; nas; ts; cs|]) ->
    let recs = Value.to_array Value.to_int recs in
    let i = Value.to_int i in
    let def = to_rec_declaration (nas, ts, cs) in
    EConstr.mkFix ((recs, i), def)
  | (15, [|i; nas; ts; cs|]) ->
    let i = Value.to_int i in
    let def = to_rec_declaration (nas, ts, cs) in
    EConstr.mkCoFix (i, def)
  | (16, [|p; c|]) ->
    let p = Value.to_ext Value.val_projection p in
    let c = Value.to_constr c in
    EConstr.mkProj (p, c)
  | _ -> assert false
  in
  return (Value.of_constr c)
end

let () = define1 "constr_check" constr begin fun c ->
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

let () = define3 "constr_substnl" (list constr) int constr begin fun subst k c ->
  let ans = EConstr.Vars.substnl subst k c in
  return (Value.of_constr ans)
end

let () = define3 "constr_closenl" (list ident) int constr begin fun ids k c ->
  let ans = EConstr.Vars.substn_vars k ids c in
  return (Value.of_constr ans)
end

let () = define3 "constr_in_context" ident constr closure begin fun id t c ->
  Proofview.Goal.goals >>= function
  | [gl] ->
    gl >>= fun gl ->
    let env = Proofview.Goal.env gl in
    let sigma = Proofview.Goal.sigma gl in
    let has_var =
      try
        let _ = Environ.lookup_named_val id (Environ.named_context_val env) in
        true
      with Not_found -> false
    in
    if has_var then
      Tacticals.New.tclZEROMSG (str "Variable already exists")
    else
      let open Context.Named.Declaration in
      let nenv = EConstr.push_named (LocalAssum (id, t)) env in
      let (sigma, (evt, _)) = Evarutil.new_type_evar nenv sigma Evd.univ_flexible in
      let (sigma, evk) = Evarutil.new_pure_evar (Environ.named_context_val nenv) sigma evt in
      Proofview.Unsafe.tclEVARS sigma >>= fun () ->
      Proofview.Unsafe.tclSETGOALS [evk] >>= fun () ->
      thaw c >>= fun _ ->
      Proofview.Unsafe.tclSETGOALS [Proofview.Goal.goal (Proofview.Goal.assume gl)] >>= fun () ->
      let args = List.map (fun d -> EConstr.mkVar (get_id d)) (EConstr.named_context env) in
      let args = Array.of_list (EConstr.mkRel 1 :: args) in
      let ans = EConstr.mkEvar (evk, args) in
      let ans = EConstr.mkLambda (Name id, t, ans) in
      return (Value.of_constr ans)
  | _ ->
    throw err_notfocussed
end

(** Patterns *)

let empty_context = EConstr.mkMeta Constr_matching.special_meta

let () = define0 "pattern_empty_context" begin
  return (Value.of_constr empty_context)
end

let () = define2 "pattern_matches" pattern constr begin fun pat c ->
  pf_apply begin fun env sigma ->
    let ans =
      try Some (Constr_matching.matches env sigma pat c)
      with Constr_matching.PatternMatchingFailure -> None
    in
    begin match ans with
    | None -> fail err_matchfailure
    | Some ans ->
      let ans = Id.Map.bindings ans in
      let of_pair (id, c) = Value.of_tuple [| Value.of_ident id; Value.of_constr c |] in
      return (Value.of_list of_pair ans)
    end
  end
end

let () = define2 "pattern_matches_subterm" pattern constr begin fun pat c ->
  let open Constr_matching in
  let rec of_ans s = match IStream.peek s with
  | IStream.Nil -> fail err_matchfailure
  | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
    let ans = Id.Map.bindings sub in
    let of_pair (id, c) = Value.of_tuple [| Value.of_ident id; Value.of_constr c |] in
    let ans = Value.of_tuple [| Value.of_constr m_ctx; Value.of_list of_pair ans |] in
    Proofview.tclOR (return ans) (fun _ -> of_ans s)
  in
  pf_apply begin fun env sigma ->
    let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
    of_ans ans
  end
end

let () = define2 "pattern_matches_vect" pattern constr begin fun pat c ->
  pf_apply begin fun env sigma ->
    let ans =
      try Some (Constr_matching.matches env sigma pat c)
      with Constr_matching.PatternMatchingFailure -> None
    in
    begin match ans with
    | None -> fail err_matchfailure
    | Some ans ->
      let ans = Id.Map.bindings ans in
      let ans = Array.map_of_list snd ans in
      return (Value.of_array Value.of_constr ans)
    end
  end
end

let () = define2 "pattern_matches_subterm_vect" pattern constr begin fun pat c ->
  let open Constr_matching in
  let rec of_ans s = match IStream.peek s with
  | IStream.Nil -> fail err_matchfailure
  | IStream.Cons ({ m_sub = (_, sub); m_ctx }, s) ->
    let ans = Id.Map.bindings sub in
    let ans = Array.map_of_list snd ans in
    let ans = Value.of_tuple [| Value.of_constr m_ctx; Value.of_array Value.of_constr ans |] in
    Proofview.tclOR (return ans) (fun _ -> of_ans s)
  in
  pf_apply begin fun env sigma ->
    let ans = Constr_matching.match_subterm env sigma (Id.Set.empty,pat) c in
    of_ans ans
  end
end

let () = define3 "pattern_matches_goal" bool (list (pair bool pattern)) (pair bool pattern) begin fun rev hp cp ->
  assert_focussed >>= fun () ->
  Proofview.Goal.enter_one begin fun gl ->
  let env = Proofview.Goal.env gl in
  let sigma = Proofview.Goal.sigma gl in
  let concl = Proofview.Goal.concl gl in
  let mk_pattern (b, pat) = if b then Tac2match.MatchPattern pat else Tac2match.MatchContext pat in
  let r = (List.map mk_pattern hp, mk_pattern cp) in
  Tac2match.match_goal env sigma concl ~rev r >>= fun (hyps, ctx, subst) ->
    let of_ctxopt ctx = Value.of_constr (Option.default empty_context ctx) in
    let hids = Value.of_array Value.of_ident (Array.map_of_list fst hyps) in
    let hctx = Value.of_array of_ctxopt (Array.map_of_list snd hyps) in
    let subs = Value.of_array Value.of_constr (Array.map_of_list snd (Id.Map.bindings subst)) in
    let cctx = of_ctxopt ctx in
    let ans = Value.of_tuple [| hids; hctx; subs; cctx |] in
    Proofview.tclUNIT ans
  end
end

let () = define2 "pattern_instantiate" constr constr begin fun ctx c ->
  let ctx = EConstr.Unsafe.to_constr ctx in
  let c = EConstr.Unsafe.to_constr c in
  let ans = Termops.subst_meta [Constr_matching.special_meta, c] ctx in
  return (Value.of_constr (EConstr.of_constr ans))
end

(** Error *)

let () = define1 "throw" exn begin fun (e, info) ->
  throw ~info e
end

(** Control *)

(** exn -> 'a *)
let () = define1 "zero" exn begin fun (e, info) ->
  fail ~info e
end

(** (unit -> 'a) -> (exn -> 'a) -> 'a *)
let () = define2 "plus" closure closure begin fun x k ->
  Proofview.tclOR (thaw x) (fun e -> Tac2ffi.apply k [Value.of_exn e])
end

(** (unit -> 'a) -> 'a *)
let () = define1 "once" closure begin fun f ->
  Proofview.tclONCE (thaw f)
end

(** (unit -> unit) list -> unit *)
let () = define1 "dispatch" (list closure) begin fun l ->
  let l = List.map (fun f -> Proofview.tclIGNORE (thaw f)) l in
  Proofview.tclDISPATCH l >>= fun () -> return v_unit
end

(** (unit -> unit) list -> (unit -> unit) -> (unit -> unit) list -> unit *)
let () = define3 "extend" (list closure) closure (list closure) begin fun lft tac rgt ->
  let lft = List.map (fun f -> Proofview.tclIGNORE (thaw f)) lft in
  let tac = Proofview.tclIGNORE (thaw tac) in
  let rgt = List.map (fun f -> Proofview.tclIGNORE (thaw f)) rgt in
  Proofview.tclEXTEND lft tac rgt >>= fun () -> return v_unit
end

(** (unit -> unit) -> unit *)
let () = define1 "enter" closure begin fun f ->
  let f = Proofview.tclIGNORE (thaw f) in
  Proofview.tclINDEPENDENT f >>= fun () -> return v_unit
end

(** (unit -> 'a) -> ('a * ('exn -> 'a)) result *)
let () = define1 "case" closure begin fun f ->
  Proofview.tclCASE (thaw f) >>= begin function
  | Proofview.Next (x, k) ->
    let k = Tac2ffi.mk_closure arity_one begin fun e ->
      let (e, info) = Value.to_exn e in
      set_bt info >>= fun info ->
      k (e, info)
    end in
    return (v_blk 0 [| Value.of_tuple [| x; Value.of_closure k |] |])
  | Proofview.Fail e -> return (v_blk 1 [| Value.of_exn e |])
  end
end

(** int -> int -> (unit -> 'a) -> 'a *)
let () = define3 "focus" int int closure begin fun i j tac ->
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

let () = define1 "new_goal" int begin fun ev ->
  let ev = Evar.unsafe_of_int ev in
  Proofview.tclEVARMAP >>= fun sigma ->
  if Evd.mem sigma ev then
    Proofview.Unsafe.tclNEWGOALS [ev] <*> Proofview.tclUNIT v_unit
  else throw err_notfound
end

(** unit -> constr *)
let () = define0 "goal" begin
  assert_focussed >>= fun () ->
  Proofview.Goal.enter_one begin fun gl ->
    let concl = Tacmach.New.pf_nf_concl gl in
    return (Value.of_constr concl)
  end
end

(** ident -> constr *)
let () = define1 "hyp" ident begin fun id ->
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
let () = define1 "refine" closure begin fun c ->
  let c = thaw c >>= fun c -> Proofview.tclUNIT ((), Value.to_constr c) in
  Proofview.Goal.enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
    Refine.generic_refine ~typecheck:true c gl
  end >>= fun () -> return v_unit
end

let () = define2 "with_holes" closure closure begin fun x f ->
  Proofview.tclEVARMAP >>= fun sigma0 ->
  thaw x >>= fun ans ->
  Proofview.tclEVARMAP >>= fun sigma ->
  Proofview.Unsafe.tclEVARS sigma0 >>= fun () ->
  Tacticals.New.tclWITHHOLES false (Tac2ffi.apply f [ans]) sigma
end

let () = define1 "progress" closure begin fun f ->
  Proofview.tclPROGRESS (thaw f)
end

let () = define2 "abstract" (option ident) closure begin fun id f ->
  Tactics.tclABSTRACT id (Proofview.tclIGNORE (thaw f)) >>= fun () ->
  return v_unit
end

let () = define2 "time" (option string) closure begin fun s f ->
  let s = Option.map Bytes.to_string s in
  Proofview.tclTIME s (thaw f)
end

let () = define0 "check_interrupt" begin
  Proofview.tclCHECKINTERRUPT >>= fun () -> return v_unit
end

(** Fresh *)

let () = define2 "fresh_free_union" (repr_ext val_free) (repr_ext val_free) begin fun set1 set2 ->
  let ans = Id.Set.union set1 set2 in
  return (Value.of_ext Value.val_free ans)
end

let () = define1 "fresh_free_of_ids" (list ident) begin fun ids ->
  let free = List.fold_right Id.Set.add ids Id.Set.empty in
  return (Value.of_ext Value.val_free free)
end

let () = define1 "fresh_free_of_constr" constr begin fun c ->
  Proofview.tclEVARMAP >>= fun sigma ->
  let rec fold accu c = match EConstr.kind sigma c with
  | Constr.Var id -> Id.Set.add id accu
  | _ -> EConstr.fold sigma fold accu c
  in
  let ans = fold Id.Set.empty c in
  return (Value.of_ext Value.val_free ans)
end

let () = define2 "fresh_fresh" (repr_ext val_free) ident begin fun avoid id ->
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
  { empty_lvar with Ltac_pretype.ltac_genargs = lfun }

let gtypref kn = GTypRef (Other kn, [])

let intern_constr self ist c =
  let (_, (c, _)) = Genintern.intern Stdarg.wit_constr ist c in
  (GlbVal c, gtypref t_constr)

let catchable_exception = function
  | Logic_monad.Exception _ -> false
  | e -> CErrors.noncritical e

let interp_constr flags ist c =
  let open Pretyping in
  let ist = to_lvar ist in
  pf_apply begin fun env sigma ->
  try
    let (sigma, c) = understand_ltac flags env sigma ist WithoutTypeConstraint c in
    let c = Value.of_constr c in
    Proofview.Unsafe.tclEVARS sigma >>= fun () ->
    Proofview.tclUNIT c
  with e when catchable_exception e ->
    let (e, info) = CErrors.push e in
    set_bt info >>= fun info ->
    match Exninfo.get info fatal_flag with
    | None -> Proofview.tclZERO ~info e
    | Some () -> throw ~info e
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
  define_ml_object Tac2quote.wit_constr obj

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
  define_ml_object Tac2quote.wit_open_constr obj

let () =
  let interp _ id = return (Value.of_ident id) in
  let print _ id = str "ident:(" ++ Id.print id ++ str ")" in
  let obj = {
    ml_intern = (fun _ _ id -> GlbVal id, gtypref t_ident);
    ml_interp = interp;
    ml_subst = (fun _ id -> id);
    ml_print = print;
  } in
  define_ml_object Tac2quote.wit_ident obj

let () =
  let intern self ist c =
    let _, pat = Constrintern.intern_constr_pattern ist.Genintern.genv ~as_type:false c in
    GlbVal pat, gtypref t_pattern
  in
  let print env pat = str "pattern:(" ++ Printer.pr_lconstr_pattern_env env Evd.empty pat ++ str ")" in
  let interp _ c = return (Value.of_pattern c) in
  let obj = {
    ml_intern = intern;
    ml_interp = interp;
    ml_subst = Patternops.subst_pattern;
    ml_print = print;
  } in
  define_ml_object Tac2quote.wit_pattern obj

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
  define_ml_object Tac2quote.wit_reference obj

let () =
  let intern self ist tac =
    (** Prevent inner calls to Ltac2 values *)
    let extra = Tac2intern.drop_ltac2_env ist.Genintern.extra in
    let ist = { ist with Genintern.extra } in
    let _, tac = Genintern.intern Ltac_plugin.Tacarg.wit_tactic ist tac in
    GlbVal tac, gtypref t_unit
  in
  let interp ist tac =
    let ist = { env_ist = Id.Map.empty } in
    let lfun = Tac2interp.set_env ist Id.Map.empty in
    let ist = Ltac_plugin.Tacinterp.default_ist () in
    let ist = { ist with Geninterp.lfun = lfun } in
    let tac = (Obj.magic Ltac_plugin.Tacinterp.eval_tactic_ist ist tac : unit Proofview.tactic) in
    let wrap (e, info) = set_bt info >>= fun info -> Proofview.tclZERO ~info e in
    Proofview.tclOR tac wrap >>= fun () ->
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
  define_ml_object Tac2quote.wit_ltac1 obj

(** Ltac2 in terms *)

let () =
  let interp ist env sigma concl tac =
    let ist = Tac2interp.get_env ist in
    let tac = Proofview.tclIGNORE (Tac2interp.interp ist tac) in
    let c, sigma = Pfedit.refine_by_tactic env sigma concl tac in
    (EConstr.of_constr c, sigma)
  in
  Pretyping.register_constr_interp0 wit_ltac2 interp

let () =
  let interp ist env sigma concl id =
    let ist = Tac2interp.get_env ist in
    let c = Id.Map.find id ist.env_ist in
    let c = Value.to_constr c in
    let evdref = ref sigma in
    let () = Typing.e_check env evdref c concl in
    (c, !evdref)
  in
  Pretyping.register_constr_interp0 wit_ltac2_quotation interp

let () =
  let pr_raw id = Genprint.PrinterBasic mt in
  let pr_glb id = Genprint.PrinterBasic (fun () -> str "$" ++ Id.print id) in
  let pr_top _ = Genprint.TopPrinterBasic mt in
  Genprint.register_print0 wit_ltac2_quotation pr_raw pr_glb pr_top

(** Ltac2 in Ltac1 *)

let () =
  let e = Tac2entries.Pltac.tac2expr in
  let inject (loc, v) = Tacexpr.TacGeneric (in_gen (rawwit wit_ltac2) v) in
  Ltac_plugin.Tacentries.create_ltac_quotation "ltac2" inject (e, None)

let () =
  let open Ltac_plugin in
  let open Tacinterp in
  let idtac = Value.of_closure (default_ist ()) (Tacexpr.TacId []) in
  let interp ist tac =
(*     let ist = Tac2interp.get_env ist.Geninterp.lfun in *)
    let ist = { env_ist = Id.Map.empty } in
    Tac2interp.interp ist tac >>= fun _ ->
    Ftactic.return idtac
  in
  Geninterp.register_interp0 wit_ltac2 interp

let () =
  let pr_raw _ = Genprint.PrinterBasic mt in
  let pr_glb e = Genprint.PrinterBasic (fun () -> Tac2print.pr_glbexpr e) in
  let pr_top _ = Genprint.TopPrinterBasic mt in
  Genprint.register_print0 wit_ltac2 pr_raw pr_glb pr_top

(** Built-in notation scopes *)

let add_scope s f =
  Tac2entries.register_scope (Id.of_string s) f

let rec pr_scope = function
| SexprStr (_, s) -> qstring s
| SexprInt (_, n) -> Pp.int n
| SexprRec (_, (_, na), args) ->
  let na = match na with
  | None -> str "_"
  | Some id -> Id.print id
  in
  na ++ str "(" ++ prlist_with_sep (fun () -> str ", ") pr_scope args ++ str ")"

let scope_fail s args =
  let args = str "(" ++ prlist_with_sep (fun () -> str ", ") pr_scope args ++ str ")" in
  CErrors.user_err (str "Invalid arguments " ++ args ++ str " in scope " ++ str s)

let q_unit = Loc.tag @@ CTacCst (AbsKn (Tuple 0))

let add_generic_scope s entry arg =
  let parse = function
  | [] ->
    let scope = Extend.Aentry entry in
    let act x = Loc.tag @@ CTacExt (arg, x) in
    Tac2entries.ScopeRule (scope, act)
  | arg -> scope_fail s arg
  in
  add_scope s parse

let () = add_scope "keyword" begin function
| [SexprStr (loc, s)] ->
  let scope = Extend.Atoken (Tok.KEYWORD s) in
  Tac2entries.ScopeRule (scope, (fun _ -> q_unit))
| arg -> scope_fail "keyword" arg
end

let () = add_scope "terminal" begin function
| [SexprStr (loc, s)] ->
  let scope = Extend.Atoken (CLexer.terminal s) in
  Tac2entries.ScopeRule (scope, (fun _ -> q_unit))
| arg -> scope_fail "terminal" arg
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
| arg -> scope_fail "list0" arg
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
| arg -> scope_fail "list1" arg
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
| arg -> scope_fail "opt" arg
end

let () = add_scope "self" begin function
| [] ->
  let scope = Extend.Aself in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "self" arg
end

let () = add_scope "next" begin function
| [] ->
  let scope = Extend.Anext in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| arg -> scope_fail "next" arg
end

let () = add_scope "tactic" begin function
| [] ->
  (** Default to level 5 parsing *)
  let scope = Extend.Aentryl (tac2expr, 5) in
  let act tac = tac in
  Tac2entries.ScopeRule (scope, act)
| [SexprInt (loc, n)] as arg ->
  let () = if n < 0 || n > 6 then scope_fail "tactic" arg in
  let scope = Extend.Aentryl (tac2expr, n) in
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

let add_expr_scope name entry f =
  add_scope name begin function
  | [] -> Tac2entries.ScopeRule (Extend.Aentry entry, f)
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

let () = add_generic_scope "constr" Pcoq.Constr.constr Tac2quote.wit_constr
let () = add_generic_scope "open_constr" Pcoq.Constr.constr Tac2quote.wit_open_constr
let () = add_generic_scope "pattern" Pcoq.Constr.constr Tac2quote.wit_pattern

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
