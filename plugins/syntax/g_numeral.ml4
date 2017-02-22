(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

DECLARE PLUGIN "numeral_notation_plugin"

open Pp
open CErrors
open Util
open Names
open Libnames
open Globnames
open Constrexpr
open Constrexpr_ops
open Constr
open Misctypes

(* Numeral notation *)

let obj_string x =
  if Obj.is_block (Obj.repr x) then
    "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
  else "int_val = " ^ string_of_int (Obj.magic x)

let eval_constr (c : Constr.t) =
  let env = Global.env () in
  let j = Arguments_renaming.rename_typing env c in
  let c'=
    Vnorm.cbv_vm env (Evd.from_env env)
                 (EConstr.of_constr j.Environ.uj_val)
                 (EConstr.of_constr j.Environ.uj_type)
  in EConstr.Unsafe.to_constr c'

let rec pos_of_bigint posty n =
  match Bigint.div2_with_rest n with
  | (q, false) ->
      let c = mkConstruct (posty, 2) in (* xO *)
      mkApp (c, [| pos_of_bigint posty q |])
  | (q, true) when not (Bigint.equal q Bigint.zero) ->
      let c = mkConstruct (posty, 1) in (* xI *)
      mkApp (c, [| pos_of_bigint posty q |])
  | (q, true) ->
      mkConstruct (posty, 3) (* xH *)

let rec bigint_of_pos c = match Constr.kind c with
  | App (c, [| d |]) ->
      begin match Constr.kind c with
      | Construct ((_, n), _) ->
          begin match n with
          | 1 -> (* xI *) Bigint.add_1 (Bigint.mult_2 (bigint_of_pos d))
          | 2 -> (* xO *) Bigint.mult_2 (bigint_of_pos d)
          | n -> assert false
          end
      | x -> raise Not_found
      end
  | Construct ((_, 3), _) -> (* xH *) Bigint.one
  | x -> anomaly (str "bigint_of_pos" ++ str (obj_string x))

let z_of_bigint (zty, posty) ty thr n =
  if Bigint.is_pos_or_zero n && not (Bigint.equal thr Bigint.zero) &&
     Bigint.less_than thr n
  then
    Feedback.msg_warning
      (strbrk "Stack overflow or segmentation fault happens when " ++
       strbrk "working with large numbers in " ++
       str (string_of_reference ty) ++
       strbrk " (threshold may vary depending" ++
       strbrk " on your system limits and on the command executed).")
  else ();
  if not (Bigint.equal n Bigint.zero) then
    let (s, n) =
      if Bigint.is_pos_or_zero n then (2, n) (* Zpos *)
      else (3, Bigint.neg n) (* Zneg *)
    in
    let c = mkConstruct (zty, s) in
    mkApp (c, [| pos_of_bigint posty n |])
  else
    mkConstruct (zty, 1) (* Z0 *)

let bigint_of_z z = match Constr.kind z with
  | App (c, [| d |]) ->
      begin match Constr.kind c with
      | Construct ((_, n), _) ->
          begin match n with
          | 2 -> (* Zpos *) bigint_of_pos d
          | 3 -> (* Zneg *) Bigint.neg (bigint_of_pos d)
          | n -> assert false
          end
      | Const (c, _) -> anomaly (str "Const " ++ str (Constant.to_string c))
      | x -> anomaly (str "bigint_of_z App c " ++ str (obj_string x))
      end
  | Construct ((_, 1), _) -> (* Z0 *) Bigint.zero
  | _ -> raise Not_found

let constr_of_global_reference = function
  | VarRef v -> mkVar v
  | ConstRef cr -> mkConst cr
  | IndRef ind -> mkInd ind
  | ConstructRef c -> mkConstruct c

let rec constr_of_glob_constr vl gc =
  match DAst.get gc with
  | Glob_term.GRef (gr, gllo) ->
      constr_of_global_reference gr
  | Glob_term.GVar (id) ->
      constr_of_glob_constr vl (List.assoc id vl)
  | Glob_term.GApp (gc, gcl) ->
      let c = constr_of_glob_constr vl gc in
      let cl = List.map (constr_of_glob_constr vl) gcl in
      mkApp (c, Array.of_list cl)
  | _ ->
      raise Not_found

let rec glob_constr_of_constr ?loc c = match Constr.kind c with
  | Var id ->
      DAst.make ?loc (Glob_term.GRef (VarRef id, None))
  | App (c, ca) ->
      let c = glob_constr_of_constr ?loc c in
      let cel = List.map (glob_constr_of_constr ?loc) (Array.to_list ca) in
      DAst.make ?loc (Glob_term.GApp (c, cel))
  | Construct (c, _) ->
      DAst.make ?loc (Glob_term.GRef (ConstructRef c, None))
  | Const (c, _) ->
      DAst.make ?loc (Glob_term.GRef (ConstRef c, None))
  | Ind (ind, _) ->
      DAst.make ?loc (Glob_term.GRef (IndRef ind, None))
  | x ->
      anomaly (str "1 constr " ++ str (obj_string x))

let interp_big_int zposty ty thr f ?loc bi =
  let t =
    let c = mkApp (mkConst f, [| z_of_bigint zposty ty thr bi |]) in
    eval_constr c
  in
  match Constr.kind t with
  | App (_, [| _; c |]) -> glob_constr_of_constr ?loc c
  | App (_, [| _ |]) ->
      CErrors.user_err ?loc
         (str "Cannot interpret this number as a value of type " ++
          str (string_of_reference ty))
  | x ->
      anomaly (str "interp_big_int " ++ str (obj_string x))

let uninterp_big_int g (Glob_term.AnyGlobConstr c) =
  match try Some (constr_of_glob_constr [] c) with Not_found -> None with
  | Some c ->
      begin match
        try Some (eval_constr (mkApp (mkConst g, [| c |])))
        with Type_errors.TypeError _ -> None
      with
      | Some t ->
          begin match Constr.kind t with
          | App (c, [| _; x |]) -> Some (bigint_of_z x)
          | x -> None
          end
      | None ->
         None
      end
  | None ->
      None

let load_numeral_notation _ (_, (zposty, ty, f, g, sc, patl, thr, path)) =
  Notation.declare_numeral_interpreter sc (path, [])
        (interp_big_int zposty ty thr f)
        (patl, uninterp_big_int g, true)

let cache_numeral_notation o = load_numeral_notation 1 o

type numeral_notation_obj =
  (Names.inductive * Names.inductive) *
  Libnames.reference * Names.Constant.t *
  Names.Constant.t *
  Notation_term.scope_name * Glob_term.glob_constr list *
  Bigint.bigint * Libnames.full_path

let inNumeralNotation : numeral_notation_obj -> Libobject.obj =
  Libobject.declare_object {
    (Libobject.default_object "NUMERAL NOTATION") with
    Libobject.cache_function = cache_numeral_notation;
    Libobject.load_function = load_numeral_notation }

let vernac_numeral_notation ty f g sc waft =
  let zposty =
    let zty =
      let c = qualid_of_ident (Id.of_string "Z") in
      try match Nametab.locate c with IndRef i -> i | _ -> raise Not_found
      with Not_found -> Nametab.error_global_not_found (CAst.make c)
    in
    let positivety =
      let c = qualid_of_ident (Id.of_string "positive") in
      try match Nametab.locate c with IndRef i -> i | _ -> raise Not_found
      with Not_found -> Nametab.error_global_not_found (CAst.make c)
    in
    (zty, positivety)
  in
  let tyc =
    let tyq = qualid_of_reference ty in
    try Nametab.locate CAst.(tyq.v) with Not_found ->
      Nametab.error_global_not_found tyq
  in
  let fc =
    let fq = qualid_of_reference f in
    try Nametab.locate_constant CAst.(fq.v) with Not_found ->
      Nametab.error_global_not_found fq
  in
  let lqid = CAst.((qualid_of_reference ty).v) in
  let crq = mkRefC (CAst.make (Qualid lqid)) in
  let app x y = CAst.make (CApp ((None, x), [(y, None)])) in
  let cref s = mkIdentC (Names.Id.of_string s) in
  let arrow x y =
    mkProdC ([CAst.make Anonymous], Default Decl_kinds.Explicit, x, y)
  in
  let _ =
    (* checking "f" is of type "Z -> option ty" *)
    let c =
      mkCastC
        (mkRefC f,
         CastConv (arrow (cref "Z") (app (cref "option") crq)))
    in
    let (sigma, env) = Pfedit.get_current_context () in
    Constrintern.intern_constr env sigma c
  in
  let thr = Bigint.of_int waft in
  let path = Nametab.path_of_global tyc in
  match tyc with
  | IndRef (sp, spi) ->
      let gc =
        let gq = qualid_of_reference g in
        try Nametab.locate_constant CAst.(gq.v) with Not_found ->
          Nametab.error_global_not_found gq
      in
      let _ =
        (* checking "g" is of type "ty -> option Z" *)
        let c =
          mkCastC
            (mkRefC g,
             CastConv (arrow crq (app (cref "option") (cref "Z"))))
        in
        let (sigma, env) = Pfedit.get_current_context () in
        Constrintern.interp_open_constr env sigma c
      in
      let env = Global.env () in
      let patl =
        let mc =
          let mib = Environ.lookup_mind sp env in
          let inds =
            List.init (Array.length mib.Declarations.mind_packets)
                      (fun x -> (sp, x))
          in
          let ind = List.hd inds in
          let mip = mib.Declarations.mind_packets.(snd ind) in
          mip.Declarations.mind_consnames
        in
        Array.to_list
          (Array.mapi
             (fun i c ->
               DAst.make
                 (Glob_term.GRef
                    (ConstructRef ((sp, spi), i + 1), None)))
             mc)
      in
      Lib.add_anonymous_leaf
        (inNumeralNotation
           (zposty, ty, fc, gc, sc, patl, thr, path))
  | ConstRef _ | ConstructRef _ | VarRef _ ->
      CErrors.user_err
        (str (string_of_reference ty) ++ str " is not an inductive type")

open Stdarg

VERNAC COMMAND EXTEND NumeralNotation CLASSIFIED AS SIDEFF
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) ] ->
    [ let waft = 0 in
      vernac_numeral_notation ty f g (Id.to_string sc) waft ]
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) "(" "warning" "after" int(waft) ")" ] ->
    [ vernac_numeral_notation ty f g (Id.to_string sc) waft ]
END
