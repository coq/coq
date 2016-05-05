(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

open Constrintern
open Pp
open Errors
open Util
open Names
open Libnames
open Globnames
open Constrexpr
open Term
open Misctypes

(* Numeral notation *)

let obj_string x =
  if Obj.is_block (Obj.repr x) then
    "tag = " ^ string_of_int (Obj.tag (Obj.repr x))
  else "int_val = " ^ string_of_int (Obj.magic x)

let eval_constr (c : constr) =
  let env = Global.env () in
  let j = Arguments_renaming.rename_typing env c in
  Vnorm.cbv_vm env j.Environ.uj_val j.Environ.uj_type

let eval_tacexpr ist env (te : Tacexpr.glob_tactic_expr) =
  let vft = Tacinterp.interp_ftactic ist te in
  let (_, pf) = Proofview.init Evd.empty [(env, mkProp)] in
  match
    try Some (Ftactic.apply env vft pf)
    with Logic_monad.TacticFailure _ -> None
  with
  | Some ([v], _, _, _) -> Some v
  | Some _ | None -> None

let rec pos'_of_bigint pos'ty n =
  match Bigint.div2_with_rest n with
  | (q, false) ->
      let c = mkConstruct (pos'ty, 2) in (* x'O *)
      mkApp (c, [| pos'_of_bigint pos'ty q |])
  | (q, true) when not (Bigint.equal q Bigint.zero) ->
      let c = mkConstruct (pos'ty, 1) in (* x'I *)
      mkApp (c, [| pos'_of_bigint pos'ty q |])
  | (q, true) ->
      mkConstruct (pos'ty, 3) (* xH' *)

let rec bigint_of_pos' c = match Constr.kind c with
  | App (c, [| d |]) ->
      begin match Constr.kind c with
      | Construct ((_, n), _) ->
          begin match n with
          | 1 -> (* x'I *) Bigint.add_1 (Bigint.mult_2 (bigint_of_pos' d))
          | 2 -> (* x'O *) Bigint.mult_2 (bigint_of_pos' d)
          | n -> assert false
          end
      | x -> raise Not_found
      end
  | Construct ((_, 3), _) -> (* x'H *) Bigint.one
  | x -> anomaly (str "bigint_of_pos'" ++ str (obj_string x))

let z'_of_bigint (z'ty, pos'ty) ty thr n =
  if Bigint.is_pos_or_zero n && not (Bigint.equal thr Bigint.zero) &&
     Bigint.less_than thr n
  then
    msg_warning
      (strbrk "Stack overflow or segmentation fault happens when " ++
       strbrk "working with large numbers in " ++
       str (string_of_reference ty) ++
       strbrk " (threshold may vary depending" ++
       strbrk " on your system limits and on the command executed).")
  else ();
  if not (Bigint.equal n Bigint.zero) then
    let (s, n) =
      if Bigint.is_pos_or_zero n then (2, n) (* Z'pos *)
      else (3, Bigint.neg n) (* Z'neg *)
    in
    let c = mkConstruct (z'ty, s) in
    mkApp (c, [| pos'_of_bigint pos'ty n |])
  else
    mkConstruct (z'ty, 1) (* Z'0 *)

let bigint_of_z' z' = match Constr.kind z' with
  | App (c, [| d |]) ->
      begin match Constr.kind c with
      | Construct ((_, n), _) ->
          begin match n with
          | 2 -> (* Z'pos *) bigint_of_pos' d
          | 3 -> (* Z'neg *) Bigint.neg (bigint_of_pos' d)
          | n -> assert false
          end
      | Const (c, _) -> anomaly (str "Const " ++ str (Constant.to_string c))
      | x -> anomaly (str "bigint_of_z' App c " ++ str (obj_string x))
      end
  | Construct ((_, 1), _) -> (* Z'0 *) Bigint.zero
  | _ -> raise Not_found

let constr_of_global_reference = function
  | VarRef v -> mkVar v
  | ConstRef cr -> mkConst cr
  | IndRef ind -> mkInd ind
  | ConstructRef c -> mkConstruct c

let rec constr_of_glob_constr vl = function
  | Glob_term.GRef (loc, gr, gllo) ->
      constr_of_global_reference gr
  | Glob_term.GVar (loc, id) ->
      constr_of_glob_constr vl (List.assoc id vl)
  | Glob_term.GApp (_, gc, gcl) ->
      let c = constr_of_glob_constr vl gc in
      let cl = List.map (constr_of_glob_constr vl) gcl in
      mkApp (c, Array.of_list cl)
  | _ ->
      raise Not_found

let rec glob_constr_of_constr loc c = match Constr.kind c with
  | Var id ->
      Glob_term.GRef (loc, VarRef id, None)
  | App (c, ca) ->
      let c = glob_constr_of_constr loc c in
      let cel = List.map (glob_constr_of_constr loc) (Array.to_list ca) in
      Glob_term.GApp (loc, c, cel)
  | Construct (c, _) ->
      Glob_term.GRef (loc, ConstructRef c, None)
  | Const (c, _) ->
      Glob_term.GRef (loc, ConstRef c, None)
  | Ind (ind, _) ->
      Glob_term.GRef (loc, IndRef ind, None)
  | x ->
      anomaly (str "1 constr " ++ str (obj_string x))

let interp_big_int zpos'ty ty thr f loc bi =
  let t =
    let c = mkApp (mkConst f, [| z'_of_bigint zpos'ty ty thr bi |]) in
    eval_constr c
  in
  match Constr.kind t with
  | App (_, [| _; c |]) -> glob_constr_of_constr loc c
  | App (_, [| _ |]) ->
      user_err_loc
        (loc, "_",
         str "Cannot interpret this number as a value of type " ++
         str (string_of_reference ty))
  | x ->
      anomaly (str "interp_big_int " ++ str (obj_string x))

let uninterp_big_int loc g c =
  match try Some (constr_of_glob_constr [] c) with Not_found -> None with
  | Some c ->
      begin match
	try Some (eval_constr (mkApp (mkConst g, [| c |])))
	with Type_errors.TypeError _ -> None
      with
      | Some t ->
          begin match Constr.kind t with
          | App (c, [| _; x |]) -> Some (bigint_of_z' x)
	  | x -> None
	  end
      | None ->
	  None
      end
  | None ->
      None

let uninterp_big_int_ltac tac c =
  let c = (c, None) in
  let loc = Loc.ghost in
  let c = Tacexpr.ConstrMayEval (Genredexpr.ConstrTerm c) in
  let ta = Tacexpr.TacCall (loc, ArgArg (loc, tac), [c]) in
  let te = Tacexpr.TacArg (loc, ta) in
  match eval_tacexpr (Tacinterp.default_ist ()) (Global.env ()) te with
  | Some v ->
      begin match Tacinterp.Value.to_constr v with
      | Some c -> Some (bigint_of_z' c)
      | None -> None
      end
  | None ->
      None

let load_numeral_notation _ (_, (loc, zpos'ty, ty, f, g, sc, patl, thr, path)) =
  match g with
  | Inl g ->
      Notation.declare_numeral_interpreter sc (path, [])
        (interp_big_int zpos'ty ty thr f)
	(patl, uninterp_big_int loc g, true)
  | Inr ltac ->
      Notation.declare_numeral_interpreter sc (path, [])
        (interp_big_int zpos'ty ty thr f)
	(patl, uninterp_big_int_ltac ltac, false)

let cache_numeral_notation o = load_numeral_notation 1 o

type numeral_notation_obj =
  Loc.t * (Names.inductive * Names.inductive) *
  Libnames.reference * Names.constant *
  (Names.constant, Nametab.ltac_constant) union *
  Notation_term.scope_name * Glob_term.glob_constr list *
  Bigint.bigint * Libnames.full_path

let inNumeralNotation : numeral_notation_obj -> Libobject.obj =
  Libobject.declare_object {
    (Libobject.default_object "NUMERAL NOTATION") with
    Libobject.cache_function = cache_numeral_notation;
    Libobject.load_function = load_numeral_notation }

let vernac_numeral_notation ty f g sc patl waft =
  let loc = Loc.ghost in
  let zpos'ty =
    let z'ty =
      let c = qualid_of_ident (Id.of_string "Z'") in
      try match Nametab.locate c with IndRef i -> i | _ -> raise Not_found
      with Not_found -> Nametab.error_global_not_found c
    in
    let positive'ty =
      let c = qualid_of_ident (Id.of_string "positive'") in
      try match Nametab.locate c with IndRef i -> i | _ -> raise Not_found
      with Not_found -> Nametab.error_global_not_found c
    in
    (z'ty, positive'ty)
  in
  let tyc =
    let (loc, tyq) = qualid_of_reference ty in
    try Nametab.locate tyq with Not_found ->
      Nametab.error_global_not_found_loc loc tyq
  in
  let fc =
    let (loc, fq) = qualid_of_reference f in
    try Nametab.locate_constant fq with Not_found ->
      Nametab.error_global_not_found_loc loc fq
  in
  let lqid = qualid_of_reference ty in
  let crq = CRef (Qualid lqid, None) in
  let identref loc s = (loc, Names.Id.of_string s) in
  let app loc x y = CApp (loc, (None, x), [(y, None)]) in
  let cref loc s = CRef (Ident (identref loc s), None) in
  let arrow loc x y =
    CProdN (loc, [([(loc, Anonymous)], Default Decl_kinds.Explicit, x)], y)
  in
  let _ =
    (* checking "f" is of type "Z' -> option ty" *)
    let c =
      CCast
        (loc, CRef (f, None),
         CastConv
           (arrow loc (cref loc "Z'") (app loc (cref loc "option") crq)))
    in
    let (sigma, env) = Lemmas.get_current_context () in
    Constrintern.intern_constr env c
  in
  let thr = Bigint.of_int waft in
  let path = Nametab.path_of_global tyc in
  match (tyc, patl) with
  | (IndRef (sp, spi), []) ->
      let gc =
        let (loc, gq) = qualid_of_reference g in
        try Nametab.locate_constant gq with Not_found ->
          Nametab.error_global_not_found_loc loc gq
      in
      let _ =
        (* checking "g" is of type "ty -> option Z'" *)
        let c =
          CCast
            (loc, CRef (g, None),
             CastConv
               (arrow loc crq (app loc (cref loc "option") (cref loc "Z'"))))
        in
        let (sigma, env) = Lemmas.get_current_context () in
        Constrintern.interp_open_constr env sigma c
      in
      let env = Global.env () in
      let patl =
        match patl with
        | _ :: _ -> anomaly (str "patl not impl")
        | [] ->
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
                   Glob_term.GRef
                     (loc, ConstructRef ((sp, spi), i + 1), None))
                 mc)
      in
      Lib.add_anonymous_leaf
        (inNumeralNotation
	   (loc, zpos'ty, ty, fc, Inl gc, sc, patl, thr, path))
  | ((IndRef _ | ConstRef _), _) ->
      let gc =
        let (loc, gq) = qualid_of_reference g in
        try Nametab.locate_tactic gq with Not_found ->
          user_err_loc
            (loc, "_",
             str "tactic " ++ str (string_of_qualid gq) ++ str " not found")
      in
      let patl =
        match patl with
        | _ :: _ ->
            List.map (fun r -> Glob_term.GRef (loc, intern_reference r, None))
              patl
        | [] -> []
      in
      Lib.add_anonymous_leaf
        (inNumeralNotation
	   (loc, zpos'ty, ty, fc, Inr gc, sc, patl, thr, path))
  | (VarRef _, _) | (ConstructRef _, _) ->
      user_err_loc
        (loc, "_", str (string_of_reference ty) ++ str " is not a type")

open Constrarg
open Stdarg

VERNAC COMMAND EXTEND NumeralNotation CLASSIFIED AS QUERY
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) ] ->
    [ let (patl, waft) = ([], 0) in
      vernac_numeral_notation ty f g (Id.to_string sc) patl waft ]
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) "(" "printing" reference_list(patl) ")" ] ->
    [ let waft = 0 in
      vernac_numeral_notation ty f g (Id.to_string sc) patl waft ]
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) "(" "warning" "after" int(waft) ")" ] ->
    [ let patl = [] in
      vernac_numeral_notation ty f g (Id.to_string sc) patl waft ]
  | [ "Numeral" "Notation" reference(ty) reference(f) reference(g) ":"
      ident(sc) "(" "printing" reference_list(patl) ")"
      "(" "warning" "after" int(waft) ")" ] ->
    [ vernac_numeral_notation ty f g (Id.to_string sc) patl waft ]
END
