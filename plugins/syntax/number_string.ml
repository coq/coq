(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open Util
open Names
open Libnames
open Glob_term
open Notation

module CSet = CSet.Make (Constr)
module CMap = CMap.Make (Constr)

let mkRef env sigma g =
  let sigma, c = Evd.fresh_global env sigma g in
  sigma, EConstr.Unsafe.to_constr c

let gref q = DAst.make (GRef (q,None))

(** * Number notation *)

type number_string_via = qualid * (bool * qualid * qualid) list
type number_option =
  | After of numnot_option
  | Via of number_string_via

let warn_abstract_large_num_no_op =
  CWarnings.create ~name:"abstract-large-number-no-op" ~category:CWarnings.CoreCategories.numbers
    (fun f ->
      strbrk "The 'abstract after' directive has no effect when " ++
      strbrk "the parsing function (" ++
      Nametab.pr_global_env (Termops.vars_of_env (Global.env ())) f ++ strbrk ") targets an " ++
      strbrk "option type.")

let get_constructors ind =
  let mib,oib = Global.lookup_inductive ind in
  let mc = oib.Declarations.mind_consnames in
  Array.to_list
    (Array.mapi (fun j c -> GlobRef.ConstructRef (ind, j + 1)) mc)

let q_option () = Rocqlib.lib_ref "core.option.type"

let unsafe_ref_ind q =
  match q with
  | GlobRef.IndRef i -> i
  | _ -> raise Not_found

let locate_z () =
  let zn = "num.Z.type" in
  let pn = "num.pos.type" in
  match Rocqlib.lib_ref zn, Rocqlib.lib_ref pn with
  | exception Rocqlib.NotFoundRef _ -> None
  | q_z, q_pos ->
    Some ({
        z_ty = unsafe_ref_ind q_z;
        pos_ty = unsafe_ref_ind q_pos;
      }, gref q_z)

let locate_number () =
  let dint = "num.int.type" in
  let duint = "num.uint.type" in
  let dec = "num.decimal.type" in
  let hint = "num.hexadecimal_int.type" in
  let huint = "num.hexadecimal_uint.type" in
  let hex = "num.hexadecimal.type" in
  let int = "num.num_int.type" in
  let uint = "num.num_uint.type" in
  let num = "num.number.type" in
  match Rocqlib.lib_ref dint, Rocqlib.lib_ref duint, Rocqlib.lib_ref dec
        , Rocqlib.lib_ref hint, Rocqlib.lib_ref huint, Rocqlib.lib_ref hex
        , Rocqlib.lib_ref int, Rocqlib.lib_ref uint, Rocqlib.lib_ref num
  with
  | exception Rocqlib.NotFoundRef _ -> None
  | q_dint, q_duint, q_dec, q_hint, q_huint, q_hex, q_int, q_uint, q_num ->
    let int_ty = {
      dec_int = unsafe_ref_ind q_dint;
      dec_uint = unsafe_ref_ind q_duint;
      hex_int = unsafe_ref_ind q_hint;
      hex_uint = unsafe_ref_ind q_huint;
      int = unsafe_ref_ind q_int;
      uint = unsafe_ref_ind q_uint;
    } in
    let num_ty = {
      int = int_ty;
      decimal = unsafe_ref_ind q_dec;
      hexadecimal = unsafe_ref_ind q_hex;
      number = unsafe_ref_ind q_num;
    } in
    Some (int_ty, gref q_int, gref q_uint, gref q_dint, gref q_duint,
          num_ty, gref q_num, gref q_dec)

let locate_int63 () =
  let pos_neg_int63n = "num.int63.pos_neg_int63" in
  match Rocqlib.lib_ref pos_neg_int63n with
  | exception Rocqlib.NotFoundRef _ -> None
  | pos_neg_int63 ->
    Some ({pos_neg_int63_ty = unsafe_ref_ind pos_neg_int63},
          gref pos_neg_int63)


let locate_float () =
  let floatn = "num.float.type" in
  match Rocqlib.lib_ref floatn with
  | exception Rocqlib.NotFoundRef _ -> None
  | q_float -> Some (gref q_float)

let has_type env sigma f ty =
  let c = DAst.make @@ GCast (f, Some Constr.DEFAULTcast, ty) in
  let flags = Pretyping.{ all_and_fail_flags with use_coercions = false } in
  try let _ = Pretyping.understand ~flags env sigma c in true
  with Pretype_errors.PretypeError _ -> false

let type_error_to f ty =
  CErrors.user_err
    (pr_qualid f ++ str " should go from Number.int to " ++
     pr_qualid ty ++ str " or (option " ++ pr_qualid ty ++ str ")." ++
     fnl () ++ str "Instead of Number.int, the types Number.uint or Z or PrimInt63.pos_neg_int63 or PrimFloat.float or Number.number could be used (you may need to require BinNums or Number or PrimInt63 or PrimFloat first).")

let type_error_of g ty =
  CErrors.user_err
    (pr_qualid g ++ str " should go from " ++ pr_qualid ty ++
     str " to Number.int or (option Number.int)." ++ fnl () ++
     str "Instead of Number.int, the types Number.uint or Z or PrimInt63.pos_neg_int63 or PrimFloat.float or Number.number could be used (you may need to require BinNums or Number or PrimInt63 or PrimFloat first).")

let error_params ind =
  CErrors.user_err
    (str "Wrong number of parameters for inductive" ++ spc ()
     ++ Printer.pr_global (GlobRef.IndRef ind) ++ str ".")

let remapping_error ?loc ty ty' ty'' =
  CErrors.user_err ?loc
    (Printer.pr_global ty
     ++ str " was already mapped to" ++ spc () ++ Printer.pr_global ty'
     ++ str " and cannot be remapped to" ++ spc () ++ Printer.pr_global ty''
     ++ str ".")

let error_missing c =
  CErrors.user_err
    (str "Missing mapping for constructor " ++ Printer.pr_global c ++ str ".")

let warn_via_remapping =
  CWarnings.create ~name:"via-type-remapping" ~category:CWarnings.CoreCategories.numbers
    (fun (env, sigma, ty, ty', ty'') ->
      let constr = Printer.pr_constr_env env sigma in
      constr ty ++ str " was already mapped to" ++ spc () ++ constr ty'
      ++ str ", mapping it also to" ++ spc () ++ constr ty''
      ++ str " might yield ill typed terms when using the notation.")

let warn_via_type_mismatch =
  CWarnings.create ~name:"via-type-mismatch" ~category:CWarnings.CoreCategories.numbers
    (fun (env, sigma, g, g', exp, actual) ->
      let constr = Printer.pr_constr_env env sigma in
      str "Type of" ++ spc() ++ Printer.pr_global g
      ++ str " seems incompatible with the type of" ++ spc ()
      ++ Printer.pr_global g' ++ str "." ++ spc ()
      ++ str "Expected type is: " ++ constr exp ++ spc ()
      ++ str "instead of " ++ constr actual ++ str "." ++ spc ()
      ++ str "This might yield ill typed terms when using the notation.")

let multiple_via_error () =
  CErrors.user_err (Pp.str "Multiple 'via' options.")

let multiple_after_error () =
  CErrors.user_err (Pp.str "Multiple 'warning after' or 'abstract after' options.")

let via_abstract_error () =
  CErrors.user_err (Pp.str "'via' and 'abstract' cannot be used together.")

let locate_global_sort_inductive_or_constant env sigma qid =
  let locate_sort qid =
    match Nametab.locate_extended qid with
    | Globnames.TrueGlobal _ -> raise Not_found
    | Globnames.Abbrev kn ->
    match Abbreviation.search_abbreviation kn with
    | [], Notation_term.NSort r ->
       let sigma,c = Evd.fresh_sort_in_family sigma (Glob_ops.glob_sort_family r) in
       let c = EConstr.ESorts.kind sigma c in
       sigma, Constr.mkSort c
    | _ -> raise Not_found in
  try locate_sort qid
  with Not_found ->
    let g = Smartlocate.global_with_alias qid in
    let () = match g with
      | IndRef _ | ConstRef _ -> ()
      | VarRef _ | ConstructRef _ ->
        CErrors.user_err Pp.(pr_qualid qid ++ spc() ++ str "is not an inductive type or a constant.")
    in
    mkRef env sigma g

let locate_global_constructor_inductive_or_constant env sigma qid =
  let g = Smartlocate.global_with_alias qid in
  let () = match g with
    | ConstructRef _ | IndRef _ | ConstRef _ -> ()
    | VarRef _ -> CErrors.user_err Pp.(pr_qualid qid ++ spc() ++ str "is a section variable.")
  in
  let sigma, c = mkRef env sigma g in
  sigma, g, c

(* [get_type env sigma c] retrieves the type of [c] and returns a pair
   [l, t] such that [c : l_0 -> ... -> l_n -> t]. *)
let get_type env sigma c =
  (* inspired from [compute_implicit_names] in "interp/impargs.ml" *)
  let rec aux env acc t =
    let t = Reductionops.whd_all env sigma t in
    match EConstr.kind sigma t with
    | Constr.Prod (na, a, b) ->
       let a = Reductionops.whd_all env sigma a in
       let rel = Context.Rel.Declaration.LocalAssum (na, a) in
       aux (EConstr.push_rel rel env) ((na, a) :: acc) b
    | _ -> List.rev acc, t in
  let t = Retyping.get_type_of env sigma (EConstr.of_constr c) in
  let l, t = aux env [] t in
  List.map (fun (na, a) -> EConstr.Unsafe.to_binder_annot na, EConstr.Unsafe.to_constr a) l,
  EConstr.Unsafe.to_constr t

(* [elaborate_to_post_params env sigma ty_ind params] builds the
   [to_post] translation (c.f., interp/notation.mli) for the numeral
   notation to parse/print type [ty_ind]. This translation is the
   identity ([ToPostCopy]) except that it checks ([ToPostCheck]) that
   the parameters of the inductive type [ty_ind] match the ones given
   in [params]. *)
let elaborate_to_post_params env sigma ty_ind params =
  let to_post_for_constructor indc =
    let sigma, c = match indc with
      | GlobRef.ConstructRef _ -> mkRef env sigma indc
      | _ -> assert false in  (* c.f. get_constructors *)
    let args, t = get_type env sigma c in
    let params_indc = match Constr.kind t with
      | Constr.App (_, a) -> Array.to_list a | _ -> [] in
    let sz = List.length args in
    let a = Array.make sz ToPostCopy in
    if List.length params <> List.length params_indc then error_params ty_ind;
    List.iter2 (fun param param_indc ->
        match param, Constr.kind param_indc with
        | Some p, Constr.Rel i when i <= sz -> a.(sz - i) <- ToPostCheck p
        | _ -> ())
      params params_indc;
    indc, indc, Array.to_list a in
  let pt_refs = get_constructors ty_ind in
  let to_post_0 = List.map to_post_for_constructor pt_refs in
  let to_post =
    let only_copy (_, _, args) = List.for_all ((=) ToPostCopy) args in
    if (List.for_all only_copy to_post_0) then [||] else [|to_post_0|] in
  to_post, pt_refs

(* [elaborate_to_post_via env sigma ty_name ty_ind l] builds the [to_post]
   translation (c.f., interp/notation.mli) for the number notation to
   parse/print type [ty_name] through the inductive [ty_ind] according
   to the pairs [constant, constructor] in the list [l]. *)
let elaborate_to_post_via env sigma ty_name ty_ind l =
  let sigma, ty_name =
    locate_global_sort_inductive_or_constant env sigma ty_name in
  let sigma, ty_ind = mkRef env sigma (IndRef ty_ind) in
  (* Retrieve constants and constructors mappings and their type.
     For each constant [cnst] and inductive constructor [indc] in [l], retrieve:
     * its location: [lcnst] and [lindc]
     * its GlobRef: [cnst] and [indc]
     * its type: [tcnst] and [tindc] (decomposed in product by [get_type] above)
     * [impls] are the implicit arguments of [cnst] *)
  let sigma, l =
    let read sigma (consider_implicits, cnst, indc) =
      let lcnst, lindc = cnst.CAst.loc, indc.CAst.loc in
      let sigma, cnst, ccnst = locate_global_constructor_inductive_or_constant env sigma cnst in
      let indc = GlobRef.ConstructRef (Smartlocate.global_constructor_with_alias indc) in
      let sigma, cindc = mkRef env sigma indc in
      let get_type_wo_params c =
        (* ignore parameters of inductive types *)
        let rm_params c = match Constr.kind c with
          | Constr.App (c, _) when Constr.isInd c -> c
          | _ -> c in
        let lc, tc = get_type env sigma c in
        List.map (fun (n, c) -> n, rm_params c) lc, rm_params tc in
      let tcnst, tindc = get_type_wo_params ccnst, get_type_wo_params cindc in
      let impls =
        if not consider_implicits then [] else
          Impargs.(select_stronger_impargs (implicits_of_global cnst)) in
      sigma, (lcnst, cnst, tcnst, lindc, indc, tindc, impls) in
    List.fold_left_map read sigma l
  in
  let eq_indc indc (_, _, _, _, indc', _, _) = Environ.QGlobRef.equal env indc indc' in
  (* Collect all inductive types involved.
     That is [ty_ind] and all final codomains of [tindc] above. *)
  let inds =
    List.fold_left (fun s (_, _, _, _, _, tindc, _) -> CSet.add (snd tindc) s)
      (CSet.singleton ty_ind) l in
  (* And for each inductive, retrieve its constructors. *)
  let constructors =
    CSet.fold (fun ind m ->
        let inductive, _ = Constr.destInd ind in
        CMap.add ind (get_constructors inductive) m)
      inds CMap.empty in
  (* Error if one [constructor] in some inductive in [inds]
     doesn't appear exactly once in [l] *)
  let _ : _ list = (* check_for duplicate constructor and error *)
    List.fold_left (fun already_seen (_, cnst, _, loc, indc, _, _) ->
        try
          let cnst' = List.assoc_f (fun c1 c2 -> Environ.QGlobRef.equal env c1 c2) indc already_seen in
          remapping_error ?loc indc cnst' cnst
        with Not_found -> (indc, cnst) :: already_seen)
    [] l in
  let () = (* check for missing constructor and error *)
    CMap.iter (fun _ ctors ->
        List.iter (fun cstr ->
            if not (List.exists (eq_indc cstr) l) then error_missing cstr)
          ctors)
      constructors in
  (* Perform some checks on types and warn if they look strange.
     These checks are neither sound nor complete, so we only warn. *)
  let () =
    (* associate inductives to types, and check that this mapping is one to one
       and maps [ty_ind] to [ty_name] *)
    let ind2ty, ty2ind =
      let add loc ckey cval m =
        match CMap.find_opt ckey m with
        | None -> CMap.add ckey cval m
        | Some old_cval ->
           if not (Constr.eq_constr_nounivs old_cval cval) then
             warn_via_remapping ?loc (env, sigma, ckey, old_cval, cval);
           m in
      List.fold_left
        (fun (ind2ty, ty2ind) (lcnst, _, (_, tcnst), lindc, _, (_, tindc), _) ->
          add lcnst tindc tcnst ind2ty, add lindc tcnst tindc ty2ind)
        CMap.(singleton ty_ind ty_name, singleton ty_name ty_ind) l in
    (* check that type of constants and constructors mapped in [l]
       match modulo [ind2ty] *)
    let rm_impls impls (l, t) =
      let rec aux impls l = match impls, l with
        | Some _ :: impls, _ :: b -> aux impls b
        | None :: impls, (n, a) :: b -> (n, a) :: aux impls b
        | _ -> l in
      aux impls l, t in
    let replace m (l, t) =
      let apply_m c = try CMap.find c m with Not_found -> c in
      List.fold_right (fun (na, a) b -> Constr.mkProd (na, (apply_m a), b))
        l (apply_m t) in
    List.iter (fun (_, cnst, tcnst, loc, indc, tindc, impls) ->
        let tcnst = rm_impls impls tcnst in
        let tcnst' = replace CMap.empty tcnst in
        if not (Constr.eq_constr_nounivs tcnst' (replace ind2ty tindc)) then
          let actual = replace CMap.empty tindc in
          let expected = replace ty2ind tcnst in
          warn_via_type_mismatch ?loc (env, sigma, indc, cnst, expected, actual))
      l in
  (* Associate an index to each inductive, starting from 0 for [ty_ind]. *)
  let ind2num, num2ind, nb_ind =
    CMap.fold (fun ind _ (ind2num, num2ind, i) ->
        CMap.add ind i ind2num, Int.Map.add i ind num2ind, i + 1)
      (CMap.remove ty_ind constructors)
      (CMap.singleton ty_ind 0, Int.Map.singleton 0 ty_ind, 1) in
  (* Finally elaborate [to_post] *)
  let to_post =
    let rec map_prod impls tindc = match impls with
      | Some _ :: impls -> ToPostHole :: map_prod impls tindc
      | _ ->
         match tindc with
         | [] -> []
         | (_, a) :: b ->
            let t = match CMap.find_opt a ind2num with
              | Some i -> ToPostAs i
              | None -> ToPostCopy in
            let impls = match impls with [] -> [] | _ :: t -> t in
            t :: map_prod impls b in
    Array.init nb_ind (fun i ->
        List.map (fun indc ->
            let _, cnst, _, _, _, tindc, impls = List.find (eq_indc indc) l in
            indc, cnst, map_prod impls (fst tindc))
          (CMap.find (Int.Map.find i num2ind) constructors)) in
  (* and use constants mapped to constructors of [ty_ind] as triggers. *)
  let pt_refs = List.map (fun (_, cnst, _) -> cnst) (to_post.(0)) in
  to_post, pt_refs

type target_type =
  | TargetInd of (inductive * Constr.t option list)
  | TargetPrim of GlobRef.t * GlobRef.t list * required_module

let locate_global_inductive_with_params allow_params qid =
  if not allow_params then raise Not_found else
    match Nametab.locate_extended qid with
    | Globnames.TrueGlobal _ -> raise Not_found
    | Globnames.Abbrev kn ->
    match Abbreviation.search_abbreviation kn with
    | [], Notation_term.(NApp (NRef (GlobRef.IndRef i,None), l)) ->
       i,
       List.map (function
           | Notation_term.NHole _ -> None
           | n ->
              let g = Notation_ops.glob_constr_of_notation_constr n in
              let c, _ =
                let env = Global.env () in
                let sigma = Evd.from_env env in
                Pretyping.understand env sigma g in
              Some (EConstr.Unsafe.to_constr c)) l
    | _ -> raise Not_found

let locate_global_inductive_or_int63_or_float env allow_params qid =
  try TargetInd (locate_global_inductive_with_params allow_params qid)
  with Not_found ->
    let int63n = "num.int63.type" in
    let int63c = "num.int63.wrap_int" in
    let int63w = "num.int63.int_wrapper" in
    let floatn = "num.float.type" in
    let floatc = "num.float.wrap_float" in
    let floatw = "num.float.float_wrapper" in
    if allow_params && Rocqlib.has_ref int63n
       && Environ.QGlobRef.equal env (Smartlocate.global_with_alias qid) (Rocqlib.lib_ref int63n)
    then TargetPrim (Rocqlib.lib_ref int63w, [Rocqlib.lib_ref int63c],
                     (Nametab.path_of_global (Rocqlib.lib_ref int63n), []))
    else if allow_params && Rocqlib.has_ref floatn
       && Environ.QGlobRef.equal env (Smartlocate.global_with_alias qid) (Rocqlib.lib_ref floatn)
    then TargetPrim (Rocqlib.lib_ref floatw, [Rocqlib.lib_ref floatc],
                     (Nametab.path_of_global (Rocqlib.lib_ref floatn), []))
    else TargetInd (Smartlocate.global_inductive_with_alias qid, [])

let intern_cref env sigma r =
  Constrintern.intern_constr env sigma (CAst.make @@ Constrexpr.CAppExpl ((r,None),[]))

let vernac_number_notation local ty f g opts scope =
  let rec parse_opts = function
    | [] -> None, Nop
    | h :: opts ->
       let via, opts = parse_opts opts in
       let via = match h, via with
         | Via _, Some _ -> multiple_via_error ()
         | Via v, None -> Some v
         | _ -> via in
       let opts = match h, opts with
         | After _, (Warning _ | Abstract _) -> multiple_after_error ()
         | After a, Nop -> a
         | _ -> opts in
       via, opts in
  let via, opts = parse_opts opts in
  (match via, opts with Some _, Abstract _ -> via_abstract_error () | _ -> ());
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let num_ty = locate_number () in
  let z_pos_ty = locate_z () in
  let int63_ty = locate_int63 () in
  let float_ty = locate_float () in
  let ty_name = ty in
  let ty, via =
    match via with None -> ty, via | Some (ty', a) -> ty', Some (ty, a) in
  let tyc_params = locate_global_inductive_or_int63_or_float env (via = None) ty in
  let to_ty = Smartlocate.global_with_alias f in
  let of_ty = Smartlocate.global_with_alias g in
  let cty = intern_cref env sigma ty in
  let f_name, f = f, intern_cref env sigma f in
  let g_name, g = g, intern_cref env sigma g in
  let app x y = DAst.make @@ GApp (x,[y]) in
  let arrow x y =
    DAst.make @@ GProd (Anonymous,None,Glob_term.Explicit, x, y)
  in
  let opt r = app (gref (q_option ())) r in
  (* Check the type of f *)
  let to_kind =
    match num_ty with
    | Some (int_ty, cint, _, _, _, _, _, _) when has_type env sigma f (arrow cint cty) -> Int int_ty, Direct
    | Some (int_ty, cint, _, _, _, _, _, _) when has_type env sigma f (arrow cint (opt cty)) -> Int int_ty, Option
    | Some (int_ty, _, cuint, _, _, _, _, _) when has_type env sigma f (arrow cuint cty) -> UInt int_ty, Direct
    | Some (int_ty, _, cuint, _, _, _, _, _) when has_type env sigma f (arrow cuint (opt cty)) -> UInt int_ty, Option
    | Some (_, _, _, _, _, num_ty, cnum, _) when has_type env sigma f (arrow cnum cty) -> Number num_ty, Direct
    | Some (_, _, _, _, _, num_ty, cnum, _) when has_type env sigma f (arrow cnum (opt cty)) -> Number num_ty, Option
    | _ ->
    match z_pos_ty with
    | Some (z_pos_ty, cZ) when has_type env sigma f (arrow cZ cty) -> Z z_pos_ty, Direct
    | Some (z_pos_ty, cZ) when has_type env sigma f (arrow cZ (opt cty)) -> Z z_pos_ty, Option
    | _ ->
    match int63_ty with
    | Some (pos_neg_int63_ty, cint63) when has_type env sigma f (arrow cint63 cty) -> Int63 pos_neg_int63_ty, Direct
    | Some (pos_neg_int63_ty, cint63) when has_type env sigma f (arrow cint63 (opt cty)) -> Int63 pos_neg_int63_ty, Option
    | _ ->
    match float_ty with
    | Some cfloat when has_type env sigma f (arrow cfloat cty) -> Float64, Direct
    | Some cfloat when has_type env sigma f (arrow cfloat (opt cty)) -> Float64, Option
    | _ -> type_error_to f_name ty
  in
  (* Check the type of g *)
  let cty = match tyc_params with TargetPrim (c, _, _) -> gref c | TargetInd _ -> cty in
  let of_kind =
    match num_ty with
    | Some (int_ty, cint, _, _, _, _, _, _) when has_type env sigma g (arrow cty cint) -> Int int_ty, Direct
    | Some (int_ty, cint, _, _, _, _, _, _) when has_type env sigma g (arrow cty (opt cint)) -> Int int_ty, Option
    | Some (int_ty, _, cuint, _, _, _, _, _) when has_type env sigma g (arrow cty cuint) -> UInt int_ty, Direct
    | Some (int_ty, _, cuint, _, _, _, _, _) when has_type env sigma g (arrow cty (opt cuint)) -> UInt int_ty, Option
    | Some (_, _, _, _, _, num_ty, cnum, _) when has_type env sigma g (arrow cty cnum) -> Number num_ty, Direct
    | Some (_, _, _, _, _, num_ty, cnum, _) when has_type env sigma g (arrow cty (opt cnum)) -> Number num_ty, Option
    | _ ->
    match z_pos_ty with
    | Some (z_pos_ty, cZ) when has_type env sigma g (arrow cty cZ) -> Z z_pos_ty, Direct
    | Some (z_pos_ty, cZ) when has_type env sigma g (arrow cty (opt cZ)) -> Z z_pos_ty, Option
    | _ ->
    match int63_ty with
    | Some (pos_neg_int63_ty, cint63) when has_type env sigma g (arrow cty cint63) -> Int63 pos_neg_int63_ty, Direct
    | Some (pos_neg_int63_ty, cint63) when has_type env sigma g (arrow cty (opt cint63)) -> Int63 pos_neg_int63_ty, Option
    | _ ->
    match float_ty with
    | Some cfloat when has_type env sigma g (arrow cty cfloat) -> Float64, Direct
    | Some cfloat when has_type env sigma g (arrow cty (opt cfloat)) -> Float64, Option
    | _ -> type_error_of g_name ty
  in
  let to_post, pt_required, pt_refs = match tyc_params with
    | TargetPrim (_, refs, path) -> [||], path, refs
    | TargetInd (tyc, params) ->
       let to_post, pt_refs =
         match via with
         | None -> elaborate_to_post_params env sigma tyc params
         | Some (ty, l) -> elaborate_to_post_via env sigma ty tyc l in
       to_post, (Nametab.path_of_global (GlobRef.IndRef tyc), []), pt_refs in
  let o = { to_kind; to_ty; to_post; of_kind; of_ty; ty_name;
            warning = opts }
  in
  (match opts, to_kind with
   | Abstract _, (_, Option) -> warn_abstract_large_num_no_op o.to_ty
   | _ -> ());
  let i =
       { pt_local = local;
         pt_scope = scope;
         pt_interp_info = NumberNotation o;
         pt_required;
         pt_refs;
         pt_in_match = true }
  in
  enable_prim_token_interpretation i

(** * String notation *)

let locate_global_inductive_or_pstring env allow_params qid =
  try TargetInd (locate_global_inductive_with_params allow_params qid)
  with Not_found ->
    let pstringn = "strings.pstring.type" in
    let pstringc = "strings.pstring.wrap_string" in
    let pstringw = "strings.pstring.string_wrapper" in
    if allow_params && Rocqlib.has_ref pstringn
       && Environ.QGlobRef.equal env (Smartlocate.global_with_alias qid) (Rocqlib.lib_ref pstringn)
    then TargetPrim (Rocqlib.lib_ref pstringw, [Rocqlib.lib_ref pstringc],
                     (Nametab.path_of_global (Rocqlib.lib_ref pstringn), []))
    else TargetInd (Smartlocate.global_inductive_with_alias qid, [])

let q_list () = Rocqlib.lib_ref "core.list.type"
let q_byte () = Rocqlib.lib_ref "core.byte.type"

let locate_pstring () =
  Option.map gref (Rocqlib.lib_ref_opt "strings.pstring.type")

let type_error_to f ty =
  CErrors.user_err
    (pr_qualid f ++ str " should go from Byte.byte, (list Byte.byte), or PrimString.string to " ++
     pr_qualid ty ++ str " or (option " ++ pr_qualid ty ++ str ").")

let type_error_of g ty =
  CErrors.user_err
    (pr_qualid g ++ str " should go from " ++ pr_qualid ty ++
     str " to T or (option T), where T is either Byte.byte, (list Byte.byte), or PrimString.string.")

let vernac_string_notation local ty f g via scope =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let pstring_ty = locate_pstring () in
  let app x y = DAst.make @@ GApp (x,[y]) in
  let arrow x y =
    DAst.make @@ GProd (Anonymous,None,Glob_term.Explicit, x, y)
  in
  let opt r = app (gref (q_option ())) r in
  let cbyte = gref (q_byte ()) in
  let clist = gref (q_list ()) in
  let clist_byte = app clist cbyte in
  let ty_name = ty in
  let ty, via =
    match via with None -> ty, via | Some (ty', a) -> ty', Some (ty, a) in
  let tyc_params = locate_global_inductive_or_pstring env (via = None) ty in
  let to_ty = Smartlocate.global_with_alias f in
  let of_ty = Smartlocate.global_with_alias g in
  let f_name, f = f, intern_cref env sigma f in
  let g_name, g = g, intern_cref env sigma g in
  let cty = intern_cref env sigma ty in
  (* Check the type of f *)
  let to_kind =
    match pstring_ty with
    | Some pstring when has_type env sigma f (arrow pstring cty) -> PString, Direct
    | Some pstring when has_type env sigma f (arrow pstring (opt cty)) -> PString, Option
    | _ ->
    if has_type env sigma f (arrow clist_byte cty) then ListByte, Direct
    else if has_type env sigma f (arrow clist_byte (opt cty)) then ListByte, Option
    else if has_type env sigma f (arrow cbyte cty) then Byte, Direct
    else if has_type env sigma f (arrow cbyte (opt cty)) then Byte, Option
    else type_error_to f_name ty
  in
  (* Check the type of g *)
  let of_kind =
    match pstring_ty with
    | Some pstring when has_type env sigma g (arrow cty pstring) -> PString, Direct
    | Some pstring when has_type env sigma g (arrow cty (opt pstring)) -> PString, Option
    | _ ->
    if has_type env sigma g (arrow cty clist_byte) then ListByte, Direct
    else if has_type env sigma g (arrow cty (opt clist_byte)) then ListByte, Option
    else if has_type env sigma g (arrow cty cbyte) then Byte, Direct
    else if has_type env sigma g (arrow cty (opt cbyte)) then Byte, Option
    else type_error_of g_name ty
  in
  let to_post, pt_required, pt_refs = match tyc_params with
    | TargetPrim (_, refs, path) -> [||], path, refs
    | TargetInd (tyc, params) ->
       let to_post, pt_refs =
         match via with
         | None -> elaborate_to_post_params env sigma tyc params
         | Some (ty, l) -> elaborate_to_post_via env sigma ty tyc l in
       to_post, (Nametab.path_of_global (GlobRef.IndRef tyc), []), pt_refs in
  let o = { to_kind; to_ty; to_post; of_kind; of_ty; ty_name; warning = () } in
  let i =
       { pt_local = local;
         pt_scope = scope;
         pt_interp_info = StringNotation o;
         pt_required;
         pt_refs;
         pt_in_match = true }
  in
  enable_prim_token_interpretation i
