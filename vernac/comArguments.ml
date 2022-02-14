(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CAst
open Util
open Names
open Vernacexpr

let smart_global r =
  let gr = Smartlocate.smart_global r in
  Dumpglob.add_glob ?loc:r.loc gr;
  gr

let cache_bidi_hints (gr, ohint) =
  match ohint with
  | None -> Pretyping.clear_bidirectionality_hint gr
  | Some nargs -> Pretyping.add_bidirectionality_hint gr nargs

let load_bidi_hints _ r =
  cache_bidi_hints r

let subst_bidi_hints (subst, (gr, ohint as orig)) =
  let gr' = Globnames.subst_global_reference subst gr in
  if gr == gr' then orig else (gr', ohint)

let discharge_bidi_hints (gr, ohint) =
  if Globnames.isVarRef gr && Lib.is_in_section gr then None
  else
    let vars = Lib.section_instance gr in
    let n = Array.length vars in
    Some (gr, Option.map ((+) n) ohint)

let inBidiHints =
  let open Libobject in
  declare_object { (default_object "BIDIRECTIONALITY-HINTS" ) with
                   load_function = load_bidi_hints;
                   cache_function = cache_bidi_hints;
                   classify_function = (fun o -> Substitute);
                   subst_function = subst_bidi_hints;
                   discharge_function = discharge_bidi_hints;
                 }


let warn_arguments_assert =
  CWarnings.create ~name:"arguments-assert" ~category:"vernacular"
    Pp.(fun sr ->
        strbrk "This command is just asserting the names of arguments of " ++
        Printer.pr_global sr ++ strbrk". If this is what you want, add " ++
        strbrk "': assert' to silence the warning. If you want " ++
        strbrk "to clear implicit arguments, add ': clear implicits'. " ++
        strbrk "If you want to clear notation scopes, add ': clear scopes'")

(* [nargs_for_red] is the number of arguments required to trigger reduction,
   [args] is the main list of arguments statuses,
   [more_implicits] is a list of extra lists of implicit statuses  *)
let vernac_arguments ~section_local reference args more_implicits flags =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let assert_flag = List.mem `Assert flags in
  let rename_flag = List.mem `Rename flags in
  let clear_scopes_flag = List.mem `ClearScopes flags in
  let extra_scopes_flag = List.mem `ExtraScopes flags in
  let clear_implicits_flag = List.mem `ClearImplicits flags in
  let default_implicits_flag = List.mem `DefaultImplicits flags in
  let never_unfold_flag = List.mem `ReductionNeverUnfold flags in
  let nomatch_flag = List.mem `ReductionDontExposeCase flags in
  let clear_bidi_hint = List.mem `ClearBidiHint flags in

  let err_incompat x y =
    CErrors.user_err Pp.(str ("Options \""^x^"\" and \""^y^"\" are incompatible.")) in

  if assert_flag && rename_flag then
    err_incompat "assert" "rename";
  if clear_scopes_flag && extra_scopes_flag then
    err_incompat "clear scopes" "extra scopes";
  if clear_implicits_flag && default_implicits_flag then
    err_incompat "clear implicits" "default implicits";

  let args, nargs_for_red, nargs_before_bidi, _i =
    List.fold_left (fun (args,red,bidi,i) arg ->
        match arg with
        | RealArg arg -> (arg::args,red,bidi,i+1)
        | VolatileArg ->
          if Option.has_some red
          then CErrors.user_err Pp.(str "The \"/\" modifier may only occur once.");
          (args,Some i,bidi,i)
        | BidiArg ->
          if Option.has_some bidi
          then CErrors.user_err Pp.(str "The \"&\" modifier may only occur once.");
          (args,red,Some i,i))
      ([],None,None,0)
      args
  in
  let args = List.rev args in

  let sr = smart_global reference in
  let inf_names =
    let ty, _ = Typeops.type_of_global_in_context env sr in
    List.map pi1 (Impargs.compute_implicits_names env sigma (EConstr.of_constr ty))
  in
  let prev_names =
    try Arguments_renaming.arguments_names sr with Not_found -> inf_names
  in
  let num_args = List.length inf_names in
  assert (Int.equal num_args (List.length prev_names));

  let names_of args = List.map (fun a -> a.name) args in

  (* Checks *)

  let err_extra_args names =
    CErrors.user_err
      Pp.(strbrk "Extra arguments: " ++
          prlist_with_sep pr_comma Name.print names ++ str ".")
  in
  let err_missing_args names =
    CErrors.user_err
      Pp.(strbrk "The following arguments are not declared: " ++
          prlist_with_sep pr_comma Name.print names ++ str ".")
  in

  let rec check_extra_args extra_args =
    match extra_args with
    | [] -> ()
    | { notation_scope = None } :: _ ->
      CErrors.user_err Pp.(str"Extra arguments should specify a scope.")
    | { notation_scope = Some _ } :: args -> check_extra_args args
  in

  let args, scopes =
    let scopes = List.map (fun { notation_scope = s } -> s) args in
    if List.length args > num_args then
      let args, extra_args = List.chop num_args args in
      if extra_scopes_flag then
        (check_extra_args extra_args; (args, scopes))
      else err_extra_args (names_of extra_args)
    else args, scopes
  in

  if Option.cata (fun n -> n > num_args) false nargs_for_red then
    CErrors.user_err Pp.(str "The \"/\" modifier should be put before any extra scope.");

  if Option.cata (fun n -> n > num_args) false nargs_before_bidi then
    CErrors.user_err Pp.(str "The \"&\" modifier should be put before any extra scope.");

  let scopes_specified = List.exists Option.has_some scopes in

  if scopes_specified && clear_scopes_flag then
    CErrors.user_err Pp.(str "The \"clear scopes\" flag is incompatible with scope annotations.");

  let names = List.map (fun { name } -> name) args in
  let names = names :: List.map (List.map fst) more_implicits in

  let rename_flag_required = ref false in
  let example_renaming = ref None in
  let save_example_renaming renaming =
    rename_flag_required := !rename_flag_required
                            || not (Name.equal (fst renaming) Anonymous);
    if Option.is_empty !example_renaming then
      example_renaming := Some renaming
  in

  let rec names_union names1 names2 =
    match names1, names2 with
    | [], [] -> []
    | _ :: _, [] -> names1
    | [], _ :: _ -> names2
    | (Name _ as name) :: names1, Anonymous :: names2
    | Anonymous :: names1, (Name _ as name) :: names2 ->
      name :: names_union names1 names2
    | name1 :: names1, name2 :: names2 ->
      if Name.equal name1 name2 then
        name1 :: names_union names1 names2
      else CErrors.user_err Pp.(str "Argument lists should agree on the names they provide.")
  in

  let names = List.fold_left names_union [] names in

  let rec rename prev_names names =
    match prev_names, names with
    | [], [] -> []
    | [], _ :: _ -> err_extra_args names
    | _ :: _, [] when assert_flag ->
      (* Error messages are expressed in terms of original names, not
           renamed ones. *)
      err_missing_args (List.lastn (List.length prev_names) inf_names)
    | _ :: _, [] -> prev_names
    | prev :: prev_names, Anonymous :: names ->
      prev :: rename prev_names names
    | prev :: prev_names, (Name id as name) :: names ->
      if not (Name.equal prev name) then save_example_renaming (prev,name);
      name :: rename prev_names names
  in

  let names = rename prev_names names in
  let renaming_specified = Option.has_some !example_renaming in

  if !rename_flag_required && not rename_flag then begin
    let msg = let open Pp in
      match !example_renaming with
      | None ->
        strbrk "To rename arguments the \"rename\" flag must be specified."
      | Some (o,n) ->
        strbrk "Flag \"rename\" expected to rename " ++ Name.print o ++
        strbrk " into " ++ Name.print n ++ str "."
    in CErrors.user_err msg
  end;

  let implicits =
    List.map (fun { name; implicit_status = i } -> (name,i)) args
  in
  let implicits = implicits :: more_implicits in

  let implicits_specified = match implicits with
    | [l] -> List.exists (function _, Glob_term.Explicit -> false | _ -> true) l
    | _ -> true in

  if implicits_specified && clear_implicits_flag then
    CErrors.user_err Pp.(str "The \"clear implicits\" flag must be omitted if implicit annotations are given.");

  if implicits_specified && default_implicits_flag then
    CErrors.user_err Pp.(str "The \"default implicits\" flag is incompatible with implicit annotations.");

  let rargs =
    Util.List.map_filter (function (n, true) -> Some n | _ -> None)
      (Util.List.map_i (fun i { recarg_like = b } -> i, b) 0 args)
  in

  let red_behavior =
    let open Reductionops.ReductionBehaviour in
    match never_unfold_flag, nomatch_flag, rargs, nargs_for_red with
    | true, false, [], None -> Some NeverUnfold
    | true, true, _, _ -> err_incompat "simpl never" "simpl nomatch"
    | true, _, _::_, _ -> err_incompat "simpl never" "!"
    | true, _, _, Some _ -> err_incompat "simpl never" "/"
    | false, false, [], None  -> None
    | false, false, _, _ -> Some (UnfoldWhen { nargs = nargs_for_red;
                                               recargs = rargs;
                                             })
    | false, true, _, _ -> Some (UnfoldWhenNoMatch { nargs = nargs_for_red;
                                                     recargs = rargs;
                                                   })
  in


  let red_modifiers_specified = Option.has_some red_behavior in

  let bidi_hint_specified = Option.has_some nargs_before_bidi in

  if bidi_hint_specified && clear_bidi_hint then
    err_incompat "clear bidirectionality hint" "&";


  (* Actions *)

  if renaming_specified then begin
    Arguments_renaming.rename_arguments section_local sr names
  end;

  if scopes_specified || clear_scopes_flag then begin
    let scopes = List.map (Option.map (fun {loc;v=k} ->
        try ignore (Notation.find_scope k); k
        with CErrors.UserError _ ->
          Notation.find_delimiters_scope ?loc k)) scopes
    in
    Notation.declare_arguments_scope section_local (smart_global reference) scopes
  end;

  if implicits_specified || clear_implicits_flag then
    Impargs.set_implicits section_local (smart_global reference) implicits;

  if default_implicits_flag then
    Impargs.declare_implicits section_local (smart_global reference);

  if red_modifiers_specified then begin
    match sr with
    | GlobRef.ConstRef _ ->
      Reductionops.ReductionBehaviour.set
        ~local:section_local sr (Option.get red_behavior)

    | _ ->
      CErrors.user_err
        Pp.(strbrk "Modifiers of the behavior of the simpl tactic "++
            strbrk "are relevant for constants only.")
  end;

  if bidi_hint_specified then begin
    let n = Option.get nargs_before_bidi in
    if section_local then
      Pretyping.add_bidirectionality_hint sr n
    else
      Lib.add_leaf (inBidiHints (sr, Some n))
  end;

  if clear_bidi_hint then begin
    if section_local then
      Pretyping.clear_bidirectionality_hint sr
    else
      Lib.add_leaf (inBidiHints (sr, None))
  end;

  if not (renaming_specified ||
          implicits_specified ||
          scopes_specified ||
          red_modifiers_specified ||
          bidi_hint_specified) && (List.is_empty flags) then
    warn_arguments_assert sr
