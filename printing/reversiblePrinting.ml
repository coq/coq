(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type kind = Term | Type

type mode =
  | UpToUnification
  (** The reparsed term, with its holes, must unify with the original
      term (holes and universes get instantiated by unification). *)
  | UpToConversionModuloSortsAndUniverses
  (** The reparsed term must elaborate on its own (no hole may need the
      original term to be resolved) to a term convertible with the
      original one when sorts and universes are ignored entirely: sort
      qualities, universe levels and universe instances may all differ.
      The laxest of the conversion-based checks. *)
  | UpToConversionModuloUniverses
  (** The reparsed term must elaborate on its own (no hole may need the
      original term to be resolved) to a term convertible with the
      original one when universe levels (and the level components of
      universe instances) are ignored but sort qualities must agree.
      Thus [Set] and [Type@{u}] are accepted, but [Prop], [SProp] and
      [Type] are pairwise distinguished. *)
  | UpToConversionModuloUniverseUnification
  (** The reparsed term must elaborate on its own to a term convertible
      with the original one, allowing new universe (in)equations to be
      enforced on the universes introduced by the reparsing (universe
      unification through the evar map). Stricter than
      [UpToConversionModuloUniverses] (a universe level cannot be set
      equal to an algebraic universe), laxer than [UpToConversion]. *)
  | UpToConversion
  (** The reparsed term must elaborate on its own to a term convertible
      with the original one, with universe (in)equations valid in the
      current graph. *)

let mode_eq m1 m2 = match m1, m2 with
  | UpToUnification, UpToUnification
  | UpToConversionModuloSortsAndUniverses, UpToConversionModuloSortsAndUniverses
  | UpToConversionModuloUniverses, UpToConversionModuloUniverses
  | UpToConversionModuloUniverseUnification, UpToConversionModuloUniverseUnification
  | UpToConversion, UpToConversion -> true
  | (UpToUnification | UpToConversionModuloSortsAndUniverses
    | UpToConversionModuloUniverses
    | UpToConversionModuloUniverseUnification | UpToConversion), _ -> false

(* The single piece of state behind the flags below, and the only one
   registered with the summary. *)
let current_mode : mode option Summary.Ref.t =
  Summary.ref ~name:"printing-reversible-mode" None

(* These flags behave like a radio button: setting one unsets the
   others; unsetting the one currently set disables the check. They
   are all views of [current_mode], which is what the summary tracks,
   so they are declared without a summary entry of their own. *)
let declare_mode_option key mode =
  let open Goptions in
  declare_option ~no_summary:true ~kind:BoolKind {
    optstage = Summary.Stage.Interp;
    optdepr  = None;
    optkey   = key;
    optread  = (fun () -> match Summary.Ref.get current_mode with
        | Some m -> mode_eq m mode
        | None -> false);
    optwrite = (fun b ->
        if b then Summary.Ref.set current_mode (Some mode)
        else match Summary.Ref.get current_mode with
          | Some m when mode_eq m mode -> Summary.Ref.set current_mode None
          | _ -> ());
  }

let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Unification"] UpToUnification
let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Conversion";"Modulo";"Sorts";"And";"Universes"]
    UpToConversionModuloSortsAndUniverses
let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Conversion";"Modulo";"Universes"]
    UpToConversionModuloUniverses
let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Conversion";"Modulo";"Universe";"Unification"]
    UpToConversionModuloUniverseUnification
let () = declare_mode_option
    ["Printing";"Reversible";"Up";"To";"Conversion"] UpToConversion

let pr_mode = function
  | UpToUnification -> Pp.str "unification"
  | UpToConversionModuloSortsAndUniverses ->
    Pp.str "conversion modulo sorts and universes"
  | UpToConversionModuloUniverses -> Pp.str "conversion modulo universes"
  | UpToConversionModuloUniverseUnification ->
    Pp.str "conversion modulo universe unification"
  | UpToConversion -> Pp.str "conversion"

let warn_not_reversible =
  CWarnings.create ~name:"reversible-printing"
    (fun mode ->
       Pp.(strbrk "The printed form of this term could not be re-parsed \
                   and re-elaborated to an equal term (up to " ++ pr_mode mode ++
           strbrk "), even with all printing options turned on."))

let lconstr_eoi = Procq.eoi_entry Procq.Constr.lconstr

(* Successively more explicit printing flags: coercions, implicit
   arguments, no notations, universes (first with, then without
   notations), parentheses, ending with the equivalent of
   [Printing All] plus [Printing Universes] and [Printing
   Parentheses]. Unsetting notations is tried after implicit arguments
   and before universes, but is not kept when escalating to universes:
   configurations are ordered by explicitness, not included in each
   other. Only extern/detype-level flags and the [parentheses] flag may
   vary along the ladder: the rendering of the returned [constr_expr]
   must be fully determined by the returned flags (see
   [Ppconstr.of_printing_flags]). *)
let ladder flags =
  let open PrintingFlags in
  let e0 = flags.extern in
  let e1 = { e0 with Extern.coercions = true } in
  let e2 = { e1 with Extern.implicits = true; Extern.implicits_defensive = true } in
  let e3 = { e2 with Extern.notations = false } in
  let d4 = { flags.detype with Detype.universes = true } in
  let e5 = { e3 with Extern.parentheses = true } in
  let raw = make_raw flags in
  let raw = { detype = { raw.detype with Detype.universes = true };
              extern = { raw.extern with Extern.parentheses = true } } in
  [ flags;
    { flags with extern = e1 };
    { flags with extern = e2 };
    { flags with extern = e3 };
    { detype = d4; extern = e2 };
    { detype = d4; extern = e3 };
    { detype = d4; extern = e5 };
    raw ]

(* Reparsing a term can spuriously emit warnings (e.g. deprecation
   warnings for notations it reuses); silence them during the check. *)
let no_warnings f =
  let saved = CWarnings.get_flags () in
  CWarnings.set_flags "-all";
  Util.try_finally f () CWarnings.set_flags saved

(* Conversion for the [UpToConversionModuloUniverses] mode: universe
   levels (and the level components of universe instances) are ignored,
   but sort qualities must agree. So [Set] and [Type@{u}] (both of
   [QType] quality) are accepted, and [Type@{u}] vs [Type@{v}] is
   accepted, but [Prop], [SProp] and [Type] are pairwise rejected; the
   quality components of instances (for sort-polymorphic constants) must
   also agree. This lets [Check Type] print plain [Type] while still
   catching a reparse whose sort quality differs from the original. *)
let modulo_universes_compare =
  let open Conversion in
  let compare_sorts _pb s1 s2 () =
    if Sorts.Quality.equal (Sorts.quality s1) (Sorts.quality s2)
    then Result.Ok () else Result.Error None
  in
  let compare_instances ~flex:_ i1 i2 () =
    let (q1, _), (q2, _) = UVars.Instance.to_array i1, UVars.Instance.to_array i2 in
    if CArray.equal Sorts.Quality.equal q1 q2
    then Result.Ok () else Result.Error None
  in
  let compare_cumul_instances _pb _variance i1 i2 () =
    compare_instances ~flex:false i1 i2 ()
  in
  { compare_sorts; compare_instances; compare_cumul_instances }

(* No [eq_constr_nounivs] fast-path here: it would treat sorts of
   different qualities as equal, defeating the sort-sensitivity we want. *)
let is_conv_modulo_universes env sigma t1 t2 =
  let evars = Evd.evar_handler sigma in
  let t1 = EConstr.Unsafe.to_constr t1 in
  let t2 = EConstr.Unsafe.to_constr t2 in
  let env = Environ.set_universes (Evd.universes sigma) env in
  match Conversion.generic_conv ~l2r:false Conversion.CONV ~evars
          TransparentState.full env ((), modulo_universes_compare) t1 t2 with
  | Result.Ok () -> true
  | Result.Error None -> false
  | Result.Error (Some e) -> Util.Empty.abort e

let reparses ~mode ~kind ~flags env sigma t expr =
  try
    no_warnings begin fun () ->
      let ppflags = Ppconstr.of_printing_flags flags in
      let str = Pp.string_of_ppcmds (Ppconstr.pr_lconstr_expr ~flags:ppflags env sigma expr) in
      let expr = Procq.parse_string lconstr_eoi str in
      let expected_type = match kind with
        | Type -> Pretyping.IsType
        | Term -> Pretyping.WithoutTypeConstraint
      in
      let sigma', t' = Constrintern.interp_open_constr ~expected_type env sigma expr in
      let no_new_undefined () =
        Evar.Set.for_all (fun ev -> Evd.mem sigma ev)
          (Evarutil.undefined_evars_of_term sigma' t')
      in
      (* Conversion (and unification) of terms does not imply that they
         have convertible types (e.g. binder types of lambdas are not
         compared), so for terms we compare the types too. For [Type]
         kind we do not compare the (algebraic) sorts the types live
         in, as elaboration is anyway allowed to pick different such
         sorts for the very same expression. *)
      let pairs = match kind with
        | Type -> [t', t]
        | Term ->
          let ty' = Retyping.get_type_of env sigma' t' in
          let ty = Retyping.get_type_of env sigma' t in
          [ty', ty; t', t]
      in
      match mode with
      | UpToUnification ->
        let sigma' = List.fold_left (fun sigma' (t', t) ->
            Evarconv.unify_delay env sigma' t' t) sigma' pairs in
        let (_ : Evd.evar_map) = Evarconv.solve_unif_constraints_with_heuristics env sigma' in
        true
      | UpToConversionModuloSortsAndUniverses ->
        (* Convertibility ignoring sorts and universes entirely
           ([Reductionops.is_conv_nounivs]): unlike modulo universes
           below, even sort qualities need not agree, so e.g. dropping a
           sort-polymorphic instance whose omission changes the
           elaborated quality is accepted. *)
        no_new_undefined () &&
        List.for_all (fun (t', t) -> Reductionops.is_conv_nounivs env sigma' t' t) pairs
      | UpToConversionModuloUniverses ->
        (* Convertibility ignoring universe levels (and the level
           components of instances) but requiring sort qualities to
           agree. Unlike a conversion enforcing universe equalities,
           this accepts e.g. a freshly elaborated [Type@{v}] against the
           original [Type@{u+1}], where [v] is a plain level that cannot
           be set equal to the algebraic [u+1]; but it still rejects a
           reparse whose sort quality differs (e.g. [Prop] vs [Type]). *)
        no_new_undefined () &&
        List.for_all (fun (t', t) -> is_conv_modulo_universes env sigma' t' t) pairs
      | UpToConversionModuloUniverseUnification ->
        (* Convertibility enforcing universe unification: the universes
           introduced by the reparsing may be unified against the
           original ones through the evar map, but a universe level
           cannot be set equal to an algebraic universe, so e.g. [Check
           Type] does not check under this mode. *)
        no_new_undefined () &&
        (let rec conv sigma' = function
           | [] -> true
           | (t', t) :: pairs ->
             match Reductionops.infer_conv ~pb:Conversion.CONV env sigma' t' t with
             | Some sigma' -> conv sigma' pairs
             | None -> false
         in
         conv sigma' pairs)
      | UpToConversion ->
        no_new_undefined () &&
        List.for_all (fun (t', t) -> Reductionops.is_conv env sigma' t' t) pairs
    end
  with e when CErrors.noncritical e -> false

(* Printing terms while checking reversibility (e.g. from the
   elaboration of the reparsed term) must not recursively trigger the
   check. *)
let in_check = ref false

let checked_extern ~flags ~extern ~kind env sigma t =
  match Summary.Ref.get current_mode with
  | None -> flags, extern ~flags
  | Some _ when !in_check -> flags, extern ~flags
  | Some mode ->
    let rec aux = function
      | [] -> assert false
      | [flags] ->
        let expr = extern ~flags in
        if not (reparses ~mode ~kind ~flags env sigma t expr) then
          warn_not_reversible mode;
        (flags, expr)
      | flags :: rest ->
        let expr = extern ~flags in
        if reparses ~mode ~kind ~flags env sigma t expr then (flags, expr)
        else aux rest
    in
    in_check := true;
    Util.try_finally (fun () -> aux (ladder flags)) () (fun () -> in_check := false) ()
