let parsing_only_core =
  Goptions.declare_bool_option_and_ref ~depr:false ~value:false
    ~key:["Parsing"; "Only"; "Core"]

let error ?loc msg =
  CErrors.user_err ?loc
    Pp.(strbrk msg ++ spc () ++ strbrk "when the" ++ spc ()
        ++ str "Parsing Only Core" ++ spc () ++ strbrk "flag is set.")

let rec check_term { CAst.loc; v = term } =
  let error = error ?loc in
  let open Constrexpr in
  match term with
  | CRef _ | CSort _ -> ()
  | CFix (_, fixpoints) ->
     List.iter (check_fix ~loc) fixpoints
  | CCoFix (_, cofixpoints) ->
     List.iter (check_cofix ~loc) cofixpoints
  | CProdN (binders, term) | CLambdaN (binders, term) ->
     List.iter check_binder binders;
     check_term term
  | CLetIn (_, _, None, _) ->
     error "Type of let-in must be provided"
  | CLetIn (_, term1, Some typ, term2) ->
     check_term term1;
     check_term typ;
     check_term term2
  | CAppExpl _ ->
     error "Implicit arguments are not supported"
  | CApp ((_, term), args) ->
     check_term term;
     List.iter check_arg args
  | CRecord fields ->
     List.iter (fun (_, term) -> check_term term) fields
  | CCases (Constr.LetPatternStyle, _, _, _) | CLetTuple _ | CIf _ ->
     error "Only regular match is supported"
  | CCases (_, None, _, _) ->
     error "A return clause is required"
  | CCases (_, _, ([] | _ :: _ :: _), _) ->
     error "Can only match on a single term"
  | CCases (_, Some return, [(term, _, in_opt)], branches) ->
     check_term term;
     check_term return;
     Option.iter check_pattern in_opt;
     List.iter check_branch branches
  | CHole _ ->
     error "Holes are not supported"
  | CPatVar _ ->
     (* FIXME: What is this for exactly? *)
     ()
  | CEvar _ ->
     error "Existential variables are not supported"
  | CCast (term, cast) ->
     Glob_term.(
      match cast with
      | CastCoerce ->
         error "Coercions are not supported"
      | CastConv typ | CastVM typ | CastNative typ ->
         check_term typ
     );
     check_term term
  | CNotation _ | CPrim _ | CDelimiters _ ->
     error "Notations are not supported"
  | CGeneralization _ ->
     error "Generalization pattern are not supported"
and check_fix ~loc (_, annotation, binders, typ, term) =
  let open Constrexpr in
  begin match annotation with
  | None ->
     error ?loc "Structural recursion annotation is required"
  | Some {CAst.v = CStructRec _} -> ()
  | Some {CAst.loc} ->
     error ?loc "Only structural recursion is supported"
  end;
  List.iter check_binder binders;
  begin match typ.CAst.v with
  | CHole _ ->
     error ?loc "Type annotation is required"
  | _ ->
     check_term typ
  end;
  check_term term
and check_cofix ~loc (_, binders, typ, term) =
  List.iter check_binder binders;
  begin match typ.CAst.v with
  | Constrexpr.CHole _ ->
     error ?loc "Type annotation is required"
  | _ ->
     check_term typ
  end;
  check_term term
and check_arg (term, explicitation) =
  begin match explicitation with
  | None -> ()
  | Some { CAst.loc } ->
     error ?loc "Implicit arguments are not supported"
  end;
  check_term term
and check_branch { CAst.loc; v = (patterns, term) } =
  begin match patterns with
  | [ [ pattern ] ] -> check_pattern pattern
  | _ -> error ?loc "A single pattern is supported"
  end;
  check_term term
and check_pattern { CAst.loc; v = pattern } =
  let open Constrexpr in
  match pattern with
  | CPatAtom _ -> ()
  | CPatCstr (_, None, subpatts)
       when List.for_all
              (function { CAst.v = CPatAtom _ } -> true | _ -> false)
              subpatts
    -> ()
  | _ ->
     error ?loc "Only basic patterns are supported"
and check_binder =
  let open Constrexpr in
  function
  | CLocalAssum (_, Default Glob_term.Explicit, typ) ->
     check_term typ
  | CLocalAssum (_, Default _, { CAst.loc }) ->
     error ?loc "Implicit arguments are not supported"
  | CLocalAssum (_, Generalized _, { CAst.loc }) ->
     error ?loc "Generalized binders are not supported"
  | CLocalDef (_, { CAst.loc } , None) ->
     error ?loc "Type annotation is required"
  | CLocalDef (_, term, Some typ) ->
     check_term term;
     check_term typ
  | CLocalPattern { CAst.loc } ->
     (* This branch is never reached for the Defintion command because of some
        translation happening in g_vernac.mlg! *)
     error ?loc "Pattern binders are not supported"

let check_fixpoint fixpoint =
  let open Vernacexpr in
  List.iter check_binder fixpoint.binders;
  if not (CList.is_empty fixpoint.notations) then
    error "Declaration of notations is not supported";
  begin match fixpoint.rtype.CAst.v with
  | Constrexpr.CHole _ ->
     (* This is how no type is represented *)
     error "All types of (co-)recursive definitions must be provided"
  | _ ->
     check_term fixpoint.rtype
  end;
  match fixpoint.body_def with
  | None -> error "All bodies of (co-)recursive definitions must be provided"
  | Some term -> check_term term

let check_constructor (coercion, (_, term)) =
  if coercion then
    error "Cannot declare coercion";
  check_term term

let check_field (decl, { Vernacexpr.rf_subclass; rf_priority; rf_notation; rf_canonical = _ }) =
  if Option.has_some rf_subclass then
    error "Cannot declare coercion";
  if Option.has_some rf_priority then
    error "Cannot declare coercion priority";
  if not (CList.is_empty rf_notation) then
    error "Cannot declare notation";
  let open Vernacexpr in
  match decl with
  | AssumExpr (_, term) -> check_term term
  | DefExpr (_, _, None) -> error "Cannot declare field without type"
  | DefExpr (_, term, Some typ) ->
     check_term term;
     check_term typ

let check_inductive (((coercion, _), (binders, binders_opt), typ, body), notations) =
  if coercion then
    error "Cannot declare coercion";
  if not (CList.is_empty notations) then
    error "Declaration of notations is not supported";
  List.iter check_binder binders;
  Option.iter (List.iter check_binder) binders_opt;
  begin match typ with
  | None -> error "All types of inductive types must be provided"
  | Some typ -> check_term typ
  end;
  let open Vernacexpr in
  match body with
  | Constructors constructors ->
     List.iter check_constructor constructors
  | RecordDecl (_, fields) ->
     List.iter check_field fields

let supported_attributes =
  let open Attributes in
  let open Notations in
  polymorphic_nowarn ++ template ++ locality

let check_vernac attrs vernac =
  if parsing_only_core () then
    begin
      Attributes.(
      let unsupported_attrs, _ = parse_with_extra supported_attributes attrs in
      match unsupported_attrs with
      | [] -> ()
      | (unsupported_attr_name, _) :: _ ->
         error ("Attribute " ^ unsupported_attr_name ^ " is not supported")
      );
      let open Vernacexpr in
      match vernac with
      (* Supported commands with terms to verify *)
      | VernacDefinition (_, _, DefineBody (binders, _, term, typ)) ->
         List.iter check_binder binders;
         begin match typ with
         | None -> error "Type of definition must be provided"
         | Some typ -> check_term typ
         end;
         check_term term
      | VernacFixpoint (_, fixpoints) ->
         List.iter check_fixpoint fixpoints
      | VernacCoFixpoint (_, cofixpoints) ->
         List.iter check_fixpoint cofixpoints
      | VernacAssumption (_, _, assumptions) ->
         List.iter (fun (_, (_, typ)) -> check_term typ) assumptions
      | VernacContext binders ->
         List.iter check_binder binders
      | VernacInductive (_, _, _, inductives) ->
         List.iter check_inductive inductives
      | VernacCheckMayEval (_, goal_selector, term) ->
         if Option.has_some goal_selector then
           error "Goal selector is not supported";
         check_term term
      | VernacGlobalCheck term ->
         check_term term
      (* Supported commands with nothing to verify *)
      | VernacUniverse _ | VernacConstraint _ -> ()
      | VernacBeginSection _ | VernacEndSegment _ -> ()
      | VernacDefineModule _ | VernacDeclareModuleType _ -> ()
      | VernacDeclareModule _ | VernacInclude _ -> ()
      | VernacRequire _ | VernacImport _ -> ()
      | VernacSetOption _ | VernacAddOption _ | VernacRemoveOption _ -> ()
      | VernacMemOption _ | VernacPrintOption _ -> ()
      | VernacDeclareReduction _ -> ()
      (* Print commands *)
      | VernacPrint (PrintTypingFlags | PrintTables | PrintFullContext) -> ()
      | VernacPrint (PrintSectionContext _ | PrintInspect _) -> ()
      | VernacPrint (PrintModules | PrintModule _ | PrintModuleType _) -> ()
      | VernacPrint (PrintName _ | PrintGraph | PrintUniverses _) -> ()
      | VernacPrint (PrintVisibility _ | PrintAbout _) -> ()
      | VernacPrint (PrintAssumptions _) -> ()
      (* Unsupported variants *)
      | VernacDefinition _ | VernacStartTheoremProof _ ->
         error "Cannot open interactive proof mode"
      (* Other commands *)
      | _ ->
         error "This command is not supported"
    end
