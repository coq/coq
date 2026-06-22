(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*i*)
open CErrors
open Util
open Names
open Nameops
open Termops
open Libnames
open Impargs
open CAst
open Notation
open Constrexpr
open Constrexpr_ops
open Notation_ops
open Glob_term
open Glob_ops
open Pattern
open Detyping
open Structures
open Notationextern

module ExternFlags = PrintingFlags.Extern
module NamedDecl = Context.Named.Declaration
(*i*)

(* Translation from glob_constr to front constr *)

(**********************************************************************)

let hole = CAst.make @@ CHole (None)

let is_reserved_type ~flags na t =
  flags.ExternFlags.use_implicit_types &&
  match na with
  | Anonymous -> false
  | Name id ->
    try
      let pat = Reserve.find_reserved_type id in
      let _ : _ * _ * _ * _ =
        match_notation_constr ~print_parentheses:true ~factorize_eqns:flags.factorize_eqns
          t ~vars:Id.Set.empty ([],pat)
      in
      true
    with Not_found | No_match -> false

(**********************************************************************)
(* Various externalisation functions *)

let insert_delimiters e = function
  | None -> e
  | Some sc -> CAst.make @@ CDelimiters (DelimUnboundedScope,sc,e)

let insert_pat_delimiters ?loc p = function
  | None -> p
  | Some sc -> CAst.make ?loc @@ CPatDelimiters (DelimUnboundedScope,sc,p)

let insert_pat_alias ?loc p = function
  | Anonymous -> p
  | Name _ as na -> CAst.make ?loc @@ CPatAlias (p,(CAst.make ?loc na))

let rec insert_entry_coercion ?loc l c = match l with
  | [] -> c
  | (inscope,ntn)::l -> CAst.make ?loc @@ CNotation (Some inscope,ntn,([insert_entry_coercion ?loc l c],[],[],[]))

let rec insert_pat_coercion ?loc l c = match l with
  | [] -> c
  | (inscope,ntn)::l -> CAst.make ?loc @@ CPatNotation (Some inscope,ntn,([insert_pat_coercion ?loc l c],[],[]),[])

(**********************************************************************)
(* conversion of references                                           *)

let extern_evar n l = CEvar (n,l)

(** We allow customization of the global_reference printer.
    For instance, in the debugger the tables of global references
    may be inaccurate *)

let default_extern_reference ?loc vars r =
  try Nametab.shortest_qualid_of_global ?loc vars r
  with Not_found ->
  match r with
  | ConstRef c when ModPath.equal (Lib.current_mp()) (Constant.modpath c) ->
    (* assume this is a side effect not yet in the nametab *)
    Libnames.qualid_of_ident ?loc (Constant.label c)
  | _ -> raise Not_found

let my_extern_reference = ref default_extern_reference

let set_extern_reference f = my_extern_reference := f
let get_extern_reference () = !my_extern_reference

let extern_reference ?loc vars l = !my_extern_reference vars l

(**********************************************************************)
(* utilities                                                          *)

let rec fill_arg_scopes args subscopes (_,scopes as all) =
  match args, subscopes with
  | [], _ -> []
  | a :: args, scopt :: subscopes ->
    (a, ((constr_some_level,None), (scopt, scopes))) :: fill_arg_scopes args subscopes all
  | a :: args, [] ->
    (a, ((constr_some_level,None), ([], scopes))) :: fill_arg_scopes args [] all

let overlap_right_left {notation_entry = entry} lev_after ((typs,_):Notation_term.interpretation) =
  List.exists (fun (_id,(({notation_subentry = entry'; notation_relative_level = lev; notation_position = side},_),_,_)) ->
      match side with
      | Some Right when notation_entry_eq entry entry' -> may_capture_cont_after lev_after lev
      | _ -> false) typs

let update_with_subscope ~flags from_entry (entry,(scopt,scl)) lev_after closed scopes =
  let {notation_subentry = entry; notation_relative_level = lev; notation_position = side} = entry in
  let lev = if flags.ExternFlags.parentheses && side <> None then LevelLe 0 (* min level *) else lev in
  let lev_after =
    match side with
    | Some Left -> Some from_entry.notation_level
    | Some Right  -> if closed then None else lev_after
    | None -> None in
  let subentry' = {notation_subentry = entry; notation_relative_level = lev; notation_position = side} in
  ((subentry',lev_after),(scopt,scl@scopes))

let find_entry_coercion_with_application ?non_included custom entry is_empty_extra_args =
  if is_empty_extra_args then
    (* We need a direct coercion from custom to entry *)
    match availability_of_entry_coercion ?non_included custom entry with
    | None -> raise No_match
    | Some coercion -> coercion, []
  else
    (* We need a coercion from custom to constr, then from constr to entry *)
    match availability_of_entry_coercion custom constr_lowest_level with
    | None -> raise No_match
    | Some appcoercion ->
    match availability_of_entry_coercion constr_some_level entry with
    | None -> raise No_match
    | Some coercion -> coercion, appcoercion

(**********************************************************************)
(* mapping patterns to cases_pattern_expr                                *)

let add_patt_for_params ind l =
  if !Flags.in_debugger then l else
    Util.List.addn (Inductiveops.inductive_nparamdecls (Global.env()) ind) (CAst.make @@ CPatAtom None) l

let add_cpatt_for_params ind l =
  if !Flags.in_debugger then l else
    Util.List.addn  (Inductiveops.inductive_nparamdecls (Global.env()) ind) (DAst.make @@ PatVar Anonymous) l

let drop_implicits_in_patt ~flags cst nb_expl ?(tags=[]) args =
  let impl_st = implicits_of_global cst in
  let impl_data = extract_impargs_data impl_st in
  let rec impls_fit l = function
    | [], t, _ -> Some (List.rev_append l t)
    | _, [], _ -> None
    | t, hh :: tt, true :: tags -> impls_fit (hh :: l) (t, tt, tags)
    | h::t, { CAst.v = CPatAtom None }::tt, ((false :: tags) | ([] as tags)) when is_status_implicit h -> impls_fit l (t,tt,tags)
    | h::_, _, _ when is_status_implicit h -> None
    | _::t, hh::tt, ((false :: tags) | ([] as tags)) -> impls_fit (hh::l) (t,tt,tags)
  in
  let try_impls_fit (imps,args,tags) =
    if not !Constrintern.parsing_explicit &&
       flags.ExternFlags.implicits &&
       List.exists is_status_implicit imps
       (* Note: !print_implicits_explicit_args=true not supported for patterns *)
    then None
    else impls_fit [] (imps,args,tags)
  in
  let rec select = function
    | [] -> None
    | (_,imps)::imps_list ->
      match try_impls_fit (imps,args, tags) with
        | None -> select imps_list
        | x -> x
  in
  if Int.equal nb_expl 0 then select impl_data
  else
    let imps = List.skipn_at_best nb_expl (select_stronger_impargs impl_st) in
    try_impls_fit (imps,args, tags)

let destPrim = function { CAst.v = CPrim t } -> Some t | _ -> None
let destPatPrim = function { CAst.v = CPatPrim t } -> Some t | _ -> None

let make_notation_gen loc ntn mknot mkprim destprim l bl =
  match snd ntn,List.map destprim l with
    (* Special case to avoid writing "- 3" for e.g. (Z.opp 3) *)
    | "- _", [Some (Number p)] when not (NumTok.Signed.is_zero p) ->
        assert (bl=[]);
        mknot (loc,ntn,([mknot (loc,(InConstrEntry,"( _ )"),l,[])]),[])
    | _ ->
        match decompose_notation_key ntn, l with
        | (InConstrEntry,[Terminal x]), [] ->
           begin match String.unquote_coq_string x with
           | Some s -> mkprim (loc, String s)
           | None ->
           match NumTok.Unsigned.parse_string x with
           | Some n -> mkprim (loc, Number (NumTok.SPlus,n))
           | None -> mknot (loc,ntn,l,bl) end
        | (InConstrEntry,[Terminal "-"; Terminal x]), [] ->
           begin match NumTok.Unsigned.parse_string x with
           | Some n -> mkprim (loc, Number (NumTok.SMinus,n))
           | None -> mknot (loc,ntn,l,bl) end
        | _ -> mknot (loc,ntn,l,bl)

let make_notation loc (inscope,ntn) (terms,termlists,binders,binderlists as subst) =
  if not (List.is_empty termlists) || not (List.is_empty binderlists) then
    CAst.make ?loc @@ CNotation (Some inscope,ntn,subst)
  else
    make_notation_gen loc ntn
      (fun (loc,ntn,l,bl) -> CAst.make ?loc @@ CNotation (Some inscope,ntn,(l,[],bl,[])))
      (fun (loc,p) -> CAst.make ?loc @@ CPrim p)
      destPrim terms binders

let make_pat_notation ?loc (inscope,ntn) (terms,termlists,binders as subst) =
  if not (List.is_empty termlists && List.is_empty binders) then
    (CAst.make ?loc @@ CPatNotation (Some inscope,ntn,subst,[]))
  else
  make_notation_gen loc ntn
    (fun (loc,ntn,l,_) -> CAst.make ?loc @@ CPatNotation (Some inscope,ntn,(l,[],[]),[]))
    (fun (loc,p)     -> CAst.make ?loc @@ CPatPrim p)
    destPatPrim terms []

let apply_pat_notation (CAst.{v;loc} as c) args =
  if List.is_empty args then c else
  match v with
  | CPatNotation (sc,ntn,subst,[]) -> CAst.make ?loc @@ CPatNotation (sc,ntn,subst,args)
  | CPatPrim _ -> raise No_match (* TODO: add support for applied primitive token, see also Constrexpr_ops.mkAppPattern *)
  | CPatDelimiters _ -> raise No_match (* TODO: add support for applied delimited patterns *)
  | _ -> assert false

let pattern_printable_in_both_syntax ~flags (ind,_ as c) =
  let impl_st = extract_impargs_data (implicits_of_global (GlobRef.ConstructRef c)) in
  let nb_params = Inductiveops.inductive_nparams (Global.env()) ind in
  List.exists (fun (_,impls) ->
    (List.length impls >= nb_params) &&
      let params,args = Util.List.chop nb_params impls in
      not flags.ExternFlags.implicits &&
      (List.for_all is_status_implicit params)&&(List.for_all (fun x -> not (is_status_implicit x)) args)
  ) impl_st

let extern_record_pattern ~flags cstrsp args =
  if not (ExternFlags.Records.use_record_syntax flags.ExternFlags.records (fst cstrsp))
  then None
  else
  try
    let projs = Structure.find_projections (Global.env ()) (fst cstrsp) in
    let rec ip projs args acc =
      match projs, args with
      | [], [] -> acc
      | proj :: q, pat :: tail ->
        let acc =
          match proj, pat with
          | _, { CAst.v = CPatAtom None } ->
            (* we don't want to have 'x := _' in our patterns *)
            acc
          | Some c, _ ->
            let loc = pat.CAst.loc in
            (extern_reference ?loc Id.Set.empty (GlobRef.ConstRef c), pat) :: acc
          | _ -> raise No_match in
        ip q tail acc
      | _ -> assert false
    in
    Some (List.rev (ip projs args []))
  with
    Not_found | No_match | Exit -> None

(* Better to use extern_glob_constr composed with injection/retraction ?? *)
let rec extern_cases_pattern_in_scope ~flags ((custom,(lev_after:int option)),scopes as allscopes) vars pat =
  try
    if !Flags.in_debugger || flags.ExternFlags.raw_literals then raise No_match;
    let (na,p,key) = uninterp_prim_token_cases_pattern ~print_float:flags.float pat scopes in
    match availability_of_entry_coercion custom constr_lowest_level with
      | None -> raise No_match
      | Some coercion ->
        let loc = cases_pattern_loc pat in
        insert_pat_coercion ?loc coercion
          (insert_pat_alias ?loc (insert_pat_delimiters ?loc (CAst.make ?loc @@ CPatPrim p) key) na)
  with No_match ->
    try
      if !Flags.in_debugger || not flags.ExternFlags.notations then raise No_match;
      extern_notation_pattern ~flags allscopes vars pat
        (uninterp_cases_pattern_notations (Global.env ()) pat)
    with No_match ->
    let loc = pat.CAst.loc in
    match DAst.get pat with
    | PatVar (Name id) when entry_has_global custom || entry_has_ident custom ->
      CAst.make ?loc (CPatAtom (Some (qualid_of_ident ?loc id)))
    | pat ->
    match availability_of_entry_coercion custom constr_lowest_level with
    | None -> raise No_match
    | Some coercion ->
      let allscopes = ((constr_some_level,None),scopes) in
      let pat = match pat with
        | PatVar (Name id) -> CAst.make ?loc (CPatAtom (Some (qualid_of_ident ?loc id)))
        | PatVar (Anonymous) -> CAst.make ?loc (CPatAtom None)
        | PatCstr(cstrsp,args,na) ->
          let args = List.map (extern_cases_pattern_in_scope ~flags allscopes vars) args in
          let p =
            match extern_record_pattern ~flags cstrsp args with
            | Some l -> CPatRecord l
            | None ->
                  let c = extern_reference vars (GlobRef.ConstructRef cstrsp) in
                  let full_args = add_patt_for_params (fst cstrsp) args in
                  let drop n =
                    let tags = try Inductiveops.constructor_alltags (Global.env()) cstrsp
                      with _ when !Flags.in_debugger -> []
                    in
                    let tags = List.skipn_at_best n tags in
                    let args = List.skipn_at_best n full_args in
                    match drop_implicits_in_patt ~flags (GlobRef.ConstructRef cstrsp) n ~tags args with
                      | Some true_args -> CPatCstr (c, None, true_args)
                      | None           -> CPatCstr (c, Some full_args, []) in
                  if Constrintern.get_asymmetric_patterns () then
                    if pattern_printable_in_both_syntax ~flags cstrsp
                    then CPatCstr (c, None, args)
                    else if Constrintern.get_asymmetric_patterns_no_implicits ()
                    then CPatCstr (c, Some full_args, [])
                    else drop (Inductiveops.inductive_nparamdecls (Global.env()) (fst cstrsp))
                  else drop 0
          in
          insert_pat_alias ?loc (CAst.make ?loc p) na
      in
      insert_pat_coercion coercion pat

and apply_notation_to_pattern ?loc ~flags gr ((terms,termlists,binders),(no_implicit,nb_to_drop,more_args))
    ((custom, lev_after), (tmp_scope, scopes) as allscopes) vars pat rule =
  let lev_after = if List.is_empty more_args then lev_after else Some Notation.app_level in
  let extra_args =
    let subscopes = find_arguments_scope (Global.env ()) gr in
    let more_args_scopes = try List.skipn nb_to_drop subscopes with Failure _ -> [] in
    let more_args = fill_arg_scopes more_args more_args_scopes (snd allscopes) in
    let more_args = List.map (fun (c,allscopes) -> extern_cases_pattern_in_scope ~flags allscopes vars c) more_args in
    if Constrintern.get_asymmetric_patterns () || not (List.is_empty termlists) then more_args
    else if no_implicit then more_args else
      match drop_implicits_in_patt ~flags gr nb_to_drop more_args with
      | Some true_args -> true_args
      | None -> raise No_match in
  match rule with
    | NotationRule (_,ntn as specific_ntn) ->
      begin
        let entry =
          let entry = fst (Notation.level_of_notation ntn) in
          if overlap_right_left entry lev_after pat then {entry with notation_level = max_int} else entry in
        let coercion, appcoercion = find_entry_coercion_with_application custom entry (List.is_empty extra_args) in
        let closed = not (List.is_empty coercion) in
        match availability_of_notation specific_ntn (tmp_scope,scopes) with
          (* Uninterpretation is not allowed in current context *)
          | None -> raise No_match
          (* Uninterpretation is allowed in current context *)
          | Some (scopt,key) ->
            let scopes' = Option.List.cons scopt scopes in
            let l =
              List.map (fun (c,subscope) ->
                let scopes = update_with_subscope ~flags entry subscope lev_after closed scopes' in
                extern_cases_pattern_in_scope ~flags scopes vars c)
                terms in
            let ll =
              List.map (fun (c,subscope) ->
                let scopes = update_with_subscope ~flags entry subscope lev_after closed scopes' in
                List.map (extern_cases_pattern_in_scope ~flags scopes vars) c)
                termlists in
            let bl =
              List.map (fun (c,subscope) ->
                let scopes = update_with_subscope ~flags entry subscope lev_after closed scopes' in
                (extern_cases_pattern_in_scope ~flags scopes vars c, Explicit))
                binders
            in
            insert_pat_coercion appcoercion
              (insert_pat_delimiters ?loc
                 (apply_pat_notation
                    (insert_pat_coercion coercion
                       (make_pat_notation ?loc specific_ntn (l,ll,bl)))
                    extra_args)
                 key)
      end
    | AbbrevRule kn ->
      match availability_of_entry_coercion custom constr_lowest_level with
      | None -> raise No_match
      | Some coercion ->
      let qid = Nametab.shortest_qualid_of_abbreviation ?loc vars kn in
      let l1 =
        List.rev_map (fun (c,(subentry,(scopt,scl))) ->
          extern_cases_pattern_in_scope ~flags ((subentry,lev_after),(scopt,scl@scopes)) vars c)
          terms in
      assert (List.is_empty termlists);
      assert (List.is_empty binders);
      insert_pat_coercion ?loc coercion (CAst.make ?loc @@ CPatCstr (qid,None,List.rev_append l1 extra_args))

and extern_notation_pattern ~flags allscopes vars t = function
  | [] -> raise No_match
  | { not_rule = keyrule; not_patt = pat; not_status = n } :: rules ->
    try
      if is_printing_inactive_rule keyrule pat then raise No_match;
      let loc = t.loc in
      match DAst.get t with
        | PatCstr (cstr,args,na) ->
          let t = if na = Anonymous then t else DAst.make ?loc (PatCstr (cstr,args,Anonymous)) in
          let p = apply_notation_to_pattern ~flags ?loc (GlobRef.ConstructRef cstr)
            (match_notation_constr_cases_pattern t pat) allscopes vars pat keyrule in
          insert_pat_alias ?loc p na
        | PatVar Anonymous -> CAst.make ?loc @@ CPatAtom None
        | PatVar (Name id) -> CAst.make ?loc @@ CPatAtom (Some (qualid_of_ident ?loc id))
    with
        No_match -> extern_notation_pattern ~flags allscopes vars t rules

let rec extern_notation_ind_pattern ~flags allscopes vars ind args = function
  | [] -> raise No_match
  | { not_rule = keyrule; not_patt = pat; not_status = n } :: rules ->
    try
      if is_printing_inactive_rule keyrule pat then raise No_match;
      apply_notation_to_pattern ~flags (GlobRef.IndRef ind)
        (match_notation_constr_ind_pattern ind args pat) allscopes vars pat keyrule
    with
        No_match -> extern_notation_ind_pattern ~flags allscopes vars ind args rules

let extern_ind_pattern_in_scope ~flags (custom,scopes as allscopes) vars ind args =
  (* pboutill: There are letins in pat which is incompatible with notations and
     not explicit application. *)
  if !Flags.in_debugger then
    let c = extern_reference vars (GlobRef.IndRef ind) in
    let args = List.map (extern_cases_pattern_in_scope ~flags allscopes vars) args in
    CAst.make @@ CPatCstr (c, Some args, [])
  else
    try
      if not flags.ExternFlags.notations || Inductiveops.inductive_has_local_defs (Global.env()) ind
        then raise No_match;
      extern_notation_ind_pattern ~flags allscopes vars ind args
          (uninterp_ind_pattern_notations (Global.env ()) ind)
    with No_match ->
      let c = extern_reference vars (GlobRef.IndRef ind) in
      let args = List.map (extern_cases_pattern_in_scope ~flags allscopes vars) args in
      let tags = Inductiveops.inductive_alltags (Global.env()) ind in
      match drop_implicits_in_patt ~flags (GlobRef.IndRef ind) 0 ~tags args with
      | Some true_args -> CAst.make @@ CPatCstr (c, None, true_args)
      | None           -> CAst.make @@ CPatCstr (c, Some args, [])

let extern_cases_pattern ~flags vars p =
  extern_cases_pattern_in_scope ~flags ((constr_some_level,None),([],[])) vars p

(**********************************************************************)
(* Externalising applications *)

let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

let is_gvar id c = match DAst.get c with
| GVar id' -> Id.equal id id'
| _ -> false

let is_projection ~flags nargs r =
  if not !Flags.in_debugger && flags.ExternFlags.projections then
    try
      match r with
      | GlobRef.ConstRef c ->
        let n = Structure.projection_nparams (Global.env ()) c + 1 in
        if n <= nargs then Some n
        else None
      | _ -> None
    with Not_found -> None
  else None

let is_hole = function CHole _ | CEvar _ -> true | _ -> false

let isCRef_no_univ = function
  | CRef (_,None) -> true
  | _ -> false

let is_significant_implicit a =
  not (is_hole (a.CAst.v))

let is_needed_for_correct_partial_application tail imp =
  List.is_empty tail && not (maximal_insertion_of imp)

exception Expl

(* Take a list of arguments starting at position [q] and their implicit status *)
(* Decide for each implicit argument if it skipped or made explicit *)
(* If the removal of implicit arguments is not possible, raise [Expl] *)
(* [inctx] tells if the term is in a context which will enforce the external type *)
(* [n] is the total number of arguments block to which the [args] belong *)
let adjust_implicit_arguments ~flags inctx n args impl =
  let rec exprec = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (args,impl) in
        let visible =
          (flags.ExternFlags.implicits && flags.ExternFlags.implicits_explicit_args) ||
          (is_needed_for_correct_partial_application tail imp) ||
          (flags.ExternFlags.implicits_defensive &&
           (not (is_inferable_implicit inctx n imp)) &&
           is_significant_implicit (Lazy.force a))
        in
        if visible then
          (Lazy.force a,Some (make @@ explicitation imp)) :: tail
        else
          tail
    | a::args, _::impl -> (Lazy.force a,None) :: exprec (args,impl)
    | args, [] -> List.map (fun a -> (Lazy.force a,None)) args (*In case of polymorphism*)
    | [], (imp :: _) when is_status_implicit imp && maximal_insertion_of imp ->
      (* The non-explicit application cannot be parsed back with the same type *)
      raise Expl
    | [], _ -> []
  in exprec (args,impl)

let extern_projection ~flags inctx f nexpectedparams args impl =
  let (args1,args2) = List.chop (nexpectedparams + 1) args in
  let nextraargs = List.length args2 in
  let (impl1,impl2) = impargs_for_proj ~nexpectedparams ~nextraargs impl in
  let n = nexpectedparams + 1 + nextraargs in
  let args1 = adjust_implicit_arguments ~flags inctx n args1 impl1 in
  let args2 = adjust_implicit_arguments ~flags inctx n args2 impl2 in
  let (c1,expl), args1 = List.sep_last args1 in
  assert (expl = None);
  let c = CProj (false,f,args1,c1) in
  if args2 = [] then c else CApp (CAst.make c, args2)

let is_start_implicit = function
  | imp :: _ -> is_status_implicit imp && maximal_insertion_of imp
  | [] -> false

let extern_record ~flags ref args =
  try
    let cstrsp = match ref with GlobRef.ConstructRef c -> c | _ -> raise Not_found in
    if not (ExternFlags.Records.use_record_syntax flags.ExternFlags.records (fst cstrsp))
    then None
    else
    let struc = Structure.find (Global.env ()) (fst cstrsp) in
    let projs = struc.Structure.projections in
    let rec cut args n =
      if Int.equal n 0 then args
      else
        match args with
        | [] -> raise No_match
        | _ :: t -> cut t (n - 1) in
    let args = cut args struc.Structure.nparams in
    let rec ip projs args acc =
      match projs with
      | [] -> acc
      | { Structure.proj_body = None } :: _ -> raise No_match
      | { Structure.proj_body = Some c; proj_true = false } :: q ->
            (* we don't want to print locals *)
            ip q args acc
      | { Structure.proj_body = Some c; proj_true = true } :: q ->
            match args with
            | [] -> raise No_match
            (* we give up since the constructor is not complete *)
            | arg :: tail ->
               let arg = Lazy.force arg in
               let loc = arg.CAst.loc in
               let ref = extern_reference ?loc Id.Set.empty (GlobRef.ConstRef c) in
               ip q tail ((ref, arg) :: acc)
    in
    Some (List.rev (ip projs args []))
  with
    | Not_found | No_match | Exit -> None

let extern_global impl f us =
  if not !Constrintern.parsing_explicit && is_start_implicit impl
  then
    CAppExpl ((f, us), [])
  else
    CRef (f,us)

(* Implicit args indexes are in ascending order *)
(* inctx is useful only if there is a last argument to be deduced from ctxt *)
let extern_applied_ref ~flags inctx impl (cf,f) us args =
  try
    if not !Constrintern.parsing_explicit &&
       flags.ExternFlags.implicits &&
       not flags.ExternFlags.implicits_explicit_args &&
       List.exists is_status_implicit impl
    then raise Expl;
    let impl = if !Constrintern.parsing_explicit then [] else impl in
    let n = List.length args in
    let ref = CRef (f,us) in
    let r = CAst.make ref in
    let ip = is_projection ~flags n cf in
    match ip with
    | Some i ->
      (* [t.(f args1) args2] projection-style notation *)
      extern_projection ~flags inctx (f,us) (i-1) args impl
    | None ->
      let args = adjust_implicit_arguments ~flags inctx n args impl in
      if args = [] then ref else CApp (r, args)
  with Expl ->
  (* A [@f args] node *)
    let args = List.map Lazy.force args in
    match is_projection ~flags (List.length args) cf with
    | Some n ->
       let args = List.map (fun c -> (c,None)) args in
       let args1, args2 = List.chop n args in
       let (c1,_), args1 = List.sep_last args1 in
       let c = CProj (true, (f,us), args1, c1) in
       if args2 = [] then c else CApp (CAst.make c, args2)
    | None ->
       CAppExpl ((f,us), args)

type application_style =
  | UseCApp of (Constrexpr.constr_expr * Constrexpr.explicitation CAst.t option) list
  | UseCAppExpl of constr_expr Lazy.t list

let is_empty_extra_args = function
  | UseCApp extra_args -> List.is_empty extra_args
  | UseCAppExpl extra_args -> List.is_empty extra_args

let extern_applied_abbreviation (cf,f) abbrevargs = function
  | UseCApp extraargs ->
    let abbrevargs = List.map (fun a -> (a,None)) abbrevargs in
    let args = abbrevargs @ extraargs in
    if args = [] then cf else CApp (CAst.make cf, args)
  | UseCAppExpl extraargs ->
    let args = abbrevargs @ List.map Lazy.force extraargs in
    CAppExpl ((f,None), args)

let mkFlattenedCApp (head,args) =
  match head.CAst.v with
  | CApp (g,args') ->
    (* may happen with notations for a prefix of an n-ary application *)
    (* or after removal of a coercion to funclass *)
    CApp (g,args'@args)
  | h ->
    if List.is_empty args then h else CApp (head, args)

let extern_applied_notation f = function
  | UseCApp args -> mkFlattenedCApp (f,args)
  | UseCAppExpl _ -> raise No_match (* No @f for notations *)

let extern_args extern env args =
  let map (arg, argscopes) = lazy (extern argscopes env arg) in
  List.map map args

let match_coercion_app c = match DAst.get c with
  | GApp (r, args) ->
    begin match DAst.get r with
    | GRef (r,_) -> Some (c.CAst.loc, r, args)
    | _ -> None
    end
  | _ -> None

let remove_one_coercion ~flags inctx c =
  try match match_coercion_app c with
  | Some (loc,r,args) when not flags.ExternFlags.coercions ->
      let nargs = List.length args in
      (match Coercionops.hide_coercion r with
          | Some nparams when
                 let inctx = inctx || (* coercion to funclass implying being in context *) nparams+1 < nargs in
                 nparams < nargs && inctx ->
              (* We skip the coercion *)
              let l = List.skipn nparams args in
              let (a,l) = match l with a::l -> (a,l) | [] -> assert false in
              (* Don't flatten App's in case of funclass so that
                 (atomic) notations on [a] work; should be compatible
                 since printer does not care whether App's are
                 collapsed or not and notations with an implicit
                 coercion using funclass either would have already
                 been confused with ordinary application or would have need
                 a surrounding context and the coercion to funclass would
                 have been made explicit to match *)
              let a' = if List.is_empty l then a else DAst.make ?loc @@ GApp (a,l) in
              let inctx = inctx || not (List.is_empty l) in
              Some (nparams+1, inctx, a')
          | _ -> None)
  | _ -> None
  with Not_found ->
    None

let rec flatten_application c = match DAst.get c with
  | GApp (f, l) ->
    begin match DAst.get f with
    | GApp(a,l') ->
      let loc = c.CAst.loc in
      flatten_application (DAst.make ?loc @@ GApp (a,l'@l))
    | _ -> c
    end
  | a -> c

let same_binder_type ty nal c =
  match nal, DAst.get c with
  | _::_, (GProd (_,_,_,ty',_) | GLambda (_,_,_,ty',_)) -> glob_constr_eq ty ty'
  | [], _ -> true
  | _ -> assert false

(**********************************************************************)
(* mapping glob_constr to numerals (in presence of coercions, choose the *)
(* one with no delimiter if possible)                                 *)

let extern_possible_prim_token ~flags ((custom,_),scopes) r =
   if flags.ExternFlags.raw_literals then raise No_match;
   let (n,key) = uninterp_prim_token ~print_float:flags.float r scopes in
   match availability_of_entry_coercion custom constr_lowest_level with
   | None -> raise No_match
   | Some coercion ->
      insert_entry_coercion coercion (insert_delimiters (CAst.make ?loc:(loc_of_glob_constr r) @@ CPrim n) key)

let filter_enough_applied nargs l =
  (* This is to ensure that notations for coercions are used only when
     the coercion is fully applied; not explicitly done yet, but we
     could also expect that the notation is exactly talking about the
     coercion *)
  match nargs with
  | None -> l
  | Some nargs ->
  List.filter (fun rule ->
      match rule.not_status with
      | AppBoundedNotation n -> n >= nargs
      | AppUnboundedNotation | NotAppNotation -> false) l

(* Helper function for safe and optimal printing of primitive tokens  *)
(* such as those for Int63                                            *)
let extern_prim_token_delimiter_if_required n key_n scope_n scopes =
  match availability_of_prim_token n scope_n scopes with
  | Some None -> CPrim n
  | None -> CDelimiters(DelimUnboundedScope, key_n, CAst.make (CPrim n))
  | Some (Some key) -> CDelimiters(DelimUnboundedScope, key, CAst.make (CPrim n))

(**********************************************************************)
(* mapping decl                                                       *)

let extended_glob_local_binder_of_decl loc = function
  | (p,r,bk,None,t) -> GLocalAssum (p,r,bk,t)
  | (p,r,bk,Some x, t) ->
    assert (bk = Explicit);
    match DAst.get t with
    | GHole (GNamedHole _) -> GLocalDef (p,r,x,Some t)
    | GHole _ -> GLocalDef (p,r,x,None)
    | _ -> GLocalDef (p,r,x,Some t)

let extended_glob_local_binder_of_decl ?loc u = DAst.make ?loc (extended_glob_local_binder_of_decl loc u)

(**********************************************************************)
(* mapping special floats                                             *)

(* this helper function is copied from notation.ml as it's not exported *)
let qualid_of_ref n =
  n |> Rocqlib.lib_ref |> Nametab.shortest_qualid_of_global Id.Set.empty

let q_infinity () = qualid_of_ref "num.float.infinity"
let q_neg_infinity () = qualid_of_ref "num.float.neg_infinity"
let q_nan () = qualid_of_ref "num.float.nan"

let extern_float f scopes =
  if Float64.is_nan f then CRef(q_nan (), None)
  else if Float64.is_infinity f then CRef(q_infinity (), None)
  else if Float64.is_neg_infinity f then CRef(q_neg_infinity (), None)
  else
    let n = NumTok.Signed.of_string (Float64.to_hex_string f) in
    extern_prim_token_delimiter_if_required (Number n)
      "float" "float_scope" scopes

(**********************************************************************)
(* mapping glob_constr to constr_expr                                    *)

type extern_env = {
  vars : Id.Set.t;
  uvars : UnivNames.universe_binders;
  flags : ExternFlags.t;
}
let extern_env ~flags env sigma = {
  vars = vars_of_env env;
  uvars = Evd.universe_binders sigma;
  flags;
}
let empty_extern_env ~flags = {
  vars = Id.Set.empty;
  uvars = UnivNames.empty_binders;
  flags;
}

let on_eenv_vars f eenv = { eenv with vars = f eenv.vars }

let extern_glob_sort_name uvars = function
  | GSProp -> CSProp
  | GProp -> CProp
  | GSet -> CSet
  | GLocalUniv u -> CType (qualid_of_lident u)
  | GRawUniv u -> CRawType u
  | GUniv u -> begin match UnivNames.qualid_of_level uvars u with
      | Some qid -> CType qid
      | None -> CRawType u
    end

let extern_glob_quality uvars = function
  | GLocalQVar {v=Anonymous;loc} -> CQAnon loc
  | GLocalQVar {v=Name id; loc} -> CQVar (qualid_of_ident ?loc id)
  | GRawQVar q -> CRawQuality (QVar q)
  | GQuality q -> begin match UnivNames.qualid_of_quality uvars q with
    | Some qid -> CQVar qid
    | None -> CRawQuality q
    end

let extern_relevance uvars = function
  | GRelevant -> CRelevant
  | GIrrelevant -> CIrrelevant
  | GRelevanceVar q -> CRelevanceVar (extern_glob_quality uvars q)

let extern_relevance_info uvars = Option.map (extern_relevance uvars)

let extern_glob_sort uvars (q, l) =
  Option.map (extern_glob_quality uvars) q,
  map_glob_sort_gen (List.map (on_fst (extern_glob_sort_name uvars))) l

let extern_instance uvars = function
  | Some (ql,ul) ->
    let ql = List.map (extern_glob_quality uvars) ql in
    let ul = List.map (map_glob_sort_gen (extern_glob_sort_name uvars)) ul in
    Some (ql,ul)
  | None -> None

let extern_ref {vars; uvars} ref us =
  extern_global (select_stronger_impargs (implicits_of_global ref))
    (extern_reference vars ref) (extern_instance uvars us)

let extern_var ?loc id = CRef (qualid_of_ident ?loc id,None)

let add_vname eenv na = { eenv with vars = add_vname eenv.vars na }

let rec insert_impargs impargs r = match impargs with
  | [] -> r
  | bk :: rest ->
    match DAst.get r with
    | GProd (na,rinfo,_,t,c) ->
      DAst.make ?loc:r.loc (GProd (na, rinfo, bk, t, insert_impargs rest c))
    | GLetIn (na,rinfo,b,t,c) ->
      DAst.make ?loc:r.loc (GLetIn (na, rinfo, b, t, insert_impargs impargs c))
    | _ -> r

(* Max printing depth is handled by a combination of this and Format's max box depth.

   Strictly speaking we will print an ellipsis for everything which
   has bigger extern depth and everything which has bigger Pp box
   depth than the limit, but in practice extern depth is always
   smaller than box depth.

   As such extern depth acts as an optimization to avoid work on
   subterms which will anyway be ellipsis'd out. *)
type depth = Unlimited | Until of { current : int; max : int }

let max_depth = ref None

let set_max_depth d = max_depth := d

let init_depth flags = match flags.ExternFlags.depth with
  | None -> Unlimited
  | Some max -> Until { current = 0; max }

let succ_depth = function
  | Unlimited -> Some Unlimited
  | Until { current; max } ->
    let current = succ current in
    if Int.equal current max then None
    else Some (Until { current; max })

let ellipsis = Constrexpr.CRef (Libnames.qualid_of_ident (Id.of_string_soft "..."), None)

let rec extern depth0 inctx scopes (eenv:extern_env) r =
  let flags = eenv.flags in
  match succ_depth depth0 with
  | None -> CAst.make ?loc:r.CAst.loc ellipsis
  | Some depth ->
  match remove_one_coercion ~flags inctx (flatten_application r) with
  | Some (nargs,inctx,r') ->
    (try extern_notations depth inctx scopes eenv (Some nargs) r
     with No_match -> extern depth0 inctx scopes eenv r')
  | None ->

  let r' = match DAst.get r with
    | GInt i when Rocqlib.has_ref "num.int63.wrap_int" ->
       let wrap = Rocqlib.lib_ref "num.int63.wrap_int" in
       DAst.make (GApp (DAst.make (GRef (wrap, None)), [r]))
    | GFloat f when Rocqlib.has_ref "num.float.wrap_float" ->
       let wrap = Rocqlib.lib_ref "num.float.wrap_float" in
       DAst.make (GApp (DAst.make (GRef (wrap, None)), [r]))
    | _ -> r in

  try extern_notations depth inctx scopes eenv None r'
  with No_match ->

  let loc = r.CAst.loc in
  match DAst.get r with
  | GRef (ref,us) when entry_has_global (fst (fst scopes)) -> CAst.make ?loc (extern_ref eenv ref us)

  | GVar id when entry_has_global (fst (fst scopes)) || entry_has_ident (fst (fst scopes)) ->
      CAst.make ?loc (extern_var ?loc id)

  | c ->

  match availability_of_entry_coercion (fst (fst scopes)) constr_lowest_level with
  | None -> raise No_match
  | Some coercion ->

  let scopes = ((constr_some_level, None), snd scopes) in
  let c = match c with

  (* The remaining cases are only for the constr entry *)

  | GRef (ref,us) -> extern_ref eenv ref us

  | GVar id -> extern_var ?loc id

  | GEvar (n,l) ->
      extern_evar n (List.map (on_snd (extern depth false scopes eenv)) l)

  | GPatVar kind ->
    (match kind with
     | Evar_kinds.SecondOrderPatVar n -> CPatVar n
     | Evar_kinds.FirstOrderPatVar n -> CEvar (CAst.make n,[]))

  | GApp (f,args) ->
      (match DAst.get f with
         | GRef (ref,us) ->
             let subscopes = find_arguments_scope (Global.env ()) ref in
             let args = fill_arg_scopes args subscopes (snd scopes) in
             let args = extern_args (extern depth true) eenv args in
             (* Try a "{|...|}" record notation *)
             (match extern_record ~flags ref args with
             | Some l -> CRecord (None, l)
             | None ->
             (* Otherwise... *)
               extern_applied_ref ~flags inctx
                 (select_stronger_impargs (implicits_of_global ref))
                 (ref,extern_reference ?loc eenv.vars ref) (extern_instance eenv.uvars us) args)
         | GProj (f,params,c) ->
             extern_applied_proj depth inctx scopes eenv f params c args
         | _ ->
             let args = List.map (fun c -> (sub_extern depth true scopes eenv c,None)) args in
             let head = sub_extern depth false scopes eenv f in
             mkFlattenedCApp (head,args))

  | GProj (f,params,c) ->
      extern_applied_proj depth inctx scopes eenv f params c []

  | GLetIn (na,_,b,t,c) ->
    CLetIn (make ?loc na,
            sub_extern depth (Option.has_some t) scopes eenv b,
            Option.map (extern_typ depth scopes eenv) t,
            extern depth inctx scopes (add_vname eenv na) c)

  | GProd (na,r,bk,t,c) ->
      factorize_prod depth scopes eenv na r bk t c

  | GLambda (na,r,bk,t,c) ->
      factorize_lambda depth inctx scopes eenv na r bk t c

  | GCases (sty,rtntypopt,tml,eqns) ->
    let vars' =
      List.fold_right (Name.fold_right Id.Set.add)
        (cases_predicate_names tml) eenv.vars in
    let eenv' = { eenv with vars = vars' } in
    let rtntypopt' = Option.map (extern_typ depth scopes eenv') rtntypopt in
    let tml = List.map (fun (tm,(na,x)) ->
                 let na' = match na, DAst.get tm with
                   | Anonymous, GVar id ->
                      begin match rtntypopt with
                            | None -> None
                            | Some ntn ->
                               if occur_glob_constr id ntn then
                                 Some (CAst.make Anonymous)
                               else None
                      end
                   | Anonymous, _ -> None
                   | Name id, GVar id' when Id.equal id id' -> None
                   | Name _, _ -> Some (CAst.make na) in
                 (sub_extern depth false scopes eenv tm,
                  na',
                  Option.map (fun {CAst.loc;v=(ind,nal)} ->
                              let args = List.map (fun x -> DAst.make @@ PatVar x) nal in
                              let fullargs = add_cpatt_for_params ind args in
                              extern_ind_pattern_in_scope ~flags scopes eenv.vars ind fullargs
                             ) x))
                tml
    in
    let eqns =
      List.map (extern_eqn depth (inctx || rtntypopt <> None) scopes eenv)
        (factorize_eqns ~flags:eenv.flags.factorize_eqns eqns)
    in
    CCases (sty,rtntypopt',tml,eqns)

  | GLetTuple (nal,(na,typopt),tm,b) ->
      let inctx = inctx || typopt <> None in
      CLetTuple (List.map CAst.make nal,
        (Option.map (fun _ -> (make na)) typopt,
         Option.map (extern_typ depth scopes (add_vname eenv na)) typopt),
        sub_extern depth false scopes eenv tm,
        extern depth inctx scopes (List.fold_left add_vname eenv nal) b)

  | GIf (c,(na,typopt),b1,b2) ->
      let inctx = inctx || typopt <> None in
      CIf (sub_extern depth false scopes eenv c,
        (Option.map (fun _ -> (CAst.make na)) typopt,
         Option.map (extern_typ depth scopes (add_vname eenv na)) typopt),
        sub_extern depth inctx scopes eenv b1, sub_extern depth inctx scopes eenv b2)

  | GRec (fk,idv,blv,tyv,bv) ->
      let eenv' = on_eenv_vars (Array.fold_right Id.Set.add idv) eenv in
      (match fk with
         | GFix (nv,n) ->
             let listdecl =
               Array.mapi (fun i fi ->
                 let (bl,ty,def) = blv.(i), tyv.(i), bv.(i) in
                 let bl = List.map (extended_glob_local_binder_of_decl ?loc) bl in
                 let (assums,ids,bl) = extern_local_binder depth scopes eenv bl in
                 let eenv0 = on_eenv_vars (List.fold_right (Name.fold_right Id.Set.add) ids) eenv in
                 let eenv1 = on_eenv_vars (List.fold_right (Name.fold_right Id.Set.add) ids) eenv' in
                 let n =
                   match nv.(i) with
                   | None -> None
                   | Some x -> Some (CAst.make @@ CStructRec (CAst.make @@ Name.get_id (List.nth assums x)))
                             in
                 ((CAst.make fi), None, n, bl, extern_typ depth scopes eenv0 ty,
                  sub_extern depth true scopes eenv1 def)) idv
             in
             CFix (CAst.(make ?loc idv.(n)), Array.to_list listdecl)
         | GCoFix n ->
             let listdecl =
               Array.mapi (fun i fi ->
                 let bl = List.map (extended_glob_local_binder_of_decl ?loc) blv.(i) in
                 let (_,ids,bl) = extern_local_binder depth scopes eenv bl in
                 let eenv0 = on_eenv_vars (List.fold_right (Name.fold_right Id.Set.add) ids) eenv in
                 let eenv1 = on_eenv_vars (List.fold_right (Name.fold_right Id.Set.add) ids) eenv' in
                 ((CAst.make fi),None,bl,extern_typ depth scopes eenv0 tyv.(i),
                  sub_extern depth true scopes eenv1 bv.(i))) idv
             in
             CCoFix (CAst.(make ?loc idv.(n)),Array.to_list listdecl))

  | GSort s -> CSort (extern_glob_sort eenv.uvars s)

  | GHole e -> CHole (Some e)

  | GGenarg arg -> CGenargGlob arg

  | GCast (c, k, c') ->
    let scl = Notation.compute_glob_type_scope c' in
    let c' = extern_typ depth scopes eenv c' in
    let c = extern depth true (fst scopes,(scl, snd (snd scopes))) eenv c in
    CCast (c, k, c')

  | GInt i ->
     extern_prim_token_delimiter_if_required
       (Number NumTok.(Signed.of_bigint CHex (Z.of_int64 (Uint63.to_int64 i))))
       "uint63" "uint63_scope" (snd scopes)

  | GFloat f -> extern_float f (snd scopes)

  | GString s ->
     extern_prim_token_delimiter_if_required
       (String (Pstring.to_string s))
       "pstring" "pstring_scope" (snd scopes)

  | GArray(u,t,def,ty) ->
    CArray(
      extern_instance eenv.uvars u,
      Array.map (extern depth inctx scopes eenv) t,
      extern depth inctx scopes eenv def,
      extern_typ depth scopes eenv ty)

  in insert_entry_coercion coercion (CAst.make ?loc c)

and extern_typ depth (subentry,(_,scopes)) =
  extern depth true (subentry,(Notation.current_type_scope_names (),scopes))

and sub_extern depth inctx (subentry,(_,scopes)) = extern depth inctx (subentry,([],scopes))

and factorize_prod depth scopes eenv na r bk t c =
  let implicit_type = is_reserved_type ~flags:eenv.flags na t in
  let r = extern_relevance_info eenv.uvars r in
  let aty = extern_typ depth scopes eenv t in
  let eenv = add_vname eenv na in
  let store, get = set_temporary_memory () in
  match na, DAst.get c with
  | Name id, GCases (Constr.LetPatternStyle, None, [(e,(Anonymous,None))],(_::_ as eqns))
         when is_gvar id e && List.length (store (factorize_eqns ~flags:eenv.flags.factorize_eqns eqns)) = 1 ->
    (match get () with
     | [{CAst.v=(ids,disj_of_patl,b)}] ->
      let disjpat = List.map (function [pat] -> pat | _ -> assert false) disj_of_patl in
      let disjpat = if occur_glob_constr id b then List.map (set_pat_alias id) disjpat else disjpat in
      let b = extern_typ depth scopes eenv b in
      let p = mkCPatOr (List.map (extern_cases_pattern_in_scope ~flags:eenv.flags scopes eenv.vars) disjpat) in
      let binder = CLocalPattern p in
      (match b.v with
      | CProdN (bl,b) -> CProdN (binder::bl,b)
      | _ -> CProdN ([binder],b))
     | _ -> assert false)
  | _, _ ->
      let c' = extern_typ depth scopes eenv c in
      match na, c'.v with
      | Name id, CProdN (CLocalAssum(nal,r',Default bk',ty)::bl,b)
        when relevance_info_expr_eq r r'
            && binding_kind_eq bk bk'
            && not (occur_var_constr_expr id ty) (* avoid na in ty escapes scope *)
            && (constr_expr_eq aty ty || (constr_expr_eq ty hole && same_binder_type t nal c)) ->
        let ty = if implicit_type then ty else aty in
        CProdN (CLocalAssum(make na::nal,r,Default bk,ty)::bl,b)
      | _, CProdN (bl,b) ->
         let ty = if implicit_type then hole else aty in
         CProdN (CLocalAssum([make na],r,Default bk,ty)::bl,b)
      | _, _ ->
         let ty = if implicit_type then hole else aty in
         CProdN ([CLocalAssum([make na],r,Default bk,ty)],c')

and factorize_lambda depth inctx scopes eenv na r bk t c =
  let implicit_type = is_reserved_type ~flags:eenv.flags na t in
  let r = extern_relevance_info eenv.uvars r in
  let aty = extern_typ depth scopes eenv t in
  let eenv = add_vname eenv na in
  let store, get = set_temporary_memory () in
  match na, DAst.get c with
  | Name id, GCases (Constr.LetPatternStyle, None, [(e,(Anonymous,None))],(_::_ as eqns))
         when is_gvar id e && List.length (store (factorize_eqns ~flags:eenv.flags.factorize_eqns eqns)) = 1 ->
    (match get () with
     | [{CAst.v=(ids,disj_of_patl,b)}] ->
      let disjpat = List.map (function [pat] -> pat | _ -> assert false) disj_of_patl in
      let disjpat = if occur_glob_constr id b then List.map (set_pat_alias id) disjpat else disjpat in
      let b = sub_extern depth inctx scopes eenv b in
      let p = mkCPatOr (List.map (extern_cases_pattern_in_scope ~flags:eenv.flags scopes eenv.vars) disjpat) in
      let binder = CLocalPattern p in
      (match b.v with
      | CLambdaN (bl,b) -> CLambdaN (binder::bl,b)
      | _ -> CLambdaN ([binder],b))
     | _ -> assert false)
  | _, _ ->
      let c' = sub_extern depth inctx scopes eenv c in
      match c'.v with
      | CLambdaN (CLocalAssum(nal,r',Default bk',ty)::bl,b)
        when relevance_info_expr_eq r r'
          && binding_kind_eq bk bk'
          && not (occur_name na ty)  (* avoid na in ty escapes scope *)
          && (constr_expr_eq aty ty || (constr_expr_eq ty hole && same_binder_type t nal c)) ->
        let aty = if implicit_type then ty else aty in
        CLambdaN (CLocalAssum(make na::nal,r,Default bk,aty)::bl,b)
      | CLambdaN (bl,b) ->
         let ty = if implicit_type then hole else aty in
         CLambdaN (CLocalAssum([make na],r,Default bk,ty)::bl,b)
      | _ ->
         let ty = if implicit_type then hole else aty in
         CLambdaN ([CLocalAssum([make na],r,Default bk,ty)],c')

and extern_local_binder depth scopes eenv = function
    [] -> ([],[],[])
  | b :: l ->
    match DAst.get b with
    | GLocalDef (na,r,bd,ty) ->
      let (assums,ids,l) =
        extern_local_binder depth scopes (on_eenv_vars (Name.fold_right Id.Set.add na) eenv) l in
      (assums,na::ids,
       CLocalDef(CAst.make na, extern_relevance_info eenv.uvars r, extern depth false scopes eenv bd,
                   Option.map (extern_typ depth scopes eenv) ty) :: l)

    | GLocalAssum (na,r,bk,ty) ->
      let implicit_type = is_reserved_type ~flags:eenv.flags na ty in
      let ty = extern_typ depth scopes eenv ty in
      (match extern_local_binder depth scopes (on_eenv_vars (Name.fold_right Id.Set.add na) eenv) l with
       | (assums,ids,CLocalAssum(nal,r',k,ty')::l)
         when (constr_expr_eq ty ty' || implicit_type && constr_expr_eq ty' hole) &&
              binder_kind_eq k (Default bk) &&
              match na with Name id -> not (occur_var_constr_expr id ty')
                          | _ -> true ->
         (na::assums,na::ids,
          CLocalAssum(CAst.make na::nal,r',k,ty')::l)
       | (assums,ids,l) ->
         let ty = if implicit_type then hole else ty in
         (na::assums,na::ids,
          CLocalAssum([CAst.make na],extern_relevance_info eenv.uvars r,Default bk,ty) :: l))

    | GLocalPattern ((p,_),_,bk,_) ->
      let p = mkCPatOr (List.map (extern_cases_pattern ~flags:eenv.flags eenv.vars) p) in
      let (assums,ids,l) = extern_local_binder depth scopes eenv l in
      (assums,ids, CLocalPattern p :: l)

and extern_eqn depth inctx scopes eenv {CAst.loc;v=(ids,pll,c)} =
  let pll = List.map (List.map (extern_cases_pattern_in_scope ~flags:eenv.flags scopes eenv.vars)) pll in
  make ?loc (pll,extern depth inctx scopes eenv c)

and extern_notations depth inctx scopes eenv nargs t =
  try extern_possible_prim_token ~flags:eenv.flags scopes t
  with No_match ->
    if not eenv.flags.notations then raise No_match;
    let t = flatten_application t in
    extern_notation depth inctx scopes eenv t (filter_enough_applied nargs (uninterp_notations (Global.env ()) t))

and extern_notation depth inctx ((custom,(lev_after: int option)),scopes as allscopes) eenv t rules =
  match rules with
  | [] -> raise No_match
  | { not_rule = keyrule; not_patt = pat; not_status = n } :: rules ->
      let loc = Glob_ops.loc_of_glob_constr t in
      try
        if is_printing_inactive_rule keyrule pat then raise No_match;
        let f,args =
          match DAst.get t with
          | GApp (f,args) -> f,args
          | _ -> t,[] in
        let nallargs = List.length args in
        let argsscopes,argsimpls =
          match DAst.get f with
          | GRef (ref,_) ->
            let subscopes = find_arguments_scope (Global.env ()) ref in
            let impls = select_stronger_impargs (implicits_of_global ref) in
            subscopes, impls
          | _ ->
            [], [] in
        (* Adjust to the number of arguments expected by the notation *)
        let (t,args,argsscopes,argsimpls) = match n with
          | AppBoundedNotation n when nallargs >= n ->
              let args1, args2 = List.chop n args in
              let args2scopes = try List.skipn n argsscopes with Failure _ -> [] in
              let args2impls =
                if n = 0 then
                  (* Note: NApp(NRef f,[]), hence n=0, encodes @f and
                     conventionally deactivates implicit arguments *)
                  []
                else try List.skipn n argsimpls with Failure _ -> [] in
              DAst.make @@ GApp (f,args1), args2, args2scopes, args2impls
          | AppUnboundedNotation -> t, [], [], []
          | NotAppNotation ->
            begin match DAst.get f with
            | GRef (ref,us) -> f, args, argsscopes, argsimpls
            | _ -> t, [], [], []
            end
          | AppBoundedNotation _ -> raise No_match in
        (* Try matching ... *)
        let terms,termlists,binders,binderlists =
          match_notation_constr
            ~print_parentheses:eenv.flags.parentheses
            ~factorize_eqns:eenv.flags.factorize_eqns
            t ~vars:eenv.vars pat
        in
        let lev_after = if List.is_empty args then lev_after else Some Notation.app_level in
        (* Try externing extra args... *)
        let extra_args =
          let args = fill_arg_scopes args argsscopes (snd allscopes) in
          let args = extern_args (extern depth true) eenv args in
          try UseCApp (adjust_implicit_arguments ~flags:eenv.flags inctx nallargs args argsimpls) with Expl -> UseCAppExpl args in
        (* Try availability of interpretation ... *)
        match keyrule with
          | NotationRule (_,ntn as specific_ntn) ->
            let entry = fst (Notation.level_of_notation ntn) in
            let non_included = overlap_right_left entry lev_after pat in
            let coercion, appcoercion = find_entry_coercion_with_application ~non_included custom entry (is_empty_extra_args extra_args) in
            (match availability_of_notation specific_ntn scopes with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
              | Some (scopt,key) ->
                  let closed = not (List.is_empty coercion) in
                  let scopes' = Option.List.cons scopt (snd scopes) in
                  let l =
                    List.map (fun ((vars,c),subscope) ->
                      let scopes = update_with_subscope ~flags:eenv.flags entry subscope lev_after closed scopes' in
                      extern depth (* assuming no overloading: *) true scopes { eenv with vars} c)
                      terms
                  in
                  let ll =
                    List.map (fun ((vars,l),subscope) ->
                      let scopes = update_with_subscope ~flags:eenv.flags entry subscope lev_after closed scopes' in
                      List.map (extern depth true scopes { eenv with vars }) l)
                      termlists
                  in
                  let bl =
                    List.map (fun ((vars,bl),subscope) ->
                      let scopes = update_with_subscope ~flags:eenv.flags entry subscope lev_after closed scopes' in
                      (mkCPatOr
                         (List.map
                            (extern_cases_pattern_in_scope ~flags:eenv.flags scopes vars) bl)),
                        Explicit)
                      binders
                  in
                  let bll =
                    List.map (fun ((vars,bl),subscope) ->
                      let scopes = update_with_subscope ~flags:eenv.flags entry subscope lev_after closed scopes' in
                      pi3 (extern_local_binder depth scopes { eenv with vars } bl))
                      binderlists
                  in
                  let c = make_notation loc specific_ntn (l,ll,bl,bll) in
                  let c = insert_entry_coercion coercion (insert_delimiters c key) in
                  insert_entry_coercion appcoercion (CAst.make ?loc @@ extern_applied_notation c extra_args))
          | AbbrevRule kn ->
              let l =
                List.map (fun ((vars,c),(subentry,(scopt,scl))) ->
                  extern depth true ((subentry,lev_after),(scopt,scl@snd scopes)) { eenv with vars } c)
                  terms
              in
              let cf = Nametab.shortest_qualid_of_abbreviation ?loc eenv.vars kn in
              let a = CRef (cf,None) in
              let c = CAst.make ?loc @@ extern_applied_abbreviation (a,cf) l extra_args in
              if isCRef_no_univ c.CAst.v && entry_has_global custom then c
              else match availability_of_entry_coercion custom constr_lowest_level with
                | None -> raise No_match
                | Some coercion -> insert_entry_coercion coercion c
      with
          No_match -> extern_notation depth inctx allscopes eenv t rules

and extern_applied_proj depth inctx scopes eenv (cst,us) params c extraargs =
  let ref = GlobRef.ConstRef cst in
  let subscopes = find_arguments_scope (Global.env ()) ref in
  let nparams = List.length params in
  let args = params @ c :: extraargs in
  let args = fill_arg_scopes args subscopes (snd scopes) in
  let args = extern_args (extern depth true) eenv args in
  let imps = select_stronger_impargs (implicits_of_global ref) in
  let f = extern_reference eenv.vars ref in
  let us = extern_instance eenv.uvars us in
  extern_projection ~flags:eenv.flags inctx (f,us) nparams args imps

let extern inctx scopes eenv c : constr_expr = extern (init_depth eenv.flags) inctx scopes eenv c

let extern_glob_constr eenv c =
  extern false ((constr_some_level,None),([],[])) eenv c

let extern_glob_type ?impargs eenv c =
  let c = Option.fold_right insert_impargs impargs c in
  extern_typ (init_depth eenv.flags) ((constr_some_level,None),([],[])) eenv c

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let extern_constr ?(inctx=false) ?scope ~(flags:PrintingFlags.t) env sigma t =
  let r = Detyping.detype Detyping.Later ~flags:flags.detype env sigma t in
  let eenv = extern_env ~flags:flags.extern env sigma in
  let scope = Option.cata (fun x -> [x]) [] scope in
  extern inctx ((constr_some_level,None),(scope,[])) eenv r

let extern_constr_in_scope ?inctx scope ~flags env sigma t =
  extern_constr ?inctx ~scope ~flags env sigma t

let make_avoid goal_concl_style env =
  if goal_concl_style then (Namegen.Generator.fresh, Fresh.of_set @@ vars_of_env env)
  (* TODO: this is linear in the size of the environment, maybe we can do better *)
  else (Namegen.Generator.fresh, Nameops.Fresh.empty)

let extern_type ?(goal_concl_style=false) ~(flags:PrintingFlags.t) env sigma ?impargs t =
  (* "goal_concl_style" means do alpha-conversion using the "goal" convention *)
  (* i.e.: avoid using the names of goal/section/rel variables and the short *)
  (* names of global definitions of current module when computing names for *)
  (* bound variables. *)
  (* Not "goal_concl_style" means do alpha-conversion avoiding only *)
  (* those goal/section/rel variables that occurs in the subterm under *)
  (* consideration; see namegen.ml for further details *)
  let avoid = make_avoid goal_concl_style env in
  let r = Detyping.detype Detyping.Later ~isgoal:goal_concl_style ~avoid ~flags:flags.detype env sigma t in
  extern_glob_type ?impargs (extern_env ~flags:flags.extern env sigma) r

let extern_sort ~universes ~sorts ~qualities sigma s =
  extern_glob_sort (Evd.universe_binders sigma)
    (detype_sort ~universes ~sorts ~qualities sigma s)

let extern_closed_glob ?(goal_concl_style=false) ?(inctx=false) ?scope ~(flags:PrintingFlags.t) env sigma t =
  let avoid = make_avoid goal_concl_style env in
  let r =
    Detyping.detype_closed_glob ~isgoal:goal_concl_style ~avoid ~flags:flags.detype env sigma t
  in
  let eenv = extern_env env sigma ~flags:flags.extern in
  let scope = Option.cata (fun x -> [x]) [] scope in
  extern inctx ((constr_some_level,None),(scope,[])) eenv r

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

(* thunk for value restriction *)
let any_any_branch () =
  (* | _ => _ *)
  CAst.make ([],[DAst.make @@ PatVar Anonymous], DAst.make @@ GHole (GInternalHole))

let genset = Namegen.Generator.idset

let next_name_away na (gen, avoid) =
  let (id, avoid) = Namegen.Generator.next_name_away gen na avoid in
  (id, (gen, avoid))

let compute_displayed_let_name_in env sigma flags (gen, avoid) na =
  let open Namegen in
  let na, avoid = compute_displayed_let_name_in gen env sigma flags avoid na in
  na, (gen, avoid)

let compute_displayed_name_in_pattern env sigma (gen, avoid) na c =
  let open Namegen in
  let na, avoid = compute_displayed_name_in_gen gen (fun _ -> Patternops.noccurn_pattern) env sigma avoid na c in
  na, (gen, avoid)

let glob_of_pat_under_context glob_of_pat avoid env sigma (nas, pat) =
  let fold (avoid, env, nas, epat) na =
    let na, avoid = compute_displayed_name_in_pattern (Global.env ()) sigma avoid na epat in
    let env = Termops.add_name na env in
    let epat = match epat with PLambda (_, _, p) -> p | _ -> assert false in
    (avoid, env, na :: nas, epat)
  in
  let epat = Array.fold_right (fun na p -> PLambda (na, PMeta None, p)) nas pat in
  let (avoid', env', nas, _) = Array.fold_left fold (avoid, env, [], epat) nas in
  let pat = glob_of_pat avoid' env' sigma pat in
  (Array.rev_of_list nas, pat)

let rec glob_of_pat
  : 'a 'g 's. ('a -> 'g glob_constr_r) -> 's Namegen.Generator.input -> _ -> _ -> 'a constr_pattern_r -> 'g glob_constr_g
  = fun (type a g s) (of_extra:a -> g glob_constr_r) (avoid : s Namegen.Generator.t * s) env sigma (pat: a constr_pattern_r) ->
  let open Sorts.Quality in
    DAst.make @@ match pat with
  | PRef ref -> GRef (ref,None)
  | PVar id  -> GVar id
  | PEvar (evk,l) ->
      let filter (id, pat) = match pat with PVar id' -> Id.equal id id' | _ -> true in
      let EvarInfo evi = Evd.find sigma evk in
      let hyps = Evd.evar_filtered_context evi in
      let map decl pat = NamedDecl.get_id decl, pat in
      let l = List.filter filter @@ List.map2 map hyps l in
      let id = match Evd.evar_ident evk sigma with
      | None -> "__"
      | Some id -> Libnames.string_of_path id
      in
      let id = Id.of_string_soft id in
      GEvar (CAst.make id,List.map (fun (id,c) -> (CAst.make id, glob_of_pat of_extra avoid env sigma c)) l)
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
        | Name id   -> id
        | Anonymous ->
            anomaly ~label:"glob_constr_of_pattern" (Pp.str "index to an anonymous variable.")
      with Not_found -> Id.of_string ("_UNBOUND_REL_"^(string_of_int n)) in
      GVar id
  | PMeta None -> GHole (GInternalHole)
  | PMeta (Some n) -> GPatVar (Evar_kinds.FirstOrderPatVar n)
  | PExtra g -> of_extra g
  | PProj (p,c) -> GApp (DAst.make @@ GRef (GlobRef.ConstRef (Environ.projection_repr_constant (Global.env ()) (Projection.repr p)),None),
                         [glob_of_pat of_extra avoid env sigma c])
  | PApp (f,args) ->
      GApp (glob_of_pat of_extra avoid env sigma f,Array.map_to_list (glob_of_pat of_extra avoid env sigma) args)
  | PSoApp (n,args) ->
      GApp (DAst.make @@ GPatVar (Evar_kinds.SecondOrderPatVar n),
        List.map (glob_of_pat of_extra avoid env sigma) args)
  | PProd (na,t,c) ->
      let na',avoid' = compute_displayed_name_in_pattern (Global.env ()) sigma avoid na c in
      let env' = Termops.add_name na' env in
      GProd (na',None,Explicit,glob_of_pat of_extra avoid env sigma t,glob_of_pat of_extra avoid' env' sigma c)
  | PLetIn (na,b,t,c) ->
      let na',avoid' = compute_displayed_let_name_in (Global.env ()) sigma Namegen.RenamingForGoal avoid na in
      let env' = Termops.add_name na' env in
      GLetIn (na',None,glob_of_pat of_extra avoid env sigma b, Option.map (glob_of_pat of_extra avoid env sigma) t,
              glob_of_pat of_extra avoid' env' sigma c)
  | PLambda (na,t,c) ->
      let na',avoid' = compute_displayed_name_in_pattern (Global.env ()) sigma avoid na c in
      let env' = Termops.add_name na' env in
      GLambda (na',None,Explicit,glob_of_pat of_extra avoid env sigma t, glob_of_pat of_extra avoid' env' sigma c)
  | PIf (c,b1,b2) ->
      GIf (glob_of_pat of_extra avoid env sigma c, (Anonymous,None),
           glob_of_pat of_extra avoid env sigma b1, glob_of_pat of_extra avoid env sigma b2)
  | PCase ({cip_style=Constr.LetStyle},None,tm,[(0,n,b)]) ->
      let n, b = glob_of_pat_under_context (glob_of_pat of_extra) avoid env sigma (n, b) in
      let nal = Array.to_list n in
      GLetTuple (nal,(Anonymous,None),glob_of_pat of_extra avoid env sigma tm,b)
  | PCase (info,p,tm,bl) ->
      let mat = match bl, info.cip_ind with
        | [], _ -> []
        | _, Some ind ->
          let map (i, n, c) =
            let n, c = glob_of_pat_under_context (glob_of_pat of_extra) avoid env sigma (n, c) in
            let nal = Array.to_list n in
            let mkPatVar na = DAst.make @@ PatVar na in
            let p = DAst.make @@ PatCstr ((ind,i+1),List.map mkPatVar nal,Anonymous) in
            let ids = List.map_filter Nameops.Name.to_option nal in
            CAst.make @@ (ids,[p],c)
          in
          List.map map bl
        | _, None -> anomaly (Pp.str "PCase with some branches but unknown inductive.")
      in
      let mat = if info.cip_extensible then mat @ [any_any_branch ()] else mat
      in
      let indnames,rtn = match p, info.cip_ind with
        | None, _ -> (Anonymous,None),None
        | Some p, Some ind ->
          let nas, p = glob_of_pat_under_context (glob_of_pat of_extra) avoid env sigma p in
          let nas = Array.rev_to_list nas in
          ((List.hd nas, Some (CAst.make (ind, List.tl nas))), Some p)
        | _ -> anomaly (Pp.str "PCase with non-trivial predicate but unknown inductive.")
      in
      GCases (Constr.MatchStyle,rtn,[glob_of_pat of_extra avoid env sigma tm,indnames],mat)
  | PFix ((ln,i),(lna,tl,bl)) ->
     let def_avoid, def_env, lfi =
       Array.fold_left
         (fun (avoid, env, l) na ->
           let id, avoid = next_name_away na avoid in
           (avoid, Name id :: env, id::l))
      (avoid, env, []) lna in
     let n = Array.length tl in
     let v = Array.map3
               (fun c t i -> Detyping.share_pattern_names (glob_of_pat of_extra) (i+1) [] def_avoid def_env sigma c (Patternops.lift_pattern n t))
    bl tl ln in
     GRec(GFix (Array.map (fun i -> Some i) ln,i),Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)
  | PCoFix (ln,(lna,tl,bl)) ->
     let def_avoid, def_env, lfi =
       Array.fold_left
         (fun (avoid, env, l) na ->
           let id, avoid = next_name_away na avoid in
           (avoid, Name id :: env, id::l))
         (avoid, env, []) lna in
     let ntys = Array.length tl in
     let v = Array.map2
               (fun c t -> share_pattern_names (glob_of_pat of_extra) 0 [] def_avoid def_env sigma c (Patternops.lift_pattern ntys t))
               bl tl in
     GRec(GCoFix ln,Array.of_list (List.rev lfi),
          Array.map (fun (bl,_,_) -> bl) v,
          Array.map (fun (_,_,ty) -> ty) v,
          Array.map (fun (_,bd,_) -> bd) v)
  | PSort (Qual (QConstant QSProp)) -> GSort Glob_ops.glob_SProp_sort
  | PSort (Qual (QConstant QProp)) -> GSort Glob_ops.glob_Prop_sort
  | PSort (Qual (QConstant QType | QVar _)) -> GSort Glob_ops.glob_Type_sort
  | PSort (Qual (QGlobal _ as q)) -> GSort (Some (GQuality q), Glob_ops.glob_rigid_univ)
  | PSort Set -> GSort Glob_ops.glob_Set_sort
  | PInt i -> GInt i
  | PFloat f -> GFloat f
  | PString s -> GString s
  | PArray(t,def,ty) ->
    let glob_of = glob_of_pat of_extra avoid env sigma in
    GArray (None, Array.map glob_of t, glob_of def, glob_of ty)

let extern_constr_pattern_gen of_extra ~flags env sigma pat =
  extern true ((constr_some_level,None),([],[]))
    (* XXX no vars? *)
    { vars = Id.Set.empty; uvars = Evd.universe_binders sigma; flags }
    (glob_of_pat of_extra (genset, Id.Set.empty) env sigma pat)

let extern_constr_pattern ~flags env sigma pat =
  let of_extra e = Util.Empty.abort e in
  extern_constr_pattern_gen of_extra ~flags env sigma pat

let extern_uninstantiated_pattern ~flags env sigma pat =
  let of_extra g = GGenarg g in
  extern_constr_pattern_gen of_extra ~flags env sigma pat

let extern_rel_context ~(flags:PrintingFlags.t) env sigma sign =
  let a = detype_rel_context Detyping.Later ~flags:flags.detype ([],env) sigma sign in
  let eenv = extern_env env sigma ~flags:flags.extern in
  let a = List.map (extended_glob_local_binder_of_decl) a in
  pi3 (extern_local_binder (init_depth eenv.flags) ((constr_some_level,None),([],[])) eenv a)
