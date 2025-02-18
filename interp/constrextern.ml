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
open Pp
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

module NamedDecl = Context.Named.Declaration
(*i*)

(* Translation from glob_constr to front constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how implicit args are printed. If on, implicit args are printed
   with the form (id:=arg) otherwise arguments are printed normally and
   the function is prefixed by "@" *)
let print_implicits = ref false
let print_implicits_explicit_args = ref false

(* Tells if implicit arguments not known to be inferable from a rigid
   position are systematically printed *)
let print_implicits_defensive = ref true

(* This forces printing of coercions *)
let print_coercions = ref false

(* This forces printing of parentheses even when
   it is implied by associativity/precedence *)
let print_parentheses = Notation_ops.print_parentheses

(* This forces printing universe names of Type{.} *)
let print_universes = Detyping.print_universes

(* This suppresses printing of notations *)
let print_no_symbol = ref false

(* This tells to skip types if a variable has this type by default *)
let { Goptions.get = print_use_implicit_types } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Use";"Implicit";"Types"]
    ~value:true
    ()

(* Print primitive tokens, like strings *)
let print_raw_literal = ref false

(**********************************************************************)

let hole = CAst.make @@ CHole (None)

let is_reserved_type na t =
  not !Flags.raw_print && print_use_implicit_types () &&
  match na with
  | Anonymous -> false
  | Name id ->
    try
      let pat = Reserve.find_reserved_type id in
      let _ = match_notation_constr ~print_univ:false t ~vars:Id.Set.empty ([],pat) in
      true
    with Not_found | No_match -> false

(**********************************************************************)
(* Turning notations and scopes on and off for printing *)
(* This governs printing of projections using the dot notation symbols *)
let print_projections = ref false

let print_meta_as_hole = ref false

let with_universes f = Flags.with_option print_universes f
let with_meta_as_hole f = Flags.with_option print_meta_as_hole f
let without_symbols f = Flags.with_option print_no_symbol f

(**********************************************************************)
(* Control printing of records *)

(* Set Record Printing flag *)
let { Goptions.get = get_record_print } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Records"]
    ~value:true
    ()

let is_record indsp =
  try
    let _ = Structure.find indsp in
    true
  with Not_found -> false

let encode_record r =
  let indsp = Nametab.global_inductive r in
  if not (is_record indsp) then
    user_err ?loc:r.CAst.loc
      (str "This type is not a structure type.");
  indsp

module PrintingRecordRecord =
  PrintingInductiveMake (struct
    let encode _env = encode_record
    let field = "Record"
    let title = "Types leading to pretty-printing using record notation: "
    let member_message s b =
      str "Terms of " ++ s ++
      str
      (if b then " are printed using record notation"
      else " are not printed using record notation")
  end)

module PrintingRecordConstructor =
  PrintingInductiveMake (struct
    let encode _env = encode_record
    let field = "Constructor"
    let title = "Types leading to pretty-printing using constructor form: "
    let member_message s b =
      str "Terms of " ++ s ++
      str
      (if b then " are printed using constructor form"
      else " are not printed using constructor form")
  end)

module PrintingRecord = Goptions.MakeRefTable(PrintingRecordRecord)
module PrintingConstructor = Goptions.MakeRefTable(PrintingRecordConstructor)

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

let rec dirpath_of_modpath = function
  | MPfile dp -> dp
  | MPbound mbid -> let (_,id,_) = MBId.repr mbid in DirPath.make [id]
  | MPdot (t, l) -> Libnames.add_dirpath_suffix (dirpath_of_modpath t) (Label.to_id l)

let path_of_global = function
  | GlobRef.VarRef id -> Libnames.make_path DirPath.empty id
  (* We rely on the tacite invariant that the label of a constant is used to build its internal name *)
  | GlobRef.ConstRef cst -> Libnames.make_path (dirpath_of_modpath (Constant.modpath cst)) (Label.to_id (Constant.label cst))
  (* We rely on the tacite invariant that an inductive block inherits the name of its first type *)
  | GlobRef.IndRef (ind,1) -> Libnames.make_path (dirpath_of_modpath (MutInd.modpath ind)) (Label.to_id (MutInd.label ind))
  (* These are hacks *)
  | GlobRef.IndRef (ind,n) -> Libnames.make_path (dirpath_of_modpath (MutInd.modpath ind)) (Id.of_string_soft ("<inductive:" ^ Label.to_string (MutInd.label ind) ^ ":" ^ string_of_int n ^ ">"))
  | GlobRef.ConstructRef ((ind,1),p) -> Libnames.make_path (dirpath_of_modpath (MutInd.modpath ind)) (Id.of_string_soft ("<constructor:" ^ Label.to_string (MutInd.label ind) ^ ":" ^ string_of_int (p+1) ^ ">"))
  | GlobRef.ConstructRef ((ind,n),p) -> Libnames.make_path (dirpath_of_modpath (MutInd.modpath ind)) (Id.of_string_soft ("<constructor:" ^ Label.to_string (MutInd.label ind) ^ ":" ^ string_of_int n ^ ":" ^ string_of_int (p+1) ^ ">"))

let default_extern_reference ?loc vars r =
  try Nametab.shortest_qualid_of_global ?loc vars r
  with Not_found when GlobRef.is_bound r -> qualid_of_path (path_of_global r)

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

let update_with_subscope from_entry (entry,(scopt,scl)) lev_after closed scopes =
  let {notation_subentry = entry; notation_relative_level = lev; notation_position = side} = entry in
  let lev = if !print_parentheses && side <> None then LevelLe 0 (* min level *) else lev in
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

let drop_implicits_in_patt cst nb_expl args =
  let impl_st = implicits_of_global cst in
  let impl_data = extract_impargs_data impl_st in
  let rec impls_fit l = function
    | [], t -> Some (List.rev_append l t)
    | _, [] -> None
    | h::t, { CAst.v = CPatAtom None }::tt when is_status_implicit h -> impls_fit l (t,tt)
    | h::_, _ when is_status_implicit h -> None
    | _::t, hh::tt -> impls_fit (hh::l) (t,tt)
  in
  let try_impls_fit (imps,args) =
    if not !Constrintern.parsing_explicit &&
       ((!Flags.raw_print || !print_implicits) &&
        List.exists is_status_implicit imps)
       (* Note: !print_implicits_explicit_args=true not supported for patterns *)
    then None
    else impls_fit [] (imps,args)
  in
  let rec select = function
    | [] -> None
    | (_,imps)::imps_list ->
      match try_impls_fit (imps,args) with
        | None -> select imps_list
        | x -> x
  in
  if Int.equal nb_expl 0 then select impl_data
  else
    let imps = List.skipn_at_best nb_expl (select_stronger_impargs impl_st) in
    try_impls_fit (imps,args)

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

let pattern_printable_in_both_syntax (ind,_ as c) =
  let impl_st = extract_impargs_data (implicits_of_global (GlobRef.ConstructRef c)) in
  let nb_params = Inductiveops.inductive_nparams (Global.env()) ind in
  List.exists (fun (_,impls) ->
    (List.length impls >= nb_params) &&
      let params,args = Util.List.chop nb_params impls in
      not !Flags.raw_print && not !print_implicits &&
      (List.for_all is_status_implicit params)&&(List.for_all (fun x -> not (is_status_implicit x)) args)
  ) impl_st

let extern_record_pattern cstrsp args =
  try
    if !Flags.raw_print then raise_notrace Exit;
    let projs = Structure.find_projections (fst cstrsp) in
    if PrintingRecord.active (fst cstrsp) then
      ()
    else if PrintingConstructor.active (fst cstrsp) then
      raise_notrace Exit
    else if not (get_record_print ()) then
      raise_notrace Exit;
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
let rec extern_cases_pattern_in_scope ((custom,(lev_after:int option)),scopes as allscopes) vars pat =
  try
    if !Flags.in_debugger || !Flags.raw_print || !print_raw_literal then raise No_match;
    let (na,p,key) = uninterp_prim_token_cases_pattern pat scopes in
    match availability_of_entry_coercion custom constr_lowest_level with
      | None -> raise No_match
      | Some coercion ->
        let loc = cases_pattern_loc pat in
        insert_pat_coercion ?loc coercion
          (insert_pat_alias ?loc (insert_pat_delimiters ?loc (CAst.make ?loc @@ CPatPrim p) key) na)
  with No_match ->
    try
      if !Flags.in_debugger || !Flags.raw_print || !print_no_symbol then raise No_match;
      extern_notation_pattern allscopes vars pat
        (uninterp_cases_pattern_notations pat)
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
          let args = List.map (extern_cases_pattern_in_scope allscopes vars) args in
          let p =
            match extern_record_pattern cstrsp args with
            | Some l -> CPatRecord l
            | None ->
                  let c = extern_reference Id.Set.empty (GlobRef.ConstructRef cstrsp) in
                  if Constrintern.get_asymmetric_patterns () then
                    if pattern_printable_in_both_syntax cstrsp
                    then CPatCstr (c, None, args)
                    else CPatCstr (c, Some (add_patt_for_params (fst cstrsp) args), [])
                  else
                    let full_args = add_patt_for_params (fst cstrsp) args in
                    match drop_implicits_in_patt (GlobRef.ConstructRef cstrsp) 0 full_args with
                      | Some true_args -> CPatCstr (c, None, true_args)
                      | None           -> CPatCstr (c, Some full_args, [])
          in
          insert_pat_alias ?loc (CAst.make ?loc p) na
      in
      insert_pat_coercion coercion pat

and apply_notation_to_pattern ?loc gr ((terms,termlists,binders),(no_implicit,nb_to_drop,more_args))
    ((custom, lev_after), (tmp_scope, scopes) as allscopes) vars pat rule =
  let lev_after = if List.is_empty more_args then lev_after else Some Notation.app_level in
  let extra_args =
    let subscopes = find_arguments_scope gr in
    let more_args_scopes = try List.skipn nb_to_drop subscopes with Failure _ -> [] in
    let more_args = fill_arg_scopes more_args more_args_scopes (snd allscopes) in
    let more_args = List.map (fun (c,allscopes) -> extern_cases_pattern_in_scope allscopes vars c) more_args in
    if Constrintern.get_asymmetric_patterns () || not (List.is_empty termlists) then more_args
    else if no_implicit then more_args else
      match drop_implicits_in_patt gr nb_to_drop more_args with
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
                let scopes = update_with_subscope entry subscope lev_after closed scopes' in
                extern_cases_pattern_in_scope scopes vars c)
                terms in
            let ll =
              List.map (fun (c,subscope) ->
                let scopes = update_with_subscope entry subscope lev_after closed scopes' in
                List.map (extern_cases_pattern_in_scope scopes vars) c)
                termlists in
            let bl =
              List.map (fun (c,subscope) ->
                let scopes = update_with_subscope entry subscope lev_after closed scopes' in
                (extern_cases_pattern_in_scope scopes vars c, Explicit))
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
          extern_cases_pattern_in_scope ((subentry,lev_after),(scopt,scl@scopes)) vars c)
          terms in
      assert (List.is_empty termlists);
      assert (List.is_empty binders);
      insert_pat_coercion ?loc coercion (CAst.make ?loc @@ CPatCstr (qid,None,List.rev_append l1 extra_args))

and extern_notation_pattern allscopes vars t = function
  | [] -> raise No_match
  | { not_rule = keyrule; not_patt = pat; not_status = n } :: rules ->
    try
      if is_printing_inactive_rule keyrule pat then raise No_match;
      let loc = t.loc in
      match DAst.get t with
        | PatCstr (cstr,args,na) ->
          let t = if na = Anonymous then t else DAst.make ?loc (PatCstr (cstr,args,Anonymous)) in
          let p = apply_notation_to_pattern ?loc (GlobRef.ConstructRef cstr)
            (match_notation_constr_cases_pattern t pat) allscopes vars pat keyrule in
          insert_pat_alias ?loc p na
        | PatVar Anonymous -> CAst.make ?loc @@ CPatAtom None
        | PatVar (Name id) -> CAst.make ?loc @@ CPatAtom (Some (qualid_of_ident ?loc id))
    with
        No_match -> extern_notation_pattern allscopes vars t rules

let rec extern_notation_ind_pattern allscopes vars ind args = function
  | [] -> raise No_match
  | { not_rule = keyrule; not_patt = pat; not_status = n } :: rules ->
    try
      if is_printing_inactive_rule keyrule pat then raise No_match;
      apply_notation_to_pattern (GlobRef.IndRef ind)
        (match_notation_constr_ind_pattern ind args pat) allscopes vars pat keyrule
    with
        No_match -> extern_notation_ind_pattern allscopes vars ind args rules

let extern_ind_pattern_in_scope (custom,scopes as allscopes) vars ind args =
  (* pboutill: There are letins in pat which is incompatible with notations and
     not explicit application. *)
  if !Flags.in_debugger||Inductiveops.inductive_has_local_defs (Global.env()) ind then
    let c = extern_reference vars (GlobRef.IndRef ind) in
    let args = List.map (extern_cases_pattern_in_scope allscopes vars) args in
    CAst.make @@ CPatCstr (c, Some (add_patt_for_params ind args), [])
  else
    try
      if !Flags.raw_print || !print_no_symbol then raise No_match;
      extern_notation_ind_pattern allscopes vars ind args
          (uninterp_ind_pattern_notations ind)
    with No_match ->
      let c = extern_reference vars (GlobRef.IndRef ind) in
      let args = List.map (extern_cases_pattern_in_scope allscopes vars) args in
      match drop_implicits_in_patt (GlobRef.IndRef ind) 0 args with
      | Some true_args -> CAst.make @@ CPatCstr (c, None, true_args)
      | None           -> CAst.make @@ CPatCstr (c, Some args, [])

let extern_cases_pattern vars p =
  extern_cases_pattern_in_scope ((constr_some_level,None),([],[])) vars p

(**********************************************************************)
(* Externalising applications *)

let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

let is_gvar id c = match DAst.get c with
| GVar id' -> Id.equal id id'
| _ -> false

let is_projection nargs r =
  if not !Flags.in_debugger && not !Flags.raw_print && !print_projections then
    try
      match r with
      | GlobRef.ConstRef c ->
        let n = Structure.projection_nparams c + 1 in
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
let adjust_implicit_arguments inctx n args impl =
  let rec exprec = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (args,impl) in
        let visible =
          !Flags.raw_print ||
          (!print_implicits && !print_implicits_explicit_args) ||
          (is_needed_for_correct_partial_application tail imp) ||
          (!print_implicits_defensive &&
           (not (is_inferable_implicit inctx n imp) || !Flags.beautify) &&
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

let extern_projection inctx f nexpectedparams args impl =
  let (args1,args2) = List.chop (nexpectedparams + 1) args in
  let nextraargs = List.length args2 in
  let (impl1,impl2) = impargs_for_proj ~nexpectedparams ~nextraargs impl in
  let n = nexpectedparams + 1 + nextraargs in
  let args1 = adjust_implicit_arguments inctx n args1 impl1 in
  let args2 = adjust_implicit_arguments inctx n args2 impl2 in
  let (c1,expl), args1 = List.sep_last args1 in
  assert (expl = None);
  let c = CProj (false,f,args1,c1) in
  if args2 = [] then c else CApp (CAst.make c, args2)

let is_start_implicit = function
  | imp :: _ -> is_status_implicit imp && maximal_insertion_of imp
  | [] -> false

let extern_record ref args =
  try
    if !Flags.raw_print then raise_notrace Exit;
    let cstrsp = match ref with GlobRef.ConstructRef c -> c | _ -> raise Not_found in
    let struc = Structure.find (fst cstrsp) in
    if PrintingRecord.active (fst cstrsp) then
      ()
    else if PrintingConstructor.active (fst cstrsp) then
      raise_notrace Exit
    else if not (get_record_print ()) then
      raise_notrace Exit;
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
let extern_applied_ref inctx impl (cf,f) us args =
  try
    if not !Constrintern.parsing_explicit &&
       ((!Flags.raw_print ||
         (!print_implicits && not !print_implicits_explicit_args)) &&
        List.exists is_status_implicit impl)
    then raise Expl;
    let impl = if !Constrintern.parsing_explicit then [] else impl in
    let n = List.length args in
    let ref = CRef (f,us) in
    let r = CAst.make ref in
    let ip = is_projection n cf in
    match ip with
    | Some i ->
      (* [t.(f args1) args2] projection-style notation *)
      extern_projection inctx (f,us) (i-1) args impl
    | None ->
      let args = adjust_implicit_arguments inctx n args impl in
      if args = [] then ref else CApp (r, args)
  with Expl ->
  (* A [@f args] node *)
    let args = List.map Lazy.force args in
    match is_projection (List.length args) cf with
    | Some n when !print_projections ->
       let args = List.map (fun c -> (c,None)) args in
       let args1, args2 = List.chop n args in
       let (c1,_), args1 = List.sep_last args1 in
       let c = CProj (true, (f,us), args1, c1) in
       if args2 = [] then c else CApp (CAst.make c, args2)
    | _ ->
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

let remove_one_coercion inctx c =
  try match match_coercion_app c with
  | Some (loc,r,args) when not (!Flags.raw_print || !print_coercions) ->
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

let extern_possible_prim_token ((custom,_),scopes) r =
   if !print_raw_literal then raise No_match;
   let (n,key) = uninterp_prim_token r scopes in
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

type extern_env = Id.Set.t * UnivNames.universe_binders
let extern_env env sigma = vars_of_env env, Evd.universe_binders sigma
let empty_extern_env = Id.Set.empty, UnivNames.empty_binders

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

let extern_glob_qvar = function
  | GLocalQVar {v=Anonymous;loc} -> CQAnon loc
  | GLocalQVar {v=Name id; loc} -> CQVar (qualid_of_ident ?loc id)
  | GRawQVar q -> CRawQVar q
  | GQVar q -> CRawQVar q

let extern_relevance = function
  | GRelevant -> CRelevant
  | GIrrelevant -> CIrrelevant
  | GRelevanceVar q -> CRelevanceVar (extern_glob_qvar q)

let extern_relevance_info = Option.map extern_relevance

let extern_glob_quality = function
  | GQConstant q -> CQConstant q
  | GQualVar q -> CQualVar (extern_glob_qvar q)

let extern_glob_sort uvars (q, l) =
  Option.map extern_glob_qvar q,
  map_glob_sort_gen (List.map (on_fst (extern_glob_sort_name uvars))) l

(** wrapper to handle print_universes: don't forget small univs *)
let extern_glob_sort uvars (s:glob_sort) =
  let really_extern = !print_universes || Option.has_some (fst s) || match snd s with
    | UNamed [s, 0] -> begin match s with
        | GSet | GProp | GSProp -> true
        | GUniv _ | GLocalUniv _ | GRawUniv _ -> false
      end
    | _ -> false
  in
  if really_extern then extern_glob_sort uvars s
  else Constrexpr_ops.expr_Type_sort

let extern_instance uvars = function
  | Some (ql,ul) when !print_universes ->
    let ql = List.map extern_glob_quality ql in
    let ul = List.map (map_glob_sort_gen (extern_glob_sort_name uvars)) ul in
    Some (ql,ul)
  | _ -> None

let extern_ref (vars,uvars) ref us =
  extern_global (select_stronger_impargs (implicits_of_global ref))
    (extern_reference vars ref) (extern_instance uvars us)

let extern_var ?loc id = CRef (qualid_of_ident ?loc id,None)

let add_vname (vars,uvars) na = add_vname vars na, uvars

let rec insert_impargs impargs r = match impargs with
  | [] -> r
  | bk :: rest ->
    match DAst.get r with
    | GProd (na,rinfo,_,t,c) ->
      DAst.make ?loc:r.loc (GProd (na, rinfo, bk, t, insert_impargs rest c))
    | GLetIn (na,rinfo,b,t,c) ->
      DAst.make ?loc:r.loc (GLetIn (na, rinfo, b, t, insert_impargs impargs c))
    | _ -> r

let rec extern inctx scopes vars r =
  match remove_one_coercion inctx (flatten_application r) with
  | Some (nargs,inctx,r') ->
    (try extern_notations inctx scopes vars (Some nargs) r
     with No_match -> extern inctx scopes vars r')
  | None ->

  let r' = match DAst.get r with
    | GInt i when Rocqlib.has_ref "num.int63.wrap_int" ->
       let wrap = Rocqlib.lib_ref "num.int63.wrap_int" in
       DAst.make (GApp (DAst.make (GRef (wrap, None)), [r]))
    | GFloat f when Rocqlib.has_ref "num.float.wrap_float" ->
       let wrap = Rocqlib.lib_ref "num.float.wrap_float" in
       DAst.make (GApp (DAst.make (GRef (wrap, None)), [r]))
    | _ -> r in

  try extern_notations inctx scopes vars None r'
  with No_match ->

  let loc = r.CAst.loc in
  match DAst.get r with
  | GRef (ref,us) when entry_has_global (fst (fst scopes)) -> CAst.make ?loc (extern_ref vars ref us)

  | GVar id when entry_has_global (fst (fst scopes)) || entry_has_ident (fst (fst scopes)) ->
      CAst.make ?loc (extern_var ?loc id)

  | c ->

  match availability_of_entry_coercion (fst (fst scopes)) constr_lowest_level with
  | None -> raise No_match
  | Some coercion ->

  let scopes = ((constr_some_level, None), snd scopes) in
  let c = match c with

  (* The remaining cases are only for the constr entry *)

  | GRef (ref,us) -> extern_ref vars ref us

  | GVar id -> extern_var ?loc id

  | GEvar (n,[]) when !print_meta_as_hole -> CHole (None)

  | GEvar (n,l) ->
      extern_evar n (List.map (on_snd (extern false scopes vars)) l)

  | GPatVar kind ->
      if !print_meta_as_hole then CHole (None) else
       (match kind with
         | Evar_kinds.SecondOrderPatVar n -> CPatVar n
         | Evar_kinds.FirstOrderPatVar n -> CEvar (CAst.make n,[]))

  | GApp (f,args) ->
      (match DAst.get f with
         | GRef (ref,us) ->
             let subscopes = find_arguments_scope ref in
             let args = fill_arg_scopes args subscopes (snd scopes) in
             let args = extern_args (extern true) vars args in
             (* Try a "{|...|}" record notation *)
             (match extern_record ref args with
             | Some l -> CRecord l
             | None ->
             (* Otherwise... *)
               extern_applied_ref inctx
                 (select_stronger_impargs (implicits_of_global ref))
                 (ref,extern_reference ?loc (fst vars) ref) (extern_instance (snd vars) us) args)
         | GProj (f,params,c) ->
             extern_applied_proj inctx scopes vars f params c args
         | _ ->
             let args = List.map (fun c -> (sub_extern true scopes vars c,None)) args in
             let head = sub_extern false scopes vars f in
             mkFlattenedCApp (head,args))

  | GProj (f,params,c) ->
      extern_applied_proj inctx scopes vars f params c []

  | GLetIn (na,_,b,t,c) ->
    CLetIn (make ?loc na,
            sub_extern (Option.has_some t) scopes vars b,
            Option.map (extern_typ scopes vars) t,
            extern inctx scopes (add_vname vars na) c)

  | GProd (na,r,bk,t,c) ->
      factorize_prod scopes vars na r bk t c

  | GLambda (na,r,bk,t,c) ->
      factorize_lambda inctx scopes vars na r bk t c

  | GCases (sty,rtntypopt,tml,eqns) ->
    let vars' =
      List.fold_right (Name.fold_right Id.Set.add)
        (cases_predicate_names tml) (fst vars) in
    let vars' = vars', snd vars in
    let rtntypopt' = Option.map (extern_typ scopes vars') rtntypopt in
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
                 (sub_extern false scopes vars tm,
                  na',
                  Option.map (fun {CAst.loc;v=(ind,nal)} ->
                              let args = List.map (fun x -> DAst.make @@ PatVar x) nal in
                              let fullargs = add_cpatt_for_params ind args in
                              extern_ind_pattern_in_scope scopes (fst vars) ind fullargs
                             ) x))
                tml
    in
    let eqns = List.map (extern_eqn (inctx || rtntypopt <> None) scopes vars) (factorize_eqns eqns) in
    CCases (sty,rtntypopt',tml,eqns)

  | GLetTuple (nal,(na,typopt),tm,b) ->
      let inctx = inctx || typopt <> None in
      CLetTuple (List.map CAst.make nal,
        (Option.map (fun _ -> (make na)) typopt,
         Option.map (extern_typ scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars tm,
        extern inctx scopes (List.fold_left add_vname vars nal) b)

  | GIf (c,(na,typopt),b1,b2) ->
      let inctx = inctx || typopt <> None in
      CIf (sub_extern false scopes vars c,
        (Option.map (fun _ -> (CAst.make na)) typopt,
         Option.map (extern_typ scopes (add_vname vars na)) typopt),
        sub_extern inctx scopes vars b1, sub_extern inctx scopes vars b2)

  | GRec (fk,idv,blv,tyv,bv) ->
      let vars' = on_fst (Array.fold_right Id.Set.add idv) vars in
      (match fk with
         | GFix (nv,n) ->
             let listdecl =
               Array.mapi (fun i fi ->
                 let (bl,ty,def) = blv.(i), tyv.(i), bv.(i) in
                 let bl = List.map (extended_glob_local_binder_of_decl ?loc) bl in
                 let (assums,ids,bl) = extern_local_binder scopes vars bl in
                 let vars0 = on_fst (List.fold_right (Name.fold_right Id.Set.add) ids) vars in
                 let vars1 = on_fst (List.fold_right (Name.fold_right Id.Set.add) ids) vars' in
                 let n =
                   match nv.(i) with
                   | None -> None
                   | Some x -> Some (CAst.make @@ CStructRec (CAst.make @@ Name.get_id (List.nth assums x)))
                             in
                 ((CAst.make fi), None, n, bl, extern_typ scopes vars0 ty,
                  sub_extern true scopes vars1 def)) idv
             in
             CFix (CAst.(make ?loc idv.(n)), Array.to_list listdecl)
         | GCoFix n ->
             let listdecl =
               Array.mapi (fun i fi ->
                 let bl = List.map (extended_glob_local_binder_of_decl ?loc) blv.(i) in
                 let (_,ids,bl) = extern_local_binder scopes vars bl in
                 let vars0 = on_fst (List.fold_right (Name.fold_right Id.Set.add) ids) vars in
                 let vars1 = on_fst (List.fold_right (Name.fold_right Id.Set.add) ids) vars' in
                 ((CAst.make fi),None,bl,extern_typ scopes vars0 tyv.(i),
                  sub_extern true scopes vars1 bv.(i))) idv
             in
             CCoFix (CAst.(make ?loc idv.(n)),Array.to_list listdecl))

  | GSort s -> CSort (extern_glob_sort (snd vars) s)

  | GHole e -> CHole (Some e)

  | GGenarg arg -> CGenargGlob arg

  | GCast (c, k, c') ->
    let scl = Notation.compute_glob_type_scope c' in
    let c' = extern_typ scopes vars c' in
    let c = extern true (fst scopes,(scl, snd (snd scopes))) vars c in
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
    CArray(extern_instance (snd vars) u,Array.map (extern inctx scopes vars) t, extern inctx scopes vars def, extern_typ scopes vars ty)

  in insert_entry_coercion coercion (CAst.make ?loc c)

and extern_typ (subentry,(_,scopes)) =
  extern true (subentry,(Notation.current_type_scope_names (),scopes))

and sub_extern inctx (subentry,(_,scopes)) = extern inctx (subentry,([],scopes))

and factorize_prod scopes vars na r bk t c =
  let implicit_type = is_reserved_type na t in
  let r = extern_relevance_info r in
  let aty = extern_typ scopes vars t in
  let vars = add_vname vars na in
  let store, get = set_temporary_memory () in
  match na, DAst.get c with
  | Name id, GCases (Constr.LetPatternStyle, None, [(e,(Anonymous,None))],(_::_ as eqns))
         when is_gvar id e && List.length (store (factorize_eqns eqns)) = 1 ->
    (match get () with
     | [{CAst.v=(ids,disj_of_patl,b)}] ->
      let disjpat = List.map (function [pat] -> pat | _ -> assert false) disj_of_patl in
      let disjpat = if occur_glob_constr id b then List.map (set_pat_alias id) disjpat else disjpat in
      let b = extern_typ scopes vars b in
      let p = mkCPatOr (List.map (extern_cases_pattern_in_scope scopes (fst vars)) disjpat) in
      let binder = CLocalPattern p in
      (match b.v with
      | CProdN (bl,b) -> CProdN (binder::bl,b)
      | _ -> CProdN ([binder],b))
     | _ -> assert false)
  | _, _ ->
      let c' = extern_typ scopes vars c in
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

and factorize_lambda inctx scopes vars na r bk t c =
  let implicit_type = is_reserved_type na t in
  let r = extern_relevance_info r in
  let aty = extern_typ scopes vars t in
  let vars = add_vname vars na in
  let store, get = set_temporary_memory () in
  match na, DAst.get c with
  | Name id, GCases (Constr.LetPatternStyle, None, [(e,(Anonymous,None))],(_::_ as eqns))
         when is_gvar id e && List.length (store (factorize_eqns eqns)) = 1 ->
    (match get () with
     | [{CAst.v=(ids,disj_of_patl,b)}] ->
      let disjpat = List.map (function [pat] -> pat | _ -> assert false) disj_of_patl in
      let disjpat = if occur_glob_constr id b then List.map (set_pat_alias id) disjpat else disjpat in
      let b = sub_extern inctx scopes vars b in
      let p = mkCPatOr (List.map (extern_cases_pattern_in_scope scopes (fst vars)) disjpat) in
      let binder = CLocalPattern p in
      (match b.v with
      | CLambdaN (bl,b) -> CLambdaN (binder::bl,b)
      | _ -> CLambdaN ([binder],b))
     | _ -> assert false)
  | _, _ ->
      let c' = sub_extern inctx scopes vars c in
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

and extern_local_binder scopes vars = function
    [] -> ([],[],[])
  | b :: l ->
    match DAst.get b with
    | GLocalDef (na,r,bd,ty) ->
      let (assums,ids,l) =
        extern_local_binder scopes (on_fst (Name.fold_right Id.Set.add na) vars) l in
      (assums,na::ids,
       CLocalDef(CAst.make na, extern_relevance_info r, extern false scopes vars bd,
                   Option.map (extern_typ scopes vars) ty) :: l)

    | GLocalAssum (na,r,bk,ty) ->
      let implicit_type = is_reserved_type na ty in
      let ty = extern_typ scopes vars ty in
      (match extern_local_binder scopes (on_fst (Name.fold_right Id.Set.add na) vars) l with
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
          CLocalAssum([CAst.make na],extern_relevance_info r,Default bk,ty) :: l))

    | GLocalPattern ((p,_),_,bk,ty) ->
      let ty =
        if !Flags.raw_print then Some (extern_typ scopes vars ty) else None in
      let p = mkCPatOr (List.map (extern_cases_pattern (fst vars)) p) in
      let (assums,ids,l) = extern_local_binder scopes vars l in
      let p = match ty with
        | None -> p
        | Some ty -> CAst.make @@ (CPatCast (p,ty)) in
      (assums,ids, CLocalPattern p :: l)

and extern_eqn inctx scopes vars {CAst.loc;v=(ids,pll,c)} =
  let pll = List.map (List.map (extern_cases_pattern_in_scope scopes (fst vars))) pll in
  make ?loc (pll,extern inctx scopes vars c)

and extern_notations inctx scopes vars nargs t =
  if !Flags.raw_print then raise No_match;
  try extern_possible_prim_token scopes t
  with No_match ->
    if !print_no_symbol then raise No_match;
    let t = flatten_application t in
    extern_notation inctx scopes vars t (filter_enough_applied nargs (uninterp_notations t))

and extern_notation inctx ((custom,(lev_after: int option)),scopes as allscopes) vars t rules =
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
            let subscopes = find_arguments_scope ref in
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
        let vars, uvars = vars in
        let terms,termlists,binders,binderlists =
          match_notation_constr ~print_univ:(!print_universes) t ~vars pat in
        let lev_after = if List.is_empty args then lev_after else Some Notation.app_level in
        (* Try externing extra args... *)
        let extra_args =
          let args = fill_arg_scopes args argsscopes (snd allscopes) in
          let args = extern_args (extern true) (vars,uvars) args in
          try UseCApp (adjust_implicit_arguments inctx nallargs args argsimpls) with Expl -> UseCAppExpl args in
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
                      let scopes = update_with_subscope entry subscope lev_after closed scopes' in
                      extern (* assuming no overloading: *) true scopes (vars,uvars) c)
                      terms
                  in
                  let ll =
                    List.map (fun ((vars,l),subscope) ->
                      let scopes = update_with_subscope entry subscope lev_after closed scopes' in
                      List.map (extern true scopes (vars,uvars)) l)
                      termlists
                  in
                  let bl =
                    List.map (fun ((vars,bl),subscope) ->
                      let scopes = update_with_subscope entry subscope lev_after closed scopes' in
                        (mkCPatOr (List.map
                                     (extern_cases_pattern_in_scope scopes vars) bl)),
                        Explicit)
                      binders
                  in
                  let bll =
                    List.map (fun ((vars,bl),subscope) ->
                      let scopes = update_with_subscope entry subscope lev_after closed scopes' in
                      pi3 (extern_local_binder scopes (vars,uvars) bl))
                      binderlists
                  in
                  let c = make_notation loc specific_ntn (l,ll,bl,bll) in
                  let c = insert_entry_coercion coercion (insert_delimiters c key) in
                  insert_entry_coercion appcoercion (CAst.make ?loc @@ extern_applied_notation c extra_args))
          | AbbrevRule kn ->
              let l =
                List.map (fun ((vars,c),(subentry,(scopt,scl))) ->
                  extern true ((subentry,lev_after),(scopt,scl@snd scopes)) (vars,uvars) c)
                  terms
              in
              let cf = Nametab.shortest_qualid_of_abbreviation ?loc vars kn in
              let a = CRef (cf,None) in
              let c = CAst.make ?loc @@ extern_applied_abbreviation (a,cf) l extra_args in
              if isCRef_no_univ c.CAst.v && entry_has_global custom then c
              else match availability_of_entry_coercion custom constr_lowest_level with
                | None -> raise No_match
                | Some coercion -> insert_entry_coercion coercion c
      with
          No_match -> extern_notation inctx allscopes vars t rules

and extern_applied_proj inctx scopes vars (cst,us) params c extraargs =
  let ref = GlobRef.ConstRef cst in
  let subscopes = find_arguments_scope ref in
  let nparams = List.length params in
  let args = params @ c :: extraargs in
  let args = fill_arg_scopes args subscopes (snd scopes) in
  let args = extern_args (extern true) vars args in
  let imps = select_stronger_impargs (implicits_of_global ref) in
  let f = extern_reference (fst vars) ref in
  let us = extern_instance (snd vars) us in
  extern_projection inctx (f,us) nparams args imps

let extern_glob_constr vars c =
  extern false ((constr_some_level,None),([],[])) vars c

let extern_glob_type ?impargs vars c =
  let c = Option.fold_right insert_impargs impargs c in
  extern_typ ((constr_some_level,None),([],[])) vars c

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let extern_constr ?(inctx=false) ?scope env sigma t =
  let r = Detyping.detype Detyping.Later env sigma t in
  let vars = extern_env env sigma in
  let scope = Option.cata (fun x -> [x]) [] scope in
  extern inctx ((constr_some_level,None),(scope,[])) vars r

let extern_constr_in_scope ?inctx scope env sigma t =
  extern_constr ?inctx ~scope env sigma t

let make_avoid goal_concl_style env =
  if goal_concl_style then (Namegen.Generator.fresh, Fresh.of_set @@ vars_of_env env)
  (* TODO: this is linear in the size of the environment, maybe we can do better *)
  else (Namegen.Generator.fresh, Nameops.Fresh.empty)

let extern_type ?(goal_concl_style=false) env sigma ?impargs t =
  (* "goal_concl_style" means do alpha-conversion using the "goal" convention *)
  (* i.e.: avoid using the names of goal/section/rel variables and the short *)
  (* names of global definitions of current module when computing names for *)
  (* bound variables. *)
  (* Not "goal_concl_style" means do alpha-conversion avoiding only *)
  (* those goal/section/rel variables that occurs in the subterm under *)
  (* consideration; see namegen.ml for further details *)
  let avoid = make_avoid goal_concl_style env in
  let r = Detyping.detype Detyping.Later ~isgoal:goal_concl_style ~avoid env sigma t in
  extern_glob_type ?impargs (extern_env env sigma) r

let extern_sort sigma s = extern_glob_sort (Evd.universe_binders sigma) (detype_sort sigma s)

let extern_closed_glob ?(goal_concl_style=false) ?(inctx=false) ?scope env sigma t =
  let avoid = make_avoid goal_concl_style env in
  let r =
    Detyping.detype_closed_glob ~isgoal:goal_concl_style ~avoid env sigma t
  in
  let vars = extern_env env sigma in
  let scope = Option.cata (fun x -> [x]) [] scope in
  extern inctx ((constr_some_level,None),(scope,[])) vars r

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let any_any_branch =
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
  : 'a 's. 's Namegen.Generator.input -> _ -> _ -> 'a constr_pattern_r -> _
  = fun (type a s) (avoid : s Namegen.Generator.t * s) env sigma (pat: a constr_pattern_r) ->
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
      | None -> Id.of_string "__"
      | Some id -> id
      in
      GEvar (CAst.make id,List.map (fun (id,c) -> (CAst.make id, glob_of_pat avoid env sigma c)) l)
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
        | Name id   -> id
        | Anonymous ->
            anomaly ~label:"glob_constr_of_pattern" (Pp.str "index to an anonymous variable.")
      with Not_found -> Id.of_string ("_UNBOUND_REL_"^(string_of_int n)) in
      GVar id
  | PMeta None -> GHole (GInternalHole)
  | PMeta (Some n) -> GPatVar (Evar_kinds.FirstOrderPatVar n)
  | PUninstantiated (PGenarg g) -> GGenarg g
  | PProj (p,c) -> GApp (DAst.make @@ GRef (GlobRef.ConstRef (Projection.constant p),None),
                         [glob_of_pat avoid env sigma c])
  | PApp (f,args) ->
      GApp (glob_of_pat avoid env sigma f,Array.map_to_list (glob_of_pat avoid env sigma) args)
  | PSoApp (n,args) ->
      GApp (DAst.make @@ GPatVar (Evar_kinds.SecondOrderPatVar n),
        List.map (glob_of_pat avoid env sigma) args)
  | PProd (na,t,c) ->
      let na',avoid' = compute_displayed_name_in_pattern (Global.env ()) sigma avoid na c in
      let env' = Termops.add_name na' env in
      GProd (na',None,Explicit,glob_of_pat avoid env sigma t,glob_of_pat avoid' env' sigma c)
  | PLetIn (na,b,t,c) ->
      let na',avoid' = compute_displayed_let_name_in (Global.env ()) sigma Namegen.RenamingForGoal avoid na in
      let env' = Termops.add_name na' env in
      GLetIn (na',None,glob_of_pat avoid env sigma b, Option.map (glob_of_pat avoid env sigma) t,
              glob_of_pat avoid' env' sigma c)
  | PLambda (na,t,c) ->
      let na',avoid' = compute_displayed_name_in_pattern (Global.env ()) sigma avoid na c in
      let env' = Termops.add_name na' env in
      GLambda (na',None,Explicit,glob_of_pat avoid env sigma t, glob_of_pat avoid' env' sigma c)
  | PIf (c,b1,b2) ->
      GIf (glob_of_pat avoid env sigma c, (Anonymous,None),
           glob_of_pat avoid env sigma b1, glob_of_pat avoid env sigma b2)
  | PCase ({cip_style=Constr.LetStyle},None,tm,[(0,n,b)]) ->
      let n, b = glob_of_pat_under_context glob_of_pat avoid env sigma (n, b) in
      let nal = Array.to_list n in
      GLetTuple (nal,(Anonymous,None),glob_of_pat avoid env sigma tm,b)
  | PCase (info,p,tm,bl) ->
      let mat = match bl, info.cip_ind with
        | [], _ -> []
        | _, Some ind ->
          let map (i, n, c) =
            let n, c = glob_of_pat_under_context glob_of_pat avoid env sigma (n, c) in
            let nal = Array.to_list n in
            let mkPatVar na = DAst.make @@ PatVar na in
            let p = DAst.make @@ PatCstr ((ind,i+1),List.map mkPatVar nal,Anonymous) in
            let ids = List.map_filter Nameops.Name.to_option nal in
            CAst.make @@ (ids,[p],c)
          in
          List.map map bl
        | _, None -> anomaly (Pp.str "PCase with some branches but unknown inductive.")
      in
      let mat = if info.cip_extensible then mat @ [any_any_branch] else mat
      in
      let indnames,rtn = match p, info.cip_ind with
        | None, _ -> (Anonymous,None),None
        | Some p, Some ind ->
          let nas, p = glob_of_pat_under_context glob_of_pat avoid env sigma p in
          let nas = Array.rev_to_list nas in
          ((List.hd nas, Some (CAst.make (ind, List.tl nas))), Some p)
        | _ -> anomaly (Pp.str "PCase with non-trivial predicate but unknown inductive.")
      in
      GCases (Constr.RegularStyle,rtn,[glob_of_pat avoid env sigma tm,indnames],mat)
  | PFix ((ln,i),(lna,tl,bl)) ->
     let def_avoid, def_env, lfi =
       Array.fold_left
         (fun (avoid, env, l) na ->
           let id, avoid = next_name_away na avoid in
           (avoid, Name id :: env, id::l))
      (avoid, env, []) lna in
     let n = Array.length tl in
     let v = Array.map3
               (fun c t i -> Detyping.share_pattern_names glob_of_pat (i+1) [] def_avoid def_env sigma c (Patternops.lift_pattern n t))
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
               (fun c t -> share_pattern_names glob_of_pat 0 [] def_avoid def_env sigma c (Patternops.lift_pattern ntys t))
               bl tl in
     GRec(GCoFix ln,Array.of_list (List.rev lfi),
          Array.map (fun (bl,_,_) -> bl) v,
          Array.map (fun (_,_,ty) -> ty) v,
          Array.map (fun (_,bd,_) -> bd) v)
  | PSort Sorts.InSProp -> GSort Glob_ops.glob_SProp_sort
  | PSort Sorts.InProp -> GSort Glob_ops.glob_Prop_sort
  | PSort Sorts.InSet -> GSort Glob_ops.glob_Set_sort
  | PSort (Sorts.InType | Sorts.InQSort) -> GSort Glob_ops.glob_Type_sort
  | PInt i -> GInt i
  | PFloat f -> GFloat f
  | PString s -> GString s
  | PArray(t,def,ty) ->
    let glob_of = glob_of_pat avoid env sigma in
    GArray (None, Array.map glob_of t, glob_of def, glob_of ty)

let extern_constr_pattern env sigma pat =
  extern true ((constr_some_level,None),([],[]))
    (* XXX no vars? *)
    (Id.Set.empty, Evd.universe_binders sigma)
    (glob_of_pat (genset, Id.Set.empty) env sigma pat)

let extern_rel_context where env sigma sign =
  let a = detype_rel_context Detyping.Later where ([],env) sigma sign in
  let vars = extern_env env sigma in
  let a = List.map (extended_glob_local_binder_of_decl) a in
  pi3 (extern_local_binder ((constr_some_level,None),([],[])) vars a)
