(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
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
open Namegen
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

module NamedDecl = Context.Named.Declaration
(*i*)

(* Translation from glob_constr to front constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars *)
let print_evar_arguments = Detyping.print_evar_arguments

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

(* This suppresses printing of primitive tokens (e.g. numeral) and notations *)
let print_no_symbol = ref false

(* This tells to skip types if a variable has this type by default *)
let print_use_implicit_types =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Use";"Implicit";"Types"]
    ~value:true

(**********************************************************************)

let hole = CAst.make @@ CHole (None, IntroAnonymous, None)

let is_reserved_type na t =
  not !Flags.raw_print && print_use_implicit_types () &&
  match na with
  | Anonymous -> false
  | Name id ->
    try
      let pat = Reserve.find_reserved_type id in
      let _ = match_notation_constr false t ([],pat) in
      true
    with Not_found | No_match -> false

(**********************************************************************)
(* Turning notations and scopes on and off for printing *)
module IRuleSet = Set.Make(struct
    type t = interp_rule
    let compare x y = compare x y
  end)

let inactive_notations_table =
  Summary.ref ~name:"inactive_notations_table" (IRuleSet.empty)
let inactive_scopes_table    =
  Summary.ref ~name:"inactive_scopes_table" CString.Set.empty

let show_scope inscope =
  match inscope with
  | LastLonelyNotation -> str ""
  | NotationInScope sc -> spc () ++ str "in scope" ++ spc () ++ str sc

let _show_inactive_notations () =
  begin
    if CString.Set.is_empty !inactive_scopes_table
    then
      Feedback.msg_notice (str "No inactive notation scopes.")
    else
      let _ = Feedback.msg_notice (str "Inactive notation scopes:") in
      CString.Set.iter (fun sc -> Feedback.msg_notice (str "  " ++ str sc))
        !inactive_scopes_table
  end;
  if IRuleSet.is_empty !inactive_notations_table
  then
    Feedback.msg_notice (str "No individual inactive notations.")
  else
    let _ = Feedback.msg_notice (str "Inactive notations:") in
    IRuleSet.iter
      (function
       | NotationRule (inscope, ntn) ->
         Feedback.msg_notice (pr_notation ntn ++ show_scope inscope)
       | SynDefRule kn -> Feedback.msg_notice (str (string_of_qualid (Nametab.shortest_qualid_of_syndef Id.Set.empty kn))))
      !inactive_notations_table

let deactivate_notation nr =
  match nr with
  | SynDefRule kn ->
     (* shouldn't we check whether it is well defined? *)
     inactive_notations_table := IRuleSet.add nr !inactive_notations_table
  | NotationRule (inscope, ntn) ->
     let scopt = match inscope with NotationInScope sc -> Some sc | LastLonelyNotation -> None in
     match availability_of_notation (inscope, ntn) (scopt, []) with
     | None -> user_err ~hdr:"Notation"
                        (pr_notation ntn ++ spc () ++ str "does not exist"
                         ++ (match inscope with
                             | LastLonelyNotation -> spc () ++ str "in the empty scope."
                             | NotationInScope _ -> show_scope inscope ++ str "."))
     | Some _ ->
        if IRuleSet.mem nr !inactive_notations_table then
          Feedback.msg_warning
            (str "Notation" ++ spc () ++ pr_notation ntn ++ spc ()
             ++ str "is already inactive" ++ show_scope inscope ++ str ".")
        else inactive_notations_table := IRuleSet.add nr !inactive_notations_table

let reactivate_notation nr =
  try
    inactive_notations_table :=
      IRuleSet.remove nr !inactive_notations_table
  with Not_found ->
    match nr with
    | NotationRule (inscope, ntn) ->
       Feedback.msg_warning (str "Notation" ++ spc () ++ pr_notation ntn ++ spc ()
                             ++ str "is already active" ++ show_scope inscope ++
  str ".")
    | SynDefRule kn ->
       let s = string_of_qualid (Nametab.shortest_qualid_of_syndef Id.Set.empty kn) in
       Feedback.msg_warning
         (str "Notation" ++ spc () ++ str s
          ++ spc () ++ str "is already active.")


let deactivate_scope sc =
  ignore (find_scope sc); (* ensures that the scope exists *)
  if CString.Set.mem sc !inactive_scopes_table
  then
    Feedback.msg_warning (str "Notation Scope" ++ spc () ++ str sc ++ spc ()
                          ++ str "is already inactive.")
  else
    inactive_scopes_table := CString.Set.add sc !inactive_scopes_table

let reactivate_scope sc =
  try
    inactive_scopes_table := CString.Set.remove sc !inactive_scopes_table
  with Not_found ->
    Feedback.msg_warning (str "Notation Scope" ++ spc () ++ str sc ++ spc ()
                          ++ str "is already active.")

let is_inactive_rule nr =
  IRuleSet.mem nr !inactive_notations_table ||
  match nr with
    | NotationRule (NotationInScope sc, ntn) -> CString.Set.mem sc !inactive_scopes_table
    | NotationRule (LastLonelyNotation, ntn) -> false
    | SynDefRule _ -> false

(* args: notation, scope, activate/deactivate *)
let toggle_scope_printing ~scope ~activate =
  if activate then
    reactivate_scope scope
  else
    deactivate_scope scope

let toggle_notation_printing ?scope ~notation ~activate =
  let inscope = match scope with
  | None -> LastLonelyNotation
  | Some sc -> NotationInScope sc in
  if activate then
    reactivate_notation (NotationRule (inscope, notation))
  else
    deactivate_notation (NotationRule (inscope, notation))

(* This governs printing of projections using the dot notation symbols *)
let print_projections = ref false

let print_meta_as_hole = ref false

let with_universes f = Flags.with_option print_universes f
let with_meta_as_hole f = Flags.with_option print_meta_as_hole f
let without_symbols f = Flags.with_option print_no_symbol f

let without_specific_symbols l =
  Flags.with_modified_ref inactive_notations_table
    (fun tbl -> IRuleSet.(union (of_list l) tbl))

(**********************************************************************)
(* Control printing of records *)

(* Set Record Printing flag *)
let get_record_print =
  Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Records"]
    ~value:true

let is_record indsp =
  try
    let _ = Recordops.lookup_structure indsp in
    true
  with Not_found -> false

let encode_record r =
  let indsp = Nametab.global_inductive r in
  if not (is_record indsp) then
    user_err ?loc:r.CAst.loc ~hdr:"encode_record"
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
  | Some sc -> CAst.make @@ CDelimiters (sc,e)

let insert_pat_delimiters ?loc p = function
  | None -> p
  | Some sc -> CAst.make ?loc @@ CPatDelimiters (sc,p)

let insert_pat_alias ?loc p = function
  | Anonymous -> p
  | Name _ as na -> CAst.make ?loc @@ CPatAlias (p,(CAst.make ?loc na))

let rec insert_entry_coercion ?loc l c = match l with
  | [] -> c
  | (inscope,ntn)::l -> CAst.make ?loc @@ CNotation (Some inscope,ntn,([insert_entry_coercion ?loc l c],[],[],[]))

let rec insert_pat_coercion ?loc l c = match l with
  | [] -> c
  | (inscope,ntn)::l -> CAst.make ?loc @@ CPatNotation (Some inscope,ntn,([insert_pat_coercion ?loc l c],[]),[])

(**********************************************************************)
(* conversion of references                                           *)

let extern_evar n l = CEvar (n,l)

(** We allow customization of the global_reference printer.
    For instance, in the debugger the tables of global references
    may be inaccurate *)

let default_extern_reference ?loc vars r =
  Nametab.shortest_qualid_of_global ?loc vars r

let my_extern_reference = ref default_extern_reference

let set_extern_reference f = my_extern_reference := f
let get_extern_reference () = !my_extern_reference

let extern_reference ?loc vars l = !my_extern_reference vars l

(**********************************************************************)
(* utilities                                                          *)

let rec fill_arg_scopes args subscopes (entry,(_,scopes) as all) =
  match args, subscopes with
  | [], _ -> []
  | a :: args, scopt :: subscopes ->
    (a, (entry, (scopt, scopes))) :: fill_arg_scopes args subscopes all
  | a :: args, [] ->
    (a, (entry, (None, scopes))) :: fill_arg_scopes args [] all

(**********************************************************************)
(* mapping patterns to cases_pattern_expr                                *)

let add_patt_for_params ind l =
  if !Flags.in_debugger then l else
    Util.List.addn (Inductiveops.inductive_nparamdecls (Global.env()) ind) (CAst.make @@ CPatAtom None) l

let add_cpatt_for_params ind l =
  if !Flags.in_debugger then l else
    Util.List.addn  (Inductiveops.inductive_nparamdecls (Global.env()) ind) (DAst.make @@ PatVar Anonymous) l

let drop_implicits_in_patt cst nb_expl args =
  let impl_st = (implicits_of_global cst) in
  let impl_data = extract_impargs_data impl_st in
  let rec impls_fit l = function
    |[],t -> Some (List.rev_append l t)
    |_,[] -> None
    |h::t, { CAst.v = CPatAtom None }::tt when is_status_implicit h -> impls_fit l (t,tt)
    |h::_,_ when is_status_implicit h -> None
    |_::t,hh::tt -> impls_fit (hh::l) (t,tt)
  in let rec aux = function
    |[] -> None
    |(_,imps)::t -> match impls_fit [] (imps,args) with
        |None -> aux t
        |x -> x
     in
     if Int.equal nb_expl 0 then aux impl_data
     else
       let imps = List.skipn_at_least nb_expl (select_stronger_impargs impl_st) in
       impls_fit [] (imps,args)

let destPrim = function { CAst.v = CPrim t } -> Some t | _ -> None
let destPatPrim = function { CAst.v = CPatPrim t } -> Some t | _ -> None

let make_notation_gen loc ntn mknot mkprim destprim l bl =
  match snd ntn,List.map destprim l with
    (* Special case to avoid writing "- 3" for e.g. (Z.opp 3) *)
    | "- _", [Some (Numeral p)] when not (NumTok.Signed.is_zero p) ->
        assert (bl=[]);
        mknot (loc,ntn,([mknot (loc,(InConstrEntrySomeLevel,"( _ )"),l,[])]),[])
    | _ ->
        match decompose_notation_key ntn, l with
        | (InConstrEntrySomeLevel,[Terminal "-"; Terminal x]), [] ->
           begin match NumTok.Unsigned.parse_string x with
           | Some n -> mkprim (loc, Numeral (NumTok.SMinus,n))
           | None -> mknot (loc,ntn,l,bl) end
        | (InConstrEntrySomeLevel,[Terminal x]), [] ->
           begin match NumTok.Unsigned.parse_string x with
           | Some n -> mkprim (loc, Numeral (NumTok.SPlus,n))
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

let make_pat_notation ?loc (inscope,ntn) (terms,termlists as subst) args =
  if not (List.is_empty termlists) then (CAst.make ?loc @@ CPatNotation (Some inscope,ntn,subst,args)) else
  make_notation_gen loc ntn
    (fun (loc,ntn,l,_) -> CAst.make ?loc @@ CPatNotation (Some inscope,ntn,(l,[]),args))
    (fun (loc,p)     -> CAst.make ?loc @@ CPatPrim p)
    destPatPrim terms []

let mkPat ?loc qid l = CAst.make ?loc @@
  (* Normally irrelevant test with v8 syntax, but let's do it anyway *)
  if List.is_empty l then CPatAtom (Some qid) else CPatCstr (qid,None,l)

let pattern_printable_in_both_syntax (ind,_ as c) =
  let impl_st = extract_impargs_data (implicits_of_global (GlobRef.ConstructRef c)) in
  let nb_params = Inductiveops.inductive_nparams (Global.env()) ind in
  List.exists (fun (_,impls) ->
    (List.length impls >= nb_params) &&
      let params,args = Util.List.chop nb_params impls in
      (List.for_all is_status_implicit params)&&(List.for_all (fun x -> not (is_status_implicit x)) args)
  ) impl_st

let extern_record_pattern cstrsp args =
  try
    if !Flags.raw_print then raise Exit;
    let projs = Recordops.lookup_projections (fst cstrsp) in
    if PrintingRecord.active (fst cstrsp) then
      ()
    else if PrintingConstructor.active (fst cstrsp) then
      raise Exit
    else if not (get_record_print ()) then
      raise Exit;
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
let rec extern_cases_pattern_in_scope (custom,scopes as allscopes) vars pat =
  try
    if !Flags.in_debugger || !Flags.raw_print || !print_no_symbol then raise No_match;
    let (na,p,key) = uninterp_prim_token_cases_pattern pat scopes in
    match availability_of_entry_coercion custom InConstrEntrySomeLevel with
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
    match availability_of_entry_coercion custom InConstrEntrySomeLevel with
    | None -> raise No_match
    | Some coercion ->
      let allscopes = (InConstrEntrySomeLevel,scopes) in
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

and apply_notation_to_pattern ?loc gr ((subst,substlist),(no_implicit,nb_to_drop,more_args))
    (custom, (tmp_scope, scopes) as allscopes) vars =
  function
    | NotationRule (_,ntn as specific_ntn) ->
      begin
        match availability_of_entry_coercion custom (fst ntn) with
        | None -> raise No_match
        | Some coercion ->
        match availability_of_notation specific_ntn (tmp_scope,scopes) with
          (* Uninterpretation is not allowed in current context *)
          | None -> raise No_match
          (* Uninterpretation is allowed in current context *)
          | Some (scopt,key) ->
            let scopes' = Option.List.cons scopt scopes in
            let l =
              List.map (fun (c,(subentry,(scopt,scl))) ->
                extern_cases_pattern_in_scope (subentry,(scopt,scl@scopes')) vars c)
                subst in
            let ll =
              List.map (fun (c,(subentry,(scopt,scl))) ->
                let subscope = (subentry,(scopt,scl@scopes')) in
                List.map (extern_cases_pattern_in_scope subscope vars) c)
                substlist in
            let subscopes = find_arguments_scope gr in
            let more_args_scopes = try List.skipn nb_to_drop subscopes with Failure _ -> [] in
            let more_args = fill_arg_scopes more_args more_args_scopes allscopes in
            let l2 = List.map (fun (c,allscopes) -> extern_cases_pattern_in_scope allscopes vars c) more_args in
            let l2' = if Constrintern.get_asymmetric_patterns () || not (List.is_empty ll) then l2
              else
                if no_implicit then l2 else
                  match drop_implicits_in_patt gr nb_to_drop l2 with
                  |Some true_args -> true_args
                  |None -> raise No_match
            in
            insert_pat_coercion coercion
              (insert_pat_delimiters ?loc
                 (make_pat_notation ?loc specific_ntn (l,ll) l2') key)
      end
    | SynDefRule kn ->
      match availability_of_entry_coercion custom InConstrEntrySomeLevel with
      | None -> raise No_match
      | Some coercion ->
      let qid = Nametab.shortest_qualid_of_syndef ?loc vars kn in
      let l1 =
        List.rev_map (fun (c,(subentry,(scopt,scl))) ->
          extern_cases_pattern_in_scope (subentry,(scopt,scl@scopes)) vars c)
          subst in
      let subscopes = find_arguments_scope gr in
      let more_args_scopes = try List.skipn nb_to_drop subscopes with Failure _ -> [] in
      let more_args = fill_arg_scopes more_args more_args_scopes allscopes in
      let l2 = List.map (fun (c,allscopes) -> extern_cases_pattern_in_scope allscopes vars c) more_args in
      let l2' = if Constrintern.get_asymmetric_patterns () then l2
        else
          if no_implicit then l2 else
            match drop_implicits_in_patt gr nb_to_drop l2 with
            |Some true_args -> true_args
            |None -> raise No_match
      in
      assert (List.is_empty substlist);
      insert_pat_coercion ?loc coercion (mkPat ?loc qid (List.rev_append l1 l2'))
and extern_notation_pattern allscopes vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
    try
      if is_inactive_rule keyrule then raise No_match;
      let loc = t.loc in
      match DAst.get t with
        | PatCstr (cstr,args,na) ->
          let t = if na = Anonymous then t else DAst.make ?loc (PatCstr (cstr,args,Anonymous)) in
          let p = apply_notation_to_pattern ?loc (GlobRef.ConstructRef cstr)
            (match_notation_constr_cases_pattern t pat) allscopes vars keyrule in
          insert_pat_alias ?loc p na
        | PatVar Anonymous -> CAst.make ?loc @@ CPatAtom None
        | PatVar (Name id) -> CAst.make ?loc @@ CPatAtom (Some (qualid_of_ident ?loc id))
    with
        No_match -> extern_notation_pattern allscopes vars t rules

let rec extern_notation_ind_pattern allscopes vars ind args = function
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
    try
      if is_inactive_rule keyrule then raise No_match;
      apply_notation_to_pattern (GlobRef.IndRef ind)
        (match_notation_constr_ind_pattern ind args pat) allscopes vars keyrule
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
           |Some true_args -> CAst.make @@ CPatCstr (c, None, true_args)
           |None           -> CAst.make @@ CPatCstr (c, Some args, [])

let extern_cases_pattern vars p =
  extern_cases_pattern_in_scope (InConstrEntrySomeLevel,(None,[])) vars p

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
      let n = Recordops.find_projection_nparams r + 1 in
      if n <= nargs then Some n
      else None
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
let adjust_implicit_arguments inctx n q args impl =
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          !Flags.raw_print ||
          (!print_implicits && !print_implicits_explicit_args) ||
          (is_needed_for_correct_partial_application tail imp) ||
          (!print_implicits_defensive &&
           (not (is_inferable_implicit inctx n imp) || !Flags.beautify) &&
           is_significant_implicit (Lazy.force a))
        in
        if visible then
          (Lazy.force a,Some (make @@ ExplByName (name_of_implicit imp))) :: tail
        else
          tail
    | a::args, _::impl -> (Lazy.force a,None) :: exprec (q+1) (args,impl)
    | args, [] -> List.map (fun a -> (Lazy.force a,None)) args (*In case of polymorphism*)
    | [], (imp :: _) when is_status_implicit imp && maximal_insertion_of imp ->
      (* The non-explicit application cannot be parsed back with the same type *)
      raise Expl
    | [], _ -> []
  in exprec q (args,impl)

let extern_projection (cf,f) args impl =
  let ip = is_projection (List.length args) cf in
  match ip with
    | Some i ->
      (* Careful: It is possible to have declared implicits ending
         before the principal argument *)
      let is_impl =
        try is_status_implicit (List.nth impl (i-1))
        with Failure _ -> false
      in
      if is_impl
      then None
      else
        let (args1,args2) = List.chop i args in
        let (impl1,impl2) = try List.chop i impl with Failure _ -> impl, [] in
        Some (i,(args1,impl1),(args2,impl2))
    | None -> None

let is_start_implicit = function
  | imp :: _ -> is_status_implicit imp && maximal_insertion_of imp
  | [] -> false

let extern_record ref args =
  try
    if !Flags.raw_print then raise Exit;
    let cstrsp = match ref with GlobRef.ConstructRef c -> c | _ -> raise Not_found in
    let struc = Recordops.lookup_structure (fst cstrsp) in
    if PrintingRecord.active (fst cstrsp) then
      ()
    else if PrintingConstructor.active (fst cstrsp) then
      raise Exit
    else if not (get_record_print ()) then
      raise Exit;
    let projs = struc.Recordops.s_PROJ in
    let locals = struc.Recordops.s_PROJKIND in
    let rec cut args n =
      if Int.equal n 0 then args
      else
        match args with
        | [] -> raise No_match
        | _ :: t -> cut t (n - 1) in
    let args = cut args struc.Recordops.s_EXPECTEDPARAM in
    let rec ip projs locs args acc =
      match projs with
      | [] -> acc
      | None :: q -> raise No_match
      | Some c :: q ->
         match locs with
         | [] -> anomaly (Pp.str "projections corruption [Constrextern.extern].")
         | { Recordops.pk_true_proj = false } :: locs' ->
            (* we don't want to print locals *)
            ip q locs' args acc
         | { Recordops.pk_true_proj = true } :: locs' ->
            match args with
            | [] -> raise No_match
            (* we give up since the constructor is not complete *)
            | arg :: tail ->
               let arg = Lazy.force arg in
               let loc = arg.CAst.loc in
               let ref = extern_reference ?loc Id.Set.empty (GlobRef.ConstRef c) in
               ip q locs' tail ((ref, arg) :: acc)
    in
    Some (List.rev (ip projs locals args []))
  with
    | Not_found | No_match | Exit -> None

let extern_global impl f us =
  if not !Constrintern.parsing_explicit && is_start_implicit impl
  then
    CAppExpl ((None, f, us), [])
  else
    CRef (f,us)

(* Implicit args indexes are in ascending order *)
(* inctx is useful only if there is a last argument to be deduced from ctxt *)
let extern_applied_ref inctx impl (cf,f) us args =
  let isproj = is_projection (List.length args) cf in
  try
    if not !Constrintern.parsing_explicit &&
       ((!Flags.raw_print ||
         (!print_implicits && not !print_implicits_explicit_args)) &&
        List.exists is_status_implicit impl)
    then raise Expl;
    let impl = if !Constrintern.parsing_explicit then [] else impl in
    let n = List.length args in
    let ref = CRef (f,us) in
    let f = CAst.make ref in
    match extern_projection (cf,f) args impl with
    (* Try a [t.(f args1) args2] projection-style notation *)
    | Some (i,(args1,impl1),(args2,impl2)) ->
      let args1 = adjust_implicit_arguments inctx n 1 args1 impl1 in
      let args2 = adjust_implicit_arguments inctx n (i+1) args2 impl2 in
      let ip = Some (List.length args1) in
      CApp ((ip,f),args1@args2)
      (* A normal application node with each individual implicit
         arguments either dropped or made explicit *)
    | None ->
      let args = adjust_implicit_arguments inctx n 1 args impl in
      if args = [] then ref else CApp ((None, f), args)
  with Expl ->
  (* A [@f args] node *)
    let args = List.map Lazy.force args in
    let isproj = if !print_projections then isproj else None in
    CAppExpl ((isproj,f,us), args)

let extern_applied_syntactic_definition n extraimpl (cf,f) syndefargs extraargs =
  try
    let syndefargs = List.map (fun a -> (a,None)) syndefargs in
    let extraargs = adjust_implicit_arguments false n (n-List.length extraargs+1) extraargs extraimpl in
    let args = syndefargs @ extraargs in
    if args = [] then cf else CApp ((None, CAst.make cf), args)
  with Expl ->
    let args = syndefargs @ List.map Lazy.force extraargs in
    CAppExpl ((None,f,None), args)

let mkFlattenedCApp (head,args) =
  match head.CAst.v with
  | CApp (g,args') ->
    (* may happen with notations for a prefix of an n-ary application *)
    (* or after removal of a coercion to funclass *)
    CApp (g,args'@args)
  | _ ->
    CApp ((None, head), args)

let extern_applied_notation n impl f args =
  if List.is_empty args then
    f.CAst.v
  else
  try
    let args = adjust_implicit_arguments false n (n-List.length args+1) args impl in
    mkFlattenedCApp (f,args)
  with Expl -> raise No_match

let extern_args extern env args =
  let map (arg, argscopes) = lazy (extern argscopes env arg) in
  List.map map args

let match_coercion_app c = match DAst.get c with
  | GApp (r, args) ->
    begin match DAst.get r with
    | GRef (r,_) -> Some (c.CAst.loc, r, 0, args)
    | _ -> None
    end
  | _ -> None

let remove_one_coercion inctx c =
  try match match_coercion_app c with
  | Some (loc,r,pars,args) when not (!Flags.raw_print || !print_coercions) ->
      let nargs = List.length args in
      (match Coercionops.hide_coercion r with
          | Some n when (n - pars) < nargs && (inctx || (n - pars)+1 < nargs) ->
              (* We skip the coercion *)
              let l = List.skipn (n - pars) args in
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
              Some (n-pars+1, inctx, a')
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
  | _::_, (GProd (_,_,ty',_) | GLambda (_,_,ty',_)) -> glob_constr_eq ty ty'
  | [], _ -> true
  | _ -> assert false

(**********************************************************************)
(* mapping glob_constr to numerals (in presence of coercions, choose the *)
(* one with no delimiter if possible)                                 *)

let extern_possible_prim_token (custom,scopes) r =
   let (n,key) = uninterp_prim_token r scopes in
   match availability_of_entry_coercion custom InConstrEntrySomeLevel with
   | None -> raise No_match
   | Some coercion ->
      insert_entry_coercion coercion (insert_delimiters (CAst.make ?loc:(loc_of_glob_constr r) @@ CPrim n) key)

let filter_enough_applied nargs l =
  match nargs with
  | None -> l
  | Some nargs ->
  List.filter (fun (keyrule,pat,n as _rule) -> match n with Some n -> n > nargs | None -> false) l

(* Helper function for safe and optimal printing of primitive tokens  *)
(* such as those for Int63                                            *)
let extern_prim_token_delimiter_if_required n key_n scope_n scopes =
  match availability_of_prim_token n scope_n scopes with
  | Some None -> CPrim n
  | None -> CDelimiters(key_n, CAst.make (CPrim n))
  | Some (Some key) -> CDelimiters(key, CAst.make (CPrim n))

(**********************************************************************)
(* mapping decl                                                       *)

let extended_glob_local_binder_of_decl loc = function
  | (p,bk,None,t) -> GLocalAssum (p,bk,t)
  | (p,bk,Some x, t) ->
    match DAst.get t with
    | GHole (_, IntroAnonymous, None) -> GLocalDef (p,bk,x,None)
    | _ -> GLocalDef (p,bk,x,Some t)

let extended_glob_local_binder_of_decl ?loc u = DAst.make ?loc (extended_glob_local_binder_of_decl loc u)

(**********************************************************************)
(* mapping special floats                                             *)

(* this helper function is copied from notation.ml as it's not exported *)
let qualid_of_ref n =
  n |> Coqlib.lib_ref |> Nametab.shortest_qualid_of_global Id.Set.empty

let q_infinity () = qualid_of_ref "num.float.infinity"
let q_neg_infinity () = qualid_of_ref "num.float.neg_infinity"
let q_nan () = qualid_of_ref "num.float.nan"

let get_printing_float = Goptions.declare_bool_option_and_ref
    ~depr:false
    ~key:["Printing";"Float"]
    ~value:true

let extern_float f scopes =
  if Float64.is_nan f then CRef(q_nan (), None)
  else if Float64.is_infinity f then CRef(q_infinity (), None)
  else if Float64.is_neg_infinity f then CRef(q_neg_infinity (), None)
  else
    let s =
      let hex = !Flags.raw_print || not (get_printing_float ()) in
      if hex then Float64.to_hex_string f else Float64.to_string f in
    let n = NumTok.Signed.of_string s in
    extern_prim_token_delimiter_if_required (Numeral n)
      "float" "float_scope" scopes

(**********************************************************************)
(* mapping glob_constr to constr_expr                                    *)

let extern_glob_sort = function
  (* In case we print a glob_constr w/o having passed through detyping *)
  | UNamed [(GSProp,0) | (GProp,0) | (GSet,0)] as u -> u
  | UNamed _ when not !print_universes -> UAnonymous {rigid=true}
  | UNamed _ | UAnonymous _ as u -> u

let extern_universes = function
  | Some _ as l when !print_universes -> l
  | _ -> None

let extern_ref vars ref us =
  extern_global (select_stronger_impargs (implicits_of_global ref))
    (extern_reference vars ref) (extern_universes us)

let extern_var ?loc id = CRef (qualid_of_ident ?loc id,None)

let rec extern inctx ?impargs scopes vars r =
  match remove_one_coercion inctx (flatten_application r) with
  | Some (nargs,inctx,r') ->
    (try extern_notations scopes vars (Some nargs) r
     with No_match -> extern inctx scopes vars r')
  | None ->

  try extern_notations scopes vars None r
  with No_match ->

  let loc = r.CAst.loc in
  match DAst.get r with
  | GRef (ref,us) when entry_has_global (fst scopes) -> CAst.make ?loc (extern_ref vars ref us)

  | GVar id when entry_has_global (fst scopes) || entry_has_ident (fst scopes) ->
      CAst.make ?loc (extern_var ?loc id)

  | c ->

  match availability_of_entry_coercion (fst scopes) InConstrEntrySomeLevel with
  | None -> raise No_match
  | Some coercion ->

  let scopes = (InConstrEntrySomeLevel, snd scopes) in
  let c = match c with

  (* The remaining cases are only for the constr entry *)

  | GRef (ref,us) -> extern_ref vars ref us

  | GVar id -> extern_var ?loc id

  | GEvar (n,[]) when !print_meta_as_hole -> CHole (None, IntroAnonymous, None)

  | GEvar (n,l) ->
      extern_evar n (List.map (on_snd (extern false scopes vars)) l)

  | GPatVar kind ->
      if !print_meta_as_hole then CHole (None, IntroAnonymous, None) else
       (match kind with
         | Evar_kinds.SecondOrderPatVar n -> CPatVar n
         | Evar_kinds.FirstOrderPatVar n -> CEvar (n,[]))

  | GApp (f,args) ->
      (match DAst.get f with
         | GRef (ref,us) ->
             let subscopes = find_arguments_scope ref in
             let args = fill_arg_scopes args subscopes scopes in
             let args = extern_args (extern true) vars args in
             (* Try a "{|...|}" record notation *)
             (match extern_record ref args with
             | Some l -> CRecord l
             | None ->
             (* Otherwise... *)
               extern_applied_ref inctx
                 (select_stronger_impargs (implicits_of_global ref))
                 (ref,extern_reference ?loc vars ref) (extern_universes us) args)
         | _ ->
             let args = List.map (fun c -> (sub_extern true scopes vars c,None)) args in
             let head = sub_extern false scopes vars f in
             mkFlattenedCApp (head,args))

  | GLetIn (na,b,t,c) ->
      CLetIn (make ?loc na,sub_extern false scopes vars b,
              Option.map (extern_typ scopes vars) t,
              extern inctx ?impargs scopes (add_vname vars na) c)

  | GProd (na,bk,t,c) ->
      factorize_prod ?impargs scopes vars na bk t c

  | GLambda (na,bk,t,c) ->
      factorize_lambda inctx scopes vars na bk t c

  | GCases (sty,rtntypopt,tml,eqns) ->
    let vars' =
      List.fold_right (Name.fold_right Id.Set.add)
        (cases_predicate_names tml) vars in
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
                              extern_ind_pattern_in_scope scopes vars ind fullargs
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
      let vars' = Array.fold_right Id.Set.add idv vars in
      (match fk with
         | GFix (nv,n) ->
             let listdecl =
               Array.mapi (fun i fi ->
                 let (bl,ty,def) = blv.(i), tyv.(i), bv.(i) in
                 let bl = List.map (extended_glob_local_binder_of_decl ?loc) bl in
                 let (assums,ids,bl) = extern_local_binder scopes vars bl in
                 let vars0 = List.fold_right (Name.fold_right Id.Set.add) ids vars in
                 let vars1 = List.fold_right (Name.fold_right Id.Set.add) ids vars' in
                 let n =
                   match nv.(i) with
                   | None -> None
                   | Some x -> Some (CAst.make @@ CStructRec (CAst.make @@ Name.get_id (List.nth assums x)))
                             in
                 ((CAst.make fi), n, bl, extern_typ scopes vars0 ty,
                  sub_extern true scopes vars1 def)) idv
             in
             CFix (CAst.(make ?loc idv.(n)), Array.to_list listdecl)
         | GCoFix n ->
             let listdecl =
               Array.mapi (fun i fi ->
                 let bl = List.map (extended_glob_local_binder_of_decl ?loc) blv.(i) in
                 let (_,ids,bl) = extern_local_binder scopes vars bl in
                 let vars0 = List.fold_right (Name.fold_right Id.Set.add) ids vars in
                 let vars1 = List.fold_right (Name.fold_right Id.Set.add) ids vars' in
                 ((CAst.make fi),bl,extern_typ scopes vars0 tyv.(i),
                  sub_extern true scopes vars1 bv.(i))) idv
             in
             CCoFix (CAst.(make ?loc idv.(n)),Array.to_list listdecl))

  | GSort s -> CSort (extern_glob_sort s)

  | GHole (e,naming,_) -> CHole (Some e, naming, None) (* TODO: extern tactics. *)

  | GCast (c, c') ->
      CCast (sub_extern true scopes vars c,
             map_cast_type (extern_typ scopes vars) c')

  | GInt i ->
     extern_prim_token_delimiter_if_required
       (Numeral (NumTok.Signed.of_int_string (Uint63.to_string i)))
       "int63" "int63_scope" (snd scopes)

  | GFloat f -> extern_float f (snd scopes)

  in insert_entry_coercion coercion (CAst.make ?loc c)

and extern_typ ?impargs (subentry,(_,scopes)) =
  extern true ?impargs (subentry,(Notation.current_type_scope_name (),scopes))

and sub_extern inctx (subentry,(_,scopes)) = extern inctx (subentry,(None,scopes))

and factorize_prod ?impargs scopes vars na bk t c =
  let implicit_type = is_reserved_type na t in
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
      let p = mkCPatOr (List.map (extern_cases_pattern_in_scope scopes vars) disjpat) in
      let binder = CLocalPattern (make ?loc:c.loc (p,None)) in
      (match b.v with
      | CProdN (bl,b) -> CProdN (binder::bl,b)
      | _ -> CProdN ([binder],b))
     | _ -> assert false)
  | _, _ ->
      let impargs_hd, impargs_tl =
        match impargs with
        | Some [hd] -> Some hd, None
        | Some (hd::tl) -> Some hd, Some tl
        | _ -> None, None in
      let bk = Option.default Explicit impargs_hd in
      let c' = extern_typ ?impargs:impargs_tl scopes vars c in
      match na, c'.v with
      | Name id, CProdN (CLocalAssum(nal,Default bk',ty)::bl,b)
           when binding_kind_eq bk bk'
                && not (occur_var_constr_expr id ty) (* avoid na in ty escapes scope *)
                && (constr_expr_eq aty ty || (constr_expr_eq ty hole && same_binder_type t nal c)) ->
         let ty = if implicit_type then ty else aty in
         CProdN (CLocalAssum(make na::nal,Default bk,ty)::bl,b)
      | _, CProdN (bl,b) ->
         let ty = if implicit_type then hole else aty in
         CProdN (CLocalAssum([make na],Default bk,ty)::bl,b)
      | _, _ ->
         let ty = if implicit_type then hole else aty in
         CProdN ([CLocalAssum([make na],Default bk,ty)],c')

and factorize_lambda inctx scopes vars na bk t c =
  let implicit_type = is_reserved_type na t in
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
      let p = mkCPatOr (List.map (extern_cases_pattern_in_scope scopes vars) disjpat) in
      let binder = CLocalPattern (make ?loc:c.loc (p,None)) in
      (match b.v with
      | CLambdaN (bl,b) -> CLambdaN (binder::bl,b)
      | _ -> CLambdaN ([binder],b))
     | _ -> assert false)
  | _, _ ->
      let c' = sub_extern inctx scopes vars c in
      match c'.v with
      | CLambdaN (CLocalAssum(nal,Default bk',ty)::bl,b)
           when binding_kind_eq bk bk'
                && not (occur_name na ty)  (* avoid na in ty escapes scope *)
                && (constr_expr_eq aty ty || (constr_expr_eq ty hole && same_binder_type t nal c)) ->
         let aty = if implicit_type then ty else aty in
         CLambdaN (CLocalAssum(make na::nal,Default bk,aty)::bl,b)
      | CLambdaN (bl,b) ->
         let ty = if implicit_type then hole else aty in
         CLambdaN (CLocalAssum([make na],Default bk,ty)::bl,b)
      | _ ->
         let ty = if implicit_type then hole else aty in
         CLambdaN ([CLocalAssum([make na],Default bk,ty)],c')

and extern_local_binder scopes vars = function
    [] -> ([],[],[])
  | b :: l ->
    match DAst.get b with
    | GLocalDef (na,bk,bd,ty) ->
      let (assums,ids,l) =
        extern_local_binder scopes (Name.fold_right Id.Set.add na vars) l in
      (assums,na::ids,
       CLocalDef(CAst.make na, extern false scopes vars bd,
                   Option.map (extern false scopes vars) ty) :: l)

    | GLocalAssum (na,bk,ty) ->
      let implicit_type = is_reserved_type na ty in
      let ty = extern_typ scopes vars ty in
      (match extern_local_binder scopes (Name.fold_right Id.Set.add na vars) l with
          (assums,ids,CLocalAssum(nal,k,ty')::l)
            when (constr_expr_eq ty ty' || implicit_type && constr_expr_eq ty' hole) &&
              match na with Name id -> not (occur_var_constr_expr id ty')
                | _ -> true ->
              (na::assums,na::ids,
               CLocalAssum(CAst.make na::nal,k,ty')::l)
        | (assums,ids,l) ->
            let ty = if implicit_type then hole else ty in
            (na::assums,na::ids,
             CLocalAssum([CAst.make na],Default bk,ty) :: l))

    | GLocalPattern ((p,_),_,bk,ty) ->
      let ty =
        if !Flags.raw_print then Some (extern_typ scopes vars ty) else None in
      let p = mkCPatOr (List.map (extern_cases_pattern vars) p) in
      let (assums,ids,l) = extern_local_binder scopes vars l in
      (assums,ids, CLocalPattern(CAst.make @@ (p,ty)) :: l)

and extern_eqn inctx scopes vars {CAst.loc;v=(ids,pll,c)} =
  let pll = List.map (List.map (extern_cases_pattern_in_scope scopes vars)) pll in
  make ?loc (pll,extern inctx scopes vars c)

and extern_notations scopes vars nargs t =
  if !Flags.raw_print || !print_no_symbol then raise No_match;
  try extern_possible_prim_token scopes t
  with No_match ->
  let t = flatten_application t in
  extern_notation scopes vars t (filter_enough_applied nargs (uninterp_notations t))

and extern_notation (custom,scopes as allscopes) vars t rules =
  match rules with
  | [] -> raise No_match
  | (keyrule,pat,n as _rule)::rules ->
      let loc = Glob_ops.loc_of_glob_constr t in
      try
        if is_inactive_rule keyrule then raise No_match;
        let f,args =
          match DAst.get t with
          | GApp (f,args) -> f,args
          | _ -> t,[] in
        let nallargs = List.length args in
        let argsscopes,argsimpls =
          match DAst.get f with
          | GRef (ref,_) ->
            let subscopes = find_arguments_scope ref in
            let impls = select_impargs_size nallargs (implicits_of_global ref) in
            subscopes, impls
          | _ ->
            [], [] in
        (* Adjust to the number of arguments expected by the notation *)
        let (t,args,argsscopes,argsimpls) = match n with
          | Some n when nallargs >= n ->
              let args1, args2 = List.chop n args in
              let args2scopes = try List.skipn n argsscopes with Failure _ -> [] in
              let args2impls =
                if n = 0 then
                  (* Note: NApp(NRef f,[]), hence n=0, encodes @f and
                     conventionally deactivates implicit arguments *)
                  []
                else try List.skipn n argsimpls with Failure _ -> [] in
              DAst.make @@ GApp (f,args1), args2, args2scopes, args2impls
          | None ->
            begin match DAst.get f with
            | GRef (ref,us) -> f, args, argsscopes, argsimpls
            | _ -> t, [], [], []
            end
          | _ -> raise No_match in
        (* Try matching ... *)
        let terms,termlists,binders,binderlists =
          match_notation_constr !print_universes t pat in
        (* Try availability of interpretation ... *)
        match keyrule with
          | NotationRule (_,ntn as specific_ntn) ->
             (match availability_of_entry_coercion custom (fst ntn) with
             | None -> raise No_match
             | Some coercion ->
               match availability_of_notation specific_ntn scopes with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
              | Some (scopt,key) ->
                  let scopes' = Option.List.cons scopt (snd scopes) in
                  let l =
                    List.map (fun (c,(subentry,(scopt,scl))) ->
                      extern (* assuming no overloading: *) true
                        (subentry,(scopt,scl@scopes')) vars c)
                      terms in
                  let ll =
                    List.map (fun (c,(subentry,(scopt,scl))) ->
                      List.map (extern true (subentry,(scopt,scl@scopes')) vars) c)
                      termlists in
                  let bl =
                    List.map (fun (bl,(subentry,(scopt,scl))) ->
                      mkCPatOr (List.map (extern_cases_pattern_in_scope (subentry,(scopt,scl@scopes')) vars) bl))
                      binders in
                  let bll =
                    List.map (fun (bl,(subentry,(scopt,scl))) ->
                      pi3 (extern_local_binder (subentry,(scopt,scl@scopes')) vars bl))
                      binderlists in
                  let c = make_notation loc specific_ntn (l,ll,bl,bll) in
                  let c = insert_entry_coercion coercion (insert_delimiters c key) in
                  let args = fill_arg_scopes args argsscopes allscopes in
                  let args = extern_args (extern true) vars args in
                  CAst.make ?loc @@ extern_applied_notation nallargs argsimpls c args)
          | SynDefRule kn ->
              let l =
                List.map (fun (c,(subentry,(scopt,scl))) ->
                  extern true (subentry,(scopt,scl@snd scopes)) vars c)
                  terms in
              let cf = Nametab.shortest_qualid_of_syndef ?loc vars kn in
              let a = CRef (cf,None) in
              let args = fill_arg_scopes args argsscopes allscopes in
              let args = extern_args (extern true) vars args in
              let c = CAst.make ?loc @@ extern_applied_syntactic_definition nallargs argsimpls (a,cf) l args in
              if isCRef_no_univ c.CAst.v && entry_has_global custom then c
             else match availability_of_entry_coercion custom InConstrEntrySomeLevel with
             | None -> raise No_match
             | Some coercion -> insert_entry_coercion coercion c
      with
          No_match -> extern_notation allscopes vars t rules

let extern_glob_constr vars c =
  extern false (InConstrEntrySomeLevel,(None,[])) vars c

let extern_glob_type ?impargs vars c =
  extern_typ ?impargs (InConstrEntrySomeLevel,(None,[])) vars c

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let extern_constr ?lax ?(inctx=false) ?scope env sigma t =
  let r = Detyping.detype Detyping.Later ?lax false Id.Set.empty env sigma t in
  let vars = vars_of_env env in
  extern inctx (InConstrEntrySomeLevel,(scope,[])) vars r

let extern_constr_in_scope ?lax ?inctx scope env sigma t =
  extern_constr ?lax ?inctx ~scope env sigma t

let extern_type ?lax ?(goal_concl_style=false) env sigma ?impargs t =
  (* "goal_concl_style" means do alpha-conversion using the "goal" convention *)
  (* i.e.: avoid using the names of goal/section/rel variables and the short *)
  (* names of global definitions of current module when computing names for *)
  (* bound variables. *)
  (* Not "goal_concl_style" means do alpha-conversion avoiding only *)
  (* those goal/section/rel variables that occurs in the subterm under *)
  (* consideration; see namegen.ml for further details *)
  let avoid = if goal_concl_style then vars_of_env env else Id.Set.empty in
  let r = Detyping.detype Detyping.Later ?lax goal_concl_style avoid env sigma t in
  extern_glob_type ?impargs (vars_of_env env) r

let extern_sort sigma s = extern_glob_sort (detype_sort sigma s)

let extern_closed_glob ?lax ?(goal_concl_style=false) ?(inctx=false) ?scope env sigma t =
  let avoid = if goal_concl_style then vars_of_env env else Id.Set.empty in
  let r =
    Detyping.detype_closed_glob ?lax goal_concl_style avoid env sigma t
  in
  let vars = vars_of_env env in
  extern inctx (InConstrEntrySomeLevel,(scope,[])) vars r

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let any_any_branch =
  (* | _ => _ *)
  CAst.make ([],[DAst.make @@ PatVar Anonymous], DAst.make @@ GHole (Evar_kinds.InternalHole,IntroAnonymous,None))

let compute_displayed_name_in_pattern sigma avoid na c =
  let open Namegen in
  compute_displayed_name_in_gen (fun _ -> Patternops.noccurn_pattern) sigma avoid na c

let rec glob_of_pat avoid env sigma pat = DAst.make @@ match pat with
  | PRef ref -> GRef (ref,None)
  | PVar id  -> GVar id
  | PEvar (evk,l) ->
      let test decl = function PVar id' -> Id.equal (NamedDecl.get_id decl) id' | _ -> false in
      let l = Evd.evar_instance_array test (Evd.find sigma evk) l in
      let id = match Evd.evar_ident evk sigma with
      | None -> Id.of_string "__"
      | Some id -> id
      in
      GEvar (id,List.map (on_snd (glob_of_pat avoid env sigma)) l)
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
        | Name id   -> id
        | Anonymous ->
            anomaly ~label:"glob_constr_of_pattern" (Pp.str "index to an anonymous variable.")
      with Not_found -> Id.of_string ("_UNBOUND_REL_"^(string_of_int n)) in
      GVar id
  | PMeta None -> GHole (Evar_kinds.InternalHole, IntroAnonymous,None)
  | PMeta (Some n) -> GPatVar (Evar_kinds.FirstOrderPatVar n)
  | PProj (p,c) -> GApp (DAst.make @@ GRef (GlobRef.ConstRef (Projection.constant p),None),
                         [glob_of_pat avoid env sigma c])
  | PApp (f,args) ->
      GApp (glob_of_pat avoid env sigma f,Array.map_to_list (glob_of_pat avoid env sigma) args)
  | PSoApp (n,args) ->
      GApp (DAst.make @@ GPatVar (Evar_kinds.SecondOrderPatVar n),
        List.map (glob_of_pat avoid env sigma) args)
  | PProd (na,t,c) ->
      let na',avoid' = compute_displayed_name_in_pattern sigma avoid na c in
      let env' = Termops.add_name na' env in
      GProd (na',Explicit,glob_of_pat avoid env sigma t,glob_of_pat avoid' env' sigma c)
  | PLetIn (na,b,t,c) ->
      let na',avoid' = Namegen.compute_displayed_let_name_in sigma Namegen.RenamingForGoal avoid na c in
      let env' = Termops.add_name na' env in
      GLetIn (na',glob_of_pat avoid env sigma b, Option.map (glob_of_pat avoid env sigma) t,
              glob_of_pat avoid' env' sigma c)
  | PLambda (na,t,c) ->
      let na',avoid' = compute_displayed_name_in_pattern sigma avoid na c in
      let env' = Termops.add_name na' env in
      GLambda (na',Explicit,glob_of_pat avoid env sigma t, glob_of_pat avoid' env' sigma c)
  | PIf (c,b1,b2) ->
      GIf (glob_of_pat avoid env sigma c, (Anonymous,None),
           glob_of_pat avoid env sigma b1, glob_of_pat avoid env sigma b2)
  | PCase ({cip_style=Constr.LetStyle; cip_ind_tags=None},PMeta None,tm,[(0,n,b)]) ->
      let nal,b = it_destRLambda_or_LetIn_names n (glob_of_pat avoid env sigma b) in
      GLetTuple (nal,(Anonymous,None),glob_of_pat avoid env sigma tm,b)
  | PCase (info,p,tm,bl) ->
      let mat = match bl, info.cip_ind with
        | [], _ -> []
        | _, Some ind ->
          let bl' = List.map (fun (i,n,c) -> (i,n,glob_of_pat avoid env sigma c)) bl in
          simple_cases_matrix_of_branches ind bl'
        | _, None -> anomaly (Pp.str "PCase with some branches but unknown inductive.")
      in
      let mat = if info.cip_extensible then mat @ [any_any_branch] else mat
      in
      let indnames,rtn = match p, info.cip_ind, info.cip_ind_tags with
        | PMeta None, _, _ -> (Anonymous,None),None
        | _, Some ind, Some nargs ->
          return_type_of_predicate ind nargs (glob_of_pat avoid env sigma p)
        | _ -> anomaly (Pp.str "PCase with non-trivial predicate but unknown inductive.")
      in
      GCases (Constr.RegularStyle,rtn,[glob_of_pat avoid env sigma tm,indnames],mat)
  | PFix ((ln,i),(lna,tl,bl)) ->
     let def_avoid, def_env, lfi =
       Array.fold_left
         (fun (avoid, env, l) na ->
           let id = Namegen.next_name_away na avoid in
           (Id.Set.add id avoid, Name id :: env, id::l))
      (avoid, env, []) lna in
     let n = Array.length tl in
     let v = Array.map3
               (fun c t i -> Detyping.share_pattern_names glob_of_pat (Option.get i + 1) [] def_avoid def_env sigma c (Patternops.lift_pattern n t))
    bl tl ln in
     GRec(GFix (ln,i),Array.of_list (List.rev lfi),
       Array.map (fun (bl,_,_) -> bl) v,
       Array.map (fun (_,_,ty) -> ty) v,
       Array.map (fun (_,bd,_) -> bd) v)
  | PCoFix (ln,(lna,tl,bl)) ->
     let def_avoid, def_env, lfi =
       Array.fold_left
         (fun (avoid, env, l) na ->
           let id = Namegen.next_name_away na avoid in
           (Id.Set.add id avoid, Name id :: env, id::l))
         (avoid, env, []) lna in
     let ntys = Array.length tl in
     let v = Array.map2
               (fun c t -> share_pattern_names glob_of_pat 0 [] def_avoid def_env sigma c (Patternops.lift_pattern ntys t))
               bl tl in
     GRec(GCoFix ln,Array.of_list (List.rev lfi),
          Array.map (fun (bl,_,_) -> bl) v,
          Array.map (fun (_,_,ty) -> ty) v,
          Array.map (fun (_,bd,_) -> bd) v)
  | PSort Sorts.InSProp -> GSort (UNamed [GSProp,0])
  | PSort Sorts.InProp -> GSort (UNamed [GProp,0])
  | PSort Sorts.InSet -> GSort (UNamed [GSet,0])
  | PSort Sorts.InType -> GSort (UAnonymous {rigid=true})
  | PInt i -> GInt i
  | PFloat f -> GFloat f

let extern_constr_pattern env sigma pat =
  extern true (InConstrEntrySomeLevel,(None,[])) Id.Set.empty (glob_of_pat Id.Set.empty env sigma pat)

let extern_rel_context where env sigma sign =
  let a = detype_rel_context Detyping.Later where Id.Set.empty (names_of_rel_context env,env) sigma sign in
  let vars = vars_of_env env in
  let a = List.map (extended_glob_local_binder_of_decl) a in
  pi3 (extern_local_binder (InConstrEntrySomeLevel,(None,[])) vars a)
