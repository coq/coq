(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(*i*)
open Pp
open Util
open Univ
open Names
open Nameops
open Term
open Termops
open Inductive
open Sign
open Environ
open Libnames
open Impargs
open Topconstr
open Rawterm
open Pattern
open Nametab
open Symbols
open Reserve
(*i*)

(* Translation from rawconstr to front constr *)

(**********************************************************************)
(* Parametrization                                                    *)

(* This governs printing of local context of references *)
let print_arguments = ref false

(* If true, prints local context of evars, whatever print_arguments *)
let print_evar_arguments = ref false

(* This governs printing of implicit arguments.  When
   [print_implicits] is on then [print_implicits_explicit_args] tells
   how implicit args are printed. If on, implicit args are printed
   prefixed by "!" otherwise the function and not the arguments is
   prefixed by "!" *)
let print_implicits = ref false
let print_implicits_explicit_args = ref false

(* This forces printing of coercions *)
let print_coercions = ref false

(* This forces printing universe names of Type{.} *)
let print_universes = ref false

(* This suppresses printing of numeral and symbols *)
let print_no_symbol = ref false

let print_meta_as_hole = ref false

let with_arguments f = Options.with_option print_arguments f
let with_implicits f = Options.with_option print_implicits f
let with_coercions f = Options.with_option print_coercions f
let with_universes f = Options.with_option print_universes f
let without_symbols f = Options.with_option print_no_symbol f
let with_meta_as_hole f = Options.with_option print_meta_as_hole f

(* For the translator *)
let temporary_implicits_out = ref []
let set_temporary_implicits_out l = temporary_implicits_out := l
let get_temporary_implicits_out id =
  try List.assoc id !temporary_implicits_out
  with Not_found -> []

(**********************************************************************)
(* Various externalisation functions *)

let insert_delimiters e = function
  | None -> e
  | Some sc -> CDelimiters (dummy_loc,sc,e)

let insert_pat_delimiters e = function
  | None -> e
  | Some sc -> CPatDelimiters (dummy_loc,sc,e)

(**********************************************************************)
(* conversion of references                                           *)

let ids_of_ctxt ctxt =
  Array.to_list
    (Array.map
       (function c -> match kind_of_term c with
	  | Var id -> id
	  | _ ->
       error
       "Termast: arbitrary substitution of references not yet implemented")
     ctxt)

let idopt_of_name = function 
  | Name id -> Some id
  | Anonymous -> None

let extern_evar loc n =
(*
  msgerrnl (str 
    "Warning: existential variable turned into meta-variable during externalization");
  CPatVar (loc,(false,make_ident "META" (Some n)))
*)
  CEvar (loc,n)

let raw_string_of_ref = function
  | ConstRef kn -> 
      "CONST("^(string_of_kn kn)^")"
  | IndRef (kn,i) ->
      "IND("^(string_of_kn kn)^","^(string_of_int i)^")"
  | ConstructRef ((kn,i),j) -> 
      "CONSTRUCT("^
      (string_of_kn kn)^","^(string_of_int i)^","^(string_of_int j)^")"
  | VarRef id -> 
      "SECVAR("^(string_of_id id)^")"

(* v7->v8 translation *)

let name_app f = function
  | Name id -> Name (f id)
  | Anonymous -> Anonymous

let avoid_wildcard_string s =
  if s = "_" then "x_" else s

let avoid_wildcard id =
  if id = id_of_string "_" then id_of_string "x_" else id

let translate_keyword = function
  | ("forall" | "fun" | "match" | "fix" | "cofix" | "for" | "let"
    | "if"  | "then" | "else" | "return" | "mod" as s) ->
      let s' = s^"_" in
      msgerrnl
      (str ("Warning: '"^
          s^"' is now a keyword; it has been translated to '"^s'^"'"));
      s'
  | s -> s

let is_coq_root d =
  let d = repr_dirpath d in d <> [] & string_of_id (list_last d) = "Coq"

let is_module m =
  let d = repr_dirpath (Lib.library_dp()) in
  d <> [] & string_of_id (List.hd d) = m

let translate_v7_string = function
  (* ZArith *)
  | "double_moins_un" -> "Pdouble_minus_one"
  | "double_moins_deux" -> "Pdouble_minus_two"
  | "double_moins_un_add_un" -> "xI_eq_Pdouble_minus_one_Psucc"
  | "add_un_double_moins_un_xO" -> "Psucc_Pdouble_minus_one_eq_xO"
  | "add_un_Zs" -> "Psucc_Zs" (* POS_is_succ_morphism ? *)
  | "entier" -> "N"
  | "SUPERIEUR" -> "Gt"
  | "EGAL" -> "Eq"
  | "INFERIEUR" -> "Lt"
  | "add" -> "Pplus"
  | "add_carry" -> "Pplus_carry"
  | "add_assoc" -> "Pplus_assoc"
  | "add_sym" -> "Pplus_comm"
  | "add_x_x" -> "Pplus_x_x"
  | "add_carry_add" -> "Pplus_carry_Pplus"
  | "simpl_add_r" -> "Pplus_simpl_r"
  | "simpl_add_l" -> "Pplus_simpl_l"
  | "simpl_add_carry_r" -> "Pplus_carry_simpl_r"
  | "simpl_add_carry_l" -> "Pplus_carry_simpl_l"
  | "xO_xI_add_double_moins_un" -> "xO_xI_Pplus_Pdouble_minus_one"
  | "double_moins_un_plus_xO_double_moins_un" ->
      "Pdouble_minus_one_Pplus_xO_Pdouble_minus_one"
  | "add_xI_double_moins_un" -> "Pplus_xI_Pdouble_minus_one"
  | "iter_pos_add" -> "iter_pos_Pplus"
  | "add_no_neutral" -> "Pplus_no_neutral"
  | "add_carry_not_add_un" -> "Pplus_carry_no_neutral"
  | "times" when not (is_module "Mapfold") -> "Pmult"
  | "times_add_distr" -> "Pmult_Pplus_distr_r"
  | "times_add_distr_l" -> "Pmult_Pplus_distr_l"
  | "times_true_sub_distr" -> "Pmult_Pminus_distr_r"
  | "times_sym" -> "Pmult_comm"
  | "times_assoc" -> "Pmult_assoc"
  | "times_convert" -> "IPN_Pmult_morphism"
  | "true_sub" -> "Pminus"
  | "times_x_1" -> "Pmult_1_right"
  | "times_x_double" -> "Pmult_xO_permute_r"
  | "times_x_double_plus_one" -> "Pmult_xI_permute_r"
  | "true_sub_convert" -> "IPN_Pminus_morphism"
  | "compare_true_sub_right" -> "Pcompare_Pminus_r"
  | "compare_true_sub_left" -> "Pcompare_Pminus_l"
  | "sub_add" -> "Lt_Pplus_Pminus" (* equiv de le_plus_minus de Arith *)
  | "sub_add_one" -> "Ppred_Psucc"
  | "add_sub_one" -> "Psucc_Ppred"
  | "add_un" -> "Psucc"
  | "add_un_not_un" -> "Psucc_not_one"
  | "add_un_inj" -> "Psucc_inj"
  | "xI_add_un_xO" -> "xI_Psucc_xO"
  | "ZL14" -> "Pplus_Psucc_permute_r"
  | "ZL14bis" -> "Pplus_Psucc_permute_l"
  | "sub_un" -> "Ppred"
  | "sub_pos" -> "PNminus"
  | "sub_pos_x_x" -> "PNminus_x_x"
  | "sub_pos_SUPERIEUR" -> "PNminus_Gt"
  | "sub_neg" -> "PNminus_carry"
  | "Nul" -> "N0"
  | "Un_suivi_de" -> "Pdouble_plus_one_mask"
  | "Zero_suivi_de" -> "Pdouble_mask"
  | "ZS" -> "double_eq_zero_inversion"
  | "US" -> "double_plus_one_zero_discr"
  | "USH" -> "double_plus_one_eq_one_inversion"
  | "ZSH" -> "double_eq_one_discr"
  | "is_double_moins_un" -> "Psucc_Pdouble_minus_one_xO"
  | "double_moins_un_add_un_xI" -> "Pdouble_minus_one_Psucc_xI"
  | "ZL1" -> "xO_Psucc_permute"
  | "Zplus_sym" -> "Zplus_comm"
  | "Zmult_sym" -> "Zmult_comm"
  | "inject_nat" -> "INZ"
  | "inject_nat_complete" -> "INZ_complete"
  | "inject_nat_complete_inf" -> "INZ_complete_inf"
  | "inject_nat_prop" -> "INZ_prop"
  | "inject_nat_set" -> "INZ_set"
  | "convert" -> "IPN"
  | "anti_convert" -> "INP_succ"
  | "positive_to_nat" -> "IPN_shift"
  | "convert_intro" -> "IPN_inj"
  | "convert_add" -> "IPN_Pplus_morphism"
  | "convert_add_un" -> "IPN_shift_Psucc"
  | "convert_add_carry" -> "IPN_shift_Pplus_carry"
  | "compare_convert_O" -> "lt_O_IPN"
  | "Zopp_intro" -> "Zopp_inj"
  | "add_verif" -> "IPN_shift_Pplus_morphism"
  | "cvt_carry" -> "IPN_Pplus_carry"
  | "iter_convert" -> "iter_IPN"
  | "compare" -> "Pcompare"
  | "compare_convert1" -> "Pcompare_not_Eq"
  | "compare_convert_INFERIEUR" -> "IPN_lt_morphism1_Pcompare"
  | "compare_convert_SUPERIEUR" -> "IPN_gt_morphism1_Pcompare"
  | "compare_convert_EGAL"      -> "compare_Eq_eq"
  | "convert_compare_INFERIEUR" -> "IPN_lt_morphism2_Pcompare"
  | "convert_compare_SUPERIEUR" -> "IPN_gt_morphism2_Pcompare"
  | "convert_compare_EGAL"      -> "Pcompare_refl"
  | "Zcompare_EGAL"             -> "Zcompare_Eq_eq"
  | "Zcompare_et_un"            -> "Zcompare_Gt_not_Lt"
  | "Zcompare_trans_SUPERIEUR"  -> "Zcompare_Gt_trans"
  | "SUPERIEUR_POS"             -> "Zcompare_Gt_POS"
  | "compare_positive_to_nat_O" -> "le_IPN_shift"
  | "ZLSI" -> "ZLGtLt"
  | "ZLIS" -> "ZLLtGt"
  | "ZLII" -> "ZLLtLt"
  | "ZLSS" -> "ZLGtGt"
  | "bij1" -> "IPN_INP_succ_eq_succ"
  | "bij2" -> "INP_succ_IPN_eq_succ"
  | "bij3" -> "pred_INP_succ_IPN_bij"
  | "absolu" -> "Zabs_nat"
  | "absolu_lt" -> "Zabs_nat_lt" (* "Zabs_nat_lt_morphism_pos" ? *)
  | "Zeq_add_S" -> "Zs_inj"
  (* IntMap *)
  | "convert_xH" -> "IPN_xH"
  | "convert_xO" -> "IPN_xO"
  | "convert_xI" -> "IPN_xI"
  | "positive_to_nat_mult" -> "IPN_shift_mult"
  | "positive_to_nat_2" -> "IPN_shift_2"
  | "positive_to_nat_4" -> "IPN_shift_4"
  (* Arith *)
  | "plus_sym" -> "plus_comm"
  | "mult_sym" -> "mult_comm"
  | "max_sym" -> "max_comm"
  | "min_sym" -> "min_comm"
  | "gt_not_sym" -> "gt_asym"
  | "simpl_plus_l" -> "plus_simpl_l"
  | "simpl_plus_r" -> "plus_simpl_r"
  | "fact_growing" -> "fact_le"
  | "lt_mult_left" -> "lt_mult_S_left"
  (* Lists *)
  | "idempot_rev" -> "involutive_rev"
  | "forall" -> "HereAndFurther"
  (* Bool *)
  | "orb_sym" -> "orb_comm"
  | "andb_sym" -> "andb_comm"
  (* Reals *)
  | s when String.length s >= 7 & (String.sub s 0 7 = "Rabsolu") ->
      "Rabs"^(String.sub s 7 (String.length s - 7))
  | s when String.length s >= 7 &
      (String.sub s (String.length s - 7) 7 = "Rabsolu") ->
      (String.sub s 0 (String.length s - 7))^"Rabs"
(*
  | "Rabsolu" -> "Rabs"
  | "Rabsolu_pos_lt" -> "Rabs_pos_lt"
  | "Rabsolu_no_R0" -> "Rabs_no_R0"
  | "Rabsolu_Rabsolu" -> "Rabs_Rabs"
  | "Rabsolu_mult" -> "Rabs_mult"
  | "Rabsolu_triang" -> "Rabs_triang"
  | "Rabsolu_Ropp" -> "Rabs_Ropp"
  | "Rabsolu_right" -> "Rabs_right"
...
  | "case_Rabsolu" -> "case_Rabs"
  | "Pow_Rabsolu" -> "Pow_Rabs"
...
*)
  | "Rle_sym1" -> "Rle_ge"
  | "Rmin_sym" -> "Rmin_comm"
  | "Rsqr_times" -> "Rsqr_mult"
  | "sqrt_times" -> "sqrt_mult"
  | s when String.length s >= 7 & 
      let s' = String.sub s 0 7 in
      (s' = "unicite" or s' = "unicity") ->
      "uniqueness"^(String.sub s 7 (String.length s - 7))
  (* Default *)
  | "_" -> 
      msgerrnl (str 
	"Warning: '_' is no longer an ident; it has been translated to 'x_'");
      "x_"
  | x -> x

let id_of_v7_string s =
  id_of_string (if !Options.v7 then s else translate_v7_string s)

let v7_to_v8_dir_id dir id =
  if Options.do_translate() then
    let s = string_of_id id in
    let s = 
      if (is_coq_root (Lib.library_dp()) or is_coq_root dir)
      then translate_v7_string s else avoid_wildcard_string s in
    id_of_string (translate_keyword s)
  else id

let v7_to_v8_id id = v7_to_v8_dir_id empty_dirpath id

let shortest_qualid_of_v7_global ctx ref =
  let fulldir,_ = repr_path (sp_of_global ref) in
  let dir,id = repr_qualid (shortest_qualid_of_global ctx ref) in
  make_qualid dir (v7_to_v8_dir_id fulldir id)

let extern_reference loc vars r =
  try Qualid (loc,shortest_qualid_of_v7_global vars r)
  with Not_found ->
    (* happens in debugger *)
    Ident (loc,id_of_string (raw_string_of_ref r))

(***********************************************************************)
(* Equality up to location (useful for translator v8) *)

let rec check_same_pattern p1 p2 =
  match p1, p2 with
    | CPatAlias(_,a1,i1), CPatAlias(_,a2,i2) when i1=i2 ->
        check_same_pattern a1 a2
    | CPatCstr(_,c1,a1), CPatCstr(_,c2,a2) when c1=c2 ->
        List.iter2 check_same_pattern a1 a2
    | CPatAtom(_,r1), CPatAtom(_,r2) when r1=r2 -> ()
    | CPatNumeral(_,i1), CPatNumeral(_,i2) when i1=i2 -> ()
    | CPatDelimiters(_,s1,e1), CPatDelimiters(_,s2,e2) when s1=s2 ->
        check_same_pattern e1 e2
    | _ -> failwith "not same pattern"

let check_same_ref r1 r2 =
  match r1,r2 with
  | Qualid(_,q1), Qualid(_,q2) when q1=q2 -> ()
  | Ident(_,i1), Ident(_,i2) when i1=i2 -> ()
  | _ -> failwith "not same ref"

let rec check_same_type ty1 ty2 =
  match ty1, ty2 with
  | CRef r1, CRef r2 -> check_same_ref r1 r2
  | CFix(_,(_,id1),fl1), CFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,i1,a1,b1) (id2,i2,a2,b2) ->
        if id1<>id2 || i1<>i2 then failwith "not same fix";
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CCoFix(_,(_,id1),fl1), CCoFix(_,(_,id2),fl2) when id1=id2 ->
      List.iter2 (fun (id1,a1,b1) (id2,a2,b2) ->
        if id1<>id2 then failwith "not same fix";
        check_same_type a1 a2;
        check_same_type b1 b2)
        fl1 fl2
  | CArrow(_,a1,b1), CArrow(_,a2,b2) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CProdN(_,bl1,a1), CProdN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLambdaN(_,bl1,a1), CLambdaN(_,bl2,a2) ->
      List.iter2 check_same_binder bl1 bl2;
      check_same_type a1 a2
  | CLetIn(_,(_,na1),a1,b1), CLetIn(_,(_,na2),a2,b2) when na1=na2 ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CAppExpl(_,r1,al1), CAppExpl(_,r2,al2) when r1=r2 ->
      List.iter2 check_same_type al1 al2
  | CApp(_,(_,e1),al1), CApp(_,(_,e2),al2) ->
      check_same_type e1 e2;
      List.iter2 (fun (a1,e1) (a2,e2) ->
                    if e1<>e2 then failwith "not same expl";
                    check_same_type a1 a2) al1 al2
  | CCases(_,_,a1,brl1), CCases(_,_,a2,brl2) ->
      List.iter2 (fun (tm1,_) (tm2,_) -> check_same_type tm1 tm2) a1 a2;
      List.iter2 (fun (_,pl1,r1) (_,pl2,r2) ->
        List.iter2 check_same_pattern pl1 pl2;
        check_same_type r1 r2) brl1 brl2
  | COrderedCase(_,_,_,a1,bl1), COrderedCase(_,_,_,a2,bl2) ->
      check_same_type a1 a2;
      List.iter2 check_same_type bl1 bl2
  | CHole _, CHole _ -> ()
  | CPatVar(_,i1), CPatVar(_,i2) when i1=i2 -> ()
  | CSort(_,s1), CSort(_,s2) when s1=s2 -> ()
  | CCast(_,a1,b1), CCast(_,a2,b2) ->
      check_same_type a1 a2;
      check_same_type b1 b2
  | CNotation(_,n1,e1), CNotation(_,n2,e2) when n1=n2 ->
      List.iter2 check_same_type e1 e2
  | CNumeral(_,i1), CNumeral(_,i2) when i1=i2 -> ()
  | CDelimiters(_,s1,e1), CDelimiters(_,s2,e2) when s1=s2 ->
      check_same_type e1 e2
  | _ when ty1=ty2 -> ()
  | _ -> failwith "not same type"

and check_same_binder (nal1,e1) (nal2,e2) =
  List.iter2 (fun (_,na1) (_,na2) ->
    if na1<>na2 then failwith "not same name") nal1 nal2;
  check_same_type e1 e2

let same c d = try check_same_type c d; true with _ -> false

(**********************************************************************)
(* conversion of terms and cases patterns                             *)

let make_current_scope (scopt,scopes) = option_cons scopt scopes

let rec extern_cases_pattern_in_scope scopes vars pat =
  try 
    if !print_no_symbol then raise No_match;
    let (sc,n) = Symbols.uninterp_cases_numeral pat in
    match Symbols.availability_of_numeral sc scopes with
    | None -> raise No_match
    | Some key ->
        let loc = pattern_loc pat in
        insert_pat_delimiters (CPatNumeral (loc,n)) key
  with No_match ->
  match pat with
  | PatVar (loc,Name id) -> CPatAtom (loc,Some (Ident (loc,v7_to_v8_id id)))
  | PatVar (loc,Anonymous) -> CPatAtom (loc, None) 
  | PatCstr(loc,cstrsp,args,na) ->
      let args = List.map (extern_cases_pattern_in_scope scopes vars) args in
      let p = CPatCstr
        (loc,extern_reference loc vars (ConstructRef cstrsp),args) in
      (match na with
	| Name id -> CPatAlias (loc,p,v7_to_v8_id id)
	| Anonymous -> p)
	
let occur_name na aty =
  match na with
    | Name id -> occur_var_constr_expr id aty
    | Anonymous -> false

let is_projection nargs = function
  | Some r ->
      (try 
	let n = Recordops.find_projection_nparams r + 1 in
	if n <= nargs then Some n else None
      with Not_found -> None)
  | None -> None

let stdlib = function
  | Some r -> 
      let dir,id = repr_path (sp_of_global r) in
      (is_coq_root (Lib.library_dp()) or is_coq_root dir)
      && not (List.mem (string_of_id id) 
        ["Zlength";"Zlength_correct";"eq_ind"])
  | None -> false

let explicit_code imp q =
  dummy_loc,
  if !Options.v7 & not (Options.do_translate()) then ExplByPos q
  else ExplByName (name_of_implicit imp)

(* Implicit args indexes are in ascending order *)
(* inctx is useful only if there is a last argument to be deduced from ctxt *)
let explicitize loc inctx impl (cf,f) args =
  let n = List.length args in
  let rec exprec q = function
    | a::args, imp::impl when is_status_implicit imp ->
        let tail = exprec (q+1) (args,impl) in
        let visible =
          (!print_implicits & !print_implicits_explicit_args)
          or (not (is_inferable_implicit inctx n imp))
	  or ((match a with CHole _ -> false | _ -> true)
	      & Options.do_translate() & not (stdlib cf)) in
        if visible then (a,Some (explicit_code imp q)) :: tail else tail
    | a::args, _::impl -> (a,None) :: exprec (q+1) (args,impl)
    | args, [] -> List.map (fun a -> (a,None)) args (*In case of polymorphism*)
    | [], _ -> [] in
  match is_projection (List.length args) cf with
    | Some i as ip ->
	if impl <> [] & is_status_implicit (List.nth impl (i-1)) then
	  let f' = match f with CRef f -> f | _ -> assert false in
	  CAppExpl (loc,(ip,f'),args)
	else
	  let (args1,args2) = list_chop i args in
	  let (impl1,impl2) = if impl=[] then [],[] else list_chop i impl in
	  let args1 = exprec 1 (args1,impl1) in
	  let args2 = exprec (i+1) (args2,impl2) in
	  CApp (loc,(Some (List.length args1),f),args1@args2)
    | None -> 
	let args = exprec 1 (args,impl) in
	if args = [] then f else CApp (loc, (None, f), args)

let rec skip_coercion dest_ref (f,args as app) =
  if !print_coercions or Options.do_translate () then app
  else
    try
      match dest_ref f with
	| Some r ->
	    (match Classops.hide_coercion r with
	       | Some n ->
		   if n >= List.length args then app
		   else (* We skip a coercion *)
		     let fargs = list_skipn n args in
	       	     skip_coercion dest_ref (List.hd fargs,List.tl fargs)
	       | None -> app)
	| None -> app
    with Not_found -> app

let extern_global loc impl f =
  if impl <> [] & List.for_all is_status_implicit impl then
    CAppExpl (loc, (None, f), [])
  else
    CRef f

let extern_app loc inctx impl (cf,f) args =
  if args = [] (* maybe caused by a hidden coercion *) then
    extern_global loc impl f
  else
  if !print_implicits &
    not !print_implicits_explicit_args &
    List.exists is_status_implicit impl
  then 
    CAppExpl (loc, (is_projection (List.length args) cf, f), args)
  else
    explicitize loc inctx impl (cf,CRef f) args

let rec extern_args extern scopes env args subscopes =
  match args with
    | [] -> []
    | a::args ->
	let argscopes, subscopes = match subscopes with
	  | [] -> (None,scopes), []
	  | scopt::subscopes -> (scopt,scopes), subscopes in
	extern argscopes env a :: extern_args extern scopes env args subscopes

let rec extern inctx scopes vars r =
  try 
    if !print_no_symbol then raise No_match;
    extern_numeral (Rawterm.loc_of_rawconstr r)
      scopes (Symbols.uninterp_numeral r)
  with No_match ->

  try 
    if !print_no_symbol then raise No_match;
    extern_symbol scopes vars r (Symbols.uninterp_notations r)
  with No_match -> match r with
  | RRef (loc,ref) ->
      extern_global loc (implicits_of_global_out ref)
        (extern_reference loc vars ref)

  | RVar (loc,id) -> CRef (Ident (loc,v7_to_v8_id id))

  | REvar (loc,n) -> extern_evar loc n

  | RPatVar (loc,n) -> if !print_meta_as_hole then CHole loc else CPatVar (loc,n)

  | RApp (loc,f,args) ->
      let (f,args) =
	if inctx then
	  skip_coercion (function RRef(_,r) -> Some r | _ -> None) (f,args)
	else 
	  (f,args) in
      (match f with
	 | REvar (loc,ev) -> extern_evar loc ev (* we drop args *)
	 | RRef (rloc,ref) ->
	     let subscopes = Symbols.find_arguments_scope ref in
	     let args =
	       extern_args (extern true) (snd scopes) vars args subscopes in
	     extern_app loc inctx (implicits_of_global_out ref)
               (Some ref,extern_reference rloc vars ref)
	       args
	 | RVar (rloc,id) -> (* useful for translation of inductive *)
	     let args = List.map (sub_extern true scopes vars) args in
	     extern_app loc inctx (get_temporary_implicits_out id)
	       (None,Ident (rloc,v7_to_v8_id id))
	       args
	 | _       -> 
	     explicitize loc inctx [] (None,sub_extern false scopes vars f)
               (List.map (sub_extern true scopes vars) args))

  | RProd (loc,Anonymous,t,c) ->
      (* Anonymous product are never factorized *)
      CArrow (loc,extern_type scopes vars t, extern_type scopes vars c)

  | RLetIn (loc,na,t,c) ->
      let na = name_app avoid_wildcard na in
      CLetIn (loc,(loc,na),sub_extern false scopes vars t,
              extern inctx scopes (add_vname vars na) c)

  | RProd (loc,na,t,c) ->
      let t = extern_type scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_prod scopes (add_vname vars na) t c in
      CProdN (loc,[(dummy_loc,na)::idl,t],c)

  | RLambda (loc,na,t,c) ->
      let t = extern_type scopes vars (anonymize_if_reserved na t) in
      let (idl,c) = factorize_lambda inctx scopes (add_vname vars na) t c in
      CLambdaN (loc,[(dummy_loc,na)::idl,t],c)

  | RCases (loc,(typopt,rtntypopt),tml,eqns) ->
      let pred = option_app (extern_type scopes vars) typopt in
      let rtntypopt = option_app (extern_type scopes vars) !rtntypopt in
      let vars' = 
	List.fold_right (name_fold Idset.add)
	  (cases_predicate_names tml) vars in
      let tml = List.map (fun (tm,{contents=(na,x)}) ->
	(sub_extern false scopes vars tm,
	(na,option_app (fun (loc,ind,nal) ->
	  let args = List.map (function
	    | Anonymous -> RHole (dummy_loc,InternalHole) 
	    | Name id -> RVar (dummy_loc,id)) nal in
	  let t = RApp (dummy_loc,RRef (dummy_loc,IndRef ind),args) in
	  (extern_type scopes vars t)) x))) tml in
      let eqns = List.map (extern_eqn (typopt<>None) scopes vars) eqns in 
      CCases (loc,(pred,rtntypopt),tml,eqns)

  | ROrderedCase (loc,cs,typopt,tm,bv,{contents = Some x}) ->
      extern false scopes vars x

  | ROrderedCase (loc,cs,typopt,tm,bv,_) ->
      let bv = Array.map (sub_extern (typopt<>None) scopes vars) bv in
      COrderedCase
	(loc,cs,option_app (extern_type scopes vars) typopt,
         sub_extern false scopes vars tm,Array.to_list bv)

  | RLetTuple (loc,nal,(na,typopt),tm,b) ->
      CLetTuple (loc,nal,
        (na,option_app (extern_type scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars tm,
        extern false scopes (List.fold_left add_vname vars nal) b)

  | RIf (loc,c,(na,typopt),b1,b2) ->
      CIf (loc,sub_extern false scopes vars c,
        (na,option_app (extern_type scopes (add_vname vars na)) typopt),
        sub_extern false scopes vars b1, sub_extern false scopes vars b2)

  | RRec (loc,fk,idv,tyv,bv) ->
      let vars' = Array.fold_right Idset.add idv vars in
      (match fk with
	 | RFix (nv,n) ->
	     let listdecl = 
	       Array.mapi (fun i fi ->
		 (fi,nv.(i),extern_type scopes vars tyv.(i),
                  extern false scopes vars' bv.(i))) idv
	     in 
	     CFix (loc,(loc,idv.(n)),Array.to_list listdecl)
	 | RCoFix n -> 
	     let listdecl =
               Array.mapi (fun i fi ->
		 (fi,extern_type scopes vars tyv.(i),
                  sub_extern false scopes vars' bv.(i))) idv
	     in
	     CCoFix (loc,(loc,idv.(n)),Array.to_list listdecl))

  | RSort (loc,s) ->
      let s = match s with
	 | RProp _ -> s
	 | RType (Some _) when !print_universes -> s
	 | RType _ -> RType None in
      CSort (loc,s)

  | RHole (loc,e) -> CHole loc

  | RCast (loc,c,t) ->
      CCast (loc,sub_extern true scopes vars c,extern_type scopes vars t)

  | RDynamic (loc,d) -> CDynamic (loc,d)

and extern_type (_,scopes) = extern true (Some Symbols.type_scope,scopes)

and sub_extern inctx (_,scopes) = extern inctx (None,scopes)

and factorize_prod scopes vars aty = function
  | RProd (loc,(Name id as na),ty,c)
      when same aty (extern_type scopes vars (anonymize_if_reserved na ty))
	& not (occur_var_constr_expr id aty) (* avoid na in ty escapes scope *)
	-> let id = avoid_wildcard id in
           let (nal,c) = factorize_prod scopes (Idset.add id vars) aty c in
           ((loc,Name id)::nal,c)
  | c -> ([],extern_type scopes vars c)

and factorize_lambda inctx scopes vars aty = function
  | RLambda (loc,na,ty,c)
      when same aty (extern_type scopes vars (anonymize_if_reserved na ty))
	& not (occur_name na aty) (* To avoid na in ty' escapes scope *)
	-> let na = name_app avoid_wildcard na in
           let (nal,c) =
	     factorize_lambda inctx scopes (add_vname vars na) aty c in
           ((loc,na)::nal,c)
  | c -> ([],sub_extern inctx scopes vars c)

and extern_eqn inctx scopes vars (loc,ids,pl,c) =
  (loc,List.map (extern_cases_pattern_in_scope (snd scopes) vars) pl,
   extern inctx scopes vars c)

and extern_numeral loc scopes (sc,n) =
  match Symbols.availability_of_numeral sc (make_current_scope scopes) with
    | None -> raise No_match
    | Some key -> insert_delimiters (CNumeral (loc,n)) key

and extern_symbol (tmp_scope,scopes as allscopes) vars t = function
  | [] -> raise No_match
  | (keyrule,pat,n as rule)::rules ->
      let loc = Rawterm.loc_of_rawconstr t in
      try
	(* Adjusts to the number of arguments expected by the notation *)
	let (t,args) = match t,n with
	  | RApp (_,f,args), Some n when List.length args > n ->
	      let args1, args2 = list_chop n args in
	      RApp (dummy_loc,f,args1), args2
	  | _ -> t,[] in
	(* Try matching ... *)
	let subst = match_aconstr t pat in
	(* Try availability of interpretation ... *)
        let e =
          match keyrule with
          | NotationRule (sc,ntn) ->
	      let scopes' = option_cons tmp_scope scopes in
	      (match Symbols.availability_of_notation (sc,ntn) scopes' with
                  (* Uninterpretation is not allowed in current context *)
              | None -> raise No_match
                  (* Uninterpretation is allowed in current context *)
	      | Some (scopt,key) ->
	          let scopes = option_cons scopt scopes in
	          let l =
		    List.map (fun (c,(scopt,scl)) ->
		      extern (* assuming no overloading: *) true
		        (scopt,scl@scopes) vars c)
                      subst in
	          insert_delimiters (CNotation (loc,ntn,l)) key)
          | SynDefRule kn ->
              CRef (Qualid (loc, shortest_qualid_of_syndef kn)) in
 	if args = [] then e 
	else
	  (* TODO: compute scopt for the extra args, in case, head is a ref *)
	  explicitize loc false [] (None,e)
	  (List.map (extern true allscopes vars) args)
      with
	  No_match -> extern_symbol allscopes vars t rules

let extern_rawconstr vars c = 
  extern false (None,Symbols.current_scopes()) vars c

let extern_rawtype vars c =
  extern_type (None,Symbols.current_scopes()) vars c

let extern_cases_pattern vars p = 
  extern_cases_pattern_in_scope (Symbols.current_scopes()) vars p

(******************************************************************)
(* Main translation function from constr -> constr_expr *)

let loc = dummy_loc (* for constr and pattern, locations are lost *)

let extern_constr_gen at_top scopt env t =
  let vars = vars_of_env env in
  let avoid = if at_top then ids_of_context env else [] in
  extern (not at_top) (scopt,Symbols.current_scopes()) vars
    (Detyping.detype (at_top,env) avoid (names_of_rel_context env) t)

let extern_constr_in_scope at_top scope env t =
  extern_constr_gen at_top (Some scope) env t

let extern_constr at_top env t =
  extern_constr_gen at_top None env t

(******************************************************************)
(* Main translation function from pattern -> constr_expr *)

let rec raw_of_pat tenv env = function
  | PRef ref -> RRef (loc,ref)
  | PVar id -> RVar (loc,id)
  | PEvar n -> REvar (loc,n)
  | PRel n ->
      let id = try match lookup_name_of_rel n env with
	| Name id   -> id
	| Anonymous ->
	    anomaly "rawconstr_of_pattern: index to an anonymous variable"
      with Not_found -> id_of_string ("[REL "^(string_of_int n)^"]") in
      RVar (loc,id)
  | PMeta None -> RHole (loc,InternalHole)
  | PMeta (Some n) -> RPatVar (loc,(false,n))
  | PApp (f,args) ->
      RApp (loc,raw_of_pat tenv env f,array_map_to_list (raw_of_pat tenv env) args)
  | PSoApp (n,args) ->
      RApp (loc,RPatVar (loc,(true,n)),
        List.map (raw_of_pat tenv env) args)
  | PProd (na,t,c) ->
      RProd (loc,na,raw_of_pat tenv env t,raw_of_pat tenv (na::env) c)
  | PLetIn (na,t,c) ->
      RLetIn (loc,na,raw_of_pat tenv env t, raw_of_pat tenv (na::env) c)
  | PLambda (na,t,c) ->
      RLambda (loc,na,raw_of_pat tenv env t, raw_of_pat tenv (na::env) c)
  | PCase ((_,(IfStyle|LetStyle as cs)),typopt,tm,bv) ->
      ROrderedCase (loc,cs,option_app (raw_of_pat tenv env) typopt,
         raw_of_pat tenv env tm,Array.map (raw_of_pat tenv env) bv, ref None)
  | PCase ((_,cs),typopt,tm,[||]) ->
      RCases (loc,(option_app (raw_of_pat tenv env) typopt,ref None (* TODO *)),
         [raw_of_pat tenv env tm,ref (Anonymous,None)],[])
  | PCase ((Some ind,cs),typopt,tm,bv) ->
      let avoid = List.fold_right (name_fold (fun x l -> x::l)) env [] in
      let k = (snd (lookup_mind_specif (Global.env()) ind)).Declarations.mind_nrealargs in
      Detyping.detype_case false (raw_of_pat tenv env)(raw_of_eqn tenv env)
	tenv avoid ind cs typopt k tm bv
  | PCase _ -> error "Unsupported case-analysis while printing pattern"
  | PFix f -> Detyping.detype (false,tenv) [] env (mkFix f)
  | PCoFix c -> Detyping.detype (false,tenv) [] env (mkCoFix c)
  | PSort s -> RSort (loc,s)

and raw_of_eqn tenv env constr construct_nargs branch =
  let make_pat x env b ids =
    let avoid = List.fold_right (name_fold (fun x l -> x::l)) env [] in
    let id = next_name_away_with_default "x" x avoid in
    PatVar (dummy_loc,Name id),(Name id)::env,id::ids
  in
  let rec buildrec ids patlist env n b =
    if n=0 then
      (dummy_loc, ids, 
       [PatCstr(dummy_loc, constr, List.rev patlist,Anonymous)],
       raw_of_pat tenv env b)
    else
      match b with
	| PLambda (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| PLetIn (x,_,b) -> 
	    let pat,new_env,new_ids = make_pat x env b ids in
            buildrec new_ids (pat::patlist) new_env (n-1) b

	| _ ->
	    error "Unsupported branch in case-analysis while printing pattern"
  in 
  buildrec [] [] env construct_nargs branch

let extern_pattern tenv env pat =
  extern true (None,Symbols.current_scopes()) Idset.empty
    (raw_of_pat tenv env pat)
