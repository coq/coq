(** Translation from coq abstract syntax trees to centaur vernac
   *)
open String;;
open Char;;
open Util;;
open Names;;
open Ascent;;
open Genarg;;
open Rawterm;;
open Tacexpr;;
open Vernacexpr;;
open Decl_kinds;;
open Topconstr;;
open Libnames;;
open Goptions;;


(* // Verify whether this is dead code, as of coq version 7 *)
(* The following three sentences have been added to cope with a change 
of strategy from the Coq team in the way rules construct ast's.  The
problem is that now grammar rules will refer to identifiers by giving
their absolute name, using the mutconstruct when needed.  Unfortunately,
when you have a mutconstruct structure, you don't have a way to guess
the corresponding identifier without an environment, and the parser
does not have an environment.  We add one, only for the constructs
that are always loaded. *)
let type_table = ((Hashtbl.create 17) :
      (string, ((string array) array)) Hashtbl.t);;

Hashtbl.add type_table "Coq.Init.Logic.and"
  [|[|"dummy";"conj"|]|];;

Hashtbl.add type_table "Coq.Init.Datatypes.prod"
  [|[|"dummy";"pair"|]|];;

Hashtbl.add type_table "Coq.Init.Datatypes.nat"
  [|[|"";"O"; "S"|]|];;

Hashtbl.add type_table "Coq.ZArith.fast_integer.Z"
[|[|"";"ZERO";"POS";"NEG"|]|];;


Hashtbl.add type_table "Coq.ZArith.fast_integer.positive"
[|[|"";"xI";"xO";"xH"|]|];;

(*The following two codes are added to cope with the distinction
  between ocaml and caml-light syntax while using ctcaml to
  manipulate the program *)
let code_plus = code (get "+" 0);;

let code_minus = code (get "-" 0);;

let coercion_description_holder = ref (function _ -> None : t -> int option);;

let coercion_description t = !coercion_description_holder t;;

let set_coercion_description f =
 coercion_description_holder:=f; ();;

let xlate_error s = print_endline ("xlate_error : "^s);failwith ("Translation error: " ^ s);;

let ctf_STRING_OPT_NONE = CT_coerce_NONE_to_STRING_OPT CT_none;;

let ctf_STRING_OPT_SOME s = CT_coerce_STRING_to_STRING_OPT s;;

let ctf_STRING_OPT = function
  | None -> ctf_STRING_OPT_NONE
  | Some s -> ctf_STRING_OPT_SOME (CT_string s)

let ctv_ID_OPT_NONE = CT_coerce_NONE_to_ID_OPT CT_none;;

let ctf_ID_OPT_SOME s = CT_coerce_ID_to_ID_OPT s;;

let ctv_ID_OPT_OR_ALL_NONE =
 CT_coerce_ID_OPT_to_ID_OPT_OR_ALL (CT_coerce_NONE_to_ID_OPT CT_none);;

let ctv_FORMULA_OPT_NONE =
  CT_coerce_ID_OPT_to_FORMULA_OPT(CT_coerce_NONE_to_ID_OPT CT_none);;

let ctv_PATTERN_OPT_NONE = CT_coerce_NONE_to_PATTERN_OPT CT_none;;

let ctv_DEF_BODY_OPT_NONE = CT_coerce_FORMULA_OPT_to_DEF_BODY_OPT 
			      ctv_FORMULA_OPT_NONE;;

let ctf_ID_OPT_OR_ALL_SOME s =
 CT_coerce_ID_OPT_to_ID_OPT_OR_ALL (ctf_ID_OPT_SOME s);;

let ctv_ID_OPT_OR_ALL_ALL = CT_all;;

let ctv_SPEC_OPT_NONE = CT_coerce_NONE_to_SPEC_OPT CT_none;;

let ct_coerce_FORMULA_to_DEF_BODY x =
    CT_coerce_CONTEXT_PATTERN_to_DEF_BODY
    (CT_coerce_FORMULA_to_CONTEXT_PATTERN x);;

let castc x = CT_coerce_TYPED_FORMULA_to_FORMULA x;;

let varc x = CT_coerce_ID_to_FORMULA x;;

let xlate_ident id = CT_ident (string_of_id id)

let ident_tac s = CT_user_tac (xlate_ident s, CT_targ_list []);;

let ident_vernac s = CT_user_vernac (CT_ident s, CT_varg_list []);;

let nums_to_int_list_aux l = List.map (fun x -> CT_int x) l;;

let nums_to_int_list l =  CT_int_list(nums_to_int_list_aux l);;

let num_or_var_to_int = function
  | ArgArg x -> CT_int x
  | _ -> xlate_error "TODO: nums_to_int_list_aux ArgVar";;

let nums_or_var_to_int_list_aux l = List.map num_or_var_to_int l;;

let nums_or_var_to_int_list l = CT_int_list(nums_or_var_to_int_list_aux l);;

let nums_or_var_to_int_ne_list n l =
  CT_int_ne_list(num_or_var_to_int n, nums_or_var_to_int_list_aux l);;

type iTARG =   Targ_command of ct_FORMULA
             | Targ_intropatt of ct_INTRO_PATT_LIST
             | Targ_id_list of ct_ID_LIST
             | Targ_spec_list of ct_SPEC_LIST
             | Targ_binding_com of ct_FORMULA
             | Targ_ident of ct_ID
             | Targ_int of ct_INT
             | Targ_binding of ct_BINDING
             | Targ_pattern of ct_PATTERN
             | Targ_unfold of ct_UNFOLD
	     | Targ_unfold_ne_list of ct_UNFOLD_NE_LIST
             | Targ_string of ct_STRING
             | Targ_fixtac of ct_FIXTAC
             | Targ_cofixtac of ct_COFIXTAC
             | Targ_tacexp of ct_TACTIC_COM
             | Targ_redexp of ct_RED_COM;;

type iVARG =   Varg_binder of ct_BINDER
             | Varg_binderlist of ct_BINDER_LIST
             | Varg_bindernelist of ct_BINDER_NE_LIST
             | Varg_call of ct_ID * iVARG list
             | Varg_constr of ct_FORMULA
             | Varg_sorttype of ct_SORT_TYPE
             | Varg_constrlist of ct_FORMULA list
             | Varg_ident of ct_ID
             | Varg_int of ct_INT
             | Varg_intlist of ct_INT_LIST
             | Varg_none
             | Varg_string of ct_STRING
             | Varg_tactic of ct_TACTIC_COM
             | Varg_ast of ct_AST
             | Varg_astlist of ct_AST_LIST
             | Varg_tactic_arg of iTARG
             | Varg_varglist of iVARG list;;


let coerce_iVARG_to_FORMULA =
 function
    | Varg_constr x -> x
    | Varg_sorttype x -> CT_coerce_SORT_TYPE_to_FORMULA x
    | Varg_ident id -> CT_coerce_ID_to_FORMULA id
    | _ -> xlate_error "coerce_iVARG_to_FORMULA: unexpected argument";;

let coerce_iVARG_to_ID =
 function Varg_ident id -> id
    | _ -> xlate_error "coerce_iVARG_to_ID";;

let coerce_VARG_to_ID =
 function
    | CT_coerce_ID_OPT_OR_ALL_to_VARG (CT_coerce_ID_OPT_to_ID_OPT_OR_ALL (CT_coerce_ID_to_ID_OPT x)) ->
     x
    | _ -> xlate_error "coerce_VARG_to_ID";;

let xlate_ident_opt =
  function
    | None -> ctv_ID_OPT_NONE
    | Some id -> ctf_ID_OPT_SOME (xlate_ident id)

let xlate_id_to_id_or_int_opt s =
   CT_coerce_ID_OPT_to_ID_OR_INT_OPT
     (CT_coerce_ID_to_ID_OPT (CT_ident (string_of_id s)));;

let xlate_int_to_id_or_int_opt n =
   CT_coerce_ID_OR_INT_to_ID_OR_INT_OPT
     (CT_coerce_INT_to_ID_OR_INT (CT_int n));;

let none_in_id_or_int_opt =
  CT_coerce_ID_OPT_to_ID_OR_INT_OPT
    (CT_coerce_NONE_to_ID_OPT(CT_none));;

let xlate_int_opt = function
  | Some n -> CT_coerce_INT_to_INT_OPT (CT_int n)
  | None ->  CT_coerce_NONE_to_INT_OPT CT_none

let xlate_int_or_var_opt_to_int_opt = function
  | Some (ArgArg n) -> CT_coerce_INT_to_INT_OPT (CT_int n)
  | Some (ArgVar _) -> xlate_error "int_or_var: TODO"
  | None ->  CT_coerce_NONE_to_INT_OPT CT_none

let apply_or_by_notation f = function
  | AN x -> f x
  | ByNotation _ -> xlate_error "TODO: ByNotation"

let tac_qualid_to_ct_ID ref = 
  CT_ident (Libnames.string_of_qualid (snd (qualid_of_reference ref)))

let loc_qualid_to_ct_ID ref =
  CT_ident (Libnames.string_of_qualid (snd (qualid_of_reference ref)))

let int_of_meta n = int_of_string (string_of_id n)
let is_int_meta n = try let _ = int_of_meta n in true with _ -> false

let xlate_qualid_list l = CT_id_list (List.map loc_qualid_to_ct_ID l)

let reference_to_ct_ID = function
  | Ident (_,id) -> CT_ident (Names.string_of_id id)
  | Qualid (_,qid) -> CT_ident (Libnames.string_of_qualid qid)

let xlate_class = function
  | FunClass -> CT_ident "FUNCLASS"
  | SortClass -> CT_ident "SORTCLASS"
  | RefClass qid -> loc_qualid_to_ct_ID qid

let id_to_pattern_var ctid =
 match ctid with
 | CT_metaid _ -> xlate_error "metaid not expected in pattern_var"
 | CT_ident "_" -> 
     CT_coerce_ID_OPT_to_MATCH_PATTERN (CT_coerce_NONE_to_ID_OPT CT_none)
 | CT_ident id_string ->
     CT_coerce_ID_OPT_to_MATCH_PATTERN 
       (CT_coerce_ID_to_ID_OPT (CT_ident id_string))
 | CT_metac _ -> assert false;;

exception Not_natural;;

let xlate_sort =
  function
    | RProp Term.Pos -> CT_sortc "Set"
    | RProp Term.Null -> CT_sortc "Prop"
    | RType None -> CT_sortc "Type"
    | RType (Some u) -> xlate_error "xlate_sort";;


let xlate_qualid a =
  let d,i = Libnames.repr_qualid a in
  let l = Names.repr_dirpath d in
  List.fold_left (fun s i1 -> (string_of_id i1) ^ "." ^ s) (string_of_id i) l;;
   
(* // The next two functions should be modified to make direct reference
  to a notation operator *)
let notation_to_formula s l = CT_notation(CT_string s, CT_formula_list l);;

let xlate_reference = function
    Ident(_,i) -> CT_ident (string_of_id i)
  | Qualid(_, q) -> CT_ident (xlate_qualid q);;
let rec xlate_match_pattern =
 function
   | CPatAtom(_, Some s) -> id_to_pattern_var (xlate_reference  s)
   | CPatAtom(_, None) -> id_to_pattern_var (CT_ident "_")
   | CPatCstr(_, f, []) -> id_to_pattern_var (xlate_reference f)
   | CPatCstr (_, f1 , (arg1 :: args)) ->
     CT_pattern_app
      (id_to_pattern_var (xlate_reference  f1),
      CT_match_pattern_ne_list
       (xlate_match_pattern arg1, 
	List.map xlate_match_pattern args))
    | CPatAlias  (_,  pattern, id) ->
     CT_pattern_as
      (xlate_match_pattern pattern, CT_coerce_ID_to_ID_OPT (xlate_ident id))
    | CPatOr (_,l) -> xlate_error "CPatOr: TODO"
    | CPatDelimiters(_, key, p) -> 
	CT_pattern_delimitors(CT_num_type key, xlate_match_pattern p)
    | CPatPrim (_,Numeral n) ->
 	CT_coerce_NUM_to_MATCH_PATTERN
	  (CT_int_encapsulator(Bigint.to_string n))
    | CPatPrim (_,String _) -> xlate_error "CPatPrim (String): TODO"
    | CPatNotation(_, s, l) -> 
	CT_pattern_notation(CT_string s,
			    CT_match_pattern_list(List.map xlate_match_pattern l))
;;


let xlate_id_opt_aux = function
    Name id -> ctf_ID_OPT_SOME(CT_ident (string_of_id id))
  | Anonymous -> ctv_ID_OPT_NONE;;

let xlate_id_opt (_, v) = xlate_id_opt_aux v;;

let xlate_id_opt_ne_list = function
    [] -> assert false
  | a::l -> CT_id_opt_ne_list(xlate_id_opt a, List.map xlate_id_opt l);;


let rec last = function
    [] -> assert false
  | [a] -> a
  | a::tl -> last tl;;

let rec decompose_last = function
    [] -> assert false
  | [a] -> [], a
  | a::tl -> let rl, b = decompose_last tl in (a::rl), b;;

let make_fix_struct (n,bl) =
  let names = names_of_local_assums bl in
  let nn = List.length names in
  if nn = 1 || n = None then ctv_ID_OPT_NONE
  else 
    let n = out_some n in 
    if n < nn then xlate_id_opt(List.nth names n)
    else xlate_error "unexpected result of parsing for Fixpoint";;


let rec xlate_binder = function
    (l,t) -> CT_binder(xlate_id_opt_ne_list l, xlate_formula t)
and xlate_return_info = function
| (Some Anonymous, None) | (None, None) ->
   CT_coerce_NONE_to_RETURN_INFO CT_none
| (None, Some t) -> CT_return(xlate_formula t)
| (Some x, Some t) -> CT_as_and_return(xlate_id_opt_aux x, xlate_formula t)
| (Some _, None) -> assert false
and xlate_formula_opt =
  function
    | None -> ctv_FORMULA_OPT_NONE
    | Some e -> CT_coerce_FORMULA_to_FORMULA_OPT (xlate_formula e)

and  xlate_binder_l = function
    LocalRawAssum(l,t) -> CT_binder(xlate_id_opt_ne_list l, xlate_formula t)
  | LocalRawDef(n,v) -> CT_coerce_DEF_to_BINDER(CT_def(xlate_id_opt n,
						       xlate_formula v))
and 
  xlate_match_pattern_ne_list = function
    [] -> assert false
  | a::l -> CT_match_pattern_ne_list(xlate_match_pattern a, 
                                     List.map xlate_match_pattern l)
and  translate_one_equation = function
    (_,[lp], a) -> CT_eqn (xlate_match_pattern_ne_list lp, xlate_formula a)
  | _ -> xlate_error "TODO: disjunctive multiple patterns"
and 
  xlate_binder_ne_list = function
    [] -> assert false
  | a::l -> CT_binder_ne_list(xlate_binder a, List.map xlate_binder l)
and 
  xlate_binder_list = function
  l -> CT_binder_list( List.map xlate_binder_l l)
and (xlate_formula:Topconstr.constr_expr -> Ascent.ct_FORMULA) = function

     CRef r -> varc (xlate_reference r)
   | CArrow(_,a,b)-> CT_arrowc (xlate_formula a, xlate_formula b)
   | CProdN(_,ll,b) as whole_term -> 
       let rec gather_binders = function
	   CProdN(_, ll, b) ->
	     ll@(gather_binders b)
	 | _ -> [] in
       let rec fetch_ultimate_body = function
	   CProdN(_, _, b) -> fetch_ultimate_body b
	 | a -> a in
	 CT_prodc(xlate_binder_ne_list (gather_binders whole_term), 
		  xlate_formula (fetch_ultimate_body b))
   | CLambdaN(_,ll,b)-> CT_lambdac(xlate_binder_ne_list ll, xlate_formula b)
   | CLetIn(_, v, a, b) -> 
       CT_letin(CT_def(xlate_id_opt v, xlate_formula a), xlate_formula b)
   | CAppExpl(_, (Some n, r), l) -> 
       let l', last = decompose_last l in
	 CT_proj(xlate_formula last,
		 CT_formula_ne_list
		   (CT_bang(varc (xlate_reference r)),
		    List.map xlate_formula l'))
   | CAppExpl(_, (None, r), []) -> CT_bang(varc(xlate_reference r))
   | CAppExpl(_, (None, r), l) -> 
       CT_appc(CT_bang(varc (xlate_reference r)),
	       xlate_formula_ne_list l)
   | CApp(_, (Some n,f), l) -> 
       let l', last = decompose_last l in
       CT_proj(xlate_formula_expl last, 
	       CT_formula_ne_list
		 (xlate_formula f, List.map xlate_formula_expl l'))
   | CApp(_, (_,f), l) -> 
       CT_appc(xlate_formula f, xlate_formula_expl_ne_list l)
   | CCases (_, _, [], _) -> assert false
   | CCases (_, ret_type, tm::tml, eqns)->
       CT_cases(CT_matched_formula_ne_list(xlate_matched_formula tm,
					   List.map xlate_matched_formula tml),
		xlate_formula_opt ret_type,
                CT_eqn_list (List.map (fun x -> translate_one_equation x) eqns))
   | CLetTuple (_,a::l, ret_info, c, b) -> 
      CT_let_tuple(CT_id_opt_ne_list(xlate_id_opt_aux a,
				     List.map xlate_id_opt_aux l),
		   xlate_return_info ret_info,
		   xlate_formula c,
		   xlate_formula b)
   | CLetTuple (_, [], _, _, _) -> xlate_error "NOT parsed: Let with ()"
   | CIf (_,c, ret_info, b1, b2) -> 
       CT_if
	 (xlate_formula c, xlate_return_info ret_info,
	  xlate_formula b1, xlate_formula b2)

   | CSort(_, s) -> CT_coerce_SORT_TYPE_to_FORMULA(xlate_sort s)
   | CNotation(_, s, l) -> notation_to_formula s (List.map xlate_formula l)
   | CPrim (_, Numeral i) -> 
       CT_coerce_NUM_to_FORMULA(CT_int_encapsulator(Bigint.to_string i))
   | CPrim (_, String _) -> xlate_error "CPrim (String): TODO"
   | CHole _ -> CT_existvarc 
(* I assume CDynamic has been inserted to make free form extension of
   the language possible, but this would go agains the logic of pcoq anyway. *)
   | CDynamic (_, _) -> assert false
   | CDelimiters (_, key, num) -> 
	 CT_num_encapsulator(CT_num_type key , xlate_formula  num)
   | CCast (_, e, CastConv (_, t)) -> 
       CT_coerce_TYPED_FORMULA_to_FORMULA
	 (CT_typed_formula(xlate_formula e, xlate_formula t))
   | CCast (_, e, CastCoerce) -> assert false
   | CPatVar (_, (_,i)) when is_int_meta i ->
       CT_coerce_ID_to_FORMULA(CT_metac (CT_int (int_of_meta i)))
   | CPatVar (_, (false, s)) ->
       CT_coerce_ID_to_FORMULA(CT_metaid (string_of_id s))
   | CPatVar (_, (true, s)) ->
       xlate_error "Second order variable not supported"
   | CEvar _ -> xlate_error "CEvar not supported"
   | CCoFix (_, (_, id), lm::lmi) -> 
     let strip_mutcorec (fid, bl,arf, ardef) =
	CT_cofix_rec (xlate_ident fid, xlate_binder_list bl,
                      xlate_formula arf, xlate_formula ardef) in
        CT_cofixc(xlate_ident id,
	  (CT_cofix_rec_list (strip_mutcorec lm, List.map strip_mutcorec lmi)))
   | CFix (_, (_, id), lm::lmi) ->       
     let strip_mutrec (fid, (n, ro), bl, arf, ardef) =
        let (struct_arg,bl,arf,ardef) =
	 (* Pierre L: could the case [n=None && bl=[]] happen ? Normally not *)
	 (* By the way, how could [bl = []] happen in V8 syntax ?  *)
         if bl = [] then
	   let n = out_some n in 
           let (bl,arf,ardef) = Ppconstr.split_fix (n+1) arf ardef in
           (xlate_id_opt(List.nth (names_of_local_assums bl) n),bl,arf,ardef)
         else (make_fix_struct (n, bl),bl,arf,ardef) in
        let arf = xlate_formula arf in
        let ardef = xlate_formula ardef in
	match xlate_binder_list bl with
	  | CT_binder_list (b :: bl) ->
	      CT_fix_rec (xlate_ident fid, CT_binder_ne_list (b, bl),
			  struct_arg, arf, ardef)
          | _ -> xlate_error "mutual recursive" in
       CT_fixc (xlate_ident id, 
         	CT_fix_binder_list
		  (CT_coerce_FIX_REC_to_FIX_BINDER 
		     (strip_mutrec lm), List.map 
		       (fun x-> CT_coerce_FIX_REC_to_FIX_BINDER (strip_mutrec x))
		       lmi)) 
   | CCoFix _ -> assert false
   | CFix _ -> assert false
and xlate_matched_formula = function
    (f, (Some x, Some y)) ->
      CT_formula_as_in(xlate_formula f, xlate_id_opt_aux x, xlate_formula y)
  | (f, (None, Some y)) ->
      CT_formula_in(xlate_formula f, xlate_formula y)
  | (f, (Some x, None)) ->
      CT_formula_as(xlate_formula f, xlate_id_opt_aux x)
  | (f, (None, None)) -> 
      CT_coerce_FORMULA_to_MATCHED_FORMULA(xlate_formula f)
and xlate_formula_expl = function
    (a, None) -> xlate_formula a
  | (a, Some (_,ExplByPos i)) -> 
      xlate_error "explicitation of implicit by rank not supported"
  | (a, Some (_,ExplByName i)) ->
      CT_labelled_arg(CT_ident (string_of_id i), xlate_formula a)
and xlate_formula_expl_ne_list = function
    [] -> assert false
  | a::l -> CT_formula_ne_list(xlate_formula_expl a, List.map xlate_formula_expl l)
and xlate_formula_ne_list = function 
    [] -> assert false
  | a::l -> CT_formula_ne_list(xlate_formula a, List.map xlate_formula l);;

let (xlate_ident_or_metaid:
      Names.identifier Util.located Tacexpr.or_metaid -> ct_ID) = function
    AI (_, x) -> xlate_ident x
  | MetaId(_, x) -> CT_metaid x;;

let xlate_hyp = function
  | AI (_,id) -> xlate_ident id
  | MetaId _ -> xlate_error "MetaId should occur only in quotations"

let xlate_hyp_location =
 function
  | (nums, AI (_,id)), InHypTypeOnly ->
      CT_intype(xlate_ident id, nums_or_var_to_int_list nums)
  | (nums, AI (_,id)), InHypValueOnly ->
      CT_invalue(xlate_ident id, nums_or_var_to_int_list nums)
  | ([], AI (_,id)), InHyp ->
      CT_coerce_UNFOLD_to_HYP_LOCATION 
	(CT_coerce_ID_to_UNFOLD (xlate_ident id))
  | (a::l, AI (_,id)), InHyp ->
      CT_coerce_UNFOLD_to_HYP_LOCATION 
	(CT_unfold_occ (xlate_ident id, 
			CT_int_ne_list(num_or_var_to_int a, 
                                       nums_or_var_to_int_list_aux l)))
  | (_, MetaId _),_ -> 
      xlate_error "MetaId not supported in xlate_hyp_location (should occur only in quotations)"



let xlate_clause cls =
  let hyps_info =
    match cls.onhyps with
    	None -> CT_coerce_STAR_to_HYP_LOCATION_LIST_OR_STAR CT_star
      | Some l -> CT_hyp_location_list(List.map xlate_hyp_location l) in
  CT_clause
    (hyps_info, 
     if cls.onconcl then 
       CT_coerce_STAR_to_STAR_OPT CT_star
     else
       CT_coerce_NONE_to_STAR_OPT CT_none)

(** Tactics
   *)
let strip_targ_spec_list =
 function
    | Targ_spec_list x -> x
    | _ -> xlate_error "strip tactic: non binding-list argument";;

let strip_targ_binding =
 function
    | Targ_binding x -> x
    | _ -> xlate_error "strip tactic: non-binding argument";;

let strip_targ_command =
 function
    | Targ_command x -> x
    | Targ_binding_com x -> x
    | _ -> xlate_error "strip tactic: non-command argument";;

let strip_targ_ident =
 function
    | Targ_ident x -> x
    | _ -> xlate_error "strip tactic: non-ident argument";;

let strip_targ_int =
 function
    | Targ_int x -> x
    | _ -> xlate_error "strip tactic: non-int argument";;

let strip_targ_pattern =
 function
    | Targ_pattern x -> x
    | _ -> xlate_error "strip tactic: non-pattern argument";;

let strip_targ_unfold =
 function
    | Targ_unfold x -> x
    | _ -> xlate_error "strip tactic: non-unfold argument";;

let strip_targ_fixtac =
 function
    | Targ_fixtac x -> x
    | _ -> xlate_error "strip tactic: non-fixtac argument";;

let strip_targ_cofixtac =
 function
    | Targ_cofixtac x -> x
    | _ -> xlate_error "strip tactic: non-cofixtac argument";;

(*Need to transform formula to id for "Prolog" tactic problem *)
let make_ID_from_FORMULA =
 function
    | CT_coerce_ID_to_FORMULA id -> id
    | _ -> xlate_error "make_ID_from_FORMULA: non-formula argument";;

let make_ID_from_iTARG_FORMULA x = make_ID_from_FORMULA (strip_targ_command x);;

let xlate_quantified_hypothesis = function
  | AnonHyp n -> CT_coerce_INT_to_ID_OR_INT (CT_int n)
  | NamedHyp id -> CT_coerce_ID_to_ID_OR_INT (xlate_ident id)

let xlate_quantified_hypothesis_opt = function
  | None -> 
      CT_coerce_ID_OPT_to_ID_OR_INT_OPT ctv_ID_OPT_NONE
  | Some (AnonHyp n) -> xlate_int_to_id_or_int_opt n
  | Some (NamedHyp id) -> xlate_id_to_id_or_int_opt id;;

let xlate_id_or_int = function
    ArgArg n -> CT_coerce_INT_to_ID_OR_INT(CT_int n)
  | ArgVar(_, s) -> CT_coerce_ID_to_ID_OR_INT(xlate_ident s);;

let xlate_explicit_binding (loc,h,c) = 
  CT_binding (xlate_quantified_hypothesis h, xlate_formula c)

let xlate_bindings = function
  | ImplicitBindings l ->
      CT_coerce_FORMULA_LIST_to_SPEC_LIST
        (CT_formula_list (List.map xlate_formula l))
  | ExplicitBindings l ->
      CT_coerce_BINDING_LIST_to_SPEC_LIST
        (CT_binding_list (List.map xlate_explicit_binding l))
  | NoBindings ->
      CT_coerce_FORMULA_LIST_to_SPEC_LIST (CT_formula_list [])

let strip_targ_spec_list =
 function
    | Targ_spec_list x -> x
    | _ -> xlate_error "strip_tar_spec_list";;

let strip_targ_intropatt =
 function
    | Targ_intropatt x -> x
    | _ -> xlate_error "strip_targ_intropatt";;

let get_flag r =
  let conv_flags, red_ids =
    let csts = List.map (apply_or_by_notation tac_qualid_to_ct_ID) r.rConst in
    if r.rDelta then
      [CT_delta], CT_unfbut csts
    else
      (if r.rConst = []
      then (* probably useless: just for compatibility *) []
      else [CT_delta]),
      CT_unf csts in
  let conv_flags = if r.rBeta then CT_beta::conv_flags else conv_flags in
  let conv_flags = if r.rIota then CT_iota::conv_flags else conv_flags in
  let conv_flags = if r.rZeta then CT_zeta::conv_flags else conv_flags in
  (* Rem: EVAR flag obsolète *)
  conv_flags, red_ids

let rec xlate_intro_pattern =
 function
  | IntroOrAndPattern [] -> assert false
  | IntroOrAndPattern (fp::ll) ->
      CT_disj_pattern
      	(CT_intro_patt_list(List.map xlate_intro_pattern fp),
	 List.map 
	   (fun l ->
	      CT_intro_patt_list(List.map xlate_intro_pattern l))
	   ll)
  | IntroWildcard -> CT_coerce_ID_to_INTRO_PATT(CT_ident "_" )
  | IntroIdentifier c -> CT_coerce_ID_to_INTRO_PATT(xlate_ident c)
  | IntroAnonymous -> xlate_error "TODO: IntroAnonymous"
  | IntroFresh _ -> xlate_error "TODO: IntroFresh"

let compute_INV_TYPE = function
   FullInversionClear -> CT_inv_clear
 | SimpleInversion -> CT_inv_simple
 | FullInversion -> CT_inv_regular

let is_tactic_special_case = function
    "AutoRewrite" -> true
  | _ -> false;;

let xlate_context_pattern = function
  | Term v -> 
      CT_coerce_FORMULA_to_CONTEXT_PATTERN (xlate_formula v)
  | Subterm (idopt, v) ->
      CT_context(xlate_ident_opt idopt, xlate_formula v)


let xlate_match_context_hyps = function
  | Hyp (na,b) -> CT_premise_pattern(xlate_id_opt na, xlate_context_pattern b);;

let xlate_arg_to_id_opt = function
    Some id -> CT_coerce_ID_to_ID_OPT(CT_ident (string_of_id id))
  | None -> ctv_ID_OPT_NONE;;

let xlate_largs_to_id_opt largs =
  match List.map xlate_arg_to_id_opt largs with
      fst::rest -> fst, rest
    | _ -> assert false;;

let xlate_int_or_constr = function
    ElimOnConstr a -> CT_coerce_FORMULA_to_FORMULA_OR_INT(xlate_formula a)
  | ElimOnIdent(_,i) ->
      CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
      	(CT_coerce_ID_to_ID_OR_INT(xlate_ident i))
  | ElimOnAnonHyp i -> 
      CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	(CT_coerce_INT_to_ID_OR_INT(CT_int i));;

let xlate_using = function
    None -> CT_coerce_NONE_to_USING(CT_none)
  | Some (c2,sl2) -> CT_using (xlate_formula c2, xlate_bindings sl2);;

let xlate_one_unfold_block = function
    ([],qid) -> 
      CT_coerce_ID_to_UNFOLD(apply_or_by_notation tac_qualid_to_ct_ID qid)
  | (n::nums, qid) ->
      CT_unfold_occ(apply_or_by_notation tac_qualid_to_ct_ID qid, 
                    nums_or_var_to_int_ne_list n nums)
;;

let xlate_with_names = function
    IntroAnonymous -> CT_coerce_ID_OPT_to_INTRO_PATT_OPT ctv_ID_OPT_NONE
  | fp -> CT_coerce_INTRO_PATT_to_INTRO_PATT_OPT (xlate_intro_pattern fp)

let rawwit_main_tactic = Pcoq.rawwit_tactic Pcoq.tactic_main_level

let rec (xlate_tacarg:raw_tactic_arg -> ct_TACTIC_ARG) =
  function
    | TacVoid ->
	CT_void
    | Tacexp t -> 
	CT_coerce_TACTIC_COM_to_TACTIC_ARG(xlate_tactic t)
    | Integer n ->
	CT_coerce_FORMULA_OR_INT_to_TACTIC_ARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_INT_to_ID_OR_INT (CT_int n)))
    | Reference r ->
	CT_coerce_FORMULA_OR_INT_to_TACTIC_ARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_ID_to_ID_OR_INT (reference_to_ct_ID r)))
    | TacDynamic _ ->
	failwith "Dynamics not treated in xlate_ast"
    | ConstrMayEval (ConstrTerm c) ->
	CT_coerce_FORMULA_OR_INT_to_TACTIC_ARG
	  (CT_coerce_FORMULA_to_FORMULA_OR_INT (xlate_formula c))
    | ConstrMayEval(ConstrEval(r,c)) ->
	CT_coerce_EVAL_CMD_to_TACTIC_ARG
	  (CT_eval(CT_coerce_NONE_to_INT_OPT CT_none, xlate_red_tactic r,
		   xlate_formula c))
    | ConstrMayEval(ConstrTypeOf(c)) -> 
	CT_coerce_TERM_CHANGE_to_TACTIC_ARG(CT_check_term(xlate_formula c))
    | MetaIdArg _ ->
	xlate_error "MetaIdArg should only be used in quotations"
    | t ->
	CT_coerce_TACTIC_COM_to_TACTIC_ARG(xlate_call_or_tacarg t)

and (xlate_call_or_tacarg:raw_tactic_arg -> ct_TACTIC_COM) =
 function
   (* Moved from xlate_tactic *)
    | TacCall (_, r, a::l) ->
	CT_simple_user_tac
	  (reference_to_ct_ID r,
	    CT_tactic_arg_list(xlate_tacarg a,List.map xlate_tacarg l))
    | Reference (Ident (_,s)) -> ident_tac s
    | ConstrMayEval(ConstrTerm a) ->
	CT_formula_marker(xlate_formula a)
    | TacFreshId [] -> CT_fresh(ctf_STRING_OPT None)
    | TacFreshId [ArgArg s] -> CT_fresh(ctf_STRING_OPT (Some s))
    | TacFreshId _ -> xlate_error "TODO: fresh with many args"
    | t -> xlate_error "TODO LATER: result other than tactic or constr"

and xlate_red_tactic =
 function
  | Red true -> xlate_error ""
  | Red false -> CT_red
  | CbvVm -> CT_cbvvm
  | Hnf -> CT_hnf
  | Simpl None -> CT_simpl ctv_PATTERN_OPT_NONE
  | Simpl (Some (l,c)) -> 
      CT_simpl 
	(CT_coerce_PATTERN_to_PATTERN_OPT
	   (CT_pattern_occ
	      (CT_int_list(nums_or_var_to_int_list_aux l), xlate_formula c)))
  | Cbv flag_list ->
     let conv_flags, red_ids = get_flag flag_list in
     CT_cbv (CT_conversion_flag_list conv_flags, red_ids)
  | Lazy flag_list ->
     let conv_flags, red_ids = get_flag flag_list in
     CT_lazy (CT_conversion_flag_list conv_flags, red_ids)
  | Unfold unf_list ->
     let ct_unf_list = List.map xlate_one_unfold_block unf_list in
     (match ct_unf_list with
      | first :: others -> CT_unfold (CT_unfold_ne_list (first, others))
      | [] -> error "there should be at least one thing to unfold")
  | Fold formula_list -> 
      CT_fold(CT_formula_list(List.map xlate_formula formula_list))
  | Pattern l ->
     let pat_list = List.map (fun (nums,c) ->
          CT_pattern_occ
           (CT_int_list (nums_or_var_to_int_list_aux nums),
            xlate_formula c)) l in
     (match pat_list with
      | first :: others -> CT_pattern (CT_pattern_ne_list (first, others))
      | [] -> error "Expecting at least one pattern in a Pattern command")
  | ExtraRedExpr _ -> xlate_error "TODO LATER: ExtraRedExpr (probably dead code)"

and xlate_local_rec_tac = function 
 (* TODO LATER: local recursive tactics and global ones should be handled in
    the same manner *)
  | ((_,x),(argl,tac)) ->
      let fst, rest = xlate_largs_to_id_opt argl in
	CT_rec_tactic_fun(xlate_ident x,
			  CT_id_opt_ne_list(fst, rest),
			  xlate_tactic tac)

and xlate_tactic =
 function
   | TacFun (largs, t) ->
       let fst, rest =  xlate_largs_to_id_opt largs in
       CT_tactic_fun (CT_id_opt_ne_list(fst, rest), xlate_tactic t)
   | TacThen (t1,[||],t2,[||]) -> 
       (match xlate_tactic t1 with
            CT_then(a,l) -> CT_then(a,l@[xlate_tactic t2])
	  | t -> CT_then (t,[xlate_tactic t2]))
   | TacThen _ -> xlate_error "TacThen generalization TODO"
   | TacThens(t1,[]) -> assert false
   | TacThens(t1,t::l) ->
       let ct = xlate_tactic t in
       let cl = List.map xlate_tactic l in
       (match xlate_tactic t1 with
	    CT_then(ct1,cl1) -> CT_then(ct1, cl1@[CT_parallel(ct, cl)])
	  | ct1 -> CT_then(ct1,[CT_parallel(ct, cl)]))
   | TacFirst([]) -> assert false
   | TacFirst(t1::l)-> CT_first(xlate_tactic t1, List.map xlate_tactic l)
   | TacSolve([]) -> assert false
   | TacSolve(t1::l)-> CT_tacsolve(xlate_tactic t1, List.map xlate_tactic l)
   | TacComplete _ -> xlate_error "TODO: tactical complete"
   | TacDo(count, t) -> CT_do(xlate_id_or_int count, xlate_tactic t)
   | TacTry t -> CT_try (xlate_tactic t)
   | TacRepeat t -> CT_repeat(xlate_tactic t)
   | TacAbstract(t,id_opt) -> 
       CT_abstract((match id_opt with
		       	None -> ctv_ID_OPT_NONE
		      | Some id -> ctf_ID_OPT_SOME (CT_ident (string_of_id id))),
		   xlate_tactic t)
   | TacProgress t -> CT_progress(xlate_tactic t)
   | TacOrelse(t1,t2) -> CT_orelse(xlate_tactic t1, xlate_tactic t2)
   | TacMatch (true,_,_) -> failwith "TODO: lazy match"
   | TacMatch (false, exp, rules) ->
        CT_match_tac(xlate_tactic exp,
                     match List.map 
                       (function 
                          | Pat ([],p,tac) ->
                              CT_match_tac_rule(xlate_context_pattern p,
                                                mk_let_value tac)
                          | Pat (_,p,tac) -> xlate_error"No hyps in pure Match"
                          | All tac ->
                              CT_match_tac_rule
                                (CT_coerce_FORMULA_to_CONTEXT_PATTERN
                                   CT_existvarc, 
                                   mk_let_value tac)) rules with
                         | [] -> assert false
                         | fst::others ->
                             CT_match_tac_rules(fst, others))
   | TacMatchContext (_,_,[]) | TacMatchContext (true,_,_) -> failwith ""
   | TacMatchContext (false,false,rule1::rules) ->
         CT_match_context(xlate_context_rule rule1,
                          List.map xlate_context_rule rules)
   | TacMatchContext (false,true,rule1::rules) ->
         CT_match_context_reverse(xlate_context_rule rule1,
                          List.map xlate_context_rule rules)
   | TacLetIn (l, t) ->
       let cvt_clause =
         function
             ((_,s),None,ConstrMayEval v) ->
                 CT_let_clause(xlate_ident s,
			       CT_coerce_NONE_to_TACTIC_OPT CT_none,
                               CT_coerce_DEF_BODY_to_LET_VALUE
                               (formula_to_def_body v))
           | ((_,s),None,Tacexp t) -> 
                 CT_let_clause(xlate_ident s,
			       CT_coerce_NONE_to_TACTIC_OPT CT_none,
                               CT_coerce_TACTIC_COM_to_LET_VALUE
                               (xlate_tactic t))
           | ((_,s),None,t) -> 
                 CT_let_clause(xlate_ident s,
			       CT_coerce_NONE_to_TACTIC_OPT CT_none,
                               CT_coerce_TACTIC_COM_to_LET_VALUE
                               (xlate_call_or_tacarg t))
           | ((_,s),Some c,t) -> 
	       CT_let_clause(xlate_ident s,
			     CT_coerce_TACTIC_COM_to_TACTIC_OPT(xlate_tactic c),
                               CT_coerce_TACTIC_COM_to_LET_VALUE
				 (xlate_call_or_tacarg t)) in
         let cl_l = List.map cvt_clause l in
         (match cl_l with
            | [] -> assert false 
            | fst::others ->
                CT_let_ltac (CT_let_clauses(fst, others), mk_let_value t))
   | TacLetRecIn([], _) -> xlate_error "recursive definition with no definition"
   | TacLetRecIn(f1::l, t) -> 
       let tl =  CT_rec_tactic_fun_list
		   (xlate_local_rec_tac f1, List.map xlate_local_rec_tac l) in
       CT_rec_tactic_in(tl, xlate_tactic t)
   | TacAtom (_, t) -> xlate_tac t 
   | TacFail (count, []) -> CT_fail(xlate_id_or_int count, ctf_STRING_OPT_NONE)
   | TacFail (count, [MsgString s]) -> CT_fail(xlate_id_or_int count,
				   ctf_STRING_OPT_SOME (CT_string s))
   | TacFail (count, _) -> xlate_error "TODO: generic fail message"
   | TacId [] -> CT_idtac ctf_STRING_OPT_NONE
   | TacId [MsgString s] -> CT_idtac(ctf_STRING_OPT_SOME (CT_string s))
   | TacId _ -> xlate_error "TODO: generic idtac message"
   | TacInfo t -> CT_info(xlate_tactic t)
   | TacArg a -> xlate_call_or_tacarg a

and xlate_tac =
  function
    | TacExtend (_, "firstorder", tac_opt::l) ->
       let t1 =
	 match
	   out_gen (wit_opt rawwit_main_tactic) tac_opt
	 with
	 | None -> CT_coerce_NONE_to_TACTIC_OPT CT_none
	 | Some t2 -> CT_coerce_TACTIC_COM_to_TACTIC_OPT (xlate_tactic t2) in
	 (match l with
	      [] -> CT_firstorder t1
	    | [l1] -> 
		(match genarg_tag l1 with
		     List1ArgType PreIdentArgType -> 
		       let l2 = List.map 
				  (fun x -> CT_ident x)
				  (out_gen (wit_list1 rawwit_pre_ident) l1) in
		       let fst,l3 = 
			 match l2 with fst::l3 -> fst,l3 | [] -> assert false in
		      	 CT_firstorder_using(t1, CT_id_ne_list(fst, l3))
		   | List1ArgType RefArgType ->
		       let l2 = List.map reference_to_ct_ID 
				  (out_gen (wit_list1 rawwit_ref) l1) in
		       let fst,l3 =
			 match  l2 with fst::l3 -> fst, l3 | [] -> assert false in
			 CT_firstorder_with(t1, CT_id_ne_list(fst, l3))
		   | _ -> assert false)
	    | _ -> assert false)
    | TacExtend (_, "refine", [c]) ->
       CT_refine (xlate_formula (snd (out_gen rawwit_casted_open_constr c)))
    | TacExtend (_,"absurd",[c]) ->
       CT_absurd (xlate_formula (out_gen rawwit_constr c))
    | TacExtend (_,"contradiction",[opt_c]) ->
	(match out_gen (wit_opt rawwit_constr_with_bindings) opt_c with
	     None -> CT_contradiction
	   | Some(c, b) ->
	       let c1 = xlate_formula c in
	       let bindings = xlate_bindings b in
		 CT_contradiction_thm(c1, bindings))
    | TacChange (None, f, b) -> CT_change (xlate_formula f, xlate_clause b)
    | TacChange (Some(l,c), f, b) -> 
	(* TODO LATER: combine with other constructions of pattern_occ *)
	CT_change_local(
	  CT_pattern_occ(CT_int_list(nums_or_var_to_int_list_aux l), 
			 xlate_formula c),
	  xlate_formula f,
	  xlate_clause b)
    | TacExtend (_,"contradiction",[]) -> CT_contradiction
    | TacDoubleInduction (n1, n2) ->
	CT_tac_double (xlate_quantified_hypothesis n1, xlate_quantified_hypothesis n2)
    | TacExtend (_,"discriminate", [idopt]) ->
     CT_discriminate_eq
         (xlate_quantified_hypothesis_opt
	    (out_gen (wit_opt rawwit_quant_hyp) idopt))
    | TacExtend (_,"simplify_eq", [idopt]) ->
	let idopt1 = out_gen (wit_opt rawwit_quant_hyp) idopt in
	let idopt2 = match idopt1 with
	    None -> CT_coerce_ID_OPT_to_ID_OR_INT_OPT
		(CT_coerce_NONE_to_ID_OPT CT_none)
	  | Some v ->
	      CT_coerce_ID_OR_INT_to_ID_OR_INT_OPT
	      	(xlate_quantified_hypothesis v) in
	  CT_simplify_eq idopt2
    | TacExtend (_,"injection", [idopt]) ->
     CT_injection_eq
         (xlate_quantified_hypothesis_opt
	    (out_gen (wit_opt rawwit_quant_hyp) idopt))
    | TacExtend (_,"injection_as", [idopt;ipat]) ->
	xlate_error "TODO: injection as"
    | TacFix (idopt, n) ->
     CT_fixtactic (xlate_ident_opt idopt, CT_int n, CT_fix_tac_list [])
    | TacMutualFix (id, n, fixtac_list) ->
     let f (id,n,c) = CT_fixtac (xlate_ident id, CT_int n, xlate_formula c) in
     CT_fixtactic
      (ctf_ID_OPT_SOME (xlate_ident id), CT_int n,
      CT_fix_tac_list (List.map f fixtac_list))
    | TacCofix idopt ->
       CT_cofixtactic (xlate_ident_opt idopt, CT_cofix_tac_list [])
    | TacMutualCofix (id, cofixtac_list) ->
     let f (id,c) = CT_cofixtac (xlate_ident id, xlate_formula c) in
     CT_cofixtactic
      (CT_coerce_ID_to_ID_OPT (xlate_ident id),
      CT_cofix_tac_list (List.map f cofixtac_list))
    | TacIntrosUntil (NamedHyp id) -> 
	CT_intros_until (CT_coerce_ID_to_ID_OR_INT (xlate_ident id))
    | TacIntrosUntil (AnonHyp n) -> 
	CT_intros_until (CT_coerce_INT_to_ID_OR_INT (CT_int n))
    | TacIntroMove (Some id1, Some (_,id2)) ->
     CT_intro_after(CT_coerce_ID_to_ID_OPT (xlate_ident id1),xlate_ident id2)
    | TacIntroMove (None, Some (_,id2)) ->
	CT_intro_after(CT_coerce_NONE_to_ID_OPT CT_none, xlate_ident id2)
    | TacMove (true, id1, id2) ->
	CT_move_after(xlate_hyp id1, xlate_hyp id2)
    | TacMove (false, id1, id2) -> xlate_error "Non dep Move is only internal"
    | TacIntroPattern patt_list ->
	CT_intros
	  (CT_intro_patt_list (List.map xlate_intro_pattern patt_list))
    | TacIntroMove (Some id, None) ->
     CT_intros (CT_intro_patt_list[CT_coerce_ID_to_INTRO_PATT(xlate_ident id)])
    | TacIntroMove (None, None) ->  CT_intro (CT_coerce_NONE_to_ID_OPT CT_none)
    | TacLeft bindl -> CT_left (xlate_bindings bindl)
    | TacRight bindl -> CT_right (xlate_bindings bindl)
    | TacSplit (false,bindl) -> CT_split (xlate_bindings bindl)
    | TacSplit (true,bindl) -> CT_exists (xlate_bindings bindl)
    | TacExtend (_,"replace", [c1; c2;cl;tac_opt]) ->
	let c1 = xlate_formula (out_gen rawwit_constr c1) in
	let c2 = xlate_formula (out_gen rawwit_constr c2) in
	let cl = 
	  (* J.F. : 18/08/2006 
	     Hack to coerce the "clause" argument of replace to a real clause 
	     To be remove if we can reuse the clause grammar entrie defined in g_tactic
	  *)
	  let cl_as_clause = Extraargs.raw_in_arg_hyp_to_clause (out_gen Extraargs.rawwit_in_arg_hyp cl) in 
	  let cl_as_xlate_arg = 
	    {cl_as_clause with 
	       Tacexpr.onhyps = 
		option_map 
		  (fun l -> 
		     List.map (fun ((l,id),hyp_flag) -> ((l, Tacexpr.AI ((),id)) ,hyp_flag)) l
		  )
		  cl_as_clause.Tacexpr.onhyps
	    }
	  in
	  cl_as_xlate_arg
	in 
	let cl = xlate_clause cl in 
	let tac_opt = 
	  match out_gen (Extraargs.rawwit_by_arg_tac) tac_opt with
	    | None -> CT_coerce_NONE_to_TACTIC_OPT  CT_none
	    | Some tac ->
		let tac =  xlate_tactic tac in
		CT_coerce_TACTIC_COM_to_TACTIC_OPT tac
	in 
	CT_replace_with (c1, c2,cl,tac_opt)
    | TacRewrite(false,[b,cbindl],cl) -> 
     let cl = xlate_clause cl 
     and c = xlate_formula (fst cbindl) 
     and bindl = xlate_bindings (snd cbindl) in
     if b then CT_rewrite_lr (c, bindl, cl)
     else CT_rewrite_rl (c, bindl, cl)
    | TacRewrite(false,_,cl) -> xlate_error "TODO: rewrite of several hyps at once"
    | TacRewrite(true,_,cl) -> xlate_error "TODO: erewrite"
    | TacExtend (_,"conditional_rewrite", [t; b; cbindl]) ->
     let t = out_gen rawwit_main_tactic t in
     let b = out_gen Extraargs.rawwit_orient b in
     let (c,bindl) = out_gen rawwit_constr_with_bindings cbindl in
     let c = xlate_formula c and bindl = xlate_bindings bindl in
     if b then CT_condrewrite_lr (xlate_tactic t, c, bindl, ctv_ID_OPT_NONE)
     else CT_condrewrite_rl (xlate_tactic t, c, bindl, ctv_ID_OPT_NONE)
    | TacExtend (_,"conditional_rewrite", [t; b; cbindl; id]) ->
     let t = out_gen rawwit_main_tactic t in
     let b = out_gen Extraargs.rawwit_orient b in
     let (c,bindl) = out_gen rawwit_constr_with_bindings cbindl in
     let c = xlate_formula c and bindl = xlate_bindings bindl in
     let id = ctf_ID_OPT_SOME (xlate_ident (snd (out_gen rawwit_var id))) in
     if b then CT_condrewrite_lr (xlate_tactic t, c, bindl, id)
     else CT_condrewrite_rl (xlate_tactic t, c, bindl, id)
    | TacExtend (_,"dependent_rewrite", [b; c]) ->
      let b = out_gen Extraargs.rawwit_orient b in
      let c = xlate_formula (out_gen rawwit_constr c) in
      (match c with
	| CT_coerce_ID_to_FORMULA (CT_ident _ as id) -> 
	    if b then CT_deprewrite_lr id else CT_deprewrite_rl id
	| _ -> xlate_error "dependent rewrite on term: not supported")
    | TacExtend (_,"dependent_rewrite", [b; c; id]) ->
	xlate_error "dependent rewrite on terms in hypothesis: not supported"
    | TacExtend (_,"cut_rewrite", [b; c]) ->
      let b = out_gen Extraargs.rawwit_orient b in
      let c = xlate_formula (out_gen rawwit_constr c) in
      if b then CT_cutrewrite_lr (c, ctv_ID_OPT_NONE)
      else CT_cutrewrite_lr (c, ctv_ID_OPT_NONE)
    | TacExtend (_,"cut_rewrite", [b; c; id]) ->
      let b = out_gen Extraargs.rawwit_orient b in
      let c = xlate_formula (out_gen rawwit_constr c) in
      let id = xlate_ident (snd (out_gen rawwit_var id)) in
      if b then CT_cutrewrite_lr (c, ctf_ID_OPT_SOME id)
      else CT_cutrewrite_lr (c, ctf_ID_OPT_SOME id)
    | TacExtend(_, "subst", [l]) ->
	CT_subst
	  (CT_id_list
	     (List.map (fun x -> CT_ident (string_of_id x))
		(out_gen (wit_list1 rawwit_ident) l)))
    | TacReflexivity -> CT_reflexivity
    | TacSymmetry cls -> CT_symmetry(xlate_clause cls)
    | TacTransitivity c -> CT_transitivity (xlate_formula c)
    | TacAssumption -> CT_assumption
    | TacExact c -> CT_exact (xlate_formula c)
    | TacExactNoCheck c -> CT_exact_no_check (xlate_formula c)
    | TacVmCastNoCheck c -> CT_vm_cast_no_check (xlate_formula c)
    | TacDestructHyp (true, (_,id)) -> CT_cdhyp (xlate_ident id)
    | TacDestructHyp (false, (_,id)) -> CT_dhyp (xlate_ident id)
    | TacDestructConcl -> CT_dconcl
    | TacSuperAuto (nopt,l,a3,a4) ->
      CT_superauto(
        xlate_int_opt nopt,
        xlate_qualid_list l,
        (if a3 then CT_destructing else CT_coerce_NONE_to_DESTRUCTING CT_none),
        (if a4 then CT_usingtdb else CT_coerce_NONE_to_USINGTDB CT_none))
    | TacAutoTDB nopt -> CT_autotdb (xlate_int_opt nopt)
    | TacAuto (nopt, [], Some []) -> CT_auto (xlate_int_or_var_opt_to_int_opt nopt)
    | TacAuto (nopt, [], None) ->
 	CT_auto_with (xlate_int_or_var_opt_to_int_opt nopt,
		      CT_coerce_STAR_to_ID_NE_LIST_OR_STAR CT_star)
    | TacAuto (nopt, [], Some (id1::idl)) ->
	CT_auto_with(xlate_int_or_var_opt_to_int_opt nopt,
             CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
             CT_id_ne_list(CT_ident id1, List.map (fun x -> CT_ident x) idl)))
    | TacAuto (nopt, _::_, _) ->
	xlate_error "TODO: auto using"
    |TacExtend(_, ("autorewritev7"|"autorewritev8"), l::t) ->
       let (id_list:ct_ID list) =
	 List.map (fun x -> CT_ident x) (out_gen (wit_list1 rawwit_pre_ident) l) in
       let fst, (id_list1: ct_ID list) =
	 match id_list with [] -> assert false | a::tl -> a,tl in
       let t1 =
	 match t with
	     [t0] -> 
	       CT_coerce_TACTIC_COM_to_TACTIC_OPT
	       (xlate_tactic(out_gen rawwit_main_tactic t0))
	   | [] -> CT_coerce_NONE_to_TACTIC_OPT CT_none
	   | _ -> assert false in
	 CT_autorewrite (CT_id_ne_list(fst, id_list1), t1)
    | TacExtend (_,"eauto", [nopt; popt; lems; idl]) ->
	let first_n =
	  match out_gen (wit_opt rawwit_int_or_var) nopt with
	    | Some (ArgVar(_, s)) -> xlate_id_to_id_or_int_opt s
	    | Some (ArgArg n) -> xlate_int_to_id_or_int_opt n
	    | None -> none_in_id_or_int_opt in
	let second_n =
	  match out_gen (wit_opt rawwit_int_or_var) popt with
	    | Some (ArgVar(_, s)) -> xlate_id_to_id_or_int_opt s
	    | Some (ArgArg n) -> xlate_int_to_id_or_int_opt n
	    | None -> none_in_id_or_int_opt in
	let _lems =
	  match out_gen Eauto.rawwit_auto_using lems with
	    | [] -> []
	    | _ -> xlate_error "TODO: eauto using" in
	let idl = out_gen Eauto.rawwit_hintbases idl in
          (match idl with
	    None -> CT_eauto_with(first_n,
				  second_n,
				  CT_coerce_STAR_to_ID_NE_LIST_OR_STAR CT_star)
	  | Some [] -> CT_eauto(first_n, second_n)
	  | Some (a::l) -> 
	      CT_eauto_with(first_n, second_n,
			    CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR
			      (CT_id_ne_list
				 (CT_ident a,
				  List.map (fun x -> CT_ident x) l))))
    | TacExtend (_,"prolog", [cl; n]) ->
      let cl = List.map xlate_formula (out_gen (wit_list0 rawwit_constr) cl) in
      (match out_gen rawwit_int_or_var n with
	| ArgVar _ -> xlate_error ""
	| ArgArg n -> CT_prolog (CT_formula_list cl, CT_int  n))
    (* eapply now represented by TacApply (true,cbindl) 
    | TacExtend (_,"eapply", [cbindl]) -> 
*)
    | TacTrivial ([],Some []) -> CT_trivial
    | TacTrivial ([],None) -> 
	CT_trivial_with(CT_coerce_STAR_to_ID_NE_LIST_OR_STAR CT_star)
    | TacTrivial ([],Some (id1::idl)) ->
	 CT_trivial_with(CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
            (CT_id_ne_list(CT_ident id1,List.map (fun x -> CT_ident x) idl))))
    | TacTrivial (_::_,_) ->
	xlate_error "TODO: trivial using"
    | TacReduce (red, l) ->
     CT_reduce (xlate_red_tactic red, xlate_clause l)
    | TacApply (false,(c,bindl)) ->
     CT_apply (xlate_formula c, xlate_bindings bindl)
    | TacApply (true,(c,bindl)) ->
     CT_eapply (xlate_formula c, xlate_bindings bindl)
    | TacConstructor (n_or_meta, bindl) ->
	let n = match n_or_meta with AI n -> n | MetaId _ -> xlate_error ""
	in CT_constructor (CT_int n, xlate_bindings bindl)
    | TacSpecialize (nopt, (c,sl)) ->
     CT_specialize (xlate_int_opt nopt, xlate_formula c, xlate_bindings sl)
    | TacGeneralize [] -> xlate_error ""
    | TacGeneralize (first :: cl) ->
     CT_generalize
      (CT_formula_ne_list (xlate_formula first, List.map xlate_formula cl))
    | TacGeneralizeDep c ->
	CT_generalize_dependent (xlate_formula c)
    | TacElimType c -> CT_elim_type (xlate_formula c)
    | TacCaseType c -> CT_case_type (xlate_formula c)
    | TacElim ((c1,sl), u) ->
     CT_elim (xlate_formula c1, xlate_bindings sl, xlate_using u)
    | TacCase (c1,sl) ->
     CT_casetac (xlate_formula c1, xlate_bindings sl)
    | TacSimpleInduction h -> CT_induction (xlate_quantified_hypothesis h)
    | TacSimpleDestruct h -> CT_destruct (xlate_quantified_hypothesis h)
    | TacCut c -> CT_cut (xlate_formula c)
    | TacLApply c -> CT_use (xlate_formula c)
    | TacDecompose ([],c) ->
	xlate_error "Decompose : empty list of identifiers?"
    | TacDecompose (id::l,c) ->
	let id' = apply_or_by_notation tac_qualid_to_ct_ID id in
	let l' = List.map (apply_or_by_notation tac_qualid_to_ct_ID) l in
        CT_decompose_list(CT_id_ne_list(id',l'),xlate_formula c)
    | TacDecomposeAnd c -> CT_decompose_record (xlate_formula c)
    | TacDecomposeOr c -> CT_decompose_sum(xlate_formula c)
    | TacClear (false,[]) ->
	xlate_error "Clear expects a non empty list of identifiers"
    | TacClear (false,id::idl) ->
       let idl' = List.map xlate_hyp idl in
       CT_clear (CT_id_ne_list (xlate_hyp id, idl'))
    | TacClear (true,_) -> xlate_error "TODO: 'clear - idl' and 'clear'"
    | (*For translating tactics/Inv.v *)
      TacInversion (NonDepInversion (k,idl,l),quant_hyp) ->
	CT_inversion(compute_INV_TYPE k, xlate_quantified_hypothesis quant_hyp,
		     xlate_with_names l,
	             CT_id_list (List.map xlate_hyp idl))
    | TacInversion (DepInversion (k,copt,l),quant_hyp) ->
	let id = xlate_quantified_hypothesis quant_hyp in
	CT_depinversion (compute_INV_TYPE k, id, 
			 xlate_with_names l, xlate_formula_opt copt)
    | TacInversion (InversionUsing (c,idlist), id) ->
	let id = xlate_quantified_hypothesis id in
	  CT_use_inversion (id, xlate_formula c,
	    CT_id_list (List.map xlate_hyp idlist))
    | TacExtend (_,"omega", []) -> CT_omega
    | TacRename [id1, id2] -> CT_rename(xlate_hyp id1, xlate_hyp id2)
    | TacRename _ -> xlate_error "TODO: add support for n-ary rename"
    | TacClearBody([]) -> assert false
    | TacClearBody(a::l) -> 
	CT_clear_body (CT_id_ne_list (xlate_hyp a, List.map xlate_hyp l))
    | TacDAuto (a, b) ->
	CT_dauto(xlate_int_or_var_opt_to_int_opt a, xlate_int_opt b)
    | TacNewDestruct(a,b,c) ->
	CT_new_destruct (* Julien F. : est-ce correct *)
	  (List.map  xlate_int_or_constr a, xlate_using b, 
	   xlate_with_names c)
    | TacNewInduction(a,b,c) ->
	CT_new_induction (* Pierre C. : est-ce correct *)
	  (List.map xlate_int_or_constr a, xlate_using b,
	   xlate_with_names c)
    (*| TacInstantiate (a, b, cl) -> 
        CT_instantiate(CT_int a, xlate_formula b,
		       assert false) *)
    | TacLetTac (na, c, cl) when cl = nowhere -> 
        CT_pose(xlate_id_opt_aux na, xlate_formula c)
    | TacLetTac (na, c, cl) ->
        CT_lettac(xlate_id_opt ((0,0),na), xlate_formula c, 
		  (* TODO LATER: This should be shared with Unfold,
		     but the structures are different *)
		  xlate_clause cl)
    | TacAssert (None, IntroIdentifier id, c) -> 
        CT_assert(xlate_id_opt ((0,0),Name id), xlate_formula c)
    | TacAssert (None, IntroAnonymous, c) -> 
        CT_assert(xlate_id_opt ((0,0),Anonymous), xlate_formula c)
    | TacAssert (Some (TacId []), IntroIdentifier id, c) -> 
        CT_truecut(xlate_id_opt ((0,0),Name id), xlate_formula c)
    | TacAssert (Some (TacId []), IntroAnonymous, c) -> 
        CT_truecut(xlate_id_opt ((0,0),Anonymous), xlate_formula c)
    | TacAssert _ ->
	xlate_error "TODO: assert with 'as' and 'by' and pose proof with 'as'"
    | TacAnyConstructor(Some tac) -> 
	CT_any_constructor
	(CT_coerce_TACTIC_COM_to_TACTIC_OPT(xlate_tactic tac))
    | TacAnyConstructor(None) -> 
	CT_any_constructor(CT_coerce_NONE_to_TACTIC_OPT CT_none)
    | TacExtend(_, "ring", [args]) -> 
	CT_ring
	  (CT_formula_list
	     (List.map xlate_formula
		(out_gen (wit_list0 rawwit_constr) args)))
    | TacExtend (_,id, l) ->
	print_endline ("Extratactics : "^ id);
     CT_user_tac (CT_ident id, CT_targ_list (List.map coerce_genarg_to_TARG l))
    | TacAlias _ -> xlate_error "Alias not supported"

and coerce_genarg_to_TARG x =
 match Genarg.genarg_tag x with
  (* Basic types *)
  | BoolArgType -> xlate_error "TODO: generic boolean argument"
  | IntArgType ->
      let n = out_gen rawwit_int x in
	CT_coerce_FORMULA_OR_INT_to_TARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_INT_to_ID_OR_INT (CT_int n)))
  | IntOrVarArgType ->
      let x = match out_gen rawwit_int_or_var x with
	| ArgArg n -> CT_coerce_INT_to_ID_OR_INT (CT_int n)
	| ArgVar (_,id) -> CT_coerce_ID_to_ID_OR_INT (xlate_ident id) in
	CT_coerce_FORMULA_OR_INT_to_TARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT x)
  | StringArgType ->
     let s = CT_string (out_gen rawwit_string x) in
       CT_coerce_SCOMMENT_CONTENT_to_TARG
	 (CT_coerce_ID_OR_STRING_to_SCOMMENT_CONTENT
	    (CT_coerce_STRING_to_ID_OR_STRING s))
  | PreIdentArgType ->
      let id = CT_ident (out_gen rawwit_pre_ident x) in
	CT_coerce_FORMULA_OR_INT_to_TARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_ID_to_ID_OR_INT id))
  | IntroPatternArgType ->
      xlate_error "TODO"
  | IdentArgType ->
      let id = xlate_ident (out_gen rawwit_ident x) in
	CT_coerce_FORMULA_OR_INT_to_TARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_ID_to_ID_OR_INT id))
  | VarArgType ->
      let id = xlate_ident (snd (out_gen rawwit_var x)) in
	CT_coerce_FORMULA_OR_INT_to_TARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_ID_to_ID_OR_INT id))
  | RefArgType ->
      let id = tac_qualid_to_ct_ID (out_gen rawwit_ref x) in
	CT_coerce_FORMULA_OR_INT_to_TARG
	  (CT_coerce_ID_OR_INT_to_FORMULA_OR_INT
	     (CT_coerce_ID_to_ID_OR_INT id))
  (* Specific types *)
  | SortArgType ->
      CT_coerce_SCOMMENT_CONTENT_to_TARG
      (CT_coerce_FORMULA_to_SCOMMENT_CONTENT
        (CT_coerce_SORT_TYPE_to_FORMULA (xlate_sort (out_gen rawwit_sort x))))
  | ConstrArgType ->
      CT_coerce_SCOMMENT_CONTENT_to_TARG
      (CT_coerce_FORMULA_to_SCOMMENT_CONTENT (xlate_formula (out_gen rawwit_constr x)))
  | ConstrMayEvalArgType -> xlate_error"TODO: generic constr-may-eval argument"
  | QuantHypArgType ->xlate_error"TODO: generic quantified hypothesis argument"
  | OpenConstrArgType b -> 
      CT_coerce_SCOMMENT_CONTENT_to_TARG
      	(CT_coerce_FORMULA_to_SCOMMENT_CONTENT(xlate_formula
					 (snd (out_gen
					    (rawwit_open_constr_gen b) x))))
  | ExtraArgType s as y when Pcoq.is_tactic_genarg y ->
      let n = out_some (Pcoq.tactic_genarg_level s) in
      let t = xlate_tactic (out_gen (Pcoq.rawwit_tactic n) x) in
      CT_coerce_TACTIC_COM_to_TARG t
  | ConstrWithBindingsArgType -> xlate_error "TODO: generic constr with bindings"
  | BindingsArgType -> xlate_error "TODO: generic with bindings"
  | RedExprArgType -> xlate_error "TODO: generic red expr"
  | List0ArgType l -> xlate_error "TODO: lists of generic arguments"
  | List1ArgType l -> xlate_error "TODO: non empty lists of generic arguments"
  | OptArgType x -> xlate_error "TODO: optional generic arguments"
  | PairArgType (u,v) -> xlate_error "TODO: pairs of generic arguments"
  | ExtraArgType s -> xlate_error "Cannot treat extra generic arguments"
and xlate_context_rule =
  function
    | Pat (hyps, concl_pat, tactic) ->
	CT_context_rule
	  (CT_context_hyp_list (List.map xlate_match_context_hyps hyps),
	   xlate_context_pattern concl_pat, xlate_tactic tactic)
    | All tactic ->
        CT_def_context_rule (xlate_tactic tactic)
and formula_to_def_body =
  function
    | ConstrEval (red, f) ->
        CT_coerce_EVAL_CMD_to_DEF_BODY(
	CT_eval(CT_coerce_NONE_to_INT_OPT CT_none,
                xlate_red_tactic red, xlate_formula f))
    | ConstrContext((_, id), f) ->
       	CT_coerce_CONTEXT_PATTERN_to_DEF_BODY
	  (CT_context
	     (CT_coerce_ID_to_ID_OPT (CT_ident (string_of_id id)),
	      xlate_formula f))
    | ConstrTypeOf f -> CT_type_of (xlate_formula f)
    | ConstrTerm c -> ct_coerce_FORMULA_to_DEF_BODY(xlate_formula c)

and mk_let_value = function 
    TacArg (ConstrMayEval v) ->
      CT_coerce_DEF_BODY_to_LET_VALUE(formula_to_def_body v)
  | v -> CT_coerce_TACTIC_COM_to_LET_VALUE(xlate_tactic v);;

let coerce_genarg_to_VARG x =
 match Genarg.genarg_tag x with
  (* Basic types *)
  | BoolArgType -> xlate_error "TODO: generic boolean argument"
  | IntArgType ->
      let n = out_gen rawwit_int x in
      CT_coerce_ID_OR_INT_OPT_to_VARG
	(CT_coerce_INT_OPT_to_ID_OR_INT_OPT
	   (CT_coerce_INT_to_INT_OPT (CT_int n)))
  | IntOrVarArgType ->
      (match out_gen rawwit_int_or_var x with
	| ArgArg n -> 
      CT_coerce_ID_OR_INT_OPT_to_VARG
	(CT_coerce_INT_OPT_to_ID_OR_INT_OPT
	   (CT_coerce_INT_to_INT_OPT (CT_int n)))
	| ArgVar (_,id) ->
	    CT_coerce_ID_OPT_OR_ALL_to_VARG
	      (CT_coerce_ID_OPT_to_ID_OPT_OR_ALL
	        (CT_coerce_ID_to_ID_OPT (xlate_ident id))))
  | StringArgType ->
     let s = CT_string (out_gen rawwit_string x) in
     CT_coerce_STRING_OPT_to_VARG (CT_coerce_STRING_to_STRING_OPT s)
  | PreIdentArgType ->
      let id = CT_ident (out_gen rawwit_pre_ident x) in
      CT_coerce_ID_OPT_OR_ALL_to_VARG
	      (CT_coerce_ID_OPT_to_ID_OPT_OR_ALL
	        (CT_coerce_ID_to_ID_OPT id))
  | IntroPatternArgType ->
      xlate_error "TODO"
  | IdentArgType ->
      let id = xlate_ident (out_gen rawwit_ident x) in
      CT_coerce_ID_OPT_OR_ALL_to_VARG
	      (CT_coerce_ID_OPT_to_ID_OPT_OR_ALL
	        (CT_coerce_ID_to_ID_OPT id))
  | VarArgType ->
      let id = xlate_ident (snd (out_gen rawwit_var x)) in
      CT_coerce_ID_OPT_OR_ALL_to_VARG
	      (CT_coerce_ID_OPT_to_ID_OPT_OR_ALL
	        (CT_coerce_ID_to_ID_OPT id))
  | RefArgType ->
      let id = tac_qualid_to_ct_ID (out_gen rawwit_ref x) in
      CT_coerce_ID_OPT_OR_ALL_to_VARG
	      (CT_coerce_ID_OPT_to_ID_OPT_OR_ALL
	        (CT_coerce_ID_to_ID_OPT id))
  (* Specific types *)
  | SortArgType ->
     CT_coerce_FORMULA_OPT_to_VARG 
      (CT_coerce_FORMULA_to_FORMULA_OPT
	(CT_coerce_SORT_TYPE_to_FORMULA (xlate_sort (out_gen rawwit_sort x))))
  | ConstrArgType ->
     CT_coerce_FORMULA_OPT_to_VARG 
      (CT_coerce_FORMULA_to_FORMULA_OPT (xlate_formula (out_gen rawwit_constr x)))
  | ConstrMayEvalArgType -> xlate_error"TODO: generic constr-may-eval argument"
  | QuantHypArgType ->xlate_error"TODO: generic quantified hypothesis argument"
  | ExtraArgType s as y when Pcoq.is_tactic_genarg y ->
      let n = out_some (Pcoq.tactic_genarg_level s) in
      let t = xlate_tactic (out_gen (Pcoq.rawwit_tactic n) x) in
      CT_coerce_TACTIC_OPT_to_VARG (CT_coerce_TACTIC_COM_to_TACTIC_OPT t)
  | OpenConstrArgType _ -> xlate_error "TODO: generic open constr"
  | ConstrWithBindingsArgType -> xlate_error "TODO: generic constr with bindings"
  | BindingsArgType -> xlate_error "TODO: generic with bindings"
  | RedExprArgType -> xlate_error "TODO: red expr as generic argument"
  | List0ArgType l -> xlate_error "TODO: lists of generic arguments"
  | List1ArgType l -> xlate_error "TODO: non empty lists of generic arguments"
  | OptArgType x -> xlate_error "TODO: optional generic arguments"
  | PairArgType (u,v) -> xlate_error "TODO: pairs of generic arguments"
  | ExtraArgType s -> xlate_error "Cannot treat extra generic arguments"


let xlate_thm x = CT_thm (string_of_theorem_kind x)

let xlate_defn k = CT_defn (string_of_definition_kind k)

let xlate_var x = CT_var (match x with
 | (Global,Definitional) -> "Parameter"
 | (Global,Logical) -> "Axiom"
 | (Local,Definitional) -> "Variable"
 | (Local,Logical) -> "Hypothesis"
 | (Global,Conjectural) -> "Conjecture"
 | (Local,Conjectural) -> xlate_error "No local conjecture");;


let xlate_dep =
 function
    | true -> CT_dep "Induction for"
    | false -> CT_dep "Minimality for";;

let xlate_locn =
 function
    | GoTo n -> CT_coerce_INT_to_INT_OR_LOCN (CT_int n)
    | GoTop -> CT_coerce_LOCN_to_INT_OR_LOCN (CT_locn "top")
    | GoPrev -> CT_coerce_LOCN_to_INT_OR_LOCN (CT_locn "prev")
    | GoNext -> CT_coerce_LOCN_to_INT_OR_LOCN (CT_locn "next")

let xlate_search_restr =
  function
    | SearchOutside [] -> CT_coerce_NONE_to_IN_OR_OUT_MODULES CT_none
    | SearchInside (m1::l1) ->
	CT_in_modules (CT_id_ne_list(loc_qualid_to_ct_ID m1,
	List.map loc_qualid_to_ct_ID l1))
    | SearchOutside (m1::l1) ->
	CT_out_modules (CT_id_ne_list(loc_qualid_to_ct_ID m1,
	List.map loc_qualid_to_ct_ID l1))
    | SearchInside [] -> xlate_error "bad extra argument for Search"

let xlate_check =
 function
    | "CHECK" -> "Check"
    | "PRINTTYPE" -> "Type"
    | _ -> xlate_error "xlate_check";;

let build_constructors l =
 let f (coe,((_,id),c)) =
   if coe then CT_constr_coercion (xlate_ident id, xlate_formula c)
   else CT_constr (xlate_ident id, xlate_formula c) in
 CT_constr_list (List.map f l)

let build_record_field_list l =
 let build_record_field (coe,d) = match d with
  | AssumExpr (id,c) ->
      if coe then CT_recconstr_coercion (xlate_id_opt id, xlate_formula c)
      else
	CT_recconstr(xlate_id_opt id, xlate_formula c)
  | DefExpr (id,c,topt) ->
      if coe then
 	CT_defrecconstr_coercion(xlate_id_opt id, xlate_formula c,
			      xlate_formula_opt topt)
      else
 	CT_defrecconstr(xlate_id_opt id, xlate_formula c, xlate_formula_opt topt) in
 CT_recconstr_list (List.map build_record_field l);;

let get_require_flags impexp spec =
 let ct_impexp =
  match impexp with
  | None -> CT_coerce_NONE_to_IMPEXP CT_none
  | Some false -> CT_import
  | Some true -> CT_export in
 let ct_spec =
  match spec with
  | None -> ctv_SPEC_OPT_NONE
  | Some true -> CT_spec
  | Some false -> ctv_SPEC_OPT_NONE in
 ct_impexp, ct_spec;;

let cvt_optional_eval_for_definition c1 optional_eval =
  match optional_eval with
    None -> ct_coerce_FORMULA_to_DEF_BODY (xlate_formula c1)
  | Some red ->
      CT_coerce_EVAL_CMD_to_DEF_BODY(
      CT_eval(CT_coerce_NONE_to_INT_OPT CT_none,
	      xlate_red_tactic red,
	      xlate_formula c1))

let cvt_vernac_binder = function
  | b,(id::idl,c) ->
      let l,t = 
	CT_id_opt_ne_list 
          (xlate_ident_opt (Some (snd id)),
           List.map (fun id -> xlate_ident_opt (Some (snd id))) idl),
          xlate_formula c in
	if b then
	  CT_binder_coercion(l,t)
	else
	  CT_binder(l,t)
  | _, _ -> xlate_error "binder with no left part, rejected";;

let cvt_vernac_binders = function
    a::args -> CT_binder_ne_list(cvt_vernac_binder a, List.map cvt_vernac_binder args)
  | [] -> assert false;;


let xlate_comment = function
    CommentConstr c -> CT_coerce_FORMULA_to_SCOMMENT_CONTENT(xlate_formula c)
  | CommentString s -> CT_coerce_ID_OR_STRING_to_SCOMMENT_CONTENT
      (CT_coerce_STRING_to_ID_OR_STRING(CT_string s))
  | CommentInt n ->
      CT_coerce_FORMULA_to_SCOMMENT_CONTENT
	(CT_coerce_NUM_to_FORMULA(CT_int_encapsulator (string_of_int n)));;

let translate_opt_notation_decl = function
    None -> CT_coerce_NONE_to_DECL_NOTATION_OPT(CT_none)
  |  Some(s, f, sc) ->
       let tr_sc = 
	 match sc with 
	     None -> ctv_ID_OPT_NONE
	   | Some id -> CT_coerce_ID_to_ID_OPT (CT_ident id) in
       CT_decl_notation(CT_string s, xlate_formula f, tr_sc);;

let xlate_level = function
    Extend.NumLevel n -> CT_coerce_INT_to_INT_OR_NEXT(CT_int n)
  | Extend.NextLevel -> CT_next_level;;

let xlate_syntax_modifier = function
    Extend.SetItemLevel((s::sl), level) ->
      CT_set_item_level
	(CT_id_ne_list(CT_ident s, List.map (fun s -> CT_ident s) sl),
	 xlate_level level)
  | Extend.SetItemLevel([], _) -> assert false
  | Extend.SetLevel level -> CT_set_level (CT_int level)
  | Extend.SetAssoc Gramext.LeftA -> CT_lefta
  | Extend.SetAssoc Gramext.RightA -> CT_righta
  | Extend.SetAssoc Gramext.NonA -> CT_nona
  | Extend.SetEntryType(x,typ) ->
      CT_entry_type(CT_ident x,
		 match typ with
		     Extend.ETIdent -> CT_ident "ident"
		   | Extend.ETReference -> CT_ident "global"
		   | Extend.ETBigint -> CT_ident "bigint"
		   | _ -> xlate_error "syntax_type not parsed")
  | Extend.SetOnlyParsing -> CT_only_parsing
  | Extend.SetFormat(_,s) -> CT_format(CT_string s);;


let rec xlate_module_type = function
  | CMTEident(_, qid) -> 
      CT_coerce_ID_to_MODULE_TYPE(CT_ident (xlate_qualid qid))
  | CMTEwith(mty, decl) ->
      let mty1 = xlate_module_type mty in
	(match decl with
	     CWith_Definition((_, idl), c) ->
	       CT_module_type_with_def(mty1, 
				       CT_id_list (List.map xlate_ident idl),
                                       xlate_formula c)
	   | CWith_Module((_, idl), (_, qid)) ->
	       CT_module_type_with_mod(mty1,
				       CT_id_list (List.map xlate_ident idl), 
				       CT_ident (xlate_qualid qid)));;

let xlate_module_binder_list (l:module_binder list) =
  CT_module_binder_list
    (List.map (fun (_, idl, mty) ->
		 let idl1 = 
		   List.map (fun (_, x) -> CT_ident (string_of_id x)) idl in
		 let fst,idl2 = match idl1 with
		     [] -> assert false
		   | fst::idl2 -> fst,idl2 in
		 CT_module_binder
		   (CT_id_ne_list(fst, idl2), xlate_module_type mty)) l);;

let xlate_module_type_check_opt = function
    None -> CT_coerce_MODULE_TYPE_OPT_to_MODULE_TYPE_CHECK
 	(CT_coerce_ID_OPT_to_MODULE_TYPE_OPT ctv_ID_OPT_NONE)
  | Some(mty, true) -> CT_only_check(xlate_module_type mty)
  | Some(mty, false) -> 
      CT_coerce_MODULE_TYPE_OPT_to_MODULE_TYPE_CHECK
	(CT_coerce_MODULE_TYPE_to_MODULE_TYPE_OPT
	   (xlate_module_type mty));;

let rec xlate_module_expr = function
    CMEident (_, qid) -> CT_coerce_ID_OPT_to_MODULE_EXPR
	(CT_coerce_ID_to_ID_OPT (CT_ident (xlate_qualid qid)))
  | CMEapply (me1, me2) -> CT_module_app(xlate_module_expr me1,
					 xlate_module_expr me2)

let rec xlate_vernac =
 function
   | VernacDeclareTacticDefinition (true, tacs) ->
       (match List.map 
	 (function
	      ((_, id), body) ->
		CT_tac_def(CT_ident (string_of_id id), xlate_tactic body))
	 tacs with
	     [] -> assert false
	   | fst::tacs1 ->
	       CT_tactic_definition
		 (CT_tac_def_ne_list(fst, tacs1)))
   | VernacDeclareTacticDefinition(false, _) -> 
       xlate_error "obsolete tactic definition not handled"
    | VernacLoad (verbose,s) ->
      CT_load (
       (match verbose with
        | false -> CT_coerce_NONE_to_VERBOSE_OPT CT_none
        | true -> CT_verbose),
       CT_coerce_STRING_to_ID_OR_STRING (CT_string s))
    | VernacCheckMayEval (Some red, numopt, f) ->
      let red = xlate_red_tactic red in
      CT_coerce_EVAL_CMD_to_COMMAND
       (CT_eval (xlate_int_opt numopt, red, xlate_formula f))
    |VernacChdir opt_s -> CT_cd (ctf_STRING_OPT opt_s)
    | VernacAddLoadPath (false,str,None) ->
 	CT_addpath (CT_string str, ctv_ID_OPT_NONE)
    | VernacAddLoadPath (false,str,Some x) ->
 	CT_addpath (CT_string str,
		    CT_coerce_ID_to_ID_OPT (CT_ident (string_of_dirpath x)))
    | VernacAddLoadPath (true,str,None) ->
 	CT_recaddpath (CT_string str, ctv_ID_OPT_NONE)
    | VernacAddLoadPath (_,str, Some x) ->
	CT_recaddpath (CT_string str,
		       CT_coerce_ID_to_ID_OPT (CT_ident (string_of_dirpath x)))
    | VernacRemoveLoadPath str -> CT_delpath (CT_string str)
    | VernacToplevelControl Quit -> CT_quit
    | VernacToplevelControl _ -> xlate_error "Drop/ProtectedToplevel not supported"
      (*ML commands *)
    | VernacAddMLPath (false,str) -> CT_ml_add_path (CT_string str)
    | VernacAddMLPath (true,str) -> CT_rec_ml_add_path (CT_string str)
    | VernacDeclareMLModule [] -> failwith ""
    | VernacDeclareMLModule (str :: l) ->
      CT_ml_declare_modules
       (CT_string_ne_list (CT_string str, List.map (fun x -> CT_string x) l))
    | VernacGoal c ->
	CT_coerce_THEOREM_GOAL_to_COMMAND (CT_goal (xlate_formula c))
    | VernacAbort (Some (_,id)) ->
	CT_abort(ctf_ID_OPT_OR_ALL_SOME(xlate_ident id))
    | VernacAbort None -> CT_abort ctv_ID_OPT_OR_ALL_NONE
    | VernacAbortAll -> CT_abort ctv_ID_OPT_OR_ALL_ALL
    | VernacRestart -> CT_restart
    | VernacSolve (n, tac, b) -> 
	CT_solve (CT_int n, xlate_tactic tac,
		  if b then CT_dotdot
                  else CT_coerce_NONE_to_DOTDOT_OPT CT_none)

(* MMode *)

    | (VernacDeclProof | VernacReturn | VernacProofInstr _) -> 
	anomaly "No MMode in CTcoq"


(* /MMode *)

    | VernacFocus nopt -> CT_focus (xlate_int_opt nopt)
    | VernacUnfocus -> CT_unfocus
    |VernacExtend("Extraction", [f;l]) ->
       let file = out_gen rawwit_string f in
       let l1 = out_gen (wit_list1 rawwit_ref) l in
       let fst,l2 = match l1 with [] -> assert false | fst::l2 -> fst, l2 in
	 CT_extract_to_file(CT_string file, 
		       CT_id_ne_list(loc_qualid_to_ct_ID fst,
				     List.map loc_qualid_to_ct_ID l2))
    | VernacExtend("ExtractionInline", [l]) ->
	let l1 = out_gen (wit_list1 rawwit_ref) l in
	let fst, l2 = match l1 with [] -> assert false | fst ::l2 -> fst, l2 in
	CT_inline(CT_id_ne_list(loc_qualid_to_ct_ID fst,
				List.map loc_qualid_to_ct_ID l2))
    | VernacExtend("ExtractionNoInline", [l]) ->
	let l1 = out_gen (wit_list1 rawwit_ref) l in
	let fst, l2 = match l1 with [] -> assert false | fst ::l2 -> fst, l2 in
	CT_no_inline(CT_id_ne_list(loc_qualid_to_ct_ID fst,
				List.map loc_qualid_to_ct_ID l2))
    | VernacExtend("Field", 
		   [fth;ainv;ainvl;div]) ->
	(match List.map (fun v -> xlate_formula(out_gen rawwit_constr v))
                   [fth;ainv;ainvl]
 	 with
             [fth1;ainv1;ainvl1] ->
	       let adiv1 =
                 xlate_formula_opt (out_gen (wit_opt rawwit_constr) div) in
	       CT_add_field(fth1, ainv1, ainvl1, adiv1)
	   |_ -> assert false)
  | VernacExtend ("HintRewrite", o::f::([b]|[_;b] as args)) ->
      let orient = out_gen Extraargs.rawwit_orient o in
      let formula_list = out_gen (wit_list1 rawwit_constr) f in
      let base = out_gen rawwit_pre_ident b in
      let t = 
	match args with [t;_] -> out_gen rawwit_main_tactic t | _ -> TacId []
      in
      let ct_orient = match orient with
	| true  -> CT_lr
	| false -> CT_rl in
      let f_ne_list = match List.map xlate_formula formula_list with
	  (fst::rest) -> CT_formula_ne_list(fst,rest)
	| _ -> assert false in
      CT_hintrewrite(ct_orient, f_ne_list, CT_ident base, xlate_tactic t)
  | VernacHints (local,dbnames,h) ->
      let dblist = CT_id_list(List.map (fun x -> CT_ident x) dbnames) in
      (match h with
	| HintsConstructors l ->
	 let n1, names = match List.map tac_qualid_to_ct_ID l with
	     n1 :: names -> n1, names
	   | _  -> failwith "" in
	   if local then
	     CT_local_hints(CT_ident "Constructors",
			    CT_id_ne_list(n1, names), dblist)
	   else
	     CT_hints(CT_ident "Constructors",
		      CT_id_ne_list(n1, names), dblist)
	| HintsExtern (n, c, t) ->
	    CT_hint_extern(CT_int n, xlate_formula c, xlate_tactic t, dblist)
        | HintsResolve l | HintsImmediate l -> 
	 let f1, formulas = match List.map xlate_formula l with
	     a :: tl -> a, tl
	   | _  -> failwith "" in
	 let l' = CT_formula_ne_list(f1, formulas) in
	   if local then
             (match h with 
		  HintsResolve _ ->
		    CT_local_hints_resolve(l', dblist)
	       	| HintsImmediate _ ->
		    CT_local_hints_immediate(l', dblist)
	       	| _ -> assert false)
	   else
	     (match h with
		  HintsResolve _ -> CT_hints_resolve(l', dblist)
		| HintsImmediate _ -> CT_hints_immediate(l', dblist)
		| _ -> assert false)
        | HintsUnfold l -> 
	 let n1, names = match List.map loc_qualid_to_ct_ID l with
	     n1 :: names -> n1, names
	   | _  -> failwith "" in
	   if local then
             CT_local_hints(CT_ident "Unfold",
			    CT_id_ne_list(n1, names), dblist)
	   else	     
             CT_hints(CT_ident "Unfold", CT_id_ne_list(n1, names), dblist)
       	| HintsDestruct(id, n, loc, f, t) ->
	    let dl = match loc with
		ConclLocation() -> CT_conclusion_location
	      | HypLocation true -> CT_discardable_hypothesis
	      | HypLocation false -> CT_hypothesis_location in
	     if local then
               CT_local_hint_destruct
		 (xlate_ident id, CT_int n,
		  dl, xlate_formula f, xlate_tactic t, dblist)
	     else
	       CT_hint_destruct
		 (xlate_ident id, CT_int n, dl, xlate_formula f,
		  xlate_tactic t, dblist)
)
  | VernacEndProof (Proved (true,None)) ->
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm "Theorem"), ctv_ID_OPT_NONE)
  | VernacEndProof (Proved (false,None)) ->
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm "Definition"), ctv_ID_OPT_NONE)
  | VernacEndProof (Proved (b,Some ((_,s), Some kind))) ->
      CT_save (CT_coerce_THM_to_THM_OPT (xlate_thm kind),
       ctf_ID_OPT_SOME (xlate_ident s))
  | VernacEndProof (Proved (b,Some ((_,s),None))) ->
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm "Theorem"),
       ctf_ID_OPT_SOME (xlate_ident s))
  | VernacEndProof Admitted ->
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm "Admitted"), ctv_ID_OPT_NONE)
  | VernacSetOpacity (false, id :: idl) ->
            CT_transparent(CT_id_ne_list(loc_qualid_to_ct_ID id,
                   List.map loc_qualid_to_ct_ID idl))
  | VernacSetOpacity (true, id :: idl)
            -> CT_opaque (CT_id_ne_list(loc_qualid_to_ct_ID id,
                   List.map loc_qualid_to_ct_ID idl))
  | VernacSetOpacity (_, []) -> xlate_error "Shouldn't occur"
  | VernacUndo n -> CT_undo (CT_coerce_INT_to_INT_OPT (CT_int n))
  | VernacShow (ShowGoal nopt) -> CT_show_goal (xlate_int_opt nopt)
  | VernacShow ShowNode -> CT_show_node
  | VernacShow ShowProof -> CT_show_proof
  | VernacShow ShowTree -> CT_show_tree
  | VernacShow ShowProofNames -> CT_show_proofs
  | VernacShow (ShowIntros true) -> CT_show_intros
  | VernacShow (ShowIntros false) -> CT_show_intro
  | VernacShow (ShowGoalImplicitly None) -> CT_show_implicit (CT_int 1)
  | VernacShow (ShowGoalImplicitly (Some n)) -> CT_show_implicit (CT_int n)
  | VernacShow ShowExistentials -> CT_show_existentials
  | VernacShow ShowScript -> CT_show_script
  | VernacShow(ShowMatch _) -> xlate_error "TODO: VernacShow(ShowMatch _)"
  | VernacShow(ShowThesis) -> xlate_error "TODO: VernacShow(ShowThesis _)"
  | VernacGo arg -> CT_go (xlate_locn arg)
  | VernacShow (ExplainProof l) -> CT_explain_proof (nums_to_int_list l)
  | VernacShow (ExplainTree l) ->
      CT_explain_prooftree (nums_to_int_list l)
  | VernacCheckGuard -> CT_guarded
  | VernacPrint p ->
      (match p with
	  PrintFullContext -> CT_print_all
	| PrintName id -> CT_print_id (loc_qualid_to_ct_ID id)
	| PrintOpaqueName id -> CT_print_opaqueid (loc_qualid_to_ct_ID id)
	| PrintSectionContext id -> CT_print_section (loc_qualid_to_ct_ID id)
	| PrintModules -> CT_print_modules
	| PrintGrammar name -> CT_print_grammar CT_grammar_none
	| PrintHintDb -> CT_print_hintdb (CT_coerce_STAR_to_ID_OR_STAR CT_star)
	| PrintHintDbName id -> 
	    CT_print_hintdb (CT_coerce_ID_to_ID_OR_STAR (CT_ident id))
	| PrintRewriteHintDbName id -> 
	    CT_print_rewrite_hintdb (CT_ident id)
	| PrintHint id ->
	    CT_print_hint (CT_coerce_ID_to_ID_OPT (loc_qualid_to_ct_ID id))
	| PrintHintGoal -> CT_print_hint ctv_ID_OPT_NONE
	| PrintLoadPath -> CT_print_loadpath
	| PrintMLLoadPath -> CT_ml_print_path
	| PrintMLModules -> CT_ml_print_modules
	| PrintGraph -> CT_print_graph
	| PrintClasses -> CT_print_classes
	| PrintLtac qid -> CT_print_ltac (loc_qualid_to_ct_ID qid)
	| PrintCoercions -> CT_print_coercions
	| PrintCoercionPaths (id1, id2) -> 
	    CT_print_path (xlate_class id1, xlate_class id2)
	| PrintCanonicalConversions ->
	    xlate_error "TODO: Print Canonical Structures"
	| PrintNeededAssumptions _ -> 
	    xlate_error "TODO: Print Needed Assumptions"
	| PrintInspect n -> CT_inspect (CT_int n)
	| PrintUniverses opt_s -> CT_print_universes(ctf_STRING_OPT opt_s)
	| PrintSetoids -> CT_print_setoids
	| PrintTables -> CT_print_tables
        | PrintModuleType a -> CT_print_module_type (loc_qualid_to_ct_ID a)
        | PrintModule a -> CT_print_module (loc_qualid_to_ct_ID a)
        | PrintScopes -> CT_print_scopes
        | PrintScope id -> CT_print_scope (CT_ident id)
	| PrintVisibility id_opt ->
	    CT_print_visibility 
	      (match id_opt with
		   Some id -> CT_coerce_ID_to_ID_OPT(CT_ident id)
		 | None -> ctv_ID_OPT_NONE)
        | PrintAbout qid -> CT_print_about(loc_qualid_to_ct_ID qid)
	| PrintImplicit qid -> CT_print_implicit(loc_qualid_to_ct_ID qid))
  | VernacBeginSection (_,id) ->
      CT_coerce_SECTION_BEGIN_to_COMMAND (CT_section (xlate_ident id))
  | VernacEndSegment (_,id) -> CT_section_end (xlate_ident id)
  | VernacStartTheoremProof (k, (_,s), (bl,c), _, _) ->
      CT_coerce_THEOREM_GOAL_to_COMMAND(
	CT_theorem_goal (CT_coerce_THM_to_DEFN_OR_THM (xlate_thm k), xlate_ident s,
           xlate_binder_list bl, xlate_formula c))
  | VernacSuspend -> CT_suspend
  | VernacResume idopt -> CT_resume (xlate_ident_opt (option_map snd idopt))
  | VernacDefinition (k,(_,s),ProveBody (bl,typ),_) ->
      CT_coerce_THEOREM_GOAL_to_COMMAND
	(CT_theorem_goal
	   (CT_coerce_DEFN_to_DEFN_OR_THM (xlate_defn k),
	    xlate_ident s, xlate_binder_list bl, xlate_formula typ))
  | VernacDefinition (kind,(_,s),DefineBody(bl,red_option,c,typ_opt),_) ->
      CT_definition
	(xlate_defn kind, xlate_ident s, xlate_binder_list bl,
	   cvt_optional_eval_for_definition c red_option,
           xlate_formula_opt typ_opt)
  | VernacAssumption (kind,inline ,b) ->xlate_error "TODO: Parameter Inline"
      (*inline : bool -> automatic delta reduction at fonctor application*)
     (* CT_variable (xlate_var kind, cvt_vernac_binders b)*)
  | VernacCheckMayEval (None, numopt, c) ->
      CT_check (xlate_formula c)
  | VernacSearch (s,x) ->
      let translated_restriction = xlate_search_restr x in
      (match s with
	| SearchPattern c ->
	    CT_search_pattern(xlate_formula c, translated_restriction)
	| SearchHead id ->
	    CT_search(loc_qualid_to_ct_ID id, translated_restriction)
	| SearchRewrite c ->
	    CT_search_rewrite(xlate_formula c, translated_restriction)
	| SearchAbout (a::l) ->
	    let xlate_search_about_item it =
	      match it with
		  SearchRef x -> 
		    CT_coerce_ID_to_ID_OR_STRING(loc_qualid_to_ct_ID x)
		| SearchString s -> 
		    CT_coerce_STRING_to_ID_OR_STRING(CT_string s) in
	    CT_search_about
	      (CT_id_or_string_ne_list(xlate_search_about_item a,
				       List.map xlate_search_about_item l),
	       translated_restriction)
  	| SearchAbout [] -> assert false)

  | (*Record from tactics/Record.v *)
    VernacRecord 
      (_, (add_coercion, (_,s)), binders, c1,
       rec_constructor_or_none, field_list) ->
      let record_constructor =
        xlate_ident_opt (option_map snd rec_constructor_or_none) in
      CT_record
       ((if add_coercion then CT_coercion_atm else
          CT_coerce_NONE_to_COERCION_OPT(CT_none)),
        xlate_ident s, xlate_binder_list binders, 
	xlate_formula c1, record_constructor,
         build_record_field_list field_list)
   | VernacInductive (isind, lmi) ->
      let co_or_ind = if isind then "Inductive" else "CoInductive" in
      let strip_mutind (((_,s), parameters, c, constructors), notopt) =
          CT_ind_spec
            (xlate_ident s, xlate_binder_list parameters, xlate_formula c,
             build_constructors constructors,
	     translate_opt_notation_decl notopt) in
        CT_mind_decl
	  (CT_co_ind co_or_ind, CT_ind_spec_list (List.map strip_mutind lmi))
   | VernacFixpoint ([],_) -> xlate_error "mutual recursive"
   | VernacFixpoint ((lm :: lmi),boxed) ->
      let strip_mutrec ((fid, (n, ro), bl, arf, ardef), _ntn) =
        let (struct_arg,bl,arf,ardef) =
	 (* Pierre L: could the case [n=None && bl=[]] happen ? Normally not *)
	 (* By the way, how could [bl = []] happen in V8 syntax ?  *)
         if bl = [] then
	   let n = out_some n in 
           let (bl,arf,ardef) = Ppconstr.split_fix (n+1) arf ardef in
           (xlate_id_opt(List.nth (names_of_local_assums bl) n),bl,arf,ardef)
         else (make_fix_struct (n, bl),bl,arf,ardef) in
        let arf = xlate_formula arf in
        let ardef = xlate_formula ardef in
	match xlate_binder_list bl with
	  | CT_binder_list (b :: bl) ->
	      CT_fix_rec (xlate_ident fid, CT_binder_ne_list (b, bl), 
			  struct_arg, arf, ardef)
          | _ -> xlate_error "mutual recursive" in
        CT_fix_decl
	  (CT_fix_rec_list (strip_mutrec lm, List.map strip_mutrec lmi))
   | VernacCoFixpoint ([],boxed) -> xlate_error "mutual corecursive"
   | VernacCoFixpoint ((lm :: lmi),boxed) ->
      let strip_mutcorec ((fid, bl, arf, ardef), _ntn) =
	CT_cofix_rec (xlate_ident fid, xlate_binder_list bl,
                      xlate_formula arf, xlate_formula ardef) in
        CT_cofix_decl
	  (CT_cofix_rec_list (strip_mutcorec lm, List.map strip_mutcorec lmi))
   | VernacScheme [] -> xlate_error "induction scheme"
   | VernacScheme (lm :: lmi) ->
      let strip_ind = function
      | (Some (_,id), InductionScheme (depstr, inde, sort)) ->
           CT_scheme_spec
            (xlate_ident id, xlate_dep depstr, 
	    CT_coerce_ID_to_FORMULA (loc_qualid_to_ct_ID inde),
	     xlate_sort sort)
      | (None, InductionScheme (depstr, inde, sort)) ->
           CT_scheme_spec
            (xlate_ident (id_of_string ""), xlate_dep depstr,
            CT_coerce_ID_to_FORMULA (loc_qualid_to_ct_ID inde),
             xlate_sort sort)
      | (_, EqualityScheme _) -> xlate_error "TODO: Scheme Equality" in
        CT_ind_scheme
	  (CT_scheme_spec_list (strip_ind lm, List.map strip_ind lmi))
   | VernacCombinedScheme _ -> xlate_error "TODO: Combined Scheme"
   | VernacSyntacticDefinition (id, c, false, _) ->
       CT_syntax_macro (xlate_ident id, xlate_formula c, xlate_int_opt None)
   | VernacSyntacticDefinition (id, c, true, _) ->
       xlate_error "TODO: Local abbreviations"
  (* Modules and Module Types *)
  | VernacDeclareModuleType((_, id), bl, mty_o)  -> 
      CT_module_type_decl(xlate_ident id,
			  xlate_module_binder_list bl,
			  match mty_o with
			      None ->
				CT_coerce_ID_OPT_to_MODULE_TYPE_OPT
				  ctv_ID_OPT_NONE
			    | Some mty1 ->
				CT_coerce_MODULE_TYPE_to_MODULE_TYPE_OPT
				  (xlate_module_type mty1))
   | VernacDefineModule(_,(_, id), bl, mty_o, mexpr_o) ->
       CT_module(xlate_ident id, 
		 xlate_module_binder_list bl,
		 xlate_module_type_check_opt mty_o,
		 match mexpr_o with
		     None -> CT_coerce_ID_OPT_to_MODULE_EXPR ctv_ID_OPT_NONE
		   | Some m -> xlate_module_expr m)
  | VernacDeclareModule(_,(_, id), bl, mty_o) -> 
       CT_declare_module(xlate_ident id, 
		 xlate_module_binder_list bl,
		 xlate_module_type_check_opt (Some mty_o),
		 CT_coerce_ID_OPT_to_MODULE_EXPR ctv_ID_OPT_NONE)
   | VernacRequire (impexp, spec, id::idl) ->
      let ct_impexp, ct_spec = get_require_flags impexp spec in
      CT_require (ct_impexp, ct_spec, 
		  CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STRING(
		  CT_id_ne_list(loc_qualid_to_ct_ID id,
				List.map loc_qualid_to_ct_ID idl)))
   | VernacRequire (_,_,[]) ->
       xlate_error "Require should have at least one id argument"
   | VernacRequireFrom (impexp, spec, filename) ->
      let ct_impexp, ct_spec = get_require_flags impexp spec in
      CT_require(ct_impexp, ct_spec, 
		 CT_coerce_STRING_to_ID_NE_LIST_OR_STRING(CT_string filename))

   | VernacOpenCloseScope(true, true, s) -> CT_local_open_scope(CT_ident s)
   | VernacOpenCloseScope(false, true, s) -> CT_open_scope(CT_ident s)
   | VernacOpenCloseScope(true, false, s) -> CT_local_close_scope(CT_ident s)
   | VernacOpenCloseScope(false, false, s) -> CT_close_scope(CT_ident s)
   | VernacArgumentsScope(true, qid, l) -> 
       CT_arguments_scope(loc_qualid_to_ct_ID qid,
		       CT_id_opt_list
		       (List.map
			  (fun x ->
				  match x with
				      None -> ctv_ID_OPT_NONE
				    | Some x -> ctf_ID_OPT_SOME(CT_ident x)) l))
   | VernacArgumentsScope(false, qid, l) -> 
       xlate_error "TODO: Arguments Scope Global"
   | VernacDelimiters(s1,s2) -> CT_delim_scope(CT_ident s1, CT_ident s2)
   | VernacBindScope(id, a::l) -> 
       let xlate_class_rawexpr = function
	   FunClass -> CT_ident "Funclass" | SortClass -> CT_ident "Sortclass"
	 | RefClass qid -> loc_qualid_to_ct_ID qid in
       CT_bind_scope(CT_ident id,
		     CT_id_ne_list(xlate_class_rawexpr a,
				   List.map xlate_class_rawexpr l))
   | VernacBindScope(id, []) -> assert false
   | VernacNotation(b, c, (s,modif_list), opt_scope) -> 
       let translated_s = CT_string s in
       let formula = xlate_formula c in
       let translated_modif_list = 
	 CT_modifier_list(List.map xlate_syntax_modifier modif_list) in
       let translated_scope = match opt_scope with
	   None -> ctv_ID_OPT_NONE
	 | Some x -> ctf_ID_OPT_SOME(CT_ident x) in
       if b then
       CT_local_define_notation
	 (translated_s, formula, translated_modif_list, translated_scope)
       else
	 CT_define_notation(translated_s, formula, 
			    translated_modif_list, translated_scope)
   | VernacSyntaxExtension(b,(s,modif_list)) -> 
       let translated_s = CT_string s in
       let translated_modif_list = 
	 CT_modifier_list(List.map xlate_syntax_modifier modif_list) in
       if b then
	 CT_local_reserve_notation(translated_s, translated_modif_list)
       else
	 CT_reserve_notation(translated_s, translated_modif_list)
   | VernacInfix (b,(str,modl),id, opt_scope) ->
       let id1 = loc_qualid_to_ct_ID id in
       let modl1 = CT_modifier_list(List.map xlate_syntax_modifier modl) in
       let s = CT_string str in
       let translated_scope = match opt_scope with
	   None -> ctv_ID_OPT_NONE
	 | Some x -> ctf_ID_OPT_SOME(CT_ident x) in
	 if b then
	   CT_local_infix(s, id1,modl1, translated_scope)
	 else
	   CT_infix(s, id1,modl1, translated_scope)
   | VernacCoercion (s, id1, id2, id3) ->
      let id_opt = CT_coerce_NONE_to_IDENTITY_OPT CT_none in
      let local_opt =
       match s with
       (* Cannot decide whether it is a global or a Local but at toplevel *)
       | Global -> CT_coerce_NONE_to_LOCAL_OPT CT_none
       | Local -> CT_local in
      CT_coercion (local_opt, id_opt, loc_qualid_to_ct_ID id1,
        xlate_class id2, xlate_class id3)

   | VernacIdentityCoercion (s, (_,id1), id2, id3) ->
      let id_opt = CT_identity in
      let local_opt =
       match s with
       (* Cannot decide whether it is a global or a Local but at toplevel *)
       | Global -> CT_coerce_NONE_to_LOCAL_OPT CT_none
       | Local -> CT_local in
      CT_coercion (local_opt, id_opt, xlate_ident id1,
        xlate_class id2, xlate_class id3)
  | VernacResetName id -> CT_reset (xlate_ident (snd id))
  | VernacResetInitial -> CT_restore_state (CT_ident "Initial")
  | VernacExtend (s, l) ->
      CT_user_vernac
       (CT_ident s, CT_varg_list (List.map coerce_genarg_to_VARG l))
  | VernacList((_, a)::l) -> 
      CT_coerce_COMMAND_LIST_to_COMMAND
	(CT_command_list(xlate_vernac a, 
			 List.map (fun (_, x) -> xlate_vernac x) l))
  | VernacList([]) -> assert false
  | VernacNop -> CT_proof_no_op
  | VernacComments l -> 
      CT_scomments(CT_scomment_content_list (List.map xlate_comment l))
  | VernacDeclareImplicits(true, id, opt_positions) ->
      CT_implicits
	(reference_to_ct_ID id,
	 match opt_positions with
	     None -> CT_coerce_NONE_to_ID_LIST_OPT CT_none
	   | Some l -> 
	       CT_coerce_ID_LIST_to_ID_LIST_OPT
	       (CT_id_list
	       (List.map
		  (function ExplByPos x, _
		       -> xlate_error
			   "explication argument by rank is obsolete"
		     | ExplByName id, _ -> CT_ident (string_of_id id)) l)))
  | VernacDeclareImplicits(false, id, opt_positions) ->
      xlate_error "TODO: Implicit Arguments Global"
  | VernacReserve((_,a)::l, f) ->
      CT_reserve(CT_id_ne_list(xlate_ident a, 
			       List.map (fun (_,x) -> xlate_ident x) l),
		 xlate_formula f)
  | VernacReserve([], _) -> assert false
  | VernacLocate(LocateTerm id) -> CT_locate(reference_to_ct_ID id)
  | VernacLocate(LocateLibrary id) -> CT_locate_lib(reference_to_ct_ID id)
  | VernacLocate(LocateModule _) -> xlate_error "TODO: Locate Module"
  | VernacLocate(LocateFile s) -> CT_locate_file(CT_string s)
  | VernacLocate(LocateNotation s) -> CT_locate_notation(CT_string s)
  | VernacTime(v) -> CT_time(xlate_vernac v)
  | VernacSetOption (Goptions.SecondaryTable ("Implicit", "Arguments"), BoolValue true)->CT_user_vernac (CT_ident "IMPLICIT_ARGS_ON", CT_varg_list[])
  |VernacExactProof f -> CT_proof(xlate_formula f)
  | VernacSetOption (table, BoolValue true) -> 
      let table1 = 
	match table with
	    PrimaryTable(s) -> CT_coerce_ID_to_TABLE(CT_ident s)
	  | SecondaryTable(s1,s2) -> CT_table(CT_ident s1, CT_ident s2)
	  | TertiaryTable(s1,s2,s3) -> xlate_error "TODO: TertiaryTable" in
	CT_set_option(table1)
  | VernacSetOption (table, v) -> 
      let table1 = 
	match table with
	    PrimaryTable(s) -> CT_coerce_ID_to_TABLE(CT_ident s)
	  | SecondaryTable(s1,s2) -> CT_table(CT_ident s1, CT_ident s2)
	  | TertiaryTable(s1,s2,s3) -> xlate_error "TODO: TertiaryTable" in
      let value =
	match v with
	  | BoolValue _ -> assert false
	  | StringValue s ->
	      CT_coerce_STRING_to_SINGLE_OPTION_VALUE(CT_string s)
	  | IntValue n ->
	      CT_coerce_INT_to_SINGLE_OPTION_VALUE(CT_int n) in
	CT_set_option_value(table1, value)
  | VernacUnsetOption(table) ->
      let table1 = 
	match table with
	    PrimaryTable(s) -> CT_coerce_ID_to_TABLE(CT_ident s)
	  | SecondaryTable(s1,s2) -> CT_table(CT_ident s1, CT_ident s2)
	  | TertiaryTable(s1,s2,s3) -> xlate_error "TODO: TertiaryTable" in
	CT_unset_option(table1)
  | VernacAddOption (table, l) ->
      let values =
	List.map
	  (function
	     | QualidRefValue x -> 
		 CT_coerce_ID_to_ID_OR_STRING(loc_qualid_to_ct_ID x)
	     | StringRefValue x -> 
		 CT_coerce_STRING_to_ID_OR_STRING(CT_string x)) l in
      let fst, values1 = 
	match values with [] -> assert false | a::b -> (a,b) in
      let table1 = 
	match table with
	    PrimaryTable(s) -> CT_coerce_ID_to_TABLE(CT_ident s)
	  | SecondaryTable(s1,s2) -> CT_table(CT_ident s1, CT_ident s2)
	  | TertiaryTable(s1,s2,s3) -> xlate_error "TODO: TertiaryTable" in
	CT_set_option_value2(table1, CT_id_or_string_ne_list(fst, values1))
  | VernacImport(true, a::l) ->
      CT_export_id(CT_id_ne_list(reference_to_ct_ID a,
				 List.map reference_to_ct_ID l))
  | VernacImport(false, a::l) ->
      CT_import_id(CT_id_ne_list(reference_to_ct_ID a,
				 List.map reference_to_ct_ID l))
  | VernacImport(_, []) -> assert false
  | VernacProof t -> CT_proof_with(xlate_tactic t)
  | VernacVar _ -> xlate_error "Grammar vernac obsolete"
  | (VernacGlobalCheck _|VernacPrintOption _|
     VernacMemOption (_, _)|VernacRemoveOption (_, _)
  | VernacBack _ | VernacBacktrack _ |VernacBackTo _|VernacRestoreState _| VernacWriteState _|
    VernacSolveExistential (_, _)|VernacCanonical _ |
     VernacTacticNotation _)
    -> xlate_error "TODO: vernac";;

let rec xlate_vernac_list =
 function
   | VernacList (v::l) ->
       CT_command_list
         (xlate_vernac (snd v), List.map (fun (_,x) -> xlate_vernac x) l)
   | VernacList [] -> xlate_error "xlate_command_list"
   | _ -> xlate_error "Not a list of commands";;
