(** Translation from coq abstract syntax trees to centaur vernac
   *)
open String;;
open Char;;
open Util;;
open Ast;;
open Names;;
open Ascent;;
open Genarg;;
open Rawterm;;
open Tacexpr;;
open Vernacexpr;;
open Decl_kinds;;
open Topconstr;;
open Libnames;;


let in_coq_ref = ref false;;

let declare_in_coq () = in_coq_ref:=true;;

let in_coq () = !in_coq_ref;;

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

let string_of_node_loc the_node =
  match loc the_node with
      (a,b) -> "(" ^ (string_of_int a) ^ ", " ^ (string_of_int b) ^ ")";;

let xlate_error s = failwith ("Translation error: " ^ s);;

let ctf_STRING_OPT_NONE = CT_coerce_NONE_to_STRING_OPT CT_none;;

let ctf_STRING_OPT_SOME s = CT_coerce_STRING_to_STRING_OPT s;;

let ctf_STRING_OPT = function
  | None -> ctf_STRING_OPT_NONE
  | Some s -> ctf_STRING_OPT_SOME s

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

let xlate_id_unit = function
    None -> CT_unit
  | Some x -> CT_coerce_ID_to_ID_UNIT (xlate_ident x);;

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
    | CPatDelimiters(_, _, _) -> xlate_error "CPatDelimitors"
    | CPatNumeral(_,_) -> xlate_error "CPatNumeral"
    | CPatNotation _ -> xlate_error "CPatNotation";;




let xlate_id_opt = function
  | (_,Name id) -> ctf_ID_OPT_SOME(CT_ident (string_of_id id))
  | (_,Anonymous) -> ctv_ID_OPT_NONE;;

let xlate_id_opt_ne_list = function
    [] -> assert false
  | a::l -> CT_id_opt_ne_list(xlate_id_opt a, List.map xlate_id_opt l);;



let rec xlate_binder = function
    (l,t) -> CT_binder(xlate_id_opt_ne_list l, xlate_formula t)
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
    (_,lp, a) -> CT_eqn ( xlate_match_pattern_ne_list lp,
	     xlate_formula a)
and 
  xlate_binder_ne_list = function
    [] -> assert false
  | a::l -> CT_binder_ne_list(xlate_binder a, List.map xlate_binder l)
and 
  xlate_binder_list = function
  l -> CT_binder_list( List.map xlate_binder_l l)
and  cvt_fixpoint_binders bl =
  CT_binder_list(List.map xlate_binder bl)
and (xlate_formula:Topconstr.constr_expr -> Ascent.ct_FORMULA) = function

     CRef r -> varc (xlate_reference r)
   | CArrow(_,a,b)-> CT_arrowc (xlate_formula a, xlate_formula b)
   | CProdN(_,ll,b)-> CT_prodc(xlate_binder_ne_list ll, xlate_formula b)
   | CLambdaN(_,ll,b)-> CT_lambdac(xlate_binder_ne_list ll, xlate_formula b)
   | CLetIn(_, v, a, b) -> 
       CT_letin(CT_def(xlate_id_opt v, xlate_formula a), xlate_formula b)
   | CAppExpl(_, (_,r), l) -> (* TODO: proj notation *)
       CT_appc(CT_bang(xlate_int_opt None, varc (xlate_reference r)),
	       xlate_formula_ne_list l)
   | CApp(_, (_,f), l) -> (* TODO: proj notation *)
       CT_appc(xlate_formula f, xlate_formula_expl_ne_list l)
   | CCases (_,(po,None),tml,eqns)-> CT_cases(xlate_formula_opt po, 
                         xlate_formula_ne_list (List.map fst tml),
                         CT_eqn_list (List.map 
         (fun x -> translate_one_equation x)
			   eqns))
   | CCases (_,(po,Some _),tml,eqns)-> xlate_error "TODO"
   | COrderedCase (_,Term.IfStyle,po,c,[b1;b2]) -> 
		   CT_if(xlate_formula_opt po,
                   xlate_formula c,xlate_formula b1,xlate_formula b2)		
   | CLetTuple (_,l, (na,po), c, b) -> xlate_error "LetTuple: TODO"
   | CIf (_,c, (na,None), b1, b2) ->
		   CT_if(ctv_FORMULA_OPT_NONE,
                   xlate_formula c,xlate_formula b1,xlate_formula b2)
   | CIf (_,c, (na,Some p), b1, b2) -> xlate_error "If: TODO"

   | COrderedCase (_,Term.LetStyle, po, c, [CLambdaN(_,[l,_],b)]) ->
       CT_inductive_let(xlate_formula_opt po,
	       xlate_id_opt_ne_list l,
	       xlate_formula c, xlate_formula b) 
   | COrderedCase (_,c,v,e,l) -> 
       let case_string = match c with
	   Term.MatchStyle -> "Match"
	 | _ -> "Case" in
	 CT_elimc(CT_case "Case", xlate_formula_opt v, xlate_formula e,
		  CT_formula_list(List.map xlate_formula l))
   | CSort(_, s) -> CT_coerce_SORT_TYPE_to_FORMULA(xlate_sort s)
   | CNotation(_, s, l) -> notation_to_formula s (List.map xlate_formula l)
   | CNumeral(_, i) -> CT_int_encapsulator(Bignat.bigint_to_string i)
   | CHole _ -> CT_existvarc 
(* I assume CDynamic has been inserted to make free form extension of
   the language possible, but this would go agains the logic of pcoq anyway. *)
   | CDynamic (_, _) -> assert false
   | CDelimiters (_, key, num) -> CT_num_encapsulator(CT_num_type key , xlate_formula  num)
   | CCast (_, e, t) -> 
       CT_coerce_TYPED_FORMULA_to_FORMULA
	 (CT_typed_formula(xlate_formula e, xlate_formula t))
   | CPatVar (_, (_,i)) when is_int_meta i ->
       CT_coerce_ID_to_FORMULA(CT_metac (CT_int (int_of_meta i)))
   | CPatVar (_, _) -> xlate_error "TODO: meta as ident"
   | CEvar (_, _) -> xlate_error "TODO: evars"
   | CCoFix (_, (_, id), lm::lmi) -> 
     let strip_mutcorec (fid, arf, ardef) =
	CT_cofix_rec (xlate_ident fid, xlate_formula arf, xlate_formula ardef) in
        CT_cofixc(xlate_ident id,
	  (CT_cofix_rec_list (strip_mutcorec lm, List.map strip_mutcorec lmi)))
   | CFix (_, (_, id), lm::lmi) ->       
     let strip_mutrec (fid, n, arf, ardef) =
        let (bl,arf,ardef) = Ppconstr.split_fix (n+1) arf ardef in
        let arf = xlate_formula arf in
        let ardef = xlate_formula ardef in
	match cvt_fixpoint_binders bl with
	  | CT_binder_list (b :: bl) ->
	      CT_fix_rec (xlate_ident fid, CT_binder_ne_list (b, bl),
                arf, ardef)
          | _ -> xlate_error "mutual recursive" in
       CT_fixc (xlate_ident id, 
         	CT_fix_binder_list
		  (CT_coerce_FIX_REC_to_FIX_BINDER 
		     (strip_mutrec lm), List.map 
		       (fun x-> CT_coerce_FIX_REC_to_FIX_BINDER (strip_mutrec x))
		       lmi)) 
   | CCoFix _ -> assert false
   | CFix _ -> assert false
and xlate_formula_expl = function
    (a, None) -> xlate_formula a
  | (a, Some (_,ExplByPos i)) -> 
      CT_bang(xlate_int_opt (Some i), xlate_formula a)
  | (a, Some (_,ExplByName i)) ->
      xlate_error "TODO: explicitation of implicit by name"
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
  | AI (_,id), _, (InHypTypeOnly,_) -> CT_intype(xlate_ident id)
  | AI (_,id), _, (InHyp,_) when !Options.v7 ->
      CT_coerce_ID_to_HYP_LOCATION (xlate_ident id)
  | AI (_,id), _, ((InHypValueOnly|InHyp),_) ->
      xlate_error "TODO in v8: InHyp now means InHyp if variable but InHypValueOnly if a local definition"
  | MetaId _, _,_ -> 
      xlate_error "MetaId not supported in xlate_hyp_location (should occur only in quotations)"

let xlate_clause cls =
  CT_clause
    (CT_hyp_location_list_opt
      (option_app
        (fun l -> CT_hyp_location_list(List.map xlate_hyp_location l))
        cls.onhyps),
      if cls.onconcl then CT_true else CT_false)

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
    if r.rDelta then
      [CT_delta], CT_unfbut (List.map tac_qualid_to_ct_ID r.rConst)
    else
      (if r.rConst = []
      then (* probably useless: just for compatibility *) []
      else [CT_delta]),
      CT_unf (List.map tac_qualid_to_ct_ID r.rConst) in
  let conv_flags = if r.rBeta then CT_beta::conv_flags else conv_flags in
  let conv_flags = if r.rIota then CT_iota::conv_flags else conv_flags in
  let conv_flags = if r.rZeta then CT_zeta::conv_flags else conv_flags in
  (* Rem: EVAR flag obsolète *)
  conv_flags, red_ids

let rec xlate_intro_pattern =
 function
  | IntroOrAndPattern [l] ->
      CT_conj_pattern(CT_intro_patt_list (List.map xlate_intro_pattern l))
  | IntroOrAndPattern ll ->
      let insert_conj l = CT_conj_pattern (CT_intro_patt_list
        (List.map xlate_intro_pattern l))
      in CT_disj_pattern(CT_intro_patt_list (List.map insert_conj ll))
  | IntroWildcard -> CT_coerce_ID_to_INTRO_PATT(CT_ident "_" )
  | IntroIdentifier c -> CT_coerce_ID_to_INTRO_PATT(xlate_ident c)

let xlate_newind_names = 
  function
    | IntroIdentifier id -> xlate_ident id
    | _ -> xlate_error "TODO: intro_patterns for NewDestruct/NewInduction"

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
  | Hyp (na,b) -> CT_premise_pattern(xlate_id_opt na, xlate_context_pattern b)


let xlate_largs_to_id_unit largs =
  match List.map xlate_id_unit largs with
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
    (nums,qid) -> 
      CT_unfold_occ (CT_int_list (List.map (fun x -> CT_int x) nums),
		     tac_qualid_to_ct_ID qid);;

let xlate_lettac_clauses = function
    (opt_l, l') ->
      let res = 
	(List.map 
	   (fun (id, l) -> 
	      CT_unfold_occ(CT_int_list (List.map (fun x -> CT_int x) l),
			    xlate_ident_or_metaid id)) l') in
	match opt_l with
	    Some l ->
	      CT_unfold_list
	      	((CT_unfold_occ
		    (CT_int_list (List.map (fun x -> CT_int x) l),
		     CT_ident "Goal"))::res)
	  | None -> CT_unfold_list res;;

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
    | t -> xlate_error "TODO LATER: result other than tactic or constr"

and xlate_red_tactic =
 function
  | Red true -> xlate_error ""
  | Red false -> CT_red
  | Hnf -> CT_hnf
  | Simpl None -> CT_simpl ctv_PATTERN_OPT_NONE
  | Simpl (Some (l,c)) -> 
      CT_simpl 
	(CT_coerce_PATTERN_to_PATTERN_OPT
	   (CT_pattern_occ
	      (CT_int_list(List.map (fun n -> CT_int n) l), xlate_formula c)))
  | Cbv flag_list ->
     let conv_flags, red_ids = get_flag flag_list in
     CT_cbv (CT_conversion_flag_list conv_flags, red_ids)
  | Lazy flag_list ->
     let conv_flags, red_ids = get_flag flag_list in
     CT_cbv (CT_conversion_flag_list conv_flags, red_ids)
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
           (CT_int_list (List.map (fun x -> CT_int x) nums),
            xlate_formula c)) l in
     (match pat_list with
      | first :: others -> CT_pattern (CT_pattern_ne_list (first, others))
      | [] -> error "Expecting at least one pattern in a Pattern command")
  | ExtraRedExpr _ -> xlate_error "TODO LATER: ExtraRedExpr (probably dead code)"

and xlate_rec_tac = function
  | ((_,x),TacFun (argl,tac)) ->
      let fst, rest = xlate_largs_to_id_unit ((Some x)::argl) in
	CT_rec_tactic_fun(xlate_ident x,
			  CT_id_unit_list(fst, rest),
			  xlate_tactic tac)
  | ((_,x),tac) ->
      CT_rec_tactic_fun(xlate_ident x,
			CT_id_unit_list (xlate_id_unit (Some x), []),
			xlate_tactic tac)

and xlate_local_rec_tac = function 
 (* TODO LATER: local recursive tactics and global ones should be handled in
    the same manner *)
  | ((_,x),(argl,tac)) ->
      let fst, rest = xlate_largs_to_id_unit ((Some x)::argl) in
	CT_rec_tactic_fun(xlate_ident x,
			  CT_id_unit_list(fst, rest),
			  xlate_tactic tac)

and xlate_tactic =
 function
   | TacFun (largs, t) ->
       let fst, rest =  xlate_largs_to_id_unit largs in
       CT_tactic_fun (CT_id_unit_list(fst, rest), xlate_tactic t)
   | TacThen (t1,t2) -> 
       (match xlate_tactic t1 with
            CT_then(a,l) -> CT_then(a,l@[xlate_tactic t2])
	  | t -> CT_then (t,[xlate_tactic t2]))
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
   | TacDo(n, t) -> CT_do(CT_int n, xlate_tactic t)
   | TacTry t -> CT_try (xlate_tactic t)
   | TacRepeat t -> CT_repeat(xlate_tactic t)
   | TacAbstract(t,id_opt) -> 
       CT_abstract((match id_opt with
		       	None -> ctv_ID_OPT_NONE
		      | Some id -> ctf_ID_OPT_SOME (CT_ident (string_of_id id))),
		   xlate_tactic t)
   | TacProgress t -> CT_progress(xlate_tactic t)
   | TacOrelse(t1,t2) -> CT_orelse(xlate_tactic t1, xlate_tactic t2)
   | TacMatch (exp, rules) ->
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
   | TacMatchContext (_,[]) -> failwith ""
   | TacMatchContext (false,rule1::rules) ->
         CT_match_context(xlate_context_rule rule1,
                          List.map xlate_context_rule rules)
   | TacMatchContext (true,rule1::rules) ->
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
   | TacFail (n,"") -> CT_fail (CT_int n)
   | TacFail (n,s) -> xlate_error "TODO: Fail n message"
   | TacId "" -> CT_idtac
   | TacId _ -> xlate_error "TODO: Idtac with argument"
   | TacInfo t -> CT_info(xlate_tactic t)
   | TacArg a -> xlate_call_or_tacarg a

and xlate_tac =
  function
    | TacExtend (_,"Absurd",[c]) ->
       CT_absurd (xlate_formula (out_gen rawwit_constr c))
    | TacChange (None, f, b) -> CT_change (xlate_formula f, xlate_clause b)
    | TacChange (Some(l,c), f, b) -> 
	(* TODO LATER: combine with other constructions of pattern_occ *)
	CT_change_local(
	  CT_pattern_occ(CT_int_list(List.map (fun n -> CT_int n) l), 
			 xlate_formula c),
	  xlate_formula f,
	  xlate_clause b)
    | TacExtend (_,"Contradiction",[]) -> CT_contradiction
    | TacDoubleInduction (n1, n2) ->
	CT_tac_double (xlate_quantified_hypothesis n1, xlate_quantified_hypothesis n2)
    | TacExtend (_,"Discriminate", [idopt]) ->
     CT_discriminate_eq
         (xlate_quantified_hypothesis_opt
	    (out_gen (wit_opt rawwit_quant_hyp) idopt))
    | TacExtend (_,"DEq", [idopt]) ->
     CT_simplify_eq
         (xlate_ident_opt (out_gen (wit_opt rawwit_ident) idopt))
    | TacExtend (_,"Injection", [idopt]) ->
     CT_injection_eq
         (xlate_quantified_hypothesis_opt
	    (out_gen (wit_opt rawwit_quant_hyp) idopt))
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
    | TacIntroPattern [] -> CT_intros (CT_intro_patt_list [])
    | TacIntroPattern patt_list ->
	CT_intros (CT_intro_patt_list (List.map xlate_intro_pattern patt_list))
    | TacIntroMove (Some id, None) ->
     CT_intros (CT_intro_patt_list[CT_coerce_ID_to_INTRO_PATT(xlate_ident id)])
    | TacIntroMove (None, None) ->  CT_intro (CT_coerce_NONE_to_ID_OPT CT_none)
    | TacLeft bindl -> CT_left (xlate_bindings bindl)
    | TacRight bindl -> CT_right (xlate_bindings bindl)
    | TacSplit (false,bindl) -> CT_split (xlate_bindings bindl)
    | TacSplit (true,bindl) -> CT_exists (xlate_bindings bindl)
    | TacExtend (_,"Replace", [c1; c2]) ->
     let c1 = xlate_formula (out_gen rawwit_constr c1) in
     let c2 = xlate_formula (out_gen rawwit_constr c2) in
     CT_replace_with (c1, c2)
    |
      TacExtend (_,"Rewrite", [b; cbindl]) ->
     let b = out_gen Extraargs.rawwit_orient b in
     let (c,bindl) = out_gen rawwit_constr_with_bindings cbindl in
     let c = xlate_formula c and bindl = xlate_bindings bindl in
     if b then CT_rewrite_lr (c, bindl, ctv_ID_OPT_NONE)
     else CT_rewrite_rl (c, bindl, ctv_ID_OPT_NONE)
    | TacExtend (_,"RewriteIn", [b; cbindl; id]) ->
     let b = out_gen Extraargs.rawwit_orient b in
     let (c,bindl) = out_gen rawwit_constr_with_bindings cbindl in
     let c = xlate_formula c and bindl = xlate_bindings bindl in
     let id = ctf_ID_OPT_SOME (xlate_ident (out_gen rawwit_ident id)) in
     if b then CT_rewrite_lr (c, bindl, id)
     else CT_rewrite_rl (c, bindl, id)
    | TacExtend (_,"ConditionalRewrite", [t; b; cbindl]) ->
     let t = out_gen rawwit_tactic t in
     let b = out_gen Extraargs.rawwit_orient b in
     let (c,bindl) = out_gen rawwit_constr_with_bindings cbindl in
     let c = xlate_formula c and bindl = xlate_bindings bindl in
     if b then CT_condrewrite_lr (xlate_tactic t, c, bindl, ctv_ID_OPT_NONE)
     else CT_condrewrite_rl (xlate_tactic t, c, bindl, ctv_ID_OPT_NONE)
    | TacExtend (_,"ConditionalRewriteIn", [t; b; cbindl; id]) ->
     let t = out_gen rawwit_tactic t in
     let b = out_gen Extraargs.rawwit_orient b in
     let (c,bindl) = out_gen rawwit_constr_with_bindings cbindl in
     let c = xlate_formula c and bindl = xlate_bindings bindl in
     let id = ctf_ID_OPT_SOME (xlate_ident (out_gen rawwit_ident id)) in
     if b then CT_condrewrite_lr (xlate_tactic t, c, bindl, id)
     else CT_condrewrite_rl (xlate_tactic t, c, bindl, id)
    | TacExtend (_,"DependentRewrite", [b; id_or_constr]) ->
      let b = out_gen Extraargs.rawwit_orient b in
      (match genarg_tag id_or_constr with
	| IdentArgType -> (*Dependent Rewrite/SubstHypInConcl*)
	    let id = xlate_ident (out_gen rawwit_ident id_or_constr) in
	    if b then CT_deprewrite_lr id else CT_deprewrite_rl id
	| ConstrArgType -> (*CutRewrite/SubstConcl*)
	    let c = xlate_formula (out_gen rawwit_constr id_or_constr) in
	    if b then CT_cutrewrite_lr (c, ctv_ID_OPT_NONE)
	    else CT_cutrewrite_rl (c, ctv_ID_OPT_NONE)
	| _ -> xlate_error "")
    | TacExtend (_,"DependentRewrite", [b; c; id]) -> (*CutRewrite in/SubstHyp*)
      let b = out_gen Extraargs.rawwit_orient b in
      let c = xlate_formula (out_gen rawwit_constr c) in
      let id = xlate_ident (out_gen rawwit_ident id) in
      if b then CT_cutrewrite_lr (c, ctf_ID_OPT_SOME id)
      else CT_cutrewrite_lr (c, ctf_ID_OPT_SOME id)
    | TacReflexivity -> CT_reflexivity
    | TacSymmetry _ -> xlate_error "TODO: Symmetry <clause>"
    | TacTransitivity c -> CT_transitivity (xlate_formula c)
    | TacAssumption -> CT_assumption
    | TacExact c -> CT_exact (xlate_formula c)
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
    | TacAuto (nopt, Some []) -> CT_auto (xlate_int_opt nopt)
    | TacAuto (nopt, None) -> CT_auto_with (xlate_int_opt nopt, CT_star)
    | TacAuto (nopt, Some (id1::idl)) ->
	CT_auto_with(xlate_int_opt nopt,
             CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
             CT_id_ne_list(CT_ident id1, List.map (fun x -> CT_ident x) idl)))
    | TacExtend (_,"EAuto", [nopt; popt; idl]) ->
	let first_n =
	  match out_gen (wit_opt rawwit_int_or_var) nopt with
	    | Some (ArgVar(_, s)) -> xlate_id_to_id_or_int_opt s
	    | Some ArgArg n -> xlate_int_to_id_or_int_opt n
	    | None -> none_in_id_or_int_opt in
	let second_n =
	  match out_gen (wit_opt rawwit_int_or_var) popt with
	    | Some (ArgVar(_, s)) -> xlate_id_to_id_or_int_opt s
	    | Some ArgArg n -> xlate_int_to_id_or_int_opt n
	    | None -> none_in_id_or_int_opt in
	let idl = out_gen Eauto.rawwit_hintbases idl in
          (match idl with
	    None -> CT_eauto_with(first_n, second_n, CT_star)
	  | Some [] -> CT_eauto(first_n, second_n)
	  | Some (a::l) -> 
	      CT_eauto_with(first_n, second_n,
			    CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR
			      (CT_id_ne_list
				 (CT_ident a,
				  List.map (fun x -> CT_ident x) l))))
    | TacExtend (_,"Prolog", [cl; n]) ->
      let cl = List.map xlate_formula (out_gen (wit_list0 rawwit_constr) cl) in
      (match out_gen wit_int_or_var n with
	| ArgVar _ -> xlate_error ""
	| ArgArg n -> CT_prolog (CT_formula_list cl, CT_int  n))
    | TacExtend (_,"EApply", [cbindl]) ->
     let (c,bindl) = out_gen rawwit_constr_with_bindings cbindl in
     let c = xlate_formula c and bindl = xlate_bindings bindl in
     CT_eapply (c, bindl)
    | TacTrivial (Some []) -> CT_trivial
    | TacTrivial None -> CT_trivial_with(CT_star)
    | TacTrivial (Some (id1::idl)) ->
	 CT_trivial_with(CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
            (CT_id_ne_list(CT_ident id1,List.map (fun x -> CT_ident x) idl))))
    | TacReduce (red, l) ->
     CT_reduce (xlate_red_tactic red, xlate_clause l)
    | TacApply (c,bindl) ->
     CT_apply (xlate_formula c, xlate_bindings bindl)
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
    | TacSimpleInduction (h,_) -> CT_induction (xlate_quantified_hypothesis h)
    | TacSimpleDestruct h -> CT_destruct (xlate_quantified_hypothesis h)
    | TacCut c -> CT_cut (xlate_formula c)
    | TacLApply c -> CT_use (xlate_formula c)
    | TacDecompose ([],c) ->
	xlate_error "Decompose : empty list of identifiers?"
    | TacDecompose (id::l,c) ->
	let id' = tac_qualid_to_ct_ID id in
	let l' = List.map tac_qualid_to_ct_ID l in
        CT_decompose_list(CT_id_ne_list(id',l'),xlate_formula c)
    | TacDecomposeAnd c -> CT_decompose_record (xlate_formula c)
    | TacDecomposeOr c -> CT_decompose_sum(xlate_formula c)
    | TacClear [] ->
	xlate_error "Clear expects a non empty list of identifiers"
    | TacClear (id::idl) ->
       let idl' = List.map xlate_hyp idl in
       CT_clear (CT_id_ne_list (xlate_hyp id, idl'))
    | (*For translating tactics/Inv.v *)
      TacInversion (NonDepInversion (k,idl,[]),quant_hyp) ->
	CT_inversion(compute_INV_TYPE k, xlate_quantified_hypothesis quant_hyp,
	             CT_id_list (List.map xlate_hyp idl))
    | TacInversion (DepInversion (k,copt,[]),quant_hyp) ->
	let id = xlate_quantified_hypothesis quant_hyp in
	CT_depinversion (compute_INV_TYPE k, id, xlate_formula_opt copt)
    | TacInversion (InversionUsing (c,idlist), id) ->
	let id = xlate_quantified_hypothesis id in
	  CT_use_inversion (id, xlate_formula c,
	    CT_id_list (List.map xlate_hyp idlist))
    | TacInversion (NonDepInversion (k,idl,names),quant_hyp) ->
	xlate_error "TODO: Inversion with names"
    | TacInversion (DepInversion (k,copt,names),quant_hyp) ->
	xlate_error "TODO: Inversion with names"
    | TacExtend (_,"Omega", []) -> CT_omega
    | TacRename (id1, id2) -> CT_rename(xlate_hyp id1, xlate_hyp id2)
    | TacClearBody([]) -> assert false
    | TacClearBody(a::l) -> 
	CT_clear_body (CT_id_ne_list (xlate_hyp a, List.map xlate_hyp l))
    | TacDAuto (a, b) -> CT_dauto(xlate_int_opt a, xlate_int_opt b)
    | TacNewDestruct(a,b,(c,_)) ->
	CT_new_destruct
	  (xlate_int_or_constr a, xlate_using b, 
	   CT_id_list_list
	     (List.map (fun l -> CT_id_list(List.map xlate_newind_names l)) c))
    | TacNewInduction(a,b,(c,_)) ->
	CT_new_induction
	  (xlate_int_or_constr a, xlate_using b, 
	   CT_id_list_list
	     (List.map (fun l -> CT_id_list(List.map xlate_newind_names l)) c))
    | TacInstantiate (a, b, _) -> 
	xlate_error "TODO: Instantiate ... <clause>"

    | TacLetTac (id, c, cl) ->
        CT_lettac(xlate_ident id, xlate_formula c, 
		  (* TODO LATER: This should be shared with Unfold,
		     but the structures are different *)
		  xlate_clause cl)
    | TacForward (true, name, c) -> 
(* TODO LATER : avoid adding a location that will be ignored *)
               CT_pose(xlate_id_opt ((0,0), name), xlate_formula c)
    | TacForward (false, name, c) -> 
               CT_assert(xlate_id_opt ((0,0),name), xlate_formula c)
    | TacTrueCut (idopt, c) -> 
                             CT_truecut(xlate_ident_opt idopt, xlate_formula c)
    | TacAnyConstructor(Some tac) -> 
	CT_any_constructor
	(CT_coerce_TACTIC_COM_to_TACTIC_OPT(xlate_tactic tac))
    | TacAnyConstructor(None) -> 
	CT_any_constructor(CT_coerce_NONE_to_TACTIC_OPT CT_none)
    | TacExtend(_, "Ring", [arg]) -> 
	CT_ring
	  (CT_formula_list
	     (List.map xlate_formula
		(out_gen (wit_list0 rawwit_constr) arg)))
    | TacExtend (_,id, l) ->
     CT_user_tac (CT_ident id, CT_targ_list (List.map coerce_genarg_to_TARG l))
    | TacAlias _ -> xlate_error "TODO LATER: aliases"

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
  | IdentArgType ->
      let id = xlate_ident (out_gen rawwit_ident x) in
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
  | TacticArgType ->
      let t = xlate_tactic (out_gen rawwit_tactic x) in
      CT_coerce_TACTIC_COM_to_TARG t
  | CastedOpenConstrArgType -> 
      CT_coerce_SCOMMENT_CONTENT_to_TARG
      	(CT_coerce_FORMULA_to_SCOMMENT_CONTENT(xlate_formula
						 (out_gen
						    rawwit_casted_open_constr x)))
  | ConstrWithBindingsArgType -> xlate_error "TODO: constr with bindings"
  | BindingsArgType -> xlate_error "TODO: with bindings"
  | RedExprArgType -> xlate_error "TODO: red expr as generic argument"
  | List0ArgType l -> xlate_error "TODO: lists of generic arguments"
  | List1ArgType l -> xlate_error "TODO: non empty lists of generic arguments"
  | OptArgType x -> xlate_error "TODO: optional generic arguments"
  | PairArgType (u,v) -> xlate_error "TODO: pairs of generic arguments"
  | ExtraArgType s -> xlate_error "Cannot treat extra generic arguments"
and xlate_context_rule =
  function
    | Pat (hyps, concl_pat, tactic) ->
	CT_context_rule(
          CT_context_hyp_list (List.map xlate_match_context_hyps hyps),
	  xlate_context_pattern concl_pat, xlate_tactic tactic)
    | All te ->
	xlate_error "TODO: wildcard match_context_rule"
and formula_to_def_body =
  function
    | ConstrEval (red, f) ->
        CT_coerce_EVAL_CMD_to_DEF_BODY(
	CT_eval(CT_coerce_NONE_to_INT_OPT CT_none,
                xlate_red_tactic red, xlate_formula f))
    | ConstrContext _ -> xlate_error "TODO: Inst"
    | ConstrTypeOf _ -> xlate_error "TODO: Check"
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
  | IdentArgType ->
      let id = xlate_ident (out_gen rawwit_ident x) in
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
  | TacticArgType ->
      let t = xlate_tactic (out_gen rawwit_tactic x) in
      CT_coerce_TACTIC_OPT_to_VARG (CT_coerce_TACTIC_COM_to_TACTIC_OPT t)
  | CastedOpenConstrArgType -> xlate_error "TODO: open constr"
  | ConstrWithBindingsArgType -> xlate_error "TODO: constr with bindings"
  | BindingsArgType -> xlate_error "TODO: with bindings"
  | RedExprArgType -> xlate_error "TODO: red expr as generic argument"
  | List0ArgType l -> xlate_error "TODO: lists of generic arguments"
  | List1ArgType l -> xlate_error "TODO: non empty lists of generic arguments"
  | OptArgType x -> xlate_error "TODO: optional generic arguments"
  | PairArgType (u,v) -> xlate_error "TODO: pairs of generic arguments"
  | ExtraArgType s -> xlate_error "Cannot treat extra generic arguments"


let xlate_thm x = CT_thm (match x with
  | Theorem -> "Theorem"
  | Remark -> "Remark"
  | Lemma -> "Lemma"
  | Fact -> "Fact")


let xlate_defn x = CT_defn (match x with
 | Local -> "Local"
 | Global -> "Definition")

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
   if coe then xlate_error "TODO: coercions in constructors"
   else CT_constr (xlate_ident id, xlate_formula c) in
 CT_constr_list (List.map f l)

let build_record_field_list l =
 let build_record_field (coe,d) = match d with
  | AssumExpr ((_,id),c) ->
      if coe then CT_constr_coercion (xlate_ident id, xlate_formula c)
      else
	CT_coerce_CONSTR_to_RECCONSTR
	  (CT_constr (xlate_ident id, xlate_formula c))
  | DefExpr ((_,id),c,topt) ->
      xlate_error "TODO: manifest fields in Record" in
 CT_recconstr_list (List.map build_record_field l);;

let get_require_flags impexp spec =
 let ct_impexp =
  match impexp with
  | false -> CT_import
  | true -> CT_export in
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
  | ((_,id),c) ->
     CT_binder(CT_id_opt_ne_list (xlate_ident_opt (Some id),[]),xlate_formula c)

let cvt_vernac_binders args =
  CT_binder_list(List.map cvt_vernac_binder args)



let xlate_comment = function
    CommentConstr c -> CT_coerce_FORMULA_to_SCOMMENT_CONTENT(xlate_formula c)
  | CommentString s -> CT_coerce_ID_OR_STRING_to_SCOMMENT_CONTENT
      (CT_coerce_STRING_to_ID_OR_STRING(CT_string s))
  | CommentInt n ->
      CT_coerce_FORMULA_to_SCOMMENT_CONTENT(CT_int_encapsulator (string_of_int n));;

let xlate_vernac =
 function
   | VernacDeclareTacticDefinition (false,[(_,id),TacFun (largs,tac)]) ->
       let fst, rest = xlate_largs_to_id_unit largs in
       let extract = function CT_unit -> xlate_error "TODO: void parameter"
	 | CT_coerce_ID_to_ID_UNIT x -> x in
       let largs = List.map extract (fst::rest) in
       CT_tactic_definition(xlate_ident id,
                           (* TODO, replace CT_id_list by CT_id_unit_list *)
			    CT_id_list largs,
			    xlate_tactic tac)
   | VernacDeclareTacticDefinition 
       (true,((id,TacFun (largs,tac))::_ as the_list)) ->
       let x_rec_tacs =
	 List.map xlate_rec_tac the_list in
       let fst, others = match x_rec_tacs with
	   fst::others -> fst, others
	 | _ -> assert false in
       CT_rec_tactic_definition(CT_rec_tactic_fun_list(fst, others))
    | VernacDeclareTacticDefinition (false,[(_,id),tac]) ->
       CT_tactic_definition(xlate_ident id, CT_id_list[], xlate_tactic tac)
    | VernacDeclareTacticDefinition (loc,_) -> xlate_error "Shouldn't occur"
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
    | VernacChdir (Some str) -> CT_cd (ctf_STRING_OPT_SOME (CT_string str))
    | VernacChdir None -> CT_cd ctf_STRING_OPT_NONE
    | VernacAddLoadPath (false,str,None) -> CT_addpath (CT_string str)
    | VernacAddLoadPath (true,str,None) -> CT_recaddpath (CT_string str)
    | VernacAddLoadPath (_,str,Some x) ->
	xlate_error"TODO: Add (Rec) LoadPath as"
    | VernacRemoveLoadPath str -> CT_delpath (CT_string str)
    | VernacToplevelControl Quit -> CT_quit
    | VernacToplevelControl _ -> xlate_error "TODO?: Drop/ProtectedToplevel"
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
    | VernacSolve (n, tac, b) -> CT_solve (CT_int n, xlate_tactic tac)
    | VernacFocus nopt -> CT_focus (xlate_int_opt nopt)
    | VernacUnfocus -> CT_unfocus
  | VernacExtend ("HintRewrite", orient :: formula_list :: base :: t) ->
      let orient = out_gen Extraargs.rawwit_orient orient in
      let formula_list = out_gen (wit_list1 (rawwit_constr)) formula_list in
      let base = out_gen rawwit_pre_ident base in
      let t = match t with
	| [] -> TacId ""
	| [t] -> out_gen rawwit_tactic t
	| _ -> failwith "" in
      let ct_orient = match orient with
	| true  -> CT_lr
	| false -> CT_rl in
      let f_ne_list = match List.map xlate_formula formula_list with
	  (fst::rest) -> CT_formula_ne_list(fst,rest)
	| _ -> assert false in
      CT_hintrewrite(ct_orient, f_ne_list, CT_ident base, xlate_tactic t)
  | VernacHints (local,dbnames,h) ->
      (* TODO: locality flag *)
      let dblist = CT_id_list(List.map (fun x -> CT_ident x) dbnames) in
      (match h with
	| HintsResolve [Some id_name, c] -> (* = Old HintResolve *)
	    CT_hint(xlate_ident id_name, dblist, CT_resolve (xlate_formula c))
	| HintsImmediate [Some id_name, c] -> (* = Old HintImmediate *)
	    CT_hint(xlate_ident id_name, dblist, CT_immediate(xlate_formula c))
	| HintsUnfold [Some id_name, q] -> (* = Old HintUnfold *)
	    CT_hint(xlate_ident id_name, dblist,
              CT_unfold_hint (loc_qualid_to_ct_ID q))
	| HintsConstructors (Some id_name, ql) ->
	    CT_hint(xlate_ident id_name, dblist,
              CT_constructors (CT_id_list(List.map loc_qualid_to_ct_ID ql)))
	| HintsExtern (Some id_name, n, c, t) ->
	    CT_hint(xlate_ident id_name, dblist,
              CT_extern(CT_int n, xlate_formula c, xlate_tactic t))
        | HintsResolve l -> (* = Old HintsResolve *)
	 let l = List.map (function (None,CRef r) -> r | _ -> failwith "") l in
	 let n1, names = match List.map tac_qualid_to_ct_ID l with
	     n1 :: names -> n1, names
	   | _  -> failwith "" in
         CT_hints(CT_ident "Resolve",
                  CT_id_ne_list(n1, names),
		  dblist)
        | HintsImmediate l -> (* = Old HintsImmediate *)
	 let l = List.map (function (None,CRef r) -> r | _ -> failwith "") l in
	 let n1, names = match List.map tac_qualid_to_ct_ID l with
	     n1 :: names -> n1, names
	   | _  -> failwith "" in
        CT_hints(CT_ident "Immediate", 
                 CT_id_ne_list(n1, names),
                 dblist)
        | HintsUnfold l ->  (* = Old HintsUnfold *)
	 let l = List.map
	   (function
	       (None,ref) -> loc_qualid_to_ct_ID ref
	     | _ -> failwith "") l in
	 let n1, names = match l with
	     n1 :: names -> n1, names
	   | _  -> failwith "" in
        CT_hints(CT_ident "Unfold", 
                 CT_id_ne_list(n1, names),
                 dblist)
        | _ -> xlate_error"TODO: Hint")
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
  | VernacEndProof Admitted -> xlate_error "TODO: Admitted"
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
  | VernacShow (ShowIntros _|ShowGoalImplicitly _|ShowExistentials|ShowScript)
      -> xlate_error "TODO: Show Intro/Intros/Implicits/Existentials/Script"
  | VernacGo arg -> CT_go (xlate_locn arg)
  | VernacShow ExplainProof l ->
      CT_explain_proof (CT_int_list (List.map (fun x -> CT_int x) l))
  | VernacShow ExplainTree l ->
      CT_explain_prooftree (CT_int_list (List.map (fun x -> CT_int x) l))
  | VernacCheckGuard -> CT_guarded
  | VernacPrint p ->
      (match p with
	  PrintFullContext -> CT_print_all
	| PrintName id -> CT_print_id (loc_qualid_to_ct_ID id)
	| PrintOpaqueName id -> CT_print_opaqueid (loc_qualid_to_ct_ID id)
	| PrintSectionContext id -> CT_print_section (loc_qualid_to_ct_ID id)
	| PrintModules -> CT_print_modules
	| PrintGrammar (phylum, name) -> CT_print_grammar CT_grammar_none
	| PrintHintDb -> CT_print_hint (CT_coerce_NONE_to_ID_OPT CT_none)
	| PrintHintDbName id -> CT_print_hintdb (CT_ident id)
	| PrintHint id ->
	    CT_print_hint (CT_coerce_ID_to_ID_OPT (loc_qualid_to_ct_ID id))
	| PrintLoadPath -> CT_print_loadpath
	| PrintMLLoadPath -> CT_ml_print_path
	| PrintMLModules -> CT_ml_print_modules
	| PrintGraph -> CT_print_graph
	| PrintClasses -> CT_print_classes
	| PrintCoercions -> CT_print_coercions
	| PrintCoercionPaths (id1, id2) -> 
	    CT_print_path (xlate_class id1, xlate_class id2)
	| PrintInspect n -> CT_inspect (CT_int n)
	| PrintUniverses _ -> xlate_error "TODO: Dump Universes"
	| PrintHintGoal -> xlate_error "TODO: Print Hint"
	| PrintLocalContext -> xlate_error "TODO: Print"
	| PrintTables -> xlate_error "TODO: Print Tables"
        | PrintModuleType _ -> xlate_error "TODO: Print Module Type"
        | PrintModule _ -> xlate_error "TODO: Print Module"
        | PrintScopes -> xlate_error "TODO: Print Scopes"
        | PrintScope _ -> xlate_error "TODO: Print Scope"
	| PrintVisibility _ -> xlate_error "TODO: Print Visibility"
        | PrintAbout _ -> xlate_error "TODO: Print About"
	| _ -> xlate_error "TODO: Print")
  | VernacBeginSection (_,id) ->
      CT_coerce_SECTION_BEGIN_to_COMMAND (CT_section (xlate_ident id))
  | VernacEndSegment (_,id) -> CT_section_end (xlate_ident id)
  | VernacStartTheoremProof (k, (_,s), ([],c), _, _) ->
      CT_coerce_THEOREM_GOAL_to_COMMAND(
	CT_theorem_goal (CT_coerce_THM_to_DEFN_OR_THM (xlate_thm k), xlate_ident s,xlate_formula c))
  | VernacStartTheoremProof (k, s, (bl,c), _, _) -> 
      xlate_error "TODO: VernacStartTheoremProof"
  | VernacSuspend -> CT_suspend
  | VernacResume idopt -> CT_resume (xlate_ident_opt (option_app snd idopt))
  | VernacDefinition ((k,_),(_,s),ProveBody (bl,typ),_) ->
      if bl <> [] then xlate_error "TODO: Def bindings";
      CT_coerce_THEOREM_GOAL_to_COMMAND(
	CT_theorem_goal (CT_coerce_DEFN_to_DEFN_OR_THM (xlate_defn k), xlate_ident s,xlate_formula typ))
  | VernacDefinition ((kind,_),(_,s),DefineBody(bl,red_option,c,typ_opt),_) ->
      CT_definition
	(xlate_defn kind, xlate_ident s, xlate_binder_list bl,
	   cvt_optional_eval_for_definition c red_option,
           xlate_formula_opt typ_opt)
  | VernacAssumption (kind, b) ->
      let b = List.map snd b in (* TODO: handle possible coercions *)
      CT_variable (xlate_var kind, cvt_vernac_binders b)
  | VernacCheckMayEval (None, numopt, c) ->
      CT_check (xlate_formula c)
  | VernacSearch (s,x) ->
      (match s with
	| SearchPattern c ->
	    CT_search_pattern(xlate_formula c, xlate_search_restr x)
	| SearchHead id ->
	    CT_search(loc_qualid_to_ct_ID id, xlate_search_restr x)
	| SearchRewrite c -> xlate_error "TODO: SearchRewrite"
	| SearchAbout id -> xlate_error "TODO: SearchAbout")

  | (*Record from tactics/Record.v *)
    VernacRecord 
      (_, (add_coercion, (_,s)), binders, CSort (_,c1), rec_constructor_or_none, field_list) ->
      let record_constructor =
        xlate_ident_opt (option_app snd rec_constructor_or_none) in
      CT_record
       ((if add_coercion then CT_coercion_atm else
          CT_coerce_NONE_to_COERCION_OPT(CT_none)),
        xlate_ident s, xlate_binder_list binders, 
	xlate_sort c1, record_constructor,
         build_record_field_list field_list)

  |    VernacRecord _ -> xlate_error "TODO: Record in a defined sort"

(* TODO
     | (*Inversions from tactics/Inv.v *)
       "MakeSemiInversionLemmaFromHyp",
         ((Varg_int n) :: ((Varg_ident id1) :: ((Varg_ident id2) :: []))) ->
      CT_derive_inversion
       (CT_inv_regular, CT_coerce_INT_to_INT_OPT n, id1, id2)
     | "MakeInversionLemmaFromHyp",
         ((Varg_int n) :: ((Varg_ident id1) :: ((Varg_ident id2) :: []))) ->
      CT_derive_inversion
       (CT_inv_clear,
       CT_coerce_INT_to_INT_OPT n, id1, id2)
     | "MakeSemiInversionLemma",
         ((Varg_ident id) :: (c :: ((Varg_sorttype sort) :: []))) ->
      CT_derive_inversion_with
       (CT_inv_regular, id, coerce_iVARG_to_FORMULA c, sort)
     | "MakeInversionLemma",
         ((Varg_ident id) :: (c :: ((Varg_sorttype sort) :: []))) ->
      CT_derive_inversion_with
       (CT_inv_clear, id,
       coerce_iVARG_to_FORMULA c, sort)
     | "MakeDependentSemiInversionLemma",
         ((Varg_ident id) :: (c :: ((Varg_sorttype sort) :: []))) ->
      CT_derive_depinversion
       (CT_inv_regular, id, coerce_iVARG_to_FORMULA c, sort)
     | "MakeDependentInversionLemma",
         ((Varg_ident id) :: (c :: ((Varg_sorttype sort) :: []))) ->
      CT_derive_depinversion
       (CT_inv_clear, id, coerce_iVARG_to_FORMULA c, sort)
*)
   | VernacInductive (isind, lmi) ->
      let co_or_ind = if isind then "Inductive" else "CoInductive" in
      let strip_mutind ((_,s), notopt, parameters, c, constructors) =
        if notopt = None then
           CT_ind_spec
            (xlate_ident s, xlate_binder_list parameters, xlate_formula c,
             build_constructors constructors)
        else xlate_error "TODO: Notation in Inductive" in
        CT_mind_decl
	  (CT_co_ind co_or_ind, CT_ind_spec_list (List.map strip_mutind lmi))
   | VernacFixpoint [] -> xlate_error "mutual recursive"
   | VernacFixpoint (lm :: lmi) ->
      let strip_mutrec ((fid, n, arf, ardef), ntn) =
	(* TODO: handle ntn in mutual recursive *)
        let (bl,arf,ardef) = Ppconstr.split_fix (n+1) arf ardef in
        let arf = xlate_formula arf in
        let ardef = xlate_formula ardef in
	match cvt_fixpoint_binders bl with
	  | CT_binder_list (b :: bl) ->
	      CT_fix_rec (xlate_ident fid, CT_binder_ne_list (b, bl),
                arf, ardef)
          | _ -> xlate_error "mutual recursive" in
        CT_fix_decl
	  (CT_fix_rec_list (strip_mutrec lm, List.map strip_mutrec lmi))
   | VernacCoFixpoint [] -> xlate_error "mutual corecursive"
   | VernacCoFixpoint (lm :: lmi) ->
      let strip_mutcorec (fid, arf, ardef) =
	CT_cofix_rec (xlate_ident fid, xlate_formula arf, xlate_formula ardef) in
        CT_cofix_decl
	  (CT_cofix_rec_list (strip_mutcorec lm, List.map strip_mutcorec lmi))
   | VernacScheme [] -> xlate_error "induction scheme"
   | VernacScheme (lm :: lmi) ->
      let strip_ind ((_,id), depstr, inde, sort) =
           CT_scheme_spec
            (xlate_ident id, xlate_dep depstr, 
	    CT_coerce_ID_to_FORMULA (loc_qualid_to_ct_ID inde),
	     xlate_sort sort) in
        CT_ind_scheme
	  (CT_scheme_spec_list (strip_ind lm, List.map strip_ind lmi))
   | VernacSyntacticDefinition ((_,id), c, nopt) ->
         CT_syntax_macro (xlate_ident id, xlate_formula c, xlate_int_opt nopt)
   | VernacRequire (None, spec, lid) -> xlate_error "TODO: Read Module"
   | VernacRequire (Some impexp, spec, [id]) ->
      let ct_impexp, ct_spec = get_require_flags impexp spec in
      CT_require (ct_impexp, ct_spec, loc_qualid_to_ct_ID id,
        CT_coerce_NONE_to_STRING_OPT CT_none)
   | VernacRequire (_,_,([]|_::_::_)) ->
       xlate_error "TODO: general form of future Require"
   | VernacRequireFrom (Some impexp, spec, filename) ->
      let ct_impexp, ct_spec = get_require_flags impexp spec 
      and id = id_of_string (Filename.basename filename)
      in
      CT_require
       (ct_impexp, ct_spec, xlate_ident id, 
         CT_coerce_STRING_to_STRING_OPT (CT_string filename))
   | VernacRequireFrom (None, _, _) -> xlate_error "TODO: Read Module"

   | VernacSyntax (phylum, l) -> xlate_error "SYNTAX not implemented"
       (*Two versions of the syntax node with and without the binder list. *)
       (*Need to update the metal file and ascent.mli first! 
         	| ("SYNTAX", [Varg_ident phy; Varg_ident s; spatarg; unparg; blist]) ->
         	        (syntaxop phy s spatarg unparg blist)
         	| ("SYNTAX", [Varg_ident phy; Varg_ident s; spatarg; unparg]) ->
         	        (syntaxop phy s spatarg unparg 
         coerce_ID_OPT_to_FORMULA_OPT(CT_coerce_NONE_to_ID_OPT(CT_none)))*)
   | VernacOpenCloseScope sc -> xlate_error "TODO: open/close scope"

   | VernacArgumentsScope _ -> xlate_error "TODO: Arguments Scope"

   | VernacDelimiters _ -> xlate_error "TODO: Delimiters"

   | VernacBindScope _ -> xlate_error "TODO: Bind Scope"

   | VernacNotation _ -> xlate_error "TODO: Notation"

   | VernacSyntaxExtension _ -> xlate_error "Syntax Extension not implemented"

   | VernacInfix (false,(str,modl),id,_,None) ->
       (match Metasyntax.interp_infix_modifiers modl with
	 | (str_assoc,Some n,false,None) ->
      CT_infix (
       (match str_assoc with
        | Some Gramext.LeftA -> CT_lefta
        | Some Gramext.RightA -> CT_righta
        | Some Gramext.NonA -> CT_nona
        | None -> CT_coerce_NONE_to_ASSOC CT_none),
       CT_int n, CT_string str, loc_qualid_to_ct_ID id)
	 | _ -> xlate_error "TODO: handle onlyparse and format")
   | VernacInfix _ -> xlate_error "TODO: handle scopes and locality"
   | VernacGrammar _ -> xlate_error "GRAMMAR not implemented"
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
  | VernacDebug b -> xlate_error "TODO: Debug On/Off"

  | (VernacList _ | VernacV7only _ | VernacV8only _) ->
      xlate_error "Not treated here"
  | VernacNop -> CT_proof_no_op
  | VernacComments l -> 
      CT_scomments(CT_scomment_content_list (List.map xlate_comment l))
  | VernacDeclareImplicits(id, opt_positions) ->
      CT_implicits
	(reference_to_ct_ID id,
	 match opt_positions with
	     None -> CT_int_list[]
	   | Some l ->
	       CT_int_list
	       (List.map (function ExplByPos x -> CT_int x | ExplByName _ ->
		 xlate_error "TODO: explicit argument by name") l))
  | VernacReserve _ -> xlate_error "TODO: Default Variable Type"
  | VernacLocate(LocateTerm id) -> CT_locate(reference_to_ct_ID id)
  | VernacLocate(LocateLibrary id) -> CT_locate_lib(reference_to_ct_ID id)
  | VernacLocate(LocateFile s) -> CT_locate_file(CT_string s)
  | VernacLocate(LocateNotation _) -> xlate_error "TODO: Locate Notation"
  | VernacSetOption (Goptions.SecondaryTable ("Implicit", "Arguments"), BoolValue true)->CT_user_vernac (CT_ident "IMPLICIT_ARGS_ON", CT_varg_list[])
  | (VernacGlobalCheck _|VernacPrintOption _|
     VernacMemOption (_, _)|VernacRemoveOption (_, _)|VernacAddOption (_, _)|
     VernacSetOption (_, _)|VernacUnsetOption _|
     VernacBack _|VernacRestoreState _|
     VernacWriteState _|VernacSolveExistential (_, _)|VernacCanonical _|
     VernacImport (_, _)|VernacExactProof _|VernacDistfix _|
     VernacTacticGrammar _|VernacVar _|VernacTime _|VernacProof _)
    -> xlate_error "TODO: vernac"

  (* Modules and Module Types *)
  | VernacDeclareModule _ -> xlate_error "TODO: vernac"
  | VernacDefineModule _ -> xlate_error "TODO: vernac"
  | VernacDeclareModuleType _ -> xlate_error "TODO: vernac"

let rec xlate_vernac_list =
 function
   | VernacList (v::l) ->
       CT_command_list
         (xlate_vernac (snd v), List.map (fun (_,x) -> xlate_vernac x) l)
   | VernacV7only v -> 
       if !Options.v7 then xlate_vernac_list v
       else xlate_error "Unknown command"
   | VernacList [] -> xlate_error "xlate_command_list"
   | _ -> xlate_error "Not a list of commands";;
