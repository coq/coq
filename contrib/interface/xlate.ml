
(** Translation from coq abstract syntax trees to centaur vernac
   *)
open String;;
open Char;;
open Util;;
open Ast;;
open Names;;
open Ctast;;
open Ascent;;

let in_coq_ref = ref false;;

let xlate_mut_stuff = ref ((fun _ -> 
          Nvar((0,0), "function xlate_mut_stuff should not be used here")):
              Ctast.t -> Ctast.t);;

let set_xlate_mut_stuff v = xlate_mut_stuff := v;;

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

type astrecurse =   Rbinder of ct_ID_OPT * astrecurse
                  | Rform of ct_FORMULA
                  | Rform_list of ct_FORMULA list;;

let ctf_STRING_OPT_NONE = CT_coerce_NONE_to_STRING_OPT CT_none;;

let ctf_STRING_OPT_SOME s = CT_coerce_STRING_to_STRING_OPT s;;

let ctv_ID_OPT_NONE = CT_coerce_NONE_to_ID_OPT CT_none;;

let ctf_ID_OPT_SOME s = CT_coerce_ID_to_ID_OPT s;;

let ctv_ID_OPT_OR_ALL_NONE =
 CT_coerce_ID_OPT_to_ID_OPT_OR_ALL (CT_coerce_NONE_to_ID_OPT CT_none);;

let ctv_FORMULA_OPT_NONE =
  CT_coerce_ID_OPT_to_FORMULA_OPT(CT_coerce_NONE_to_ID_OPT CT_none);;

let ctf_ID_OPT_OR_ALL_SOME s =
 CT_coerce_ID_OPT_to_ID_OPT_OR_ALL (ctf_ID_OPT_SOME s);;

let ctv_ID_OPT_OR_ALL_ALL = CT_all;;

let ctv_SPEC_OPT_NONE = CT_coerce_NONE_to_SPEC_OPT CT_none;;

let ct_coerce_FORMULA_to_DEF_BODY x =
    CT_coerce_CONTEXT_PATTERN_to_DEF_BODY
    (CT_coerce_FORMULA_to_CONTEXT_PATTERN x);;

let castc x = CT_coerce_TYPED_FORMULA_to_FORMULA x;;

let varc x = CT_coerce_ID_to_FORMULA x;;

let ident_tac s = CT_user_tac (CT_ident s, CT_targ_list []);;

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

let coerce_iTARG_to_TARG =
 function
    | Targ_intropatt x -> xlate_error "coerce_iTARG_to_TARG (3)"
    | Targ_command x -> CT_coerce_FORMULA_to_TARG x
    | Targ_id_list x -> xlate_error "coerce_iTARG_to_TARG"
    | Targ_spec_list x -> CT_coerce_SPEC_LIST_to_TARG x
    | Targ_binding_com x -> CT_coerce_FORMULA_to_TARG x
    | Targ_ident x -> CT_coerce_ID_OR_INT_to_TARG (CT_coerce_ID_to_ID_OR_INT x)
    | Targ_int x -> CT_coerce_ID_OR_INT_to_TARG (CT_coerce_INT_to_ID_OR_INT x)
    | Targ_binding x -> CT_coerce_BINDING_to_TARG x
    | Targ_pattern x -> CT_coerce_PATTERN_to_TARG x
    | Targ_unfold_ne_list x -> CT_coerce_UNFOLD_NE_LIST_to_TARG x
    | Targ_unfold x -> CT_coerce_UNFOLD_to_TARG x
    | Targ_string x ->
     CT_coerce_ID_OR_STRING_to_TARG (CT_coerce_STRING_to_ID_OR_STRING x)
    | Targ_fixtac x -> CT_coerce_FIXTAC_to_TARG x
    | Targ_cofixtac x -> CT_coerce_COFIXTAC_to_TARG x
    | Targ_tacexp x -> CT_coerce_TACTIC_COM_to_TARG x
    | Targ_redexp x -> xlate_error "coerce_iTarg_to_TARG(2)";;

let rec coerce_iVARG_to_VARG =
 function
    | Varg_binder x -> CT_coerce_BINDER_to_VARG x
    | Varg_binderlist x -> CT_coerce_BINDER_LIST_to_VARG x
    | Varg_bindernelist x -> CT_coerce_BINDER_NE_LIST_to_VARG x
    | Varg_call (id, l) -> xlate_error "coerce_iVARG_to_VARG: CALL as varg"
    | Varg_constr x ->
     CT_coerce_FORMULA_OPT_to_VARG (CT_coerce_FORMULA_to_FORMULA_OPT x)
    | Varg_sorttype x ->
     CT_coerce_FORMULA_OPT_to_VARG
      (CT_coerce_FORMULA_to_FORMULA_OPT (CT_coerce_SORT_TYPE_to_FORMULA x))
    | Varg_constrlist x -> CT_coerce_FORMULA_LIST_to_VARG (CT_formula_list x)
    | Varg_ident x ->
     CT_coerce_ID_OPT_OR_ALL_to_VARG
      (CT_coerce_ID_OPT_to_ID_OPT_OR_ALL (CT_coerce_ID_to_ID_OPT x))
    | Varg_int x -> CT_coerce_INT_OPT_to_VARG (CT_coerce_INT_to_INT_OPT x)
    | Varg_intlist x -> CT_coerce_INT_LIST_to_VARG x
    | Varg_none -> CT_coerce_FORMULA_OPT_to_VARG ctv_FORMULA_OPT_NONE
    | Varg_string x ->
     CT_coerce_STRING_OPT_to_VARG (CT_coerce_STRING_to_STRING_OPT x)
    | Varg_tactic x -> 
	CT_coerce_TACTIC_OPT_to_VARG (CT_coerce_TACTIC_COM_to_TACTIC_OPT x)
    | Varg_astlist x -> CT_coerce_AST_LIST_to_VARG x
    | Varg_ast x -> CT_coerce_AST_to_VARG x
    | Varg_varglist x ->
     CT_coerce_VARG_LIST_to_VARG
      (CT_varg_list (List.map coerce_iVARG_to_VARG x))
    | _ -> xlate_error "coerce_iVARG_to_VARG: leftover case";;

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

let xlate_id =
 function
    | Nvar (_, id) ->
     (match id with
     | "_" -> xlate_error "xlate_id: '_' is ident option"
     | s -> CT_ident s)
    | Id (_, id) ->
     (match id with
     | "_" -> xlate_error "xlate_id: '_' is ident option"
     | s -> CT_ident s)
    | _ -> xlate_error "xlate_id: not an identifier";;

let xlate_id_unit = function
    Node(_, "VOID", []) -> CT_unit
  | x -> CT_coerce_ID_to_ID_UNIT (xlate_id x);;

let xlate_id_opt =
 function
    | Nvar (_, id) ->
     (match id with
     | "_" -> ctv_ID_OPT_NONE
     | s -> ctf_ID_OPT_SOME (CT_ident s))
    | _ -> xlate_error "xlate_id: not an identifier";;

let xlate_int =
 function
    | Num (_, n) -> CT_int n
    | _ -> xlate_error "xlate_int: not an int";;

let xlate_string =
 function
    | Str (_, s) -> CT_string s
    | _ -> xlate_error "xlate_string: not a string";;

(** Formulae
   *)
let strip_Rform =
 function
    | Rform body -> body
    | _ -> xlate_error "strip_Rform: binder expression as formula";;

let rec flatten_one_level = function
  [Node(_, _, l)] -> l
| Node(_, _, l)::tl -> List.append l (flatten_one_level tl)
| _ -> assert false;;

let make_lambdac dom boundcod =
 let rec gather =
  function
     | Rbinder (x, body) ->
      let l, body' = gather body in
      x::l, body'
     | Rform body -> [], body
     | _ -> xlate_error "make_lambdac : not Rbinder or Rform" in
 let varlist, cod = gather boundcod in
 match varlist with
  | [] -> xlate_error "make_lamdac: empty binder list"
  | id :: l -> CT_lambdac (CT_binder (CT_id_opt_ne_list (id, l), dom), cod);;

let rec make_prodc dom =
 let rec gather =
  function
     | Rbinder (id_opt, body) ->
      let l, body' = gather body in
      id_opt::l, body'
     | Rform body -> [], body
     | _ -> xlate_error "gather for make_prodc : not Rbinder or Rform" in
 function
     | Rform body -> xlate_error "make_prodc: empty binder list in make_binder"
     | boundrange ->
      let varlist, range = gather boundrange in
      (match varlist with
       | [] -> range
       | id :: l -> CT_prodc (CT_binder (CT_id_opt_ne_list (id, l), dom), range));;

let make_appln =
 function
    | [] -> xlate_error "make_appln: empty application list"
    | (Rform m) :: [] -> m
    | (Rform m) :: ((Rform n) :: l) ->
     CT_appc (m, CT_formula_ne_list (n, List.map strip_Rform l))
    | _ -> xlate_error "make_appln: binder expression in application";;

let make_casec casety =
 function
    | [] -> xlate_error "bad case expression"
    | x :: [] -> xlate_error "bad case expression"
    | (Rform a) :: ((Rform m) :: l) ->
     CT_elimc (CT_case casety, a, m, CT_formula_list (List.map strip_Rform l))
    | _ -> xlate_error "make_casec: binder expression as formula";;

let qualid_to_ct_ID =
  function
      Nvar(_, s) -> Some(CT_ident s)
    | Node(_, ("QUALID"|"QUALIDARG"|"QUALIDCONSTARG"), l) ->
	(* // to be modified when qualified identifiers are introducted. *)
	let rec f = 
	  function
	      [] -> xlate_error "empty list in qualified identifier"
	    | [Nvar(_,a)] -> a
	    | (Nvar(_,s))::l ->  s ^ "." ^ (f l)
	    | _ -> assert false in
	  Some(CT_ident (f l))
    | Node(_, "QUALIDMETA",[Num(_,n)]) -> Some(CT_metac (CT_int n))
    | _ -> None;;


let special_case_qualid cont_function astnode =
  match qualid_to_ct_ID astnode with
      Some(id) -> Some(Rform(CT_coerce_ID_to_FORMULA id))
    | None -> None;;

let xlate_op the_node opn a b =
 match opn with
 | "META" ->
  (match a, b with
  | ((Num (_, n)) :: []), [] -> CT_coerce_ID_to_FORMULA(CT_metac (CT_int n))
  | _, _ -> xlate_error "xlate_op : META ")
 | "ISEVAR" -> CT_existvarc
 | "FORCEIF" ->
   (match a,b with
     | [], l ->
      make_casec "Case" l
     | _,_ -> xlate_error "xlate_op : FORCEIF")	
 | "PROP" ->
  (match a, b with
  | [], [] ->
   CT_coerce_SORT_TYPE_to_FORMULA (CT_sortc "Prop")
  | _, _ -> xlate_error "xlate_op : PROP ")
 | "SET" ->
  (match a, b with
  | [], [] ->
   CT_coerce_SORT_TYPE_to_FORMULA (CT_sortc "Set")
  | _, _ -> xlate_error "xlate_op : PROP ")
 | (*The number of elements in the argument list is left unspecified: this list
     varies when the object is type-checked <Yves Bertot 21/3/95> *)
   "TYPE" ->
  (match a, b with
  | _, _ -> CT_coerce_SORT_TYPE_to_FORMULA (CT_sortc "Type"))
 | "CAST" ->
  (match a, b with
  | [], ((Rform c1) :: ((Rform c2) :: [])) -> castc (CT_typed_formula (c1, c2))
  | _, _ -> xlate_error "xlate_op : CAST ")
 | "PROD" ->
  (match a, b with
  | [],
      ((Rform c1) ::
        ((Rbinder ((CT_coerce_NONE_to_ID_OPT CT_none), (Rform c2))) :: [])) ->
   CT_arrowc (c1, c2)
  | [],
      ((Rform c1) :: ((Rbinder ((CT_coerce_ID_to_ID_OPT id), (Rform c2))) :: [])) ->
   CT_prodc
    (CT_binder (CT_id_opt_ne_list (CT_coerce_ID_to_ID_OPT id, []), c1), c2)
  | _, _ -> xlate_error "xlate_op : PROD")
 | "LAMBDA" ->
  (match a, b with
  | [], [Rform c1;Rbinder (b, (Rform c2))] ->
   CT_lambdac (CT_binder (CT_id_opt_ne_list (b, []), c1), c2)
  | _, _ -> xlate_error "xlate_op : LAMBDA")
 | "PRODLIST" ->
  (match a, b with
  | [], ((Rform c1) :: (c2 :: [])) -> make_prodc c1 c2
  | _, _ -> xlate_error "xlate_op : PRODLIST")
 | "LAMBDALIST" ->
  (match a, b with
  | [], ((Rform c1) :: (c2 :: [])) -> make_lambdac c1 c2
  | _, _ -> xlate_error "xlate_op : LAMBDALIST")
 | "APPLIST" ->
  (match a, b with
  | [], tl -> make_appln tl
  | _, _ -> xlate_error "xlate_op : APPLIST")
 | (** string_of_path needs to be investigated.
      *)
   "CONST" ->
  (match a, b with
  | ((Path (_, sl)) :: []), [] ->
    CT_coerce_ID_to_FORMULA(CT_ident
       (Names.string_of_id (Nameops.basename (section_path sl))))
  | ((Path (_, sl)) :: []), tl ->
 CT_coerce_ID_to_FORMULA(CT_ident   
       (Names.string_of_id(Nameops.basename (section_path sl))))
  | _, _ -> xlate_error "xlate_op : CONST")
 | (** string_of_path needs to be investigated.
    *)
 "MUTIND" ->
     (match a, b with
  	| [Path(_, sl); Num(_, tyi)], [] ->
	    if !in_coq_ref then
	      match special_case_qualid ()
		(!xlate_mut_stuff (Node((0,0),"MUTIND", a))) with
		    Some (Rform x) -> x
		  | _ -> assert false
	    else
	    CT_coerce_ID_to_FORMULA(
	      CT_ident(Names.string_of_id
			 (Nameops.basename (section_path sl))))
  	| _, _ -> xlate_error "xlate_op : MUTIND")
 | "CASE"
 | "MATCH" ->
     (let compute_flag s = 
       	match s with "CASE" -> "Case" | "MATCH" -> "Match" | _ -> assert false in
	match a, b with
          | [], tl -> make_casec (compute_flag opn) tl
      	  | [Str(_, "SYNTH")], tl ->
              make_casec (compute_flag opn) (Rform CT_existvarc::tl)
	| _, _ -> assert false)
 | (** string_of_path needs to be investigated.
      *)
   "MUTCONSTRUCT" ->
  (match a, b with
	  | [Path(_, sl);Num(_, tyi);Num(_, n)], cl ->
   if !in_coq_ref then
     match
       special_case_qualid ()
	 (!xlate_mut_stuff (Node((0,0),"MUTCONSTRUCT",a))) with
	 | Some(Rform x) -> x
	 | _ -> assert false
   else
   let name = Names.string_of_path (section_path sl) in
     (* This is rather a patch to cope with the fact that identifier
        names have disappeared from the vo files for grammar rules *)
       let type_desc = (try Some (Hashtbl.find type_table name) with
                          Not_found -> None) in
        (match type_desc with
           None -> 
	     xlate_error
	       ("MUTCONSTRUCT:" ^ 
                " can't describe a constructor without its name " ^
		name ^ "(" ^ (string_of_int tyi) ^ "," ^
	       (string_of_int n) ^ ")")
         | Some type_desc' -> 
              let type_desc'' = type_desc'.(tyi) in
              let ident = type_desc''.(n) in
              CT_coerce_ID_to_FORMULA(CT_ident ident))
  | _, _ -> xlate_error "xlate_op : MUTCONSTRUCT")
 |"EXPL" ->(match a, b with
  | [(Num (_, i))], ((Rform t)::[]) -> 
             CT_bang (CT_coerce_INT_to_INT_OPT (CT_int i), t)
  | _, _ -> xlate_error "xlate_op : EXPL ")
    
 | opn  -> xlate_error ("xlate_op : " ^ opn ^ " doesn't exist (" ^
			    (string_of_node_loc the_node) ^ ")");;

let split_params =
 let rec sprec acc =
  function
     | (Id _ as p) :: l -> sprec (p::acc) l
     | (Str _ as p) :: l -> sprec (p::acc) l
     | (Num _ as p) :: l -> sprec (p::acc) l
     | (Path _ as p) :: l -> sprec (p::acc) l
     | l -> List.rev acc, l in
 sprec [];;

let id_to_pattern_var ctid =
 match ctid with
 | CT_ident "_" -> 
     CT_coerce_ID_OPT_to_MATCH_PATTERN (CT_coerce_NONE_to_ID_OPT CT_none)
 | CT_ident id_string ->
     CT_coerce_ID_OPT_to_MATCH_PATTERN 
       (CT_coerce_ID_to_ID_OPT (CT_ident id_string))
 | _ -> assert false;;

let rec xlate_cases_pattern cont_function =
 function
   | Nvar(_, s) -> id_to_pattern_var (CT_ident s)
    | Node (_, "QUALID", l) as it ->
	(match qualid_to_ct_ID it with
	     Some x -> id_to_pattern_var x
	   | None -> assert false)
    | Node (_, "PATTCONSTRUCT", (f1 :: (arg1 :: args))) ->
     CT_pattern_app
      (xlate_cases_pattern cont_function f1,
      CT_match_pattern_ne_list
       (xlate_cases_pattern cont_function arg1, 
	List.map (xlate_cases_pattern cont_function) args))
    | Node (_, "PATTAS", [Nvar (_, id); pattern]) ->
     CT_pattern_as
      (xlate_cases_pattern
	 cont_function pattern, CT_coerce_ID_to_ID_OPT (CT_ident id))
    | Node (_, "PATTCONSTRUCT", [f]) ->	xlate_cases_pattern cont_function f
    | Node (_, ("MUTCONSTRUCT" as s), args) as it -> 
	let pl, tl = split_params args in
        (match xlate_op it s pl (List.map cont_function tl) with
	   | CT_coerce_ID_to_FORMULA id -> id_to_pattern_var id
	   | _ -> assert false)
    | Node(_, s, _) -> xlate_error ("error for a pattern " ^ s)
    | Path(_,sl) -> 
        id_to_pattern_var (CT_ident (List.fold_right
				       (fun a b ->
					  if b = "" then
					    a
					  else
					    a ^ "." ^ b) sl ""))
    | _ -> xlate_error "Unexpected data while translating a pattern";;

(*This function recognizes and translates let constructs
  // I think this code should be adapted to build a real let construct *)
let special_case_let_construct cont_function =
 function
    | Node (_, "LETIN", [val_arg;Slam(_, (Some b), body)]) ->
     Some
      (Rform
      (CT_letin(CT_ident b, strip_Rform (cont_function val_arg),
		strip_Rform (cont_function body))))
    | _ -> None;;

let cvt_binder cont_function =
 function 
    | Node (_,"BINDER", (c :: idl)) ->
        (match idl with
           | [] -> xlate_error "cvt_binder empty identifier list"
           | id :: l -> 
               CT_binder
                 (CT_id_opt_ne_list (xlate_id_opt id,
                              List.map xlate_id_opt l),
                        cont_function c))
    | _ -> failwith "cvt_binder";;

let cvt_binders cont_function =
  function
     | Node(_,name, args) when name = "BINDERLIST" or name = "BINDERS" ->
        CT_binder_list(List.map (cvt_binder cont_function) args)
     | _ -> failwith "cvt_binders";;


(*This function recognizes and translates the Fix construct *)
let special_case_fix cont_function =
 function
    | Node (_, "FIX", ((Nvar (_, iddef)) :: (l :: ldecl))) ->
     let xlate_fixbinder =
      function
         | Node (_, "NUMFDECL",
                   ((Nvar (_, fi)) ::
                     ((Num (_, ni)) :: (v_Type :: (v_Value :: []))))) ->
          let v_Type' = strip_Rform (cont_function v_Type) in
          let v_Value' = strip_Rform (cont_function v_Value) in
          CT_fix_binder (CT_ident fi, CT_int ni, v_Type', v_Value')
         | Node (_, "FDECL",
                   ((Nvar (_, fi)) ::
                     (binder :: (v_Type :: (v_Value :: []))))) ->
          let v_Type' = strip_Rform (cont_function v_Type) in
          let v_Value' = strip_Rform (cont_function v_Value) in
          (match cvt_binders (compose strip_Rform cont_function) binder with
            | CT_binder_list(a::tl) -> 
                   CT_coerce_FIX_REC_to_FIX_BINDER
                     (CT_fix_rec (CT_ident fi, CT_binder_ne_list(a,tl),
                              v_Type', v_Value'))
            | _ -> xlate_error ("special_case_fix : " ^
				"empty list of binders"))
         | _ ->
          xlate_error
           ("special_case_fix : " ^ "FIX, unexpected form in xlate_fixbinder")
     in
     Some
      (Rform
      (CT_fixc
      (CT_ident iddef,
      CT_fix_binder_list (xlate_fixbinder l, List.map xlate_fixbinder ldecl))))
    | _ -> None;;

(*This function recognizes and translates cofix constructs *)
let special_case_cofix cont_function =
 function
    | Node (_, "COFIX", ((Nvar (_, iddef)) :: (l :: ldecl))) ->
     let xlate_cofixbinder =
      function
         | Node (_, "CFDECL", ((Nvar (_, fi)) :: (v_Type :: (v_Value :: [])))) ->
          let v_Type' = strip_Rform (cont_function v_Type) in
          let v_Value' = strip_Rform (cont_function v_Value) in
          CT_cofix_rec (CT_ident fi, v_Type', v_Value')
         | _ ->
          xlate_error
           ("special_case_cofix : " ^
             "COFIX, unexpected form in xlate_fixbinder") in
     Some
      (Rform
      (CT_cofixc
      (CT_ident iddef,
      CT_cofix_rec_list (xlate_cofixbinder l, List.map xlate_cofixbinder ldecl))))
    | _ -> None;;



let rec list_last = function
  | [a] -> a
  | a::l -> list_last l
  | [] -> failwith "list_last called on an empty list";;

let rec slam_body = function
  | Slam(_, _, b) -> slam_body b
  | c -> c;;

let translate_one_equation cont_function = function
  | Node (_, "EQN", body::first_pattern::patterns) ->
      let translated_patterns = List.map 
				  (xlate_cases_pattern cont_function)
				  patterns in
	CT_eqn
	  (CT_match_pattern_ne_list
	     (xlate_cases_pattern
		cont_function first_pattern, translated_patterns),
	     strip_Rform (cont_function body))
       | _ ->
           xlate_error "Unexpected equation shape while translating a Cases"

(*this function recognizes and translates Cases constructs *)
let special_case_cases cont_function =
 function
   | Node(_, s,
	  type_returned::matched_arg::equations) when
       (s = "CASES") or (s = "FORCELET") or (s = "FORCEIF") ->
       let simple_type_returned =
	 match type_returned with
	   | (Str (_, "SYNTH")) -> ctv_FORMULA_OPT_NONE
	   | _ ->
	       CT_coerce_FORMULA_to_FORMULA_OPT
		 (strip_Rform (cont_function type_returned)) in
     let extract_equation = (function
       | Node(_, "EQN", l) as it -> it
       | _ -> xlate_error "equation is not an EQN") in
     let translated_equations =
       List.map 
         (fun x -> translate_one_equation cont_function (extract_equation x))
				  equations in
     let first_value, translated_matched_values =
      match matched_arg with
      | Node (_, "TOMATCH", matched_values) ->
       (match
        List.map (function x -> strip_Rform (cont_function x)) matched_values
        with
       | a :: b -> a, b
       | _ -> xlate_error "Empty list of match values while translating a Cases")
      | one_matched_value -> strip_Rform (cont_function one_matched_value), []
     in
     Some
      (Rform
      (CT_cases
      (simple_type_returned,
      CT_formula_ne_list (first_value, translated_matched_values),
      CT_eqn_list translated_equations)))
    | _ -> None;;

(*These functions are auxiliary to the function that translate annotated
  formulas for the natural language presentation of proofs *)
let xlate_ID =
 function
    | Node (_, "ident", ((Str (_, str)) :: [])) -> CT_ident str
    | Node (_, str, l) ->
     xlate_error ("xlate_ID:" ^ str ^ ":" ^ string_of_int (List.length l))
    | _ -> xlate_error "xlate_ID";;

let xlate_STRING =
 function
    | Str (_, str) -> CT_string str
    | Node (_, str, l) ->
     xlate_error ("xlate_STRING:" ^ str ^ ":" ^ string_of_int (List.length l))
    | _ -> xlate_error "xlate_STRING";;

let rec strip_bang cont_function =
 function
    | [] -> [], false
    | a :: tl ->
     (match a with
     | Node (_, "XTRA", ((Str (_, "!")) :: ((Num (_, n)) :: (f :: [])))) ->
      if in_coq () then
	strip_bang cont_function tl
      else 
	begin
          let l, b = strip_bang cont_function tl in
            strip_Rform (cont_function f)::l, b
      	end
     | Node (_, "EXPL", [Num(_, n); f]) ->
      let l, _ = strip_bang cont_function tl in
      strip_Rform (cont_function f)::l, true
     | _ ->
      let l, b = strip_bang cont_function tl in
      strip_Rform (cont_function a)::l, b);;

let special_case_bang cont_function =
 function
    | Node (_, "APPLISTEXPL", f::tl) ->
     let l, b = strip_bang cont_function tl in
     let compiled_f = strip_Rform (cont_function f) in
     let
     real_function =
      if in_coq () then
      (if b then CT_bang (CT_coerce_NONE_to_INT_OPT CT_none, compiled_f)
      else compiled_f)
      else CT_bang (CT_coerce_NONE_to_INT_OPT CT_none, compiled_f) in
     (match l with
      | [] -> xlate_error "special_case_bang: empty argument list?"
      | elnt :: l' ->
       Some (Rform (CT_appc (real_function, CT_formula_ne_list (elnt, l')))))
    | _ -> None;;

exception Not_natural;;

let rec nat_to_number =
 function
    | Node (_, "APPLIST", ((Nvar (_, "S")) :: (v :: []) as v0)) ->
     1 + nat_to_number v
    | Nvar (_, "O") -> 0
    | _ -> raise Not_natural;;

let g_nat_syntax_flag = ref false;;

let set_flags = ref (function () -> ());;

let special_case_S cont_function ast =
 if !g_nat_syntax_flag then (match ast with
 | Node (_, "APPLIST", ((Nvar (_, "S")) :: (v :: []))) as v0 -> begin
   try Some (Rform (CT_int_encapsulator (CT_int (nat_to_number v0))))
   with
   | Not_natural -> None
 end
 | Nvar (_, "O") -> Some (Rform (CT_int_encapsulator (CT_int 0)))
 | _ -> None)
 else None;;

let xlate_formula_special_cases =
 [special_case_qualid;
 special_case_let_construct;
 special_case_fix;
 special_case_cofix;
 special_case_cases;
 special_case_bang; special_case_S];;

let xlate_special_cases cont_function arg =
 let rec xlate_rec =
  function
     | f :: tl ->
      (match f cont_function arg with
      | Some _ as it -> it
      | None -> xlate_rec tl)
     | [] -> None in
 xlate_rec xlate_formula_special_cases;;

let xlate_formula a =
  !set_flags ();
  let rec ctrec =
    function
      | Nvar (_, id) -> Rform (varc (CT_ident id))
      | Slam (_, na, t) ->
	  let id =
       	    match na with
	      | None -> ctv_ID_OPT_NONE
	      | Some id -> if id = "_" then ctv_ID_OPT_NONE
         	else ctf_ID_OPT_SOME (CT_ident id) in
	  let body = ctrec t in
      	    Rbinder (id, body)
      | Node (_, opn, tl) as it ->
	  (match xlate_special_cases ctrec it with
	     | Some result -> result
	     | None ->
		 let pl, tl' = split_params tl in
		   Rform (xlate_op it opn pl (List.map ctrec tl')))
      | _ -> xlate_error "xlate_formula" in
 strip_Rform (ctrec a);;

let xlate_formula_opt =
 function
    | Node (_, "None", []) -> ctv_FORMULA_OPT_NONE
    | e -> CT_coerce_FORMULA_to_FORMULA_OPT (xlate_formula e);;

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

let filter_binding_or_command_list bl =
 match bl with
 | (Targ_binding_com cmd) :: bl' ->
  CT_coerce_FORMULA_LIST_to_SPEC_LIST
   (CT_formula_list (List.map strip_targ_command bl))
 | (Targ_binding b) :: bl' ->
  CT_coerce_BINDING_LIST_to_SPEC_LIST
   (CT_binding_list (List.map strip_targ_binding bl))
 | [] -> CT_coerce_FORMULA_LIST_to_SPEC_LIST (CT_formula_list [])
 | _ -> xlate_error "filter_binding_or_command_list";;

let strip_targ_spec_list =
 function
    | Targ_spec_list x -> x
    | _ -> xlate_error "strip_tar_spec_list";;

let strip_targ_intropatt =
 function
    | Targ_intropatt x -> x
    | _ -> xlate_error "strip_targ_intropatt";;


let rec get_flag_rec =
 function
    | n1 :: tail ->
     	let conv_id_fun = (fun x -> match qualid_to_ct_ID x with
                             Some y -> y
                             | None -> assert false) in
     let conv_flags, red_ids = get_flag_rec tail in
     (match n1 with
      | Node (_, "Beta", []) -> CT_beta::conv_flags, red_ids
      | Node (_, "Delta", []) -> CT_delta::conv_flags, red_ids
      | Node (_, "Iota", []) -> CT_iota::conv_flags, red_ids
      | Node (_, "Zeta", []) -> CT_zeta::conv_flags, red_ids
      | Node (_, "Evar", []) -> CT_evar::conv_flags, red_ids
      | Node (_, "Unf", l) ->
       (match red_ids with
       | CT_unf [] -> conv_flags, CT_unf (List.map conv_id_fun l)
       | _ -> error "Cannot specify identifiers to unfold twice")
      | Node (_, "UnfBut", l) ->
       (match red_ids with
       | CT_unf [] -> conv_flags, CT_unfbut (List.map conv_id_fun l)
       | _ -> error "Cannot specify identifiers to unfold twice")
      | Node (_, a, _) -> error ("get_flag_rec : unexpected flag " ^ a)
      | _ -> error "get_flag_rec : unexpected flag")
    | [] -> [], CT_unf [];;

let rec xlate_intro_pattern =
    function
    | Node(_,"CONJPATTERN", l) ->
        CT_conj_pattern(CT_intro_patt_list (List.map xlate_intro_pattern 
                                               (flatten_one_level l)))
    | Node(_, "DISJPATTERN", l) ->
        CT_disj_pattern(CT_intro_patt_list (List.map xlate_intro_pattern 
                                               (flatten_one_level l)))
    | Node(_, "IDENTIFIER",  [Nvar(_,c)]) ->
        CT_coerce_ID_to_INTRO_PATT(CT_ident c)
    | Node(_, a, _) -> failwith ("xlate_intro_pattern on node " ^ a)
    | _ -> failwith "xlate_intro_pattern";;

let compute_INV_TYPE_from_string = function
   "InversionClear" -> CT_inv_clear
 | "HalfInversion" -> CT_inv_simple
 | "Inversion" -> CT_inv_regular
 | _ -> failwith "unexpected Inversion type";;

let is_tactic_special_case = function
    "AutoRewrite" -> true
  | _ -> false;;

let tactic_special_case cont_function cvt_arg = function
    "AutoRewrite", (tac::v::bl) ->
      CT_autorewrite
	(CT_id_ne_list(xlate_id v, List.map xlate_id bl),
	   CT_coerce_TACTIC_COM_to_TACTIC_OPT(cont_function tac))
  | "AutoRewrite", (v::bl) ->
      CT_autorewrite
	(CT_id_ne_list(xlate_id v, List.map xlate_id bl),
	 CT_coerce_NONE_to_TACTIC_OPT CT_none)
  | _ -> assert false;;
	      
let xlate_context_pattern = function
    Node(_,"TERM", [Node(_, "COMMAND", [v])]) -> 
      CT_coerce_FORMULA_to_CONTEXT_PATTERN (xlate_formula v)
  | Node(_,"SUBTERM", [Node(_,"COMMAND",[v])]) ->
      CT_context(ctv_ID_OPT_NONE, xlate_formula v)
  | Node(_,"SUBTERM", [Nvar(_, s); Node(_, "COMMAND", [v])]) ->
      CT_context(ctf_ID_OPT_SOME (CT_ident s), xlate_formula v)
  | _ -> assert false;;

let xlate_match_context_hyps = function
    [b] -> CT_premise_pattern(ctv_ID_OPT_NONE, xlate_context_pattern b)
  | [Nvar(_,s);b] -> CT_premise_pattern(ctf_ID_OPT_SOME (CT_ident s),
					xlate_context_pattern b)
  | _ -> assert false;;


let xlate_largs_to_id_unit largs =
  match List.map xlate_id_unit largs with
      fst::rest -> fst, rest
    | _ -> assert false;;

let rec cvt_arg =
 function
    | Nvar (_, id) -> Targ_ident (CT_ident id)
    | Str (_, s) -> Targ_string (CT_string s)
    | Num (_, n) -> Targ_int (CT_int n)
    | Node (_, "LETPATTERNS", fst::l) ->
	let mk_unfold_occ = function
	    Node(_, "HYPPATTERN", Nvar(_, name)::ints) ->
	      CT_unfold_occ(
	        CT_int_list (List.map xlate_int ints), CT_ident name)
	  | Node(_, "CCLPATTERN", ints) ->
	      CT_unfold_occ(
	        CT_int_list (List.map xlate_int ints), CT_ident "Goal")
	  | _ -> xlate_error "unexpected argument in mk_unfold_occ" in
	Targ_unfold_ne_list(
	CT_unfold_ne_list(mk_unfold_occ fst, List.map mk_unfold_occ l))
    | Node (_, "COMMAND", (c :: [])) -> Targ_command (xlate_formula c)
    | Node (_, ("CASTEDCOMMAND"|"CASTEDOPENCOMMAND"), (c :: [])) -> Targ_command (xlate_formula c)
    | Node (_, "BINDINGS", bl) ->
     Targ_spec_list (filter_binding_or_command_list (List.map cvt_arg bl))
    | Node (_, "BINDING", ((Node (_, "COMMAND", (c :: []))) :: [])) ->
     Targ_binding_com (xlate_formula c)
    | Node (_, "BINDING",
              ((Num (_, n)) :: ((Node (_, "COMMAND", (c :: []))) :: []))) ->
     Targ_binding
      (CT_binding (CT_coerce_INT_to_ID_OR_INT (CT_int n), xlate_formula c))
    | Node (_, "BINDING",
              ((Nvar (_, id)) :: ((Node (_, "COMMAND", (c :: []))) :: []))) ->
     Targ_binding
      (CT_binding (CT_coerce_ID_to_ID_OR_INT (CT_ident id), xlate_formula c))
    | Node (_, "TACTIC", (t :: [])) -> Targ_tacexp (xlate_tactic t)
    | Node (_, "FIXEXP",
              ((Nvar (_, id)) ::
                ((Num (_, n)) :: ((Node (_, "COMMAND", (c :: []))) :: [])))) ->
     Targ_fixtac (CT_fixtac (CT_ident id, CT_int n, xlate_formula c))
    | Node (_, "COFIXEXP",
              ((Nvar (_, id)) :: ((Node (_, "COMMAND", (c :: []))) :: []))) ->
     Targ_cofixtac (CT_cofixtac (CT_ident id, xlate_formula c))
    | Node ((l1,l2), "CLAUSE", l) ->
 	Targ_id_list (CT_id_list 
			(List.map 
			   (function
			      | Node(_, "INHYP", [Nvar (_, x)]) -> CT_ident x
			      | Node(_, "INHYP", 
				     [Node(_, "COMMAND",
					     [Node(_, "META",
						   [Num (_, x)])])]) ->
				  CT_metac (CT_int x)
                              | _ ->
                                  xlate_error
                                    ("expected identifiers in a CLAUSE " ^
				     (string_of_int l1) ^ " " ^
				    (string_of_int l2))) l))
    | Node (_, "REDEXP", (tac :: [])) -> Targ_redexp (xlate_red_tactic tac)
    | Node (_, "INTROPATTERN", 
          [Node(_,"LISTPATTERN", l)]) -> 
              Targ_intropatt (CT_intro_patt_list(List.map xlate_intro_pattern l))
    | Node(_, "Str", [x]) -> cvt_arg x
    | Node ((l1,l2), a, _) -> failwith ("cvt_arg on node " ^ a ^ " at " ^
				       (string_of_int l1) ^ " " ^
				       (string_of_int l2))
    | _ -> failwith "cvt_arg"
and xlate_red_tactic =
 function
    | Node (loc, s, []) ->
     (match s with
     | "Red" -> CT_red
     | "Hnf" -> CT_hnf
     | "Simpl" -> CT_simpl
     | "Fold" -> CT_fold(CT_formula_list[])
     | _ -> xlate_error ("xlate_red_tactic, unexpected singleton " ^ s))
    | Node ((l1,l2), "Unfold", unf_list) ->
     let ct_unf_list = List.map (function
         | Node (_, "UNFOLD", qid::nums) ->
	     (match qualid_to_ct_ID qid with
		 Some x -> 
		   CT_unfold_occ (CT_int_list (List.map xlate_int nums), x)
	       	| _ -> failwith ("bad form in Unfold at characters " ^
                                 (string_of_int l1) ^ " " ^
				 (string_of_int l2))  )
         | n -> 
	     xlate_error ("xlate_red_tactic, expected unfold occurrence at " ^
			  (string_of_node_loc n)))
      unf_list in
     (match ct_unf_list with
      | first :: others -> CT_unfold (CT_unfold_ne_list (first, others))
      | [] -> error "there should be at least one thing to unfold")
    | Node (_, "Cbv", flag_list) ->
     let conv_flags, red_ids = get_flag_rec flag_list in
     CT_cbv (CT_conversion_flag_list conv_flags, red_ids)
    | Node (_, "Lazy", flag_list) ->
     let conv_flags, red_ids = get_flag_rec flag_list in
     CT_lazy (CT_conversion_flag_list conv_flags, red_ids)
    | Node (_, "Pattern", l) ->
     let pat_list = List.map (function
         | Node (_, "PATTERN", ((Node (_, "COMMAND", (c :: []))) :: nums)) ->
          CT_pattern_occ
           (CT_int_list (List.map xlate_int nums), xlate_formula c)
         | _ -> error "Expecting patterns in a Pattern command") l in
     (match pat_list with
      | first :: others -> CT_pattern (CT_pattern_ne_list (first, others))
      | [] -> error "Expecting at least one pattern in a Pattern command")
    | Node (_, "Fold", formula_list) ->
      CT_fold(CT_formula_list(List.map 
                    (function Node(_,"COMMAND", [c]) -> xlate_formula c
                           | _ -> error("xlate_red_tactic expected a COMMAND"))
                formula_list))
    | Node (_, a, _) -> error ("xlate_red_tactic: unexpected argument " ^ a)
    | _ -> error "xlate_red_tactic : unexpected argument"
and xlate_tactic =
 function
    | Node (_, s, l) ->
     (match s, l with
     | "FUN", [Node(_, "FUNVAR", largs); t] ->
	 let fst, rest =  xlate_largs_to_id_unit largs in
	 CT_tactic_fun
	   (CT_id_unit_list(fst, rest), xlate_tactic t)
     | "TACTICLIST", (t :: tl) ->
      (match List.map xlate_tactic (t::tl) with
      | [] -> xlate_error "xlate_tactic: internal xlate_error"
      | xt :: [] -> xt
      | CT_then(xt,xtl1) :: xtl -> CT_then (xt, xtl1@xtl)
      | xt :: xtl -> CT_then (xt, xtl))
     | "TACTICLIST", _ ->
      xlate_error "xlate_tactic: malformed tactic-expression TACTICLIST"
     | "TACLIST", (t :: tl) ->
      (match List.map xlate_tactic (t::tl) with
      | [] -> xlate_error "xlate_tactic: internal xlate_error"
      | xt :: [] -> xt
      | xt :: xtl -> CT_parallel (xt, xtl))
     | "FIRST", (a::l) ->
	 CT_first(xlate_tactic a,List.map xlate_tactic l)
     | "TCLSOLVE", (a::l) ->
         CT_tacsolve(xlate_tactic a, List.map xlate_tactic l)
     | "DO", ((Num (_, n)) :: (t :: [])) -> CT_do (CT_int n, xlate_tactic t)
     | "DO", _ -> xlate_error "xlate_tactic: malformed tactic-expression DO"
     | "TRY", (t :: []) -> CT_try (xlate_tactic t)
     | "TRY", _ -> xlate_error "xlate_tactic: malformed tactic-expression TRY"
     | "REPEAT", (t :: []) -> CT_repeat (xlate_tactic t)
     | "ABSTRACT", (Node(_,_,[t]) :: []) -> CT_abstract(ctv_ID_OPT_NONE, (xlate_tactic t))
     | "ABSTRACT", (Nvar(_, id)::(Node(_,"TACTIC",[t]) :: [])) -> 
             CT_abstract(ctf_ID_OPT_SOME (CT_ident id), (xlate_tactic t))
     | "INFO", (t :: []) -> CT_info (xlate_tactic t)
     | "REPEAT", _ ->
      xlate_error "xlate_tactic: malformed tactic-expression REPEAT"
     | "ORELSE", (t1 :: (t2 :: [])) ->
      CT_orelse (xlate_tactic t1, xlate_tactic t2)
     | "ORELSE", _ ->
      xlate_error "xlate_tactic: malformed tactic-expression ORELSE"
     | ((s, l) as it) when (is_tactic_special_case s) ->
	 tactic_special_case xlate_tactic cvt_arg it
     | "APP", (Nvar(_,s))::l ->
         let args = 
	   List.map (function 
                       | Node(_, "COMMAND", [x]) -> 
			   CT_coerce_FORMULA_to_TACTIC_ARG (xlate_formula x)
		       | x -> 
			   CT_coerce_TACTIC_COM_to_TACTIC_ARG(xlate_tactic x))
	     l in
         let fst,args2 = 
	   match args with
	       fst::args2 -> fst, args2
	     | _ -> assert false in
	 CT_simple_user_tac(CT_ident s, CT_tactic_arg_list(fst, args2))
     | "MATCH", exp::rules ->
        CT_match_tac(mk_let_value exp,
		     match List.map 
		       (function 
			  | Node(_,"MATCHRULE", 
				 [Node(_,"TERM", [Node(_,"COMMAND", [p])]);
				 tac]) ->
			      CT_match_tac_rule(
			      	CT_coerce_FORMULA_to_CONTEXT_PATTERN 
						  (xlate_formula p),
						  mk_let_value tac)
                          | Node(_,"MATCHRULE", [tac]) ->
			      CT_match_tac_rule
				(CT_coerce_FORMULA_to_CONTEXT_PATTERN
				   CT_existvarc, 
				   mk_let_value tac)
			  | Node((l1,l2),s,_) ->
                             failwith ("problem with match_tac at " ^
				      (string_of_int l1) ^
				      " " ^
				      (string_of_int l2) ^
				      ": " ^ s)
			  | _ -> assert false) rules with
			 | [] -> assert false
			 | fst::others ->
			     CT_match_tac_rules(fst, others))
     | "MATCHCONTEXT", rule1::rules ->
	 CT_match_context(xlate_context_rule rule1,
                          List.map xlate_context_rule rules)
     | "LET", [Node(_, "LETDECL",l);
               t] -> 
	 let cvt_clause =
	   function
	     | Node(_, "LETCLAUSE", [Nvar(_, s);Node(_,"COMMAND",[v])]) ->
		 CT_let_clause(CT_ident s,
			       CT_coerce_DEF_BODY_to_LET_VALUE
                               (formula_to_def_body v)) 
	     | Node(_, "LETCLAUSE", [Nvar(_, s); v]) ->
		 CT_let_clause(CT_ident s,
			       CT_coerce_TACTIC_COM_to_LET_VALUE
                               (xlate_tactic v)) 
	     | Node(_, s, _) -> failwith ("cvt_clause : unexpected " ^ s)
	     | _ -> assert false in
	 let cl_l = List.map cvt_clause l in
         (match cl_l with
	    | [] -> assert false 
	    | fst::others ->
	   	CT_lettac (CT_let_clauses(fst, others), mk_let_value t))
     | s, l -> xlate_tac (s, List.map cvt_arg l))
    | Nvar(_, s) -> ident_tac s
    | the_node -> xlate_error ("xlate_tactic at " ^
			       (string_of_node_loc the_node) )

and xlate_tac =
 function
    | "Absurd", ((Targ_command c) :: []) -> CT_absurd c
    | "Change", [Targ_command f; Targ_id_list b] -> CT_change(f,b)
    | "Contradiction", [] -> CT_contradiction
    | "DoubleInd", ((Targ_int n1) :: ((Targ_int n2) :: [])) ->
     CT_tac_double (n1, n2)
    | "Discr", [] -> CT_discriminate_eq ctv_ID_OPT_NONE
    | "DiscrHyp", ((Targ_ident id) :: []) ->
     CT_discriminate_eq (ctf_ID_OPT_SOME id)
    | "DEqConcl", [] -> CT_simplify_eq ctv_ID_OPT_NONE
    | "DEqHyp", ((Targ_ident id) :: []) -> CT_simplify_eq (ctf_ID_OPT_SOME id)
    | "Inj", [] -> CT_injection_eq ctv_ID_OPT_NONE
    | "InjHyp", ((Targ_ident id) :: []) -> CT_injection_eq (ctf_ID_OPT_SOME id)
    | "Fix", ((Targ_int n) :: []) ->
     CT_fixtactic (ctv_ID_OPT_NONE, n, CT_fix_tac_list [])
    | "Fix", ((Targ_ident id) :: ((Targ_int n) :: fixtac_list)) ->
     CT_fixtactic
      (ctf_ID_OPT_SOME id, n,
      CT_fix_tac_list (List.map strip_targ_fixtac fixtac_list))
    | "Cofix", [] -> CT_cofixtactic (ctv_ID_OPT_NONE, CT_cofix_tac_list [])
    | "Cofix", ((Targ_ident id) :: cofixtac_list) ->
     CT_cofixtactic
      (CT_coerce_ID_to_ID_OPT id,
      CT_cofix_tac_list (List.map strip_targ_cofixtac cofixtac_list))
    | "IntrosUntil", ((Targ_ident id) :: []) -> CT_intros_until id
    | "IntroMove", [Targ_ident id1;Targ_ident id2] ->
	CT_intro_after(CT_coerce_ID_to_ID_OPT id1, id2)
    | "IntroMove", [Targ_ident id2] ->
	CT_intro_after(CT_coerce_NONE_to_ID_OPT CT_none, id2)
    | "MoveDep", [Targ_ident id1;Targ_ident id2] ->
	CT_move_after(id1, id2)
    | "Intros", [] -> CT_intros (CT_intro_patt_list [])
    | "Intros", [patt_list] ->
     CT_intros (strip_targ_intropatt patt_list)
    | "Intro", [Targ_ident (CT_ident id)] ->
     CT_intros (CT_intro_patt_list [CT_coerce_ID_to_INTRO_PATT(CT_ident id)])
    | "Left", (bindl :: []) -> CT_left (strip_targ_spec_list bindl)
    | "Right", (bindl :: []) -> CT_right (strip_targ_spec_list bindl)
    | "Split", (bindl :: []) -> CT_split (strip_targ_spec_list bindl)
    | "Replace", ((Targ_command c1) :: ((Targ_command c2) :: [])) ->
     CT_replace_with (c1, c2)
    | (*Changes to Equality.v some more rewrite possibilities *)
      "RewriteLR", [(Targ_command c); bindl] ->
     CT_rewrite_lr (c, strip_targ_spec_list bindl, ctv_ID_OPT_NONE)
    | "RewriteLRin", ((Targ_ident id) :: ((Targ_command c) :: (bindl::[]))) ->
     CT_rewrite_lr (c, strip_targ_spec_list bindl, ctf_ID_OPT_SOME id)
    | "RewriteRL", [Targ_command c; bindl] ->
     CT_rewrite_rl (c, strip_targ_spec_list bindl, ctv_ID_OPT_NONE)
    | "RewriteRLin", [Targ_ident id; Targ_command c; bindl] ->
     CT_rewrite_rl (c, strip_targ_spec_list bindl, ctf_ID_OPT_SOME id)
    | "CondRewriteLR", [Targ_tacexp t; Targ_command c; bindl] ->
     CT_condrewrite_lr (t, c, strip_targ_spec_list bindl, ctv_ID_OPT_NONE)
    | "CondRewriteRL", [Targ_tacexp t; Targ_command c; bindl] ->
     CT_condrewrite_rl (t, c, strip_targ_spec_list bindl, ctv_ID_OPT_NONE)
    | "CondRewriteLRin",  [Targ_tacexp t; Targ_ident id; Targ_command c; bindl] ->
     CT_condrewrite_lr (t, c, strip_targ_spec_list bindl, ctf_ID_OPT_SOME id)
    | "CondRewriteRLin",  [Targ_tacexp t; Targ_ident id; Targ_command c; bindl] ->
     CT_condrewrite_rl (t, c, strip_targ_spec_list bindl, ctf_ID_OPT_SOME id)
    | "SubstConcl_LR", ((Targ_command c) :: []) ->
     CT_cutrewrite_lr (c, ctv_ID_OPT_NONE)
    | "SubstHyp_LR", ((Targ_command c) :: ((Targ_ident id) :: [])) ->
     CT_cutrewrite_lr (c, ctf_ID_OPT_SOME id)
    | "SubstConcl_RL", ((Targ_command c) :: []) ->
     CT_cutrewrite_rl (c, ctv_ID_OPT_NONE)
    | "SubstHyp_RL", ((Targ_command c) :: ((Targ_ident id) :: [])) ->
     CT_cutrewrite_rl (c, ctf_ID_OPT_SOME id)
    | "SubstHypInConcl_LR", ((Targ_ident id) :: []) -> CT_deprewrite_lr id
    | "SubstHypInConcl_RL", ((Targ_ident id) :: []) -> CT_deprewrite_rl id
    | "Reflexivity", [] -> CT_reflexivity
    | "Symmetry", [] -> CT_symmetry
    | "Transitivity", ((Targ_command c) :: []) -> CT_transitivity c
    | "Assumption", [] -> CT_assumption
    | "FAIL", [] -> CT_fail
    | "IDTAC", [] -> CT_idtac
    | "Exact", ((Targ_command c) :: []) -> CT_exact c
    | "DHyp", [Targ_ident id] -> CT_dhyp id
    | "CDHyp", [Targ_ident id] -> CT_cdhyp id
    | "DConcl", [] -> CT_dconcl
    | "SuperAuto", [a1;a2;a3;a4] ->
          CT_superauto(
             (match a1 with
              | Targ_int n -> (CT_coerce_INT_to_INT_OPT n)
              |  _ -> (CT_coerce_NONE_to_INT_OPT CT_none)),
             (match a2 with
              | Targ_id_list l -> l
              | _ -> xlate_error 
                     "SuperAuto expects a list of identifiers as second argument"),
             (match a3 with
              | Targ_string (CT_string "Destructing") -> CT_destructing
              | _ -> (CT_coerce_NONE_to_DESTRUCTING CT_none)),
             (match a4 with
              | Targ_string (CT_string "UsingTDB") -> CT_usingtdb
              | _ -> (CT_coerce_NONE_to_USINGTDB CT_none)))
             

    | "AutoTDB", [Targ_int n] -> CT_autotdb  (CT_coerce_INT_to_INT_OPT n)
    | "AutoTDB", [] -> CT_autotdb (CT_coerce_NONE_to_INT_OPT CT_none)
    | "Auto", ((Targ_int n) :: []) -> CT_auto (CT_coerce_INT_to_INT_OPT n)
    | "Auto", ((Targ_string (CT_string "*"))::[]) 
         -> CT_auto_with((CT_coerce_NONE_to_INT_OPT CT_none), CT_star)
    | "Auto", [] -> CT_auto (CT_coerce_NONE_to_INT_OPT CT_none)
    | "Auto", ((Targ_int n) :: ((Targ_ident id1) :: idl)) ->
                    CT_auto_with ((CT_coerce_INT_to_INT_OPT n),
                      CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
                       CT_id_ne_list(id1, List.map (function Targ_ident(x) -> x
                                                 | _ -> xlate_error
                                                       "Auto expects identifiers")
                                           idl)))
    | "Auto", ((Targ_ident id1) :: idl) ->
                    CT_auto_with ((CT_coerce_NONE_to_INT_OPT CT_none),
                      CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
                       CT_id_ne_list(id1, List.map (function Targ_ident(x) -> x
                                                 | _ -> xlate_error
                                                       "Auto expects identifiers")
                                           idl)))
    | "Auto", ((Targ_int n) :: ((Targ_string (CT_string "*")) :: [])) ->
          CT_auto_with ((CT_coerce_INT_to_INT_OPT n), CT_star)
    | "EAuto", ((Targ_int n) :: []) -> CT_eauto (CT_coerce_INT_to_INT_OPT n)
    | "EAuto", [] -> CT_eauto (CT_coerce_NONE_to_INT_OPT CT_none)
    | "EAuto", ((Targ_int n) :: ((Targ_ident id1) :: idl)) ->
                    CT_eauto_with ((CT_coerce_INT_to_INT_OPT n),
                      CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
                       CT_id_ne_list(id1, List.map (function Targ_ident(x) -> x
                                                 | _ -> xlate_error
                                                       "Auto expects identifiers")
                                           idl)))
    | "EAuto", ((Targ_ident id1) :: idl) ->
                    CT_eauto_with ((CT_coerce_NONE_to_INT_OPT CT_none),
                      CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
                       CT_id_ne_list(id1, List.map (function Targ_ident(x) -> x
                                                 | _ -> xlate_error
                                                       "Auto expects identifiers")
                                           idl)))
    | "EAuto", ((Targ_int n) :: ((Targ_string (CT_string "*")) :: [])) ->
          CT_eauto_with ((CT_coerce_INT_to_INT_OPT n), CT_star)
    | "EAuto", ((Targ_string (CT_string "*"))::[]) 
         -> CT_eauto_with((CT_coerce_NONE_to_INT_OPT CT_none), CT_star)
    | "Prolog", ((Targ_int n) :: idlist) ->
     (*according to coqdev the code is right, they want formula *)
     CT_prolog (CT_formula_list (List.map strip_targ_command idlist), n)
    | (**)
      "EApplyWithBindings", ((Targ_command c) :: (bindl :: [])) ->
     CT_eapply (c, strip_targ_spec_list bindl)
    | "Trivial", [] -> CT_trivial
    | "Trivial", ((Targ_string (CT_string "*"))::[]) ->
         CT_trivial_with(CT_star)
    | "Trivial", ((Targ_ident id1):: idl) ->
         CT_trivial_with(CT_coerce_ID_NE_LIST_to_ID_NE_LIST_OR_STAR(
               (CT_id_ne_list(id1,
                   List.map (function Targ_ident x -> x
                          | _ -> xlate_error "Trivial expects identifiers")
                   idl))))
    | "Reduce", ((Targ_redexp id) :: ((Targ_id_list l) :: [])) ->
     CT_reduce (id, l)
    | "Apply", ((Targ_command c) :: (bindl :: [])) ->
     CT_apply (c, strip_targ_spec_list bindl)
    | "Constructor", ((Targ_int n) :: (bindl :: [])) ->
     CT_constructor (n, strip_targ_spec_list bindl)
    | "Specialize",
        ((Targ_int n) :: ((Targ_command c) :: ((Targ_spec_list sl) :: []))) ->
     CT_specialize (CT_coerce_INT_to_INT_OPT n, c, sl)
    | "Specialize", ((Targ_command c) :: ((Targ_spec_list sl) :: [])) ->
     CT_specialize (CT_coerce_NONE_to_INT_OPT CT_none, c, sl)
    | "Generalize", (first :: cl) ->
     CT_generalize
      (CT_formula_ne_list
      (strip_targ_command first, List.map strip_targ_command cl))
    | "GeneralizeDep", [Targ_command c] ->
	CT_generalize_dependent c
    | "ElimType", ((Targ_command c) :: []) -> CT_elim_type c
    | "CaseType", ((Targ_command c) :: []) -> CT_case_type c
    | "Elim", ((Targ_command c1) :: ((Targ_spec_list sl) :: [])) ->
     CT_elim (c1, sl, CT_coerce_NONE_to_USING CT_none)
    | "Elim",
        ((Targ_command c1) ::
          ((Targ_spec_list sl) ::
            ((Targ_command c2) :: ((Targ_spec_list sl2) :: [])))) ->
     CT_elim (c1, sl, CT_using (c2, sl2))
    | "Case", ((Targ_command c1) :: ((Targ_spec_list sl) :: [])) ->
     CT_casetac (c1, sl)
    | "Induction", ((Targ_ident id) :: []) ->
     CT_induction (CT_coerce_ID_to_ID_OR_INT id)
    | "Induction", ((Targ_int n) :: []) ->
     CT_induction (CT_coerce_INT_to_ID_OR_INT n)
    | "Destruct", ((Targ_ident id) :: []) ->
     CT_destruct (CT_coerce_ID_to_ID_OR_INT id)
    | "Destruct", ((Targ_int n) :: []) ->
     CT_destruct (CT_coerce_INT_to_ID_OR_INT n)
    | "Cut", ((Targ_command c) :: []) -> CT_cut c
    | "CutAndApply", ((Targ_command c) :: []) -> CT_use c
    | "DecomposeThese", ((Targ_id_list l) :: ((Targ_command c) :: [])) ->
      (match l with
          CT_id_list (id :: l') -> 
                  CT_decompose_list(
                      CT_id_ne_list(id,l'),c)
        | _ -> xlate_error "DecomposeThese : empty list of identifiers?")
    | "Clear", [id_list] ->
     (match id_list with
        Targ_id_list(CT_id_list(id::idl)) ->
       CT_clear (CT_id_ne_list (id, idl))
      | _ -> xlate_error "Clear expects a non empty list of identifiers")
    | (*For translating tactics/Inv.v *)
      "Inv", [Targ_string (CT_string s); Targ_ident id] ->
     CT_inversion (compute_INV_TYPE_from_string s, id, CT_id_list [])
    | "InvIn", ((Targ_ident (CT_ident s))::((Targ_ident id) :: idlist)) ->
     CT_inversion
      (compute_INV_TYPE_from_string s, id,
      CT_id_list (List.map strip_targ_ident idlist))
    | "DInv", ((Targ_ident (CT_ident s))::((Targ_ident id) :: [])) ->
     CT_depinversion
      (compute_INV_TYPE_from_string s, id, ctv_FORMULA_OPT_NONE)
    | "DInvWith", ((Targ_ident (CT_ident s))::
                    ((Targ_ident id) :: ((Targ_command c) :: []))) ->
     CT_depinversion
      (compute_INV_TYPE_from_string s, id, CT_coerce_FORMULA_to_FORMULA_OPT c)
    | "UseInversionLemma", ((Targ_ident id) :: ((Targ_command c) :: [])) ->
     CT_use_inversion (id, c, CT_id_list [])
    | "UseInversionLemmaIn", ((Targ_ident id) :: ((Targ_command c) :: idlist)) ->
     CT_use_inversion (id, c, CT_id_list (List.map strip_targ_ident idlist))
    | "Omega", [] -> CT_omega
    | "APP", (Targ_ident id)::l ->
     CT_user_tac (id, CT_targ_list (List.map coerce_iTARG_to_TARG l))
    | s, l ->
     CT_user_tac (CT_ident s, CT_targ_list (List.map coerce_iTARG_to_TARG l))
and (xlate_context_rule: Ctast.t -> ct_CONTEXT_RULE) =
  function
    | Node(_, "MATCHCONTEXTRULE", parts) ->
	let rec xlate_ctxt_rule_aux = function
	    [concl_pat; tac] ->
	      [], xlate_context_pattern concl_pat, xlate_tactic tac
	  | Node(_,"MATCHCONTEXTHYPS", hyp_parts)::b ->
	      let hyps, cpat, tactic = xlate_ctxt_rule_aux b in
	      (xlate_match_context_hyps hyp_parts)::hyps, cpat, tactic
	  | _ -> assert false in
	let hyps, cpat, tactic = xlate_ctxt_rule_aux parts in
	  CT_context_rule(CT_context_hyp_list hyps, cpat, tactic)
    | _ -> assert false
and (formula_to_def_body : Ctast.t -> ct_DEF_BODY) =
  function
    | Node(_, "EVAL", [f;Node(_, "REDEXP", [tac])]) ->
	(try 
        CT_coerce_EVAL_CMD_to_DEF_BODY(
	CT_eval(CT_coerce_NONE_to_INT_OPT CT_none,
                xlate_red_tactic tac,
		xlate_formula f))
	with Failure s ->
	  failwith ("error raised inside formula_to_def_body " ^
		    s))
    | f -> (try ct_coerce_FORMULA_to_DEF_BODY(xlate_formula f)
            with Failure s -> 
	      match f with
		  Node(_,s1, _) ->
		    failwith ("error raised inside formula_to_def_body (2) " ^
			      s1 ^ " " ^ s)
		| _ ->
		    failwith("error raised inside formula_to_def_body (3) " ^
			     s))
and mk_let_value = function 
    Node(_, "COMMAND", [v]) -> 
      CT_coerce_DEF_BODY_to_LET_VALUE(formula_to_def_body v)
  | v -> CT_coerce_TACTIC_COM_to_LET_VALUE(xlate_tactic v);;

let strip_varg_int =
 function
    | Varg_int n -> n
    | _ -> xlate_error "strip vernac: non-integer argument";;

let strip_varg_string =
 function
    | Varg_string str -> str
    | _ -> xlate_error "strip vernac: non-string argument";;

let strip_varg_ident =
 function
    | Varg_ident id -> id
    | _ -> xlate_error "strip vernac: non-ident argument";;

let strip_varg_binder =
 function
    | Varg_binder n -> n
    | _ -> xlate_error "strip vernac: non-binder argument";;

let xlate_thm x = CT_thm (match x with
 | "THEOREM" -> "Theorem"
 | "REMARK" -> "Remark"
 | "LEMMA" -> "Lemma"
 | "FACT" -> "Fact"
 | _ -> xlate_error "xlate_thm");;

let xlate_defn x = CT_defn (match x with
 | "DEFINITION" -> "Definition"
 | "LOCAL" -> "Local"
 | "OBJECT" -> "@Definition"
 | "LOBJECT" -> "@Local"
 | "OBJCOERCION" -> "@Coercion"
 | "LOBJCOERCION" -> "LOBJCOERCION"
 | "SUBCLASS" -> "SubClass"
 | "LSUBCLASS" -> "LSUBCLASS"
 | "COERCION" -> "Coercion"
 | "LCOERCION" -> "LCOERCION"
 | _ -> xlate_error "xlate_defn");;

let xlate_defn_or_thm s =
 try CT_coerce_THM_to_DEFN_OR_THM (xlate_thm s)
 with
 | _ -> CT_coerce_DEFN_to_DEFN_OR_THM (xlate_defn s);;

let xlate_var x = CT_var (match x with
 | "HYPOTHESES" -> "Hypothesis"
 | "HYPOTHESIS" -> "Hypothesis"
 | "VARIABLE" -> "Variable"
 | "VARIABLES" -> "Variable"
 | "AXIOM" -> "Axiom"
 | "PARAMETER" -> "Parameter"
 | "PARAMETERS" -> "Parameter"
 | (*backwards compatible with 14a leave for now *)
   "Axiom" as s -> s
 | "Parameter" as s -> s
 | _ -> xlate_error "xlate_var");;

let xlate_dep =
 function
    | "DEP" -> CT_dep "Induction for"
    | "NODEP" -> CT_dep "Minimality for"
    | _ -> xlate_error "xlate_dep";;

let xlate_locn =
 function
    | Varg_int n -> CT_coerce_INT_to_INT_OR_LOCN n
    | Varg_string (CT_string "top") ->
     CT_coerce_LOCN_to_INT_OR_LOCN (CT_locn "top")
    | Varg_string (CT_string "prev") ->
     CT_coerce_LOCN_to_INT_OR_LOCN (CT_locn "prev")
    | Varg_string (CT_string "next") ->
     CT_coerce_LOCN_to_INT_OR_LOCN (CT_locn "next")
    | _ -> xlate_error "xlate_locn";;

let xlate_check =
 function
    | "CHECK" -> "Check"
    | "PRINTTYPE" -> "Type"
    | _ -> xlate_error "xlate_check";;

let build_constructors l =
 let strip_coerce =
  function
     | CT_coerce_ID_to_ID_OPT id -> id
     | _ -> xlate_error "build_constructors" in
 let rec rebind =
  function
     | [] -> []
     | (CT_binder ((CT_id_opt_ne_list (id, ids)), c)) :: l ->
      (List.map (function id_opt -> CT_constr (strip_coerce id_opt, c))
       (id::ids)) @ rebind l in
 CT_constr_list (rebind l);;

let build_record_field_list l =
 let build_record_field =
  function
     | Varg_varglist ((Varg_string (CT_string "")) ::((Varg_string assum) ::
                       ((Varg_ident id) :: (c :: [])))) ->
      CT_coerce_CONSTR_to_RECCONSTR (CT_constr (id, coerce_iVARG_to_FORMULA c))
     | Varg_varglist ((Varg_string (CT_string "COERCION")) 
                       ::((Varg_string assum) ::
                       ((Varg_ident id) :: (c :: [])))) ->
      CT_constr_coercion (id, coerce_iVARG_to_FORMULA c)
     | _ -> xlate_error "unexpected field in build_record_field_list" in
 CT_recconstr_list (List.map build_record_field l);;

let xlate_ast =
 let rec xlate_ast_aux =
  function
     | Node (_, s, tl) ->
      CT_astnode (CT_ident s, CT_ast_list (List.map xlate_ast_aux tl))
     | Nvar (_, s) ->
      CT_coerce_ID_OR_STRING_to_AST
       (CT_coerce_STRING_to_ID_OR_STRING (CT_string s))
     | Slam (_, (Some s), t) ->
      CT_astslam (CT_coerce_ID_to_ID_OPT (CT_ident s), xlate_ast_aux t)
     | Slam (_, None, t) -> CT_astslam (ctv_ID_OPT_NONE, xlate_ast_aux t)
     | Num (_, i) -> failwith "Numbers not treated in xlate_ast"
     | Id (_, s) ->
      CT_coerce_ID_OR_STRING_to_AST
       (CT_coerce_STRING_to_ID_OR_STRING (CT_string s))
     | Str (_, s) ->
      CT_coerce_ID_OR_STRING_to_AST
       (CT_coerce_STRING_to_ID_OR_STRING (CT_string s))
     | Dynamic(_,_) -> failwith "Dynamics not treated in xlate_ast"
     | Path (_, sl) ->
      CT_astpath
       (CT_id_list (List.map (function s -> CT_ident s) sl)) in
 xlate_ast_aux;;

let get_require_flags impexp spec =
 let ct_impexp =
  match impexp with
  | CT_string "IMPORT" -> CT_import
  | CT_string "EXPORT" -> CT_export
  | CT_string s -> xlate_error ("unexpected Require import flag " ^ s) in
 let ct_spec =
  match spec with
  | CT_string "UNSPECIFIED" -> ctv_SPEC_OPT_NONE
  | CT_string "SPECIFICATION" -> CT_spec
  | CT_string "IMPLEMENTATION" -> ctv_SPEC_OPT_NONE
  | CT_string s -> xlate_error ("unexpected Require specification flag " ^ s) in
 ct_impexp, ct_spec;;

let cvt_optional_eval_for_definition c1 optional_eval =
  match optional_eval with
    None -> ct_coerce_FORMULA_to_DEF_BODY c1
  | Some (Targ_redexp red_com) ->
      CT_coerce_EVAL_CMD_to_DEF_BODY(
      CT_eval(CT_coerce_NONE_to_INT_OPT CT_none,
	      red_com,
	      c1))
  | _ -> xlate_error 
	"bad extra argument (tactic?) for Definition";;

let rec cvt_varg =
 function
    | Node (_, "VERNACARGLIST", l) -> Varg_varglist (List.map cvt_varg l)
    | Node (_, "VERNACCALL", ((Str (_, na)) :: l)) ->
     Varg_call (CT_ident na, List.map cvt_varg l)
    | Node (_, "VERNACCALL", ((Id (_, na)) :: l)) ->
     Varg_call (CT_ident na, List.map cvt_varg l)
    | Node (_, ("QUALIDARG"|"QUALIDCONSTARG"), _) as it ->
	(match qualid_to_ct_ID it with
	     Some x -> Varg_ident x
	   | None -> assert false)
    | Nvar (_, id) -> Varg_ident (CT_ident id)
    | Str (_, s) -> Varg_string (CT_string s)
    | Num (_, n) -> Varg_int (CT_int n)
    | Node (_, "NONE", []) -> Varg_none
    | Node (_, "CONSTR", ((Node (_, "PROP", ((Id (_, c)) :: []))) :: [])) ->
     (match c with
     | "Pos" -> Varg_sorttype (CT_sortc "Set")
     | "Null" -> Varg_sorttype (CT_sortc "Prop")
     | _ -> xlate_error "cvt_varg : PROP : Failed match ")
    | Node (_, "CONSTR", ((Node (_, "PROP", [])) :: [])) ->
     Varg_sorttype (CT_sortc "Prop")
    | Node (_, "CONSTR", ((Node (_, "TYPE", _)) :: [])) ->
     Varg_sorttype (CT_sortc "Type")
    | Node (_, "CONSTR", [c]) -> Varg_constr (xlate_formula c)
    | Node (_, "CONSTRLIST", cs) -> Varg_constrlist (List.map xlate_formula cs)
    | Node (_, "TACTIC", [c]) -> Varg_tactic (xlate_tactic c)
    | Node (_, "BINDER", args) as arg ->
      Varg_binder(cvt_binder xlate_formula arg)
    | Node (_, "BINDERLIST", l) as arg ->
     Varg_binderlist(cvt_binders xlate_formula arg)
    | Node (_, "BINDERS", l) as arg ->
     Varg_binderlist(cvt_binders xlate_formula arg)
    | Node (_, "NUMBERLIST", ln) ->
     Varg_intlist (CT_int_list (List.map xlate_int ln))
    | Node (_, "AST", [Node(_, "ASTACT", [
                Node(_, "ASTLIST", [Node(_, "TACTICLIST", _) as it])])]) ->
         Varg_tactic(xlate_tactic it)
    | Node (_, "AST", (a :: [])) -> Varg_ast (xlate_ast a)
    | Node (_, "ASTLIST", al) ->
     Varg_astlist (CT_ast_list (List.map xlate_ast al))
    | Node (_, "TACTIC_ARG", (targ :: [])) -> Varg_tactic_arg (cvt_arg targ)
    | Node (_, s, _) as it -> failwith ("cvt_varg : " ^ s ^ " at location " ^
				       (string_of_node_loc it))
    | the_node -> failwith ("cvt_varg : " ^ (string_of_node_loc the_node))
and xlate_vernac =
 function
   | Node(_, "TACDEF", [Nvar(_,id);
			Node(_,"AST",
			     [Node(_,"FUN",
				   [Node(_,"FUNVAR",
					 largs);
				    tac])])]) ->
       CT_tactic_definition(CT_ident id,
			    CT_id_list(List.map xlate_id largs),
			    xlate_tactic tac)
   | Node(_, "TACDEF", Nvar(_, id)::
	    ((Node(_, "AST",[Node(_, "REC", [vc])])::tl) as the_list)) ->
       let x_rec_tacs =
	 List.fold_right
           (fun e res -> match e with
	      	Node(_,"AST",
		     [Node(_,"REC",
			   [Node(_,"RECCLAUSE", [Nvar(_,x); 
						 Node(_, "FUNVAR", argl);
						 tac])])]) ->
		  let fst, rest = xlate_largs_to_id_unit argl in
	 	  CT_rec_tactic_fun(CT_ident x,
				 CT_id_unit_list(fst, rest),
				 xlate_tactic tac)::res
	      | _ -> res) the_list [] in
       let fst, others = match x_rec_tacs with
	   fst::others -> fst, others
	 | _ -> assert false in
       CT_rec_tactic_definition(CT_rec_tactic_fun_list(fst, others))
   | Node(_, "TACDEF", [Nvar(_,id);Node(_,"AST",[tac])]) ->
       CT_tactic_definition(CT_ident id, CT_id_list[], xlate_tactic tac)
    | Node (_, s, l) ->
     (match s, List.map cvt_varg l with
     | "LoadFile", ((Varg_string verbose) :: ((Varg_string s) :: [])) ->
      CT_load (
       (match verbose with
        | CT_string "" -> CT_coerce_NONE_to_VERBOSE_OPT CT_none
        | CT_string "Verbose" as it -> CT_verbose
        | CT_string s ->
         xlate_error ("expecting the keyword Verbose only :" ^ s)),
       CT_coerce_STRING_to_ID_OR_STRING s)
     | "Eval",
         ((Varg_tactic_arg (Targ_redexp tac)) :: ((Varg_constr f) :: tail)) ->
      let numopt =
       match tail with
       | (Varg_int i) :: [] -> CT_coerce_INT_to_INT_OPT i
       | [] -> CT_coerce_NONE_to_INT_OPT CT_none
       | _ -> xlate_error "Eval expects an optional integer" in
      CT_coerce_EVAL_CMD_to_COMMAND(CT_eval (numopt, tac, f))
     | "PWD", [] -> CT_pwd
     | "CD", ((Varg_string str) :: []) -> CT_cd (ctf_STRING_OPT_SOME str)
     | "CD", [] -> CT_cd ctf_STRING_OPT_NONE
     | "ADDPATH", ((Varg_string str) :: []) -> CT_addpath str
     | "RECADDPATH", ((Varg_string str) :: []) -> CT_recaddpath str
     | "DELPATH", ((Varg_string str) :: []) -> CT_delpath str
     | "PrintPath", [] ->  CT_print_loadpath
     | "QUIT", [] -> CT_quit
     | (*ML commands *)
       "AddMLPath", ((Varg_string str) :: []) -> CT_ml_add_path str
     | "RecAddMLPath", ((Varg_string str) :: []) -> CT_rec_ml_add_path str
     | "PrintMLPath", [] -> CT_ml_print_path
     | "PrintMLModules", [] -> CT_ml_print_modules
     | "DeclareMLModule", (str :: l) ->
      CT_ml_declare_modules
       (CT_string_ne_list (strip_varg_string str, List.map strip_varg_string l))
     | "GOAL", [] -> CT_proof_no_op
     | "GOAL", (c :: []) -> CT_coerce_THEOREM_GOAL_to_COMMAND (CT_goal (coerce_iVARG_to_FORMULA c))
     | (*My attempt at getting all variants of Abort to use abort node *)
       "ABORT", ((Varg_ident id) :: []) -> CT_abort (ctf_ID_OPT_OR_ALL_SOME id)
     | "ABORT", [] -> CT_abort ctv_ID_OPT_OR_ALL_NONE
     | "ABORTALL", [] -> CT_abort ctv_ID_OPT_OR_ALL_ALL
     | (*formerly | ("ABORTALL", []) -> ident_vernac "Abort All" *)
       "RESTART", [] -> CT_restart
     | "PROOF", (c :: []) -> CT_proof (coerce_iVARG_to_FORMULA c)
     | "SOLVE", ((Varg_int n) :: ((Varg_tactic tcom) :: [])) ->
       CT_solve (n, tcom)
     | "FOCUS", [] -> CT_focus (CT_coerce_NONE_to_INT_OPT CT_none)
     | "FOCUS", [Varg_int n] -> CT_focus (CT_coerce_INT_to_INT_OPT n)
     | "UNFOCUS", [] -> CT_unfocus
     | "HintRewrite", [orient; formula_list; Varg_ident base; Varg_tactic t] ->
          let ct_orient = match orient with
	    | Varg_string (CT_string "LR") -> CT_lr
	    | Varg_string (CT_string "Rl") -> CT_rl
	    | _ -> assert false in
	  let f_ne_list = match formula_list with
	      Varg_constrlist (fst::rest) -> CT_formula_ne_list(fst,rest)
	    | _ -> assert false in
          CT_hintrewrite(ct_orient, f_ne_list, base, t)
     | "HintResolve", 
          ((Varg_ident id_name) ::
           ((Varg_varglist dbnames) :: ((Varg_constr c)::[]))) ->
      CT_hint(id_name,
              CT_id_list(List.map coerce_iVARG_to_ID
                              dbnames), CT_resolve(c))
     | "HintUnfold",
          ((Varg_ident id_name) ::
           ((Varg_varglist dbnames) :: ((Varg_ident c)::[]))) ->
      CT_hint(id_name,
              CT_id_list(List.map coerce_iVARG_to_ID
                              dbnames), CT_unfold_hint(c))
     | "HintConstructors",
          ((Varg_ident id_name) ::
           ((Varg_varglist dbnames) :: ((Varg_ident c)::[]))) ->
      CT_hint(id_name,
              CT_id_list(List.map coerce_iVARG_to_ID
                              dbnames), CT_constructors(c))
     | "HintImmediate",
          ((Varg_ident id_name) ::
           ((Varg_varglist dbnames) :: ((Varg_constr c)::[]))) ->
      CT_hint(id_name,
              CT_id_list(List.map coerce_iVARG_to_ID
                              dbnames), CT_immediate(c))
     | "HintExtern",
         [Varg_ident id_name;
          Varg_varglist dbnames;
          Varg_int n;
          Varg_constr c;
          Varg_tactic t] ->
       CT_hint(id_name, CT_id_list (List.map coerce_iVARG_to_ID dbnames),
               CT_extern(n, c, t))
     | "HintsResolve",
          (Varg_varglist(dbnames)::(Varg_ident n1) :: names) ->
        CT_hints(CT_ident "Resolve", 
                 CT_id_ne_list(n1, List.map coerce_iVARG_to_ID names),
                 CT_id_list(List.map coerce_iVARG_to_ID dbnames))
     | "HintsImmediate", 
          (Varg_varglist(dbnames)::(Varg_ident n1) :: names) ->
        CT_hints(CT_ident "Immediate", 
                 CT_id_ne_list(n1, List.map coerce_iVARG_to_ID names),
                 CT_id_list(List.map coerce_iVARG_to_ID dbnames))
     | "HintsUnfold",
          (Varg_varglist(dbnames)::(Varg_ident n1) :: names) ->
        CT_hints(CT_ident "Unfold", 
                 CT_id_ne_list(n1, List.map coerce_iVARG_to_ID names),
                 CT_id_list(List.map coerce_iVARG_to_ID dbnames))
     | "BY", ((Varg_tactic tcom) :: []) -> xlate_error "BY not implemented"
     | (*My attempt to get all variants of Save to use the same node *)
       "SaveNamed", [] ->
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm "Theorem"), ctv_ID_OPT_NONE)
     | "DefinedNamed", [] ->
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm "Definition"), ctv_ID_OPT_NONE)
     | "SaveAnonymous", [Varg_string (CT_string kind); Varg_ident s] ->
	let kind_string = 
	  match kind with
	      "THEOREM" -> "Theorem"
	    | "LEMMA" -> "Lemma"
	    | "FACT" -> "Fact"
	    | "REMARK" -> "Remark"
	    | "DECL" -> "Decl"
	    | _ -> assert false in
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm kind_string), ctf_ID_OPT_SOME s)
     | "SaveAnonymous", [Varg_ident s] ->
      CT_save (CT_coerce_THM_to_THM_OPT (CT_thm "Theorem"), ctf_ID_OPT_SOME s)
     | "TRANSPARENT", (id :: idl) ->
            CT_transparent(CT_id_ne_list(strip_varg_ident id,
                   List.map strip_varg_ident idl))
     | "OPAQUE",  (id :: idl)
            -> CT_opaque (CT_id_ne_list(strip_varg_ident id,
                   List.map strip_varg_ident idl))
     | "WriteModule", ((Varg_ident id) :: []) ->
      CT_write_module (id, CT_coerce_NONE_to_STRING_OPT CT_none)
     | "UNDO", ((Varg_int n) :: []) -> CT_undo (CT_coerce_INT_to_INT_OPT n)
     | "SHOW", [] -> CT_show_goal (CT_coerce_NONE_to_INT_OPT CT_none)
     | "SHOW", ((Varg_int n) :: []) -> CT_show_goal (CT_coerce_INT_to_INT_OPT n)
     | "ShowNode", [] -> CT_show_node
     | "ShowProof", [] -> CT_show_proof
     | "ShowTree", [] -> CT_show_tree
     | "ShowScript", [] -> CT_show_script
     | "ShowProofs", [] -> CT_show_proofs
     | "SHOWIMPL", [] -> CT_show_implicits
     | "Go", (arg :: []) -> CT_go (xlate_locn arg)
     | "ExplainProof", l ->
      CT_explain_proof (CT_int_list (List.map strip_varg_int l))
     | "ExplainProofTree", l ->
      CT_explain_prooftree (CT_int_list (List.map strip_varg_int l))
     | "PrintHint", [] -> CT_print_hint (CT_coerce_NONE_to_ID_OPT CT_none)
     | "PrintHintDb", [Varg_ident id] -> CT_print_hintdb id
     | "CheckGuard", [] -> CT_guarded
     | "PrintHintId", ((Varg_ident id) :: []) -> 
                      CT_print_hint (CT_coerce_ID_to_ID_OPT id)
     | "PrintAll", [] -> CT_print_all
     | "PrintId", ((Varg_ident id) :: []) -> CT_print_id id
     | "PrintOpaqueId", ((Varg_ident id) :: []) -> CT_print_opaqueid id
     | "PrintSec", ((Varg_ident id) :: []) -> CT_print_section id
     | "PrintStates", [] -> CT_print_states
     | "PrintModules", [] -> CT_print_modules
     | "PrintGrammar", ((Varg_ident phylum) :: ((Varg_ident name) :: [])) ->
      CT_print_grammar CT_grammar_none
     | "BeginModule", ((Varg_ident id) :: []) -> CT_module id
     | "BeginSection", ((Varg_ident id) :: []) ->
      CT_coerce_SECTION_BEGIN_to_COMMAND (CT_section id)
     | "EndSection", ((Varg_ident id) :: []) -> CT_section_end id
     | "StartProof",
         ((Varg_string (CT_string kind)) :: ((Varg_ident s) :: (c :: []))) ->
      CT_coerce_THEOREM_GOAL_to_COMMAND(
	CT_theorem_goal (xlate_defn_or_thm kind, s, coerce_iVARG_to_FORMULA c))
     | (*My attempt: suspend and resume as separate nodes *)
       "SUSPEND", [] -> CT_suspend
     | "RESUME", ((Varg_ident id) :: []) -> CT_resume (ctf_ID_OPT_SOME id)
     | "RESUME", [] -> CT_resume ctv_ID_OPT_NONE
     | (*formerly |  ("SUSPEND", []) -> suspend(CT_true)
         	            |  ("RESUME", []) -> suspend(CT_false)
          *)
       "DEFINITION",
       (* reference : toplevel/vernacentries.ml *)
         (Varg_string (CT_string kind):: Varg_ident s :: Varg_constr c :: rest) ->
         let typ_opt, red_option = match rest with
	   | [] -> ctv_FORMULA_OPT_NONE, None
	   | [Varg_constr b] -> CT_coerce_FORMULA_to_FORMULA_OPT b, None
	   | [Varg_tactic_arg r] -> ctv_FORMULA_OPT_NONE, Some r
	   | [Varg_constr b; Varg_tactic_arg r] ->
	       CT_coerce_FORMULA_to_FORMULA_OPT b, Some r
	   | [Varg_sorttype b] -> 
               CT_coerce_FORMULA_to_FORMULA_OPT 
                    (CT_coerce_SORT_TYPE_to_FORMULA b), None
	   | _ -> assert false in
         CT_definition
	   (xlate_defn kind, s, 
	    cvt_optional_eval_for_definition c red_option, typ_opt)
     | "VARIABLE",
         ((Varg_string (CT_string kind)) :: ((Varg_binderlist b) :: [])) ->
      CT_variable (xlate_var kind, b)
     | "PARAMETER",
         ((Varg_string (CT_string kind)) :: ((Varg_binderlist b) :: [])) ->
      CT_variable (xlate_var kind, b)
     | "Check", ((Varg_string (CT_string kind)) :: (c :: [])) ->
      CT_check (coerce_iVARG_to_FORMULA c)
     | "SearchPattern",Varg_constr c::l ->
          (match l with
	     | [] -> CT_search_pattern(c, 
                            CT_coerce_NONE_to_IN_OR_OUT_MODULES CT_none)
	     | (Varg_string (CT_string x))::(Varg_ident m1)::l1 ->
		 let l2 = CT_id_ne_list(m1, List.map coerce_iVARG_to_ID l1) in
                 let modifier = 
		   (match x with
		      | "inside" -> CT_in_modules l2
		      | "outside" -> CT_out_modules l2
		      | _ -> xlate_error "bad extra argument for Search") in
		   CT_search_pattern(c, modifier)
	     | _ -> xlate_error "bad argument list for SearchPattern")

     | "SEARCH", (Varg_ident id):: l -> 
          (match l with
	     | [] -> CT_search(id, CT_coerce_NONE_to_IN_OR_OUT_MODULES CT_none)
	     | (Varg_string (CT_string x))::(Varg_ident m1)::l1 ->
		 let l2 = CT_id_ne_list(m1, List.map coerce_iVARG_to_ID l1) in
                 let modifier = 
		   (match x with
		      | "inside" -> CT_in_modules l2
		      | "outside" -> CT_out_modules l2
		      | _ -> xlate_error "bad extra argument for Search") in
		   CT_search(id, modifier)
	     | _ -> xlate_error "bad argument list for Search")
     | "INSPECT", ((Varg_int n) :: []) -> CT_inspect n
     | (*Record from tactics/Record.v *)
       "RECORD",
         ((Varg_string coercion_or_not) :: ((Varg_ident s) ::
           ((Varg_binderlist binders) ::
             (c1 ::
               ((Varg_varglist rec_constructor_or_none) ::
                 ((Varg_varglist field_list) :: [])))))) ->
      let record_constructor =
       match rec_constructor_or_none with
       | [] -> CT_coerce_NONE_to_ID_OPT CT_none
       | (Varg_ident id) :: [] -> CT_coerce_ID_to_ID_OPT id
       | _ -> xlate_error "unexpected record constructor" in
      CT_record
       ((match coercion_or_not with CT_string "" ->
          CT_coerce_NONE_to_COERCION_OPT(CT_none)
        | _ -> CT_coercion_atm),
        s, binders, 
        (match c1 with (Varg_sorttype c) -> c
        |(Varg_constr (CT_coerce_SORT_TYPE_to_FORMULA c)) -> c
        | _ -> assert false),
         record_constructor,
         build_record_field_list field_list)
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
     | 
       "ONEINDUCTIVE",
         ((Varg_string (CT_string f)) ::
           ((Varg_ident s) ::
             (c ::
               ((Varg_binderlist binders) ::
                 ((Varg_binderlist (CT_binder_list constructors)) :: []))))) ->
         CT_mind_decl
	   (CT_co_ind f,
            CT_ind_spec_list(
              [CT_ind_spec(s,binders, coerce_iVARG_to_FORMULA c,
                           build_constructors constructors)]))
     | "OLDMUTUALINDUCTIVE",
         [Varg_binderlist binders; Varg_string(CT_string f);
          Varg_varglist lmi] ->
       let strip_mutind =
        function
          | Varg_varglist([Varg_ident s;c;
                            Varg_binderlist (CT_binder_list constructors)]) ->
           CT_ind_spec(s, binders, coerce_iVARG_to_FORMULA c,
                       build_constructors constructors)
          | _ -> xlate_error "mutual inductive, old style" in
         CT_mind_decl(CT_co_ind f, CT_ind_spec_list(List.map strip_mutind lmi))
     | "MUTUALINDUCTIVE",
         ((Varg_string (CT_string co_or_ind)) ::
           ((Varg_varglist lmi) ::[])) ->
      let strip_mutind =
       function
          | Varg_varglist ((Varg_ident s) ::
                            (c ::
                              ((Varg_binderlist parameters) ::
                              ((Varg_binderlist (CT_binder_list constructors))
                                :: [])))) ->
           CT_ind_spec
            (s, parameters, coerce_iVARG_to_FORMULA c,
             build_constructors constructors)
          | _ -> xlate_error "mutual inductive" in
        CT_mind_decl
	  (CT_co_ind co_or_ind, CT_ind_spec_list (List.map strip_mutind lmi))
     | "MUTUALRECURSIVE", ((Varg_varglist (lm :: lmi)) :: []) ->
      let strip_mutrec =
       function
          | Varg_varglist ((Varg_ident fid) ::
                            ((Varg_binderlist (CT_binder_list (b :: bl))) ::
                              (arf :: (ardef :: [])))) ->
           CT_fix_rec
            (fid, CT_binder_ne_list (b, bl), coerce_iVARG_to_FORMULA arf,
            coerce_iVARG_to_FORMULA ardef)
          | _ -> xlate_error "mutual recursive" in
        CT_fix_decl
	  (CT_fix_rec_list (strip_mutrec lm, List.map strip_mutrec lmi))
     | "MUTUALCORECURSIVE", ((Varg_varglist (lm :: lmi)) :: []) ->
      let strip_mutcorec =
       function
          | Varg_varglist ((Varg_ident fid) :: (arf :: (ardef :: []))) ->
           CT_cofix_rec
            (fid, coerce_iVARG_to_FORMULA arf, coerce_iVARG_to_FORMULA ardef)
          | _ -> xlate_error "mutual corecursive" in
        CT_cofix_decl
	  (CT_cofix_rec_list (strip_mutcorec lm, List.map strip_mutcorec lmi))
     | "INDUCTIONSCHEME", ((Varg_varglist (lm :: lmi)) :: []) ->
      let strip_ind =
       function
          | Varg_varglist ((Varg_ident fid) ::
                            ((Varg_string (CT_string depstr)) ::
                              (inde :: ((Varg_sorttype sort) :: [])))) ->
           CT_scheme_spec
            (fid, xlate_dep depstr, coerce_iVARG_to_FORMULA inde, sort)
          | _ -> xlate_error "induction scheme" in
        CT_ind_scheme
	  (CT_scheme_spec_list (strip_ind lm, List.map strip_ind lmi))
     | 
       "SyntaxMacro", ((Varg_ident id) :: (c :: [])) ->
         CT_syntax_macro
	   (id, coerce_iVARG_to_FORMULA c, CT_coerce_NONE_to_INT_OPT CT_none)
     | "SyntaxMacro", ((Varg_ident id) :: (c :: ((Varg_int n) :: []))) ->
         CT_syntax_macro
	   (id, coerce_iVARG_to_FORMULA c, CT_coerce_INT_to_INT_OPT n)
     | "ABSTRACTION", ((Varg_ident id) :: (c :: l)) ->
         CT_abstraction
	   (id, coerce_iVARG_to_FORMULA c, CT_int_list (List.map strip_varg_int l))
     | "Require",
         ((Varg_string impexp) ::
           ((Varg_string spec) :: ((Varg_ident id) :: []))) ->
      let ct_impexp, ct_spec = get_require_flags impexp spec in
      CT_require (ct_impexp, ct_spec, id, CT_coerce_NONE_to_STRING_OPT CT_none)
     | "RequireFrom",
         ((Varg_string impexp) ::
           ((Varg_string spec) ::
             ((Varg_ident id) :: ((Varg_string filename) :: [])))) ->
      let ct_impexp, ct_spec = get_require_flags impexp spec in
      CT_require
       (ct_impexp, ct_spec, id, CT_coerce_STRING_to_STRING_OPT filename)
     | "SYNTAX", ((Varg_ident phylum) :: ((Varg_ident s) :: (x :: (y :: l)))) ->
      xlate_error "SYNTAX not implemented"
     | (*Two versions of the syntax node with and without the binder list. *)
       (*Need to update the metal file and ascent.mli first! 
         	| ("SYNTAX", [Varg_ident phy; Varg_ident s; spatarg; unparg; blist]) ->
         	        (syntaxop phy s spatarg unparg blist)
         	| ("SYNTAX", [Varg_ident phy; Varg_ident s; spatarg; unparg]) ->
         	        (syntaxop phy s spatarg unparg 
         coerce_ID_OPT_to_FORMULA_OPT(CT_coerce_NONE_to_ID_OPT(CT_none)))*)
       "TOKEN", ((Varg_string str) :: []) -> CT_token str
     | "INFIX",
         ((Varg_ast (CT_coerce_ID_OR_STRING_to_AST
                         (CT_coerce_STRING_to_ID_OR_STRING 
                            (CT_string str_assoc)))) ::
           ((Varg_int n) :: ((Varg_string str) :: ((Varg_ident id) :: [])))) ->
      CT_infix (
       (match str_assoc with
        | "LEFTA" -> CT_lefta
        | "RIGHTA" -> CT_righta
        | "NONA" -> CT_nona
        | "NONE" -> CT_coerce_NONE_to_ASSOC CT_none
        | _ -> xlate_error "infix1"), n, str, id)
     | "GRAMMAR", (ge :: []) -> xlate_error "GRAMMAR not implemented"
     | "SETUNDO", ((Varg_int n) :: []) -> CT_setundo n
     | "UNSETUNDO", [] -> CT_unsetundo
     | "SETHYPSLIMIT", ((Varg_int n) :: []) -> CT_sethyp n
     | "UNSETHYPSLIMIT", [] -> CT_unsethyp
     | "COERCION",
         ((Varg_string (CT_string s)) ::
           ((Varg_string (CT_string str)) ::
             ((Varg_ident id1) :: ((Varg_ident id2) :: ((Varg_ident id3) :: []))))) ->
      let id_opt =
       match str with
       | "IDENTITY" -> CT_identity
       | "" -> CT_coerce_NONE_to_IDENTITY_OPT CT_none
       | _ -> xlate_error "unknown flag for a coercion1" in
      let local_opt =
       match s with
       | "LOCAL" -> CT_local
       | "" -> CT_coerce_NONE_to_LOCAL_OPT CT_none
       | _ -> xlate_error "unknown flag for a coercion2" in
      CT_coercion (local_opt, id_opt, id1, id2, id3)
     | "CLASS", (_ :: ((Varg_ident id1) :: [])) -> CT_class id1
     | "PrintGRAPH", [] -> CT_print_graph
     | "PrintCLASSES", [] -> CT_print_classes
     | "PrintCOERCIONS", [] -> CT_print_coercions
     | "PrintPATH", ((Varg_ident id1) :: ((Varg_ident id2) :: [])) ->
      CT_print_path (id1, id2)
     | "SelectLanguageText", ((Varg_ident id) :: []) -> CT_set_natural id
     | "PrintText", ((Varg_ident id) :: []) -> CT_print_natural id
     | "AddTextParamOmit", ((Varg_ident id) :: []) ->
      CT_add_natural_feature (CT_implicit, id)
     | "MemTextParamOmit", ((Varg_ident id) :: []) ->
      CT_test_natural_feature (CT_implicit, id)
     | "RemoveTextParamOmit", ((Varg_ident id) :: []) ->
      CT_remove_natural_feature (CT_implicit, id)
     | "PrintTextParamOmit", [] -> CT_print_natural_feature CT_implicit
     | "AddTextParamRecSub", ((Varg_ident id) :: []) ->
      CT_add_natural_feature (CT_contractible, id)
     | "MemTextParamRecSub", ((Varg_ident id) :: []) ->
      CT_test_natural_feature (CT_contractible, id)
     | "RemoveTextParamRecSub", ((Varg_ident id) :: []) ->
      CT_remove_natural_feature (CT_contractible, id)
     | "PrintTextParamRecSub", [] -> CT_print_natural_feature CT_contractible
     | "AddTextParamImmediate", ((Varg_ident id) :: []) ->
      CT_add_natural_feature (CT_nat_transparent, id)
     | "MemTextParamImmediate", ((Varg_ident id) :: []) ->
      CT_test_natural_feature (CT_nat_transparent, id)
     | "RemoveTextParamImmediate", ((Varg_ident id) :: []) ->
      CT_remove_natural_feature (CT_nat_transparent, id)
     | "PrintTextParamImmediate", [] ->
      CT_print_natural_feature CT_nat_transparent
     | "ResetName", ((Varg_ident id) :: []) -> CT_reset id
     | "ResetSection", ((Varg_ident id) :: []) -> CT_reset_section id
     | "ResetInitial", [] -> CT_restore_state (CT_ident "Initial")
     | "OmegaFlag", ((Varg_string (CT_string s)) :: []) ->
      let fst_code = code (get s 0) in
      let
      set_or_unset, tail =
       if fst_code = code_plus then (CT_set, sub s 1 (length s - 1))
       else if fst_code = code_minus then (CT_unset, sub s 1 (length s - 1))
       else (CT_switch, s) in
      (match tail with
       | "time" -> CT_omega_flag (set_or_unset, CT_flag_time)
       | "action" -> CT_omega_flag (set_or_unset, CT_flag_action)
       | "system" -> CT_omega_flag (set_or_unset, CT_flag_system)
       | _ ->
        CT_omega_flag
         (set_or_unset, CT_coerce_STRING_to_OMEGA_FEATURE (CT_string s)))
     | s, l ->
      CT_user_vernac
       (CT_ident s, CT_varg_list (List.map coerce_iVARG_to_VARG l)))
    | _ -> xlate_error "xlate_vernac";;

let xlate_vernac_list =
 function
    | Node (_, "vernac_list", (v :: l)) ->
     CT_command_list (xlate_vernac v, List.map xlate_vernac l)
    | _ -> xlate_error "xlate_command_list";;
