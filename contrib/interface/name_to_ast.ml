open Sign;;
open Classops;;
open Names;;
open Nameops
open Coqast;;
open Ast;;
open Termast;;
open Term;;
open Impargs;;
open Reduction;;
open Libobject;;
open Environ;;
open Declarations;;
open Prettyp;;
open Inductive;;
open Util;;
open Pp;;
open Declare;;
open Nametab
open Vernacexpr;;
open Decl_kinds;;

(* This function converts the parameter binders of an inductive definition,
   in particular you have to be careful to handle each element in the
   context containing all previously defined variables.  This squeleton
   of this procedure is taken from the function print_env in pretty.ml *)
let convert_env =
    let convert_binder env (na, _, c) =
      match na with 
       | Name id -> (id, ast_of_constr true env c)
       | Anonymous -> failwith "anomaly: Anonymous variables in inductives" in
    let rec cvrec env = function
       [] -> []
     | b::rest -> (convert_binder env b)::(cvrec (push_rel b env) rest) in
    cvrec (Global.env());;

(* let mib string = 
     let sp = Nametab.sp_of_id CCI (id_of_string string) in
     let lobj = Lib.map_leaf (objsp_of sp) in
     let (cmap, _) = outMutualInductive lobj in
     Listmap.map cmap CCI;; *)

(* This function is directly inspired by print_impl_args in pretty.ml *)

let impl_args_to_string = function
    [] -> None
  | [i] -> Some(" position " ^ (string_of_int i) ^ " is implicit.")
  | l -> Some (" positions " ^
                (List.fold_right (fun i s -> (string_of_int i) ^ " " ^ s)
                     l
                     " are implicit."));;

(* This function is directly inspired by implicit_args_id in pretty.ml *)

let implicit_args_id_to_ast_list id l ast_list = 
    (match impl_args_to_string l with
           None -> ast_list
         | Some(s) -> CommentString ("For " ^ (string_of_id id))::
                      CommentString s::
                      ast_list);;

(* This function construct an ast to enumerate the implicit positions for an
   inductive type and its constructors. It is obtained directly from
   implicit_args_msg in pretty.ml.  *)

let implicit_args_to_ast_list sp mipv =
    let implicit_args_descriptions = 
      let ast_list = ref [] in
       	(Array.iteri
           (fun i mip  ->
	      let imps = inductive_implicits_list(sp, i) in
		      (ast_list :=
	      	implicit_args_id_to_ast_list mip.mind_typename imps !ast_list;
	      	Array.iteri
		  (fun j idc ->
		     let impls = constructor_implicits_list ((sp,i), succ j) in
		       ast_list := 
		       implicit_args_id_to_ast_list idc impls !ast_list)
		  mip.mind_consnames))
	  mipv;
	 !ast_list) in
      match implicit_args_descriptions with
	  [] -> []
	| _ -> [VernacComments (List.rev implicit_args_descriptions)];;
	      
let convert_qualid qid =
  let d, id = Nametab.repr_qualid qid in
    match repr_dirpath d with
	[] -> nvar id
      | d -> ope("QUALID", List.fold_left (fun l s -> (nvar s)::l)
		   [nvar id] d);;

(* This function converts constructors for an inductive definition to a
   Coqast.t.  It is obtained directly from print_constructors in pretty.ml *)

let convert_constructors envpar names types =
  let array_idC = 
    array_map2 
      (fun n t -> 
	let coercion_flag = false (* arbitrary *) in
	(coercion_flag, (n, ast_of_constr true envpar t)))
      names types in
  Array.to_list array_idC;;
  
(* this function converts one inductive type in a possibly multiple inductive
   definition *)

let convert_one_inductive sp tyi =
  let (ref, params, arity, cstrnames, cstrtypes) = build_inductive sp tyi in
  let env = Global.env () in
  let envpar = push_rel_context params env in
  let sp = sp_of_global env (IndRef (sp, tyi)) in
  (basename sp,
   convert_env(List.rev params),
   (ast_of_constr true envpar arity),
   convert_constructors envpar cstrnames cstrtypes);;

(* This function converts a Mutual inductive definition to a Coqast.t.
   It is obtained directly from print_mutual in pretty.ml.  However, all
   references to kinds have been removed and it treats only CCI stuff. *)

let mutual_to_ast_list sp mib =
  let mipv = (Global.lookup_mind sp).mind_packets in
  let _, l =
    Array.fold_right
      (fun mi (n,l) -> (n+1, (convert_one_inductive sp n)::l)) mipv (0, []) in
  VernacInductive (mib.mind_finite, l)
  :: (implicit_args_to_ast_list sp mipv);;

let constr_to_ast v = 
  ast_of_constr true (Global.env()) v;;

let implicits_to_ast_list implicits =
  match (impl_args_to_string implicits) with
    | None -> []
    | Some s -> [VernacComments [CommentString s]];;

(*
let make_variable_ast name typ implicits =
   (ope("VARIABLE",
    [string "VARIABLE";
     ope("BINDERLIST",
         [ope("BINDER",
            [(constr_to_ast (body_of_type typ));
             nvar name])])]))::(implicits_to_ast_list implicits)
    ;;
*)
let make_variable_ast name typ implicits =
  (VernacAssumption
    ((Local,Definitional), [false,(name, constr_to_ast (body_of_type typ))]))
  ::(implicits_to_ast_list implicits);;
    
(*
let make_definition_ast name c typ implicits =
 (ope("DEFINITION",
      [string "DEFINITION";
       nvar name;
       ope("COMMAND",
           [ope("CAST",
                [(constr_to_ast c);
		 (constr_to_ast (body_of_type typ))])])]))::
  (implicits_to_ast_list implicits);;
*)
let make_definition_ast name c typ implicits =
  VernacDefinition (Global, name, DefineBody ([], None,
    (constr_to_ast c), Some (constr_to_ast (body_of_type typ))),
    (fun _ _ -> ()))
  ::(implicits_to_ast_list implicits);;

(* This function is inspired by print_constant *)
let constant_to_ast_list sp =
  let cb = Global.lookup_constant sp in
  let c = cb.const_body in
  let typ = cb.const_type in
  let l = constant_implicits_list sp in
  (match c with
      None -> 
	make_variable_ast (basename sp) typ l
    | Some c1 ->
	make_definition_ast (basename sp) c1 typ l)

let variable_to_ast_list sp =
  let (id, c, v) = get_variable sp in
  let l = implicits_of_var sp in
    (match c with
	 None -> 
	   make_variable_ast id v l
       | Some c1 ->
	   make_definition_ast id c1 v l);;

(* this function is taken from print_inductive in file pretty.ml *)

let inductive_to_ast_list sp =
  let mib = Global.lookup_mind sp in
  mutual_to_ast_list sp mib

(* this function is inspired by print_leaf_entry from pretty.ml *)

let leaf_entry_to_ast_list (sp,lobj) =
  let tag = object_tag lobj in
  match (sp,tag) with
  | (_, "VARIABLE") -> variable_to_ast_list (basename sp)
  | (_, ("CONSTANT"|"PARAMETER")) -> constant_to_ast_list sp
  | (_, "INDUCTIVE") -> inductive_to_ast_list sp
  | (_, s) -> 
      errorlabstrm 
      	"print" (str ("printing of unrecognized object " ^
		      s ^ " has been required"));;




(* this function is inspired by print_name *)
let name_to_ast (qid:Nametab.qualid) = 
  let l = 
    try
      let sp = Nametab.locate_obj qid in
      let (sp,lobj) = 
      	let (sp,entry) =
          List.find (fun en -> (fst en) = sp) (Lib.contents_after None)
      	in
	  match entry with
            | Lib.Leaf obj -> (sp,obj)
            | _ -> raise Not_found
      in
    	leaf_entry_to_ast_list (sp,lobj)
    with Not_found -> 
      try 
    	match Nametab.locate qid with
	  | ConstRef sp -> constant_to_ast_list sp
	  | IndRef (sp,_) -> inductive_to_ast_list sp
	  | ConstructRef ((sp,_),_) -> inductive_to_ast_list sp
	  | VarRef sp -> variable_to_ast_list sp
  	with Not_found -> 
	  try  (* Var locale de but, pas var de section... donc pas d'implicits *)
	    let dir,name = Nametab.repr_qualid qid in 
	      if (repr_dirpath dir) <> [] then raise Not_found;
	      let (_,c,typ) = Global.lookup_named name in 
		(match c with
		     None -> make_variable_ast name typ []
		   | Some c1 -> make_definition_ast name c1 typ [])
	  with Not_found ->
	    try
	      let sp = Syntax_def.locate_syntactic_definition qid in
		errorlabstrm "print"
      		  (str "printing of syntax definitions not implemented")
	    with Not_found ->
	      errorlabstrm "print"
		(Nametab.pr_qualid qid ++
		 spc () ++ str "not a defined object")
  in
  VernacList (List.map (fun x -> (dummy_loc,x)) l)

