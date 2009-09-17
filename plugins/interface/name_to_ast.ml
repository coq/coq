open Sign;;
open Classops;;
open Names;;
open Nameops
open Term;;
open Impargs;;
open Reduction;;
open Libnames;;
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
open Constrextern;;
open Topconstr;;

(* This function converts the parameter binders of an inductive definition,
   in particular you have to be careful to handle each element in the
   context containing all previously defined variables.  This squeleton
   of this procedure is taken from the function print_env in pretty.ml *)
let convert_env =
    let convert_binder env (na, b, c) =
      match b with
       | Some b -> LocalRawDef ((dummy_loc,na), extern_constr true env b)
       | None -> LocalRawAssum ([dummy_loc,na], default_binder_kind, extern_constr true env c) in
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

let impl_args_to_string_by_pos = function
    [] -> None
  | [i] -> Some(" position " ^ (string_of_int i) ^ " is implicit.")
  | l -> Some (" positions " ^
                (List.fold_right (fun i s -> (string_of_int i) ^ " " ^ s)
                     l
                     " are implicit."));;

(* This function is directly inspired by implicit_args_id in pretty.ml *)

let impl_args_to_string l =
  impl_args_to_string_by_pos (positions_of_implicits l)

let implicit_args_id_to_ast_list id l ast_list =
    (match impl_args_to_string l with
           None -> ast_list
         | Some(s) -> CommentString s::
                      CommentString ("For " ^ (string_of_id id))::
                      ast_list);;

(* This function construct an ast to enumerate the implicit positions for an
   inductive type and its constructors. It is obtained directly from
   implicit_args_msg in pretty.ml.  *)

let implicit_args_to_ast_list sp mipv =
    let implicit_args_descriptions =
      let ast_list = ref [] in
       	(Array.iteri
           (fun i mip  ->
	      let imps = implicits_of_global (IndRef (sp, i)) in
		      (ast_list :=
	      	implicit_args_id_to_ast_list mip.mind_typename imps !ast_list;
	      	Array.iteri
		  (fun j idc ->
		     let impls = implicits_of_global
		       (ConstructRef ((sp,i),j+1)) in
		       ast_list :=
		       implicit_args_id_to_ast_list idc impls !ast_list)
		  mip.mind_consnames))
	  mipv;
	 !ast_list) in
      match implicit_args_descriptions with
	  [] -> []
	| _ -> [VernacComments (List.rev implicit_args_descriptions)];;

(* This function converts constructors for an inductive definition to a
   Coqast.t.  It is obtained directly from print_constructors in pretty.ml *)

let convert_constructors envpar names types =
  let array_idC =
    array_map2
      (fun n t ->
	let coercion_flag = false (* arbitrary *) in
	(coercion_flag, ((dummy_loc,n), extern_constr true envpar t)))
      names types in
  Array.to_list array_idC;;

(* this function converts one inductive type in a possibly multiple inductive
   definition *)

let convert_one_inductive sp tyi =
  let (ref, params, arity, cstrnames, cstrtypes) = build_inductive sp tyi in
  let env = Global.env () in
  let envpar = push_rel_context params env in
  let sp = path_of_global (IndRef (sp, tyi)) in
  (((false,(dummy_loc,basename sp)),
   convert_env(List.rev params),
   Some (extern_constr true envpar arity), Vernacexpr.Inductive_kw ,
   Constructors (convert_constructors envpar cstrnames cstrtypes)), None);;

(* This function converts a Mutual inductive definition to a Coqast.t.
   It is obtained directly from print_mutual in pretty.ml.  However, all
   references to kinds have been removed and it treats only CCI stuff. *)

let mutual_to_ast_list sp mib =
  let mipv = (Global.lookup_mind sp).mind_packets in
  let _, l =
    Array.fold_right
      (fun mi (n,l) -> (n+1, (convert_one_inductive sp n)::l)) mipv (0, []) in
  VernacInductive ((if mib.mind_finite then Decl_kinds.Finite else Decl_kinds.CoFinite), false, l)
  :: (implicit_args_to_ast_list sp mipv);;

let constr_to_ast v =
  extern_constr true (Global.env()) v;;

let implicits_to_ast_list implicits =
  match (impl_args_to_string implicits) with
    | None -> []
    | Some s -> [VernacComments [CommentString s]];;

let make_variable_ast name typ implicits =
  (VernacAssumption
    ((Local,Definitional),false,(*inline flag*)
     [false,([dummy_loc,name], constr_to_ast typ)]))
  ::(implicits_to_ast_list implicits);;


let make_definition_ast name c typ implicits =
  VernacDefinition ((Global,false,Definition), (dummy_loc,name),
		   DefineBody ([], None, constr_to_ast c, Some (constr_to_ast typ)),
    (fun _ _ -> ()))
  ::(implicits_to_ast_list implicits);;

(* This function is inspired by print_constant *)
let constant_to_ast_list kn =
  let cb = Global.lookup_constant kn in
  let c = cb.const_body in
  let typ = Typeops.type_of_constant_type (Global.env()) cb.const_type in
  let l = implicits_of_global (ConstRef kn) in
  (match c with
      None ->
	make_variable_ast (id_of_label (con_label kn)) typ l
    | Some c1 ->
	make_definition_ast (id_of_label (con_label kn)) (Declarations.force c1) typ l)

let variable_to_ast_list sp =
  let (id, c, v) = Global.lookup_named sp in
  let l = implicits_of_global (VarRef sp) in
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

let leaf_entry_to_ast_list ((sp,kn),lobj) =
  let tag = object_tag lobj in
  match tag with
  | "VARIABLE" -> variable_to_ast_list (basename sp)
  | "CONSTANT" -> constant_to_ast_list (constant_of_kn kn)
  | "INDUCTIVE" -> inductive_to_ast_list kn
  | s ->
      errorlabstrm
      	"print" (str ("printing of unrecognized object " ^
		      s ^ " has been required"));;




(* this function is inspired by print_name *)
let name_to_ast ref =
  let (loc,qid) = qualid_of_reference ref in
  let l =
      try
    	match Nametab.locate qid with
	  | ConstRef sp -> constant_to_ast_list sp
	  | IndRef (sp,_) -> inductive_to_ast_list sp
	  | ConstructRef ((sp,_),_) -> inductive_to_ast_list sp
	  | VarRef sp -> variable_to_ast_list sp
  	with Not_found ->
	  try  (* Var locale de but, pas var de section... donc pas d'implicits *)
	    let dir,name = repr_qualid qid in
	      if (repr_dirpath dir) <> [] then raise Not_found;
	      let (_,c,typ) = Global.lookup_named name in
		(match c with
		     None -> make_variable_ast name typ []
		   | Some c1 -> make_definition_ast name c1 typ [])
	  with Not_found ->
	    try
	      let _sp = Nametab.locate_syndef qid in
		errorlabstrm "print"
      		  (str "printing of syntax definitions not implemented")
	    with Not_found ->
	      errorlabstrm "print"
		(pr_qualid qid ++
		 spc () ++ str "not a defined object")
  in
  VernacList (List.map (fun x -> (dummy_loc,x)) l)

