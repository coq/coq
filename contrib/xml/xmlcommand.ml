(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)
(*****************************************************************************)
(*                                                                           *)
(*                             PROJECT MoWGLI                                *)
(*                                                                           *)
(*                    A module to print Coq objects in XML                   *)
(*                                                                           *)
(*               Claudio Sacerdoti Coen <sacerdot@cs.unibo.it>               *)
(*                                22/06/2002                                 *)
(*                                                                           *)
(*****************************************************************************)


(* CONFIGURATION PARAMETERS *)

(*CSC: was false*)
let verbose = ref true;; (* always set to true during a "Print XML All" *)

(* UTILITY FUNCTIONS *)

let print_if_verbose s = if !verbose then print_string s;;

type tag =
   Constant
 | Inductive
 | Variable
;;

(* Next exception is used only inside print_coq_object and tag_of_string_tag *)
exception Uninteresting;;

let tag_of_string_tag =
 function
    "CONSTANT"
  | "PARAMETER"       -> Constant
  | "INDUCTIVE"       -> Inductive
  | "VARIABLE"        -> Variable
  | _                 -> raise Uninteresting
;;

let ext_of_tag =
 function
    Constant  -> "con"
  | Inductive -> "ind"
  | Variable  -> "var"
;;

(* Internally, for Coq V7, params of inductive types are associated     *)
(* not to the whole block of mutual inductive (as it was in V6) but to  *)
(* each member of the block; but externally, all params are required    *)
(* to be the same; the following function checks that the parameters    *)
(* of each inductive of a same block are all the same, then returns     *)
(* this number; it fails otherwise                                      *)
let extract_nparams pack =
 let module D = Declarations in
 let module U = Util in
 let module S = Sign in

  let {D.mind_nparams=nparams0} = pack.(0) in
  let arity0 = pack.(0).D.mind_user_arity in
  let params0, _ = S.decompose_prod_n_assum nparams0 arity0 in
  for i = 1 to Array.length pack - 1 do
    let {D.mind_nparams=nparamsi} = pack.(i) in
    let arityi = pack.(i).D.mind_user_arity in
    let paramsi, _ = S.decompose_prod_n_assum nparamsi arityi in
    if params0 <> paramsi then U.error "Cannot convert a block of inductive definitions with parameters specific to each inductive to a block of mutual inductive definitions with parameters global to the whole block"
  done;
  nparams0

(* could_have_namesakes sp = true iff o is an object that could be cooked and *)
(* than that could exists in cooked form with the same name in a super        *)
(* section of the actual section                                              *)
let could_have_namesakes o sp =      (* namesake = omonimo in italian *)
 let module N = Nametab in
 let module D = Declare in
  let tag = Libobject.object_tag o in
   print_if_verbose ("Object tag: " ^ tag ^ "\n") ;
   match tag with
      "CONSTANT" ->
        (match D.constant_strength sp with
          | N.DischargeAt _  -> false (* a local definition *)
          | N.NotDeclare     -> false (* not a definition *)
          | N.NeverDischarge -> true  (* a non-local one    *)
        )
    | "PARAMETER"                 (* axioms and                               *)
    | "INDUCTIVE"       -> true   (* mutual inductive types are never local   *)
    | "VARIABLE"        -> false  (* variables are local, so no namesakes     *)
    | _                 -> false  (* uninteresting thing that won't be printed*)
;;


let uri_of_path sp tag =
 let module N = Names in
 let module No = Nameops in
  let ext_of_sp sp = ext_of_tag tag in
  let dir0 = No.extend_dirpath (No.dirpath sp) (No.basename sp) in
  let dir = List.map N.string_of_id (List.rev (N.repr_dirpath dir0)) in
   "cic:/" ^ (String.concat "/" dir) ^ "." ^ (ext_of_sp sp)
;;

(* A SIMPLE DATA STRUCTURE AND SOME FUNCTIONS TO MANAGE THE CURRENT *)
(* ENVIRONMENT (= [l1, ..., ln] WHERE li IS THE LIST OF VARIABLES   *)
(* DECLARED IN THE i-th SUPER-SECTION OF THE CURRENT SECTION        *)

let pvars = ref ([[]] : string list list);;
let cumenv = ref Environ.empty_env;;

(* filter_params pvars hyps *)
(* filters out from pvars (which is a list of lists) all the variables *)
(* that does not belong to hyps (which is a simple list)               *)
(* It returns a list of couples level of depth -- list of variable     *)
(* names.                                                              *)
let filter_params pvars hyps =
 let rec aux n =
  function
     [] -> []
   | he::tl ->
      let he' = n, List.filter (function x -> List.mem x hyps) he in
      let tl' = aux (n+1) tl in
       match he' with
          _,[] -> tl'
        | _,_  -> he'::tl'
 in
  aux 0 pvars
;;

type variables_type = 
   Definition of string * Term.constr * Term.types
 | Assumption of string * Term.constr
;;

let add_to_pvars x =
 let module E = Environ in
  let v =
   match x with
      Definition (v, bod, typ) ->
       cumenv :=
         E.push_named (Names.id_of_string v, Some bod, typ) !cumenv ;
       v
    | Assumption (v, typ) ->
       cumenv :=
         E.push_named (Names.id_of_string v, None, typ) !cumenv ;
       v
  in
   match !pvars with
      []       -> assert false
    | (he::tl) -> pvars := (v::he)::tl
;;

(* The computation is very inefficient, but we can't do anything *)
(* better unless this function is reimplemented in the Declare   *)
(* module.                                                       *)
let rec search_variables =
 let module N = Names in
  function
     [] -> []
   | he::tl as modules ->
      let one_section_variables =
       let dirpath = N.make_dirpath modules in
        match List.map N.string_of_id (Declare.last_section_hyps dirpath) with
          [] -> []
        | t -> [t]
       in
        one_section_variables @ search_variables tl
;;

(* FUNCTIONS TO PRINT A SINGLE OBJECT OF COQ *)

let print_object uri obj sigma proof_tree_infos filename typesfilename prooftreefilename =
 (* function to pretty print and compress an XML file *)
(*CSC: Unix.system "gzip ..." is an orrible non-portable solution. *)
 let pp xml filename =
  Xml.pp xml filename ;
  match filename with
     None -> ()
   | Some fn -> ignore (Unix.system ("gzip " ^ fn ^ ".xml"))
 in
  let (annobj,_,constr_to_ids,_,ids_to_inner_sorts,ids_to_inner_types,_,_) =
   Cic2acic.acic_object_of_cic_object !pvars sigma obj in
  let xml = Acic2Xml.print_object uri ids_to_inner_sorts annobj in
  let xmltypes =
   Acic2Xml.print_inner_types uri ids_to_inner_sorts ids_to_inner_types in
  pp xml filename ;
  pp xmltypes typesfilename ;
  match proof_tree_infos with
     None -> ()
   | Some (proof_tree,proof_tree_to_constr) ->
      let xmlprooftree =
       ProofTree2Xml.print_proof_tree
        uri proof_tree proof_tree_to_constr constr_to_ids
      in
       pp xmlprooftree prooftreefilename
;;

let string_list_of_named_context_list =
 List.map
  (function (n,_,_) -> Names.string_of_id n)
;;

let types_filename_of_filename =
 function
    Some f -> Some (f ^ ".types")
  | None   -> None
;;

let prooftree_filename_of_filename =
 function
    Some f -> Some (f ^ ".proof_tree")
  | None   -> None
;;

(* Functions to construct an object *)

let mk_variable_obj id body typ =
 let unsharedbody =
  match body with
     None -> None
   | Some bo -> Some (Term.unshare bo)
 in
  Acic.Variable
   (Names.string_of_id id,unsharedbody,
    (Term.unshare (Term.body_of_type typ)))
;;

(* Unsharing is not performed on the body, that must be already unshared. *)
(* The evar map and the type, instead, are unshared by this function.     *)
let mk_current_proof_obj id bo ty evar_map env =
 let unshared_ty = Term.unshare (Term.body_of_type ty) in
 let metasenv' =
  List.map
   (function
     (n, {Evd.evar_concl = evar_concl ;
          Evd.evar_hyps = evar_hyps}
      ) ->
       let context =
        List.map
         (function
             (n,None,t)   -> n, Acic.Decl (Term.unshare t)
           | (n,Some b,_) -> n, Acic.Def  (Term.unshare b)
         ) evar_hyps
       in
        (n,context,Term.unshare evar_concl)
   ) (Evd.non_instantiated evar_map)
 in
  let id' = Names.string_of_id id in
   if metasenv' = [] then
    let ids =
     Names.Idset.union
      (Environ.global_vars_set env bo) (Environ.global_vars_set env ty) in
    let hyps0 = Environ.keep_hyps env ids in
    let hyps = string_list_of_named_context_list hyps0 in
    (* Variables are the identifiers of the variables in scope *)
    let variables = search_variables (Names.repr_dirpath (Lib.cwd ())) in
    let params = filter_params variables hyps in
     Acic.Definition (id',bo,unshared_ty,params)
   else
    Acic.CurrentProof (id',metasenv',bo,unshared_ty)
;;

let mk_constant_obj id bo ty variables hyps =
 let hyps = string_list_of_named_context_list hyps in
 let ty = Term.unshare (Term.body_of_type ty) in
 let params = filter_params variables hyps in
  match bo with
     None -> Acic.Axiom (Names.string_of_id id,ty,params)
   | Some c -> Acic.Definition (Names.string_of_id id,Term.unshare c,ty,params)
;;

let mk_inductive_obj packs variables hyps finite =
 let module D = Declarations in
  let hyps = string_list_of_named_context_list hyps in
  let params = filter_params variables hyps in
  let nparams = extract_nparams packs in
   let tys =
    Array.fold_right
     (fun p i ->
       let {D.mind_consnames=consnames ;
            D.mind_typename=typename ;
            D.mind_nf_lc=lc ;
            D.mind_nf_arity=arity} = p
       in
        let cons =
         (Array.fold_right (fun (name,lc) i -> (name,lc)::i)
          (Array.mapi
           (fun j x -> (x,Term.unshare (Term.body_of_type lc.(j)))) consnames)
          []
         )
        in
         (typename,finite,Term.unshare arity,cons)::i
     ) packs []
   in
    Acic.InductiveDefinition (tys,params,nparams)
;;

(* print id dest                                                          *)
(*  where sp   is the qualified identifier (section path) of a            *)
(*             definition/theorem, variable or inductive definition       *)
(*  and   dest is either None (for stdout) or (Some filename)             *)
(* pretty prints via Xml.pp the object whose identifier is id on dest     *)
(* Note: it is printed only (and directly) the most cooked available      *)
(*       form of the definition (all the parameters are                   *)
(*       lambda-abstracted, but the object can still refer to variables)  *)
let print (_,qid as locqid) fn =
 let module D = Declarations in
 let module De = Declare in
 let module G = Global in
 let module N = Names in
 let module Nt = Nametab in
 let module T = Term in
 let module X = Xml in
  let (_,id) = Nt.repr_qualid qid in
  let glob_ref =
(*CSC: ask Hugo why Nametab.global does not work with variables and *)
(*CSC: we have to do this hugly try ... with                        *)
   try
    Nt.global locqid
   with
    _ -> let (_,id) = Nt.repr_qualid qid in Nt.VarRef id
  in
  (* Variables are the identifiers of the variables in scope *)
  let variables = search_variables (Names.repr_dirpath (Lib.cwd ())) in
  let sp,tag,obj =
   match glob_ref with
      Nt.VarRef id ->
       let sp = Declare.find_section_variable id in
       let (_,body,typ) = G.lookup_named id in
        sp,Variable,mk_variable_obj id body typ
    | Nt.ConstRef sp ->
       let {D.const_body=val0 ; D.const_type = typ ; D.const_hyps = hyps} =
        G.lookup_constant sp in
        sp,Constant,mk_constant_obj id val0 typ variables hyps
    | Nt.IndRef (sp,_) ->
       let {D.mind_packets=packs ;
            D.mind_hyps=hyps;
            D.mind_finite=finite} = G.lookup_mind sp in
          sp,Inductive,mk_inductive_obj packs variables hyps finite
    | Nt.ConstructRef _ ->
       Util.anomaly ("print: this should not happen")
  in
   print_object (uri_of_path sp tag) obj Evd.empty None fn
    (types_filename_of_filename fn) (prooftree_filename_of_filename fn)
;;

(* show dest                                                  *)
(*  where dest is either None (for stdout) or (Some filename) *)
(* pretty prints via Xml.pp the proof in progress on dest     *)
let show_pftreestate fn pftst =
 let id = Pfedit.get_current_proof_name () in
 let str = Names.string_of_id id in
 let pf = Tacmach.proof_of_pftreestate pftst in
 let typ = (Proof_trees.goal_of_proof pf).Evd.evar_concl in
 let val0,evar_map,proof_tree_to_constr =
  Proof2aproof.extract_open_pftreestate pftst in
 let sp = Lib.make_path id in
 let env = Global.env () in
 let obj = mk_current_proof_obj id val0 typ evar_map env in
  print_object (uri_of_path sp Constant) obj evar_map
   (Some (pf,proof_tree_to_constr)) fn (types_filename_of_filename fn)
    (prooftree_filename_of_filename fn)
;;

let show fn =
 let pftst = Pfedit.get_pftreestate () in
  show_pftreestate fn pftst
;;

(* FUNCTIONS TO PRINT AN ENTIRE SECTION OF COQ *)

(* list of (name, uncooked sp, most cooked sp, uncooked leaf object,  *)
(*          list of possible variables, directory name)               *)
(* used to collect informations on the uncooked and most cooked forms *)
(* of objects that could be cooked (have namesakes)                   *)
let printed = ref [];;

(* makes a filename from a directory name, a section path and an extension *)
let mkfilename dn sp ext =
 let dir_list_of_dirpath s =
  let rec aux n =
   try
    let pos = String.index_from s n '/' in
    let head = String.sub s n (pos - n) in
     head::(aux (pos + 1))
   with
    Not_found -> [String.sub s n (String.length s - n)]
  in
   aux 0
 in
 let rec join_dirs cwd =
   function
      []  -> assert false
    | [he] -> "/" ^ he
    | he::tail ->
       let newcwd = cwd ^ "/" ^ he in
        (try
          Unix.mkdir newcwd 0o775
         with _ -> () (* Let's ignore the errors on mkdir *)
        ) ;
        "/" ^ he ^ join_dirs newcwd tail
 in
  let module L = Library in
  let module S = System in
  let module N = Names in
  let module No = Nameops in
   match dn with
      None         -> None
    | Some basedir ->
	let dir0 = No.extend_dirpath (No.dirpath sp) (No.basename sp) in
	let dir = List.map N.string_of_id (List.rev (N.repr_dirpath dir0)) in
       Some (basedir ^ join_dirs basedir dir ^ "." ^ ext)
;;

(* print_coq_object leaf_object id section_path directory_name formal_vars  *)
(*  where leaf_object    is a leaf object                                   *)
(*  and   id             is the identifier (name) of the definition/theorem *)
(*                       or of the inductive definition o                   *)
(*  and   section_path   is the section path of o                           *)
(*  and   directory_name is the base directory in which putting the print   *)
(*  and   formal_vars    is the list of parameters (variables) of o         *)
(* pretty prints via Xml.pp the object o in the right directory deduced     *)
(* from directory_name and section_path                                     *)
(* Note: it is printed only the uncooked available form of the object plus  *)
(*       the list of parameters of the object deduced from it's most cooked *)
(*       form                                                               *)
let print_coq_object lobj id sp dn fv env =
 let module D = Declarations in
 let module E = Environ in
 let module G = Global in
 let module N = Names in
 let module T = Term in
 let module X = Xml in
(*CSC: GROSSO BUG: env e' l'environment cumulativo in cui aggiungiamo passo passo tutte le variabili. Qui, invece, non lo stiamo piu' usando per nulla. Quindi la prima variabile che incontreremo non verra' trovata ;-(((( Direi che l'environment vada passato fino alla print_object che a sua volta lo passera' a chi di dovere (ovvero sia a Cic2Acic che a DoubleTypeInference *)
  let strtag = Libobject.object_tag lobj in
   try
    let tag = tag_of_string_tag strtag in
    let obj =
     match strtag with
        "CONSTANT"  (* = Definition, Theorem *)
      | "PARAMETER" (* = Axiom *) ->
          let {D.const_body=val0 ; D.const_type = typ ; D.const_hyps = hyps} =
           G.lookup_constant sp
          in
           mk_constant_obj id val0 typ fv hyps
      | "INDUCTIVE" ->
           let
            {D.mind_packets=packs ;
             D.mind_hyps = hyps;
             D.mind_finite = finite
            } = G.lookup_mind sp
           in
            mk_inductive_obj packs fv hyps finite
      | "VARIABLE" ->
          let (_,(_,varentry,_)) = Declare.out_variable lobj in
           begin
            match varentry with
               Declare.SectionLocalDef (body,optt) ->
                 let typ = match optt with
		   | None -> Retyping.get_type_of env Evd.empty body 
		   | Some t -> t in
                 add_to_pvars (Definition (N.string_of_id id, body, typ)) ;
                 mk_variable_obj id (Some body) typ
             | Declare.SectionLocalAssum typ ->
                add_to_pvars (Assumption (N.string_of_id id, typ)) ;
                mk_variable_obj id None (T.body_of_type typ)
           end
      | "CLASS"
      | "COERCION"
      | _ -> raise Uninteresting
    in
     let fileext () = ext_of_tag tag in
     let fn = mkfilename dn sp (fileext ()) in
      print_object (uri_of_path sp tag) obj Evd.empty None fn
       (types_filename_of_filename fn) (prooftree_filename_of_filename fn)
   with
    Uninteresting -> ()
;;

(* print_library_segment state bprintleaf directory_name                      *)
(*  where state          is a list of (section-path, node)                    *)
(*  and   bprintleaf     is true iff the leaf objects should be printed       *)
(*  and   directory_name is the name of the base directory in which to print  *)
(*                       the files                                            *)
(* print via print_node all the nodes (leafs excluded if bprintleaf is false) *)(* in state                                                                   *)
let rec print_library_segment state bprintleaf dn =
  List.iter
   (function (sp, node) ->
     print_if_verbose ("Print_library_segment: " ^ Names.string_of_path sp ^ "\n") ;
     print_node node (Nameops.basename sp) sp bprintleaf dn ;
     print_if_verbose "\n"
   ) (List.rev state)
(* print_node node id section_path bprintleaf directory_name             *)
(* prints a single node (and all it's subnodes via print_library_segment *)
and print_node n id sp bprintleaf dn =
 let module L = Lib in
  match n with
     L.Leaf o ->
      print_if_verbose "LEAF\n" ;
      if bprintleaf then
       begin
         if not (List.mem id !printed) then
          (* this is an uncooked term or a local (with no namesakes) term *)
          begin
(*CSC: pezza quando i .vo sono magri
try
*)
           if could_have_namesakes o sp then
            begin
             (* this is an uncooked term *)
             print_if_verbose ("OK, stampo solo questa volta " ^ Names.string_of_id id ^ "\n") ;
             print_coq_object o id sp dn !pvars !cumenv ;
             printed := id::!printed
            end
           else
            begin
             (* this is a local term *)
             print_if_verbose ("OK, stampo " ^ Names.string_of_id id ^ "\n") ;
             print_coq_object o id sp dn !pvars !cumenv
            end
(*CSC: pezza quando i .vo sono magri
with _ -> print_if_verbose ("EXCEPTION RAISED!!!\n");
*)
          end
         else
          begin
           (* update the least cooked sp *)
           print_if_verbose ("Suppongo gia' stampato " ^ Names.string_of_id id ^ "\n")
          end
       end
   | L.OpenedSection (dir,_) ->
       let id = snd (Nameops.split_dirpath dir) in
       print_if_verbose ("OpenDir " ^ Names.string_of_id id ^ "\n")
   | L.ClosedSection (_,dir,state) ->
      let id = snd (Nameops.split_dirpath dir) in
      print_if_verbose("ClosedDir " ^ Names.string_of_id id ^ "\n") ;
      if bprintleaf then
       begin
        (* open a new scope *)
        pvars := []::!pvars ;
        print_library_segment state bprintleaf dn ;
        (* close the scope *)
        match !pvars with
           [] -> assert false
         | he::tl -> pvars := tl
       end ;
      print_if_verbose "/ClosedDir\n"
   | L.Module s ->
      print_if_verbose ("Module " ^ (Names.string_of_dirpath s) ^ "\n")
   | L.FrozenState _ ->
      print_if_verbose ("FrozenState\n")
;;

(* print_closed_section module_name node directory_name                      *)
(*  where module_name is the name of a module                                *)
(*  and   node is the library segment of the module                          *)
(*  and   directory_name is the base directory in which to put the xml files *)
(* prints all the leaf objects of the tree rooted in node using              *)
(* print_library_segment on all its sons                                     *)
let print_closed_section s ls dn =
 let module L = Lib in
  printed := [] ;
  pvars := [[]] ;
  cumenv := Safe_typing.env_of_safe_env (Global.safe_env ()) ;
  print_if_verbose ("Module " ^ s ^ ":\n") ;
  print_library_segment ls true dn ;
  print_if_verbose "\n/Module\n" ;
;;

(* printModule identifier directory_name                                     *)
(*  where identifier     is the name of a module (section) d                 *)
(*  and   directory_name is the directory in which to root all the xml files *)
(* prints all the xml files and directories corresponding to the subsections *)
(* and terms of the module d                                                 *)
(* Note: the terms are printed in their uncooked form plus the informations  *)
(* on the parameters of their most cooked form                               *)
let printModule (loc,qid) dn =
 let module L = Library in
 let module N = Nametab in
 let module X = Xml in

  let (_,dir_path,_) = L.locate_qualified_library qid in

  let str = N.string_of_qualid qid in 
  let ls = L.module_segment (Some dir_path) in
   print_if_verbose ("MODULE_BEGIN " ^ str ^ " " ^
    (L.module_full_filename dir_path) ^ "\n") ;
   print_closed_section str (List.rev ls) dn ;
   print_if_verbose ("MODULE_END " ^ str ^ " " ^
    (L.module_full_filename dir_path) ^ "\n")
;;

(* printSection identifier directory_name                                    *)
(*  where identifier     is the name of a closed section d                   *)
(*  and   directory_name is the directory in which to root all the xml files *)
(* prints all the xml files and directories corresponding to the subsections *)
(* and terms of the closed section d                                         *)
(* Note: the terms are printed in their uncooked form plus the informations  *)
(* on the parameters of their most cooked form                               *)
let printSection id dn =
 let module L = Library in
 let module N = Names in
 let module No = Nameops in
 let module X = Xml in
  let sp = Lib.make_path id in
  let ls =
   let rec find_closed_section =
    function
       [] -> raise Not_found
     | (_,Lib.ClosedSection (_,dir,ls))::_ when snd (No.split_dirpath dir) = id
	 -> ls
     | _::t -> find_closed_section t
   in
    print_string ("Searching " ^ Names.string_of_path sp ^ "\n") ;
    find_closed_section (Lib.contents_after None)
  in
  let str = N.string_of_id id in 
   print_if_verbose ("SECTION_BEGIN " ^ str ^ " " ^ N.string_of_path sp ^ "\n");
   print_closed_section str ls dn ;
   print_if_verbose ("SECTION_END " ^ str ^ " " ^ N.string_of_path sp ^ "\n")
;;

(* print All () prints what is the structure of the current environment of *)
(* Coq. No terms are printed. Useful only for debugging                    *)
let printAll () =
 let state = Library.module_segment None in
  let oldverbose = !verbose in
   verbose := true ;
   print_library_segment state false None ;
(*
   let ml = Library.loaded_modules () in
    List.iter (function i -> printModule (Names.id_of_string i) None) ml ;
*)
    verbose := oldverbose
;;


(*CSC: from here on a temporary solution for debugging *)

let rec join_dirs cwd =
 function
    []  -> assert false
  | [he] -> cwd ^ "/" ^ he
  | he::tail ->
     let newcwd = cwd ^ "/" ^ he in
      (try
        Unix.mkdir newcwd 0o775
       with _ -> () (* Let's ignore the errors on mkdir *)
      ) ;
      join_dirs newcwd tail
;;

let filename_of_path ?(keep_sections=false) xml_library_root sp tag =
 let module N = Names in
 let module No = Nameops in
  let dir0 = No.extend_dirpath (No.dirpath sp) (No.basename sp) in
  let dir1 =
   if not keep_sections then
    Cic2acic.remove_sections_from_dirpath dir0
   else
    dir0
  in
  let dir = List.map N.string_of_id (List.rev (N.repr_dirpath dir1)) in
   (join_dirs xml_library_root dir) ^ "." ^ (ext_of_tag tag)
;;

(* Let's register the callbacks *)
let _ =
 let xml_library_root =
  try
   Sys.getenv "XML_LIBRARY_ROOT"
  with Not_found -> "/home/projects/helm/EXPORT/examples7.3/objects"
 in
 let proof_to_export = ref None in (* holds the proof-tree to export *)
  Pfedit.set_xml_cook_proof
   (function pftreestate -> proof_to_export := Some pftreestate) ;
  Declare.set_xml_declare_variable
   (function sp ->
     let filename =
      filename_of_path ~keep_sections:true xml_library_root sp Variable
     in
     let dummy_location = -1,-1 in
      print (dummy_location,Nametab.qualid_of_sp sp) (Some filename)) ;
  Declare.set_xml_declare_constant
   (function sp ->
     let filename = filename_of_path xml_library_root sp Constant in
     match !proof_to_export with
        None ->
         let dummy_location = -1,-1 in
          print (dummy_location,Nametab.qualid_of_sp sp) (Some filename)
      | Some pftreestate ->
         (* It is a proof. Let's export it starting from the proof-tree *)
         (* I saved in the Pfedit.set_xml_cook_proof callback.          *)
         show_pftreestate (Some filename) pftreestate ;
         proof_to_export := None
   ) ;
  Declare.set_xml_declare_inductive
   (function sp ->
     let filename = filename_of_path xml_library_root sp Inductive in
     let dummy_location = -1,-1 in
      print (dummy_location,Nametab.qualid_of_sp sp) (Some filename)) ;
;;
