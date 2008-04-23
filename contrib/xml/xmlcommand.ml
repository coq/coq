(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

(* CONFIGURATION PARAMETERS *)

let verbose = ref false;;

(* HOOKS *)
let print_proof_tree, set_print_proof_tree =
 let print_proof_tree = ref (fun _ _ _ _ _ _ -> None) in
  (fun () -> !print_proof_tree),
   (fun f ->
     print_proof_tree :=
     fun
      curi sigma0 pf proof_tree_to_constr proof_tree_to_flattened_proof_tree
      constr_to_ids
     ->
      Some
       (f curi sigma0 pf proof_tree_to_constr
        proof_tree_to_flattened_proof_tree constr_to_ids))
;;

(* UTILITY FUNCTIONS *)

let print_if_verbose s = if !verbose then print_string s;;

(* Next exception is used only inside print_coq_object and tag_of_string_tag *)
exception Uninteresting;;

(* NOT USED anymore, we back to the V6 point of view with global parameters 

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

*)

(* could_have_namesakes sp = true iff o is an object that could be cooked and *)
(* than that could exists in cooked form with the same name in a super        *)
(* section of the actual section                                              *)
let could_have_namesakes o sp =      (* namesake = omonimo in italian *)
 let module DK = Decl_kinds in
 let module D = Declare in
  let tag = Libobject.object_tag o in
   print_if_verbose ("Object tag: " ^ tag ^ "\n") ;
   match tag with
      "CONSTANT"        -> true   (* constants/parameters are non global *)
    | "INDUCTIVE"       -> true   (* mutual inductive types are never local   *)
    | "VARIABLE"        -> false  (* variables are local, so no namesakes     *)
    | _                 -> false  (* uninteresting thing that won't be printed*)
;;


(* A SIMPLE DATA STRUCTURE AND SOME FUNCTIONS TO MANAGE THE CURRENT *)
(* ENVIRONMENT (= [(name1,l1); ...;(namen,ln)] WHERE li IS THE LIST *)
(* OF VARIABLES DECLARED IN THE i-th SUPER-SECTION OF THE CURRENT   *)
(* SECTION, WHOSE PATH IS namei                                     *)

let pvars = ref ([] : string list);;
let cumenv = ref Environ.empty_env;;

(* filter_params pvars hyps *)
(* filters out from pvars (which is a list of lists) all the variables *)
(* that does not belong to hyps (which is a simple list)               *)
(* It returns a list of couples relative section path -- list of       *)
(* variable names.                                                     *)
let filter_params pvars hyps =
 let rec aux ids =
  function
     [] -> []
   | (id,he)::tl ->
      let ids' = id::ids in
      let ids'' =
       "cic:/" ^
        String.concat "/" (List.rev (List.map Names.string_of_id ids')) in
      let he' =
       ids'', List.rev (List.filter (function x -> List.mem x hyps) he) in
      let tl' = aux ids' tl in
       match he' with
          _,[] -> tl'
        | _,_  -> he'::tl'
 in
  let cwd = Lib.cwd () in
  let cwdsp = Libnames.make_path cwd (Names.id_of_string "dummy") in
  let modulepath = Cic2acic.get_module_path_of_section_path cwdsp in
   aux (Names.repr_dirpath modulepath) (List.rev pvars)
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
  pvars := v::!pvars
;;

(* The computation is very inefficient, but we can't do anything *)
(* better unless this function is reimplemented in the Declare   *)
(* module.                                                       *)
let search_variables () =
 let module N = Names in
  let cwd = Lib.cwd () in
  let cwdsp = Libnames.make_path cwd (Names.id_of_string "dummy") in
  let modulepath = Cic2acic.get_module_path_of_section_path cwdsp in
   let rec aux =
    function
       [] -> []
     | he::tl as modules ->
        let one_section_variables =
         let dirpath = N.make_dirpath (modules @ N.repr_dirpath modulepath) in
          let t = List.map N.string_of_id (Decls.last_section_hyps dirpath) in
           [he,t]
        in
         one_section_variables @ aux tl
   in
    aux
     (Cic2acic.remove_module_dirpath_from_dirpath
       ~basedir:modulepath cwd)
;;

(* FUNCTIONS TO PRINT A SINGLE OBJECT OF COQ *)

let rec join_dirs cwd =
 function
    []  -> cwd
  | he::tail ->
      (try
        Unix.mkdir cwd 0o775
       with _ -> () (* Let's ignore the errors on mkdir *)
      ) ;
     let newcwd = cwd ^ "/" ^ he in
      join_dirs newcwd tail
;;

let filename_of_path xml_library_root tag =
 let module N = Names in
  match xml_library_root with
     None -> None  (* stdout *)
   | Some xml_library_root' ->
      let tokens = Cic2acic.token_list_of_kernel_name tag in
       Some (join_dirs xml_library_root' tokens)
;;

let body_filename_of_filename =
 function
    Some f -> Some (f ^ ".body")
  | None   -> None
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

let theory_filename xml_library_root =
 let module N = Names in
  match xml_library_root with
    None -> None  (* stdout *)
  | Some xml_library_root' ->
     let toks = List.map N.string_of_id (N.repr_dirpath (Lib.library_dp ())) in
     (* theory from A/B/C/F.v goes into A/B/C/F.theory *)
     let alltoks = List.rev toks in
       Some (join_dirs xml_library_root' alltoks ^ ".theory")

let print_object uri obj sigma proof_tree_infos filename =
 (* function to pretty print and compress an XML file *)
(*CSC: Unix.system "gzip ..." is an horrible non-portable solution. *)
 let pp xml filename =
  Xml.pp xml filename ;
  match filename with
     None -> ()
   | Some fn ->
      let fn' =
       let rec escape s n =
        try
         let p = String.index_from s n '\'' in
          String.sub s n (p - n) ^ "\\'" ^ escape s (p+1)
        with Not_found -> String.sub s n (String.length s - n)
       in
        escape fn 0
      in
       ignore (Unix.system ("gzip " ^ fn' ^ ".xml"))
 in
  let (annobj,_,constr_to_ids,_,ids_to_inner_sorts,ids_to_inner_types,_,_) =
   Cic2acic.acic_object_of_cic_object !pvars sigma obj in
  let (xml, xml') = Acic2Xml.print_object uri ids_to_inner_sorts annobj in
  let xmltypes =
   Acic2Xml.print_inner_types uri ids_to_inner_sorts ids_to_inner_types in
  pp xml filename ;
  begin
   match xml' with
      None -> ()
    | Some xml' -> pp xml' (body_filename_of_filename filename)
  end ;
  pp xmltypes (types_filename_of_filename filename) ;
  match proof_tree_infos with
     None -> ()
   | Some (sigma0,proof_tree,proof_tree_to_constr,
           proof_tree_to_flattened_proof_tree) ->
      let xmlprooftree =
       print_proof_tree ()
        uri sigma0 proof_tree proof_tree_to_constr
        proof_tree_to_flattened_proof_tree constr_to_ids
      in
       match xmlprooftree with
          None -> ()
        | Some xmlprooftree ->
           pp xmlprooftree (prooftree_filename_of_filename filename)
;;

let string_list_of_named_context_list =
 List.map
  (function (n,_,_) -> Names.string_of_id n)
;;

(* Function to collect the variables that occur in a term. *)
(* Used only for variables (since for constants and mutual *)
(* inductive types this information is already available.  *)
let find_hyps t =
 let module T = Term in
  let rec aux l t =
   match T.kind_of_term t with
      T.Var id when not (List.mem id l) ->
       let (_,bo,ty) = Global.lookup_named id in
        let boids = 
         match bo with
            Some bo' -> aux l bo'
          | None -> l
        in
         id::(aux boids ty)
    | T.Var _
    | T.Rel _
    | T.Meta _
    | T.Evar _
    | T.Sort _ -> l
    | T.Cast (te,_, ty) -> aux (aux l te) ty
    | T.Prod (_,s,t) -> aux (aux l s) t
    | T.Lambda (_,s,t) -> aux (aux l s) t
    | T.LetIn (_,s,_,t) -> aux (aux l s) t
    | T.App (he,tl) -> Array.fold_left (fun i x -> aux i x) (aux l he) tl
    | T.Const con ->
       let hyps = (Global.lookup_constant con).Declarations.const_hyps in
        map_and_filter l hyps @ l
    | T.Ind ind
    | T.Construct (ind,_) ->
       let hyps = (fst (Global.lookup_inductive ind)).Declarations.mind_hyps in
        map_and_filter l hyps @ l
    | T.Case (_,t1,t2,b) ->
       Array.fold_left (fun i x -> aux i x) (aux (aux l t1) t2) b
    | T.Fix (_,(_,tys,bodies))
    | T.CoFix (_,(_,tys,bodies)) ->
       let r = Array.fold_left (fun i x -> aux i x) l tys in
        Array.fold_left (fun i x -> aux i x) r bodies
  and map_and_filter l =
   function
      [] -> []
    | (n,_,_)::tl when not (List.mem n l) -> n::(map_and_filter l tl)
    | _::tl -> map_and_filter l tl
  in
   aux [] t
;;

(* Functions to construct an object *)

let mk_variable_obj id body typ =
 let hyps,unsharedbody =
  match body with
     None -> [],None
   | Some bo -> find_hyps bo, Some (Unshare.unshare bo)
 in
  let hyps' = find_hyps typ @ hyps in
  let hyps'' = List.map Names.string_of_id hyps' in
  let variables = search_variables () in
  let params = filter_params variables hyps'' in
   Acic.Variable
    (Names.string_of_id id, unsharedbody, Unshare.unshare typ, params)
;;

(* Unsharing is not performed on the body, that must be already unshared. *)
(* The evar map and the type, instead, are unshared by this function.     *)
let mk_current_proof_obj is_a_variable id bo ty evar_map env =
 let unshared_ty = Unshare.unshare ty in
 let metasenv =
  List.map
   (function
     (n, {Evd.evar_concl = evar_concl ;
          Evd.evar_hyps = evar_hyps}
      ) ->
       (* We map the named context to a rel context and every Var to a Rel *)
       let final_var_ids,context =
        let rec aux var_ids =
         function
            [] -> var_ids,[]
          | (n,None,t)::tl ->
              let final_var_ids,tl' = aux (n::var_ids) tl in
              let t' = Term.subst_vars var_ids t in
               final_var_ids,(n, Acic.Decl (Unshare.unshare t'))::tl'
          | (n,Some b,t)::tl ->
              let final_var_ids,tl' = aux (n::var_ids) tl in
              let b' = Term.subst_vars var_ids b in
               (* t will not be exported to XML. Thus no unsharing performed *)
               final_var_ids,(n, Acic.Def  (Unshare.unshare b',t))::tl'
        in
         aux [] (List.rev (Environ.named_context_of_val evar_hyps))
       in
        (* We map the named context to a rel context and every Var to a Rel *)
        (n,context,Unshare.unshare (Term.subst_vars final_var_ids evar_concl))
   ) (Evarutil.non_instantiated evar_map)
 in
  let id' = Names.string_of_id id in
   if metasenv = [] then
    let ids =
     Names.Idset.union
      (Environ.global_vars_set env bo) (Environ.global_vars_set env ty) in
    let hyps0 = Environ.keep_hyps env ids in
    let hyps = string_list_of_named_context_list hyps0 in
    (* Variables are the identifiers of the variables in scope *)
    let variables = search_variables () in
    let params = filter_params variables hyps in
     if is_a_variable then
      Acic.Variable (id',Some bo,unshared_ty,params)
     else
      Acic.Constant (id',Some bo,unshared_ty,params)
   else
    Acic.CurrentProof (id',metasenv,bo,unshared_ty)
;;

let mk_constant_obj id bo ty variables hyps =
 let hyps = string_list_of_named_context_list hyps in
 let ty = Unshare.unshare ty in
 let params = filter_params variables hyps in
  match bo with
     None ->
      Acic.Constant (Names.string_of_id id,None,ty,params)
   | Some c ->
      Acic.Constant
       (Names.string_of_id id, Some (Unshare.unshare (Declarations.force c)),
         ty,params)
;;

let mk_inductive_obj sp mib packs variables nparams hyps finite =
 let module D = Declarations in
  let hyps = string_list_of_named_context_list hyps in
  let params = filter_params variables hyps in
(*  let nparams = extract_nparams packs in *)
   let tys =
    let tyno = ref (Array.length packs) in
    Array.fold_right
     (fun p i ->
       decr tyno ;
       let {D.mind_consnames=consnames ;
            D.mind_typename=typename } = p
       in
        let arity = Inductive.type_of_inductive (Global.env()) (mib,p) in
        let lc = Inductiveops.arities_of_constructors (Global.env ()) (sp,!tyno) in
        let cons =
         (Array.fold_right (fun (name,lc) i -> (name,lc)::i)
          (Array.mapi
           (fun j x ->(x,Unshare.unshare lc.(j))) consnames)
          []
         )
        in
         (typename,finite,Unshare.unshare arity,cons)::i
     ) packs []
   in
    Acic.InductiveDefinition (tys,params,nparams)
;;

(* The current channel for .theory files *)
let theory_buffer = Buffer.create 4000;;

let theory_output_string ?(do_not_quote = false) s = 
  (* prepare for coqdoc post-processing *)
  let s = if do_not_quote then s else "(** #"^s^"\n#*)\n" in
  print_if_verbose s;
   Buffer.add_string theory_buffer s
;;

let kind_of_global_goal = function
  | Decl_kinds.Global, Decl_kinds.DefinitionBody _ -> "DEFINITION","InteractiveDefinition"
  | Decl_kinds.Global, (Decl_kinds.Proof k) -> "THEOREM",Decl_kinds.string_of_theorem_kind k
  | Decl_kinds.Local, _ -> assert false

let kind_of_inductive isrecord kn =
 "DEFINITION",
 if (fst (Global.lookup_inductive (kn,0))).Declarations.mind_finite
 then if isrecord then "Record" else "Inductive"
 else "CoInductive"
;;

let kind_of_variable id =
  let module DK = Decl_kinds in
  match Decls.variable_kind id with
    | DK.IsAssumption DK.Definitional -> "VARIABLE","Assumption"
    | DK.IsAssumption DK.Logical -> "VARIABLE","Hypothesis"
    | DK.IsAssumption DK.Conjectural -> "VARIABLE","Conjecture"
    | DK.IsDefinition DK.Definition -> "VARIABLE","LocalDefinition"
    | DK.IsProof _ -> "VARIABLE","LocalFact"
    | _ -> Util.anomaly "Unsupported variable kind"
;;

let kind_of_constant kn = 
  let module DK = Decl_kinds in
  match Decls.constant_kind kn with
    | DK.IsAssumption DK.Definitional -> "AXIOM","Declaration"
    | DK.IsAssumption DK.Logical -> "AXIOM","Axiom"
    | DK.IsAssumption DK.Conjectural ->
        Pp.warning "Conjecture not supported in dtd (used Declaration instead)";
        "AXIOM","Declaration"
    | DK.IsDefinition DK.Definition -> "DEFINITION","Definition"
    | DK.IsDefinition DK.Example -> 
        Pp.warning "Example not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.Coercion ->
        Pp.warning "Coercion not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.SubClass ->
        Pp.warning "SubClass not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.CanonicalStructure ->
        Pp.warning "CanonicalStructure not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.Fixpoint ->
        Pp.warning "Fixpoint not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.CoFixpoint ->
        Pp.warning "CoFixpoint not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.Scheme ->
        Pp.warning "Scheme not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.StructureComponent ->
        Pp.warning "StructureComponent not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.IdentityCoercion ->
        Pp.warning "IdentityCoercion not supported in dtd (used Definition instead)";
        "DEFINITION","Definition"
    | DK.IsDefinition DK.Instance ->
        Pp.warning "Instance not supported in dtd (used Definition instead)";
        "DEFINITION","Definition" 
   | DK.IsProof (DK.Theorem|DK.Lemma|DK.Corollary|DK.Fact|DK.Remark as thm) ->
        "THEOREM",DK.string_of_theorem_kind thm
    | DK.IsProof _ ->
        Pp.warning "Unsupported theorem kind (used Theorem instead)";
        "THEOREM",DK.string_of_theorem_kind DK.Theorem
;;

let kind_of_global r =
  let module Ln = Libnames in
  let module DK = Decl_kinds in
  match r with
  | Ln.IndRef kn | Ln.ConstructRef (kn,_) -> 
      let isrecord =
	try let _ = Recordops.lookup_projections kn in true
        with Not_found -> false in
      kind_of_inductive isrecord (fst kn)
  | Ln.VarRef id -> kind_of_variable id
  | Ln.ConstRef kn -> kind_of_constant kn
;;

let print_object_kind uri (xmltag,variation) =
  let s =
    Printf.sprintf "<ht:%s uri=\"%s\" as=\"%s\"/>\n" xmltag uri variation
  in
  theory_output_string s
;;

(* print id dest                                                          *)
(*  where sp   is the qualified identifier (section path) of a            *)
(*             definition/theorem, variable or inductive definition       *)
(*  and   dest is either None (for stdout) or (Some filename)             *)
(* pretty prints via Xml.pp the object whose identifier is id on dest     *)
(* Note: it is printed only (and directly) the most cooked available      *)
(*       form of the definition (all the parameters are                   *)
(*       lambda-abstracted, but the object can still refer to variables)  *)
let print internal glob_ref kind xml_library_root =
 let module D = Declarations in
 let module De = Declare in
 let module G = Global in
 let module N = Names in
 let module Nt = Nametab in
 let module T = Term in
 let module X = Xml in
 let module Ln = Libnames in
  (* Variables are the identifiers of the variables in scope *)
  let variables = search_variables () in
  let tag,obj =
   match glob_ref with
      Ln.VarRef id ->
       (* this kn is fake since it is not provided by Coq *)
       let kn = 
        let (mod_path,dir_path) = Lib.current_prefix () in
        N.make_kn mod_path dir_path (N.label_of_id id)
       in
       let (_,body,typ) = G.lookup_named id in
        Cic2acic.Variable kn,mk_variable_obj id body typ
    | Ln.ConstRef kn ->
       let id = N.id_of_label (N.con_label kn) in
       let {D.const_body=val0 ; D.const_type = typ ; D.const_hyps = hyps} =
        G.lookup_constant kn in
       let typ = Typeops.type_of_constant_type (Global.env()) typ in
        Cic2acic.Constant kn,mk_constant_obj id val0 typ variables hyps
    | Ln.IndRef (kn,_) ->
       let mib = G.lookup_mind kn in
       let {D.mind_nparams=nparams;
	    D.mind_packets=packs ;
            D.mind_hyps=hyps;
            D.mind_finite=finite} = mib in
          Cic2acic.Inductive kn,mk_inductive_obj kn mib packs variables nparams hyps finite
    | Ln.ConstructRef _ ->
       Util.error ("a single constructor cannot be printed in XML")
  in
  let fn = filename_of_path xml_library_root tag in
  let uri = Cic2acic.uri_of_kernel_name tag in
   if not internal then print_object_kind uri kind;
   print_object uri obj Evd.empty None fn
;;

let print_ref qid fn =
  let ref = Nametab.global qid in
  print false ref (kind_of_global ref) fn

(* show dest                                                  *)
(*  where dest is either None (for stdout) or (Some filename) *)
(* pretty prints via Xml.pp the proof in progress on dest     *)
let show_pftreestate internal fn (kind,pftst) id =
 let pf = Tacmach.proof_of_pftreestate pftst in
 let typ = (Proof_trees.goal_of_proof pf).Evd.evar_concl in
 let val0,evar_map,proof_tree_to_constr,proof_tree_to_flattened_proof_tree,
     unshared_pf
 =
  Proof2aproof.extract_open_pftreestate pftst in
 let env = Global.env () in
 let obj =
  mk_current_proof_obj (fst kind = Decl_kinds.Local) id val0 typ evar_map env in
 let uri =
  match kind with
     Decl_kinds.Local, _ ->
      let uri =
       "cic:/" ^ String.concat "/"
        (Cic2acic.token_list_of_path (Lib.cwd ()) id Cic2acic.TVariable)
      in
      let kind_of_var = "VARIABLE","LocalFact" in
       if not internal then print_object_kind uri kind_of_var;
      uri
   | Decl_kinds.Global, _ ->
      let uri = Cic2acic.uri_of_declaration id Cic2acic.TConstant in
       if not internal then print_object_kind uri (kind_of_global_goal kind);
       uri
 in
  print_object uri obj evar_map
   (Some (Tacmach.evc_of_pftreestate pftst,unshared_pf,proof_tree_to_constr,
    proof_tree_to_flattened_proof_tree)) fn
;;

let show fn =
 let pftst = Pfedit.get_pftreestate () in
 let (id,kind,_,_) = Pfedit.current_proof_statement () in
  show_pftreestate false fn (kind,pftst) id
;;


(* Let's register the callbacks *)
let xml_library_root =
  try
   Some (Sys.getenv "COQ_XML_LIBRARY_ROOT")
  with Not_found -> None
;;

let proof_to_export = ref None (* holds the proof-tree to export *)
;;

let _ =
  Pfedit.set_xml_cook_proof
   (function pftreestate -> proof_to_export := Some pftreestate)
;;

let _ =
  Declare.set_xml_declare_variable
   (function (sp,kn) ->
     let id = Libnames.basename sp in
     print false (Libnames.VarRef id) (kind_of_variable id) xml_library_root ;
     proof_to_export := None)
;;

let _ =
  Declare.set_xml_declare_constant
   (function (internal,kn) ->
     match !proof_to_export with
        None ->
          print internal (Libnames.ConstRef kn) (kind_of_constant kn) 
	    xml_library_root
      | Some pftreestate ->
         (* It is a proof. Let's export it starting from the proof-tree *)
         (* I saved in the Pfedit.set_xml_cook_proof callback.          *)
        let fn = filename_of_path xml_library_root (Cic2acic.Constant kn) in
         show_pftreestate internal fn pftreestate 
	  (Names.id_of_label (Names.con_label kn)) ;
         proof_to_export := None)
;;

let _ =
  Declare.set_xml_declare_inductive
   (function (isrecord,(sp,kn)) ->
      print false (Libnames.IndRef (kn,0)) (kind_of_inductive isrecord kn) 
        xml_library_root)
;;

let _ =
  Vernac.set_xml_start_library
   (function () ->
     Buffer.reset theory_buffer;
     theory_output_string "<?xml version=\"1.0\" encoding=\"latin1\"?>\n";
     theory_output_string ("<!DOCTYPE html [\n" ^
      "<!ENTITY % xhtml-lat1.ent    SYSTEM \"http://helm.cs.unibo.it/dtd/xhtml-lat1.ent\">\n" ^
      "<!ENTITY % xhtml-special.ent SYSTEM \"http://helm.cs.unibo.it/dtd/xhtml-special.ent\">\n" ^
      "<!ENTITY % xhtml-symbol.ent  SYSTEM \"http://helm.cs.unibo.it/dtd/xhtml-symbol.ent\">\n\n" ^
      "%xhtml-lat1.ent;\n" ^
      "%xhtml-special.ent;\n" ^
      "%xhtml-symbol.ent;\n" ^
      "]>\n\n");
     theory_output_string "<html xmlns=\"http://www.w3.org/1999/xhtml\" xmlns:ht=\"http://www.cs.unibo.it/helm/namespaces/helm-theory\" xmlns:helm=\"http://www.cs.unibo.it/helm\">\n";
     theory_output_string "<head></head>\n<body>\n")
;;

let _ =
  Vernac.set_xml_end_library
   (function () ->
      theory_output_string "</body>\n</html>\n";
      let ofn = theory_filename xml_library_root in
       begin
        match ofn with
           None ->
             Buffer.output_buffer stdout theory_buffer ;
         | Some fn ->
            let ch = open_out (fn ^ ".v") in
             Buffer.output_buffer ch theory_buffer ;
             close_out ch
       end ;
       Option.iter 
	(fun fn ->
	  let coqdoc = Coq_config.bindir^"/coqdoc" in
	  let options = " --html -s --body-only --no-index --latin1 --raw-comments" in
	  let dir = Option.get xml_library_root in
          let command cmd =
           if Sys.command cmd <> 0 then
            Util.anomaly ("Error executing \"" ^ cmd ^ "\"")
          in
           command (coqdoc^options^" -d "^dir^" "^fn^".v");
           let dot = if fn.[0]='/' then "." else "" in
           command ("mv "^dir^"/"^dot^"*.html "^fn^".xml ");
           command ("rm "^fn^".v");
           print_string("\nWriting on file \"" ^ fn ^ ".xml\" was successful\n"))
       ofn)
;;

let _ = Lexer.set_xml_output_comment (theory_output_string ~do_not_quote:true) ;;

let uri_of_dirpath dir =
  "/" ^ String.concat "/" 
    (List.map Names.string_of_id (List.rev (Names.repr_dirpath dir)))
;;

let _ =
  Lib.set_xml_open_section
    (fun _ ->
      let s = "cic:" ^ uri_of_dirpath (Lib.cwd ()) in
      theory_output_string ("<ht:SECTION uri=\""^s^"\">"))
;;

let _ =
  Lib.set_xml_close_section
    (fun _ -> theory_output_string "</ht:SECTION>")
;;

let _ =
  Library.set_xml_require
    (fun d -> theory_output_string 
      (Printf.sprintf "<b>Require</b> <a helm:helm_link=\"href\" href=\"theory:%s.theory\">%s</a>.<br/>"
       (uri_of_dirpath d) (Names.string_of_dirpath d)))
;;
