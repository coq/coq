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

let verbose = ref false;; (* always set to true during a "Print XML All" *)

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
 let module DK = Decl_kinds in
 let module D = Declare in
  let tag = Libobject.object_tag o in
   print_if_verbose ("Object tag: " ^ tag ^ "\n") ;
   match tag with
      "CONSTANT" ->
        (match D.constant_strength sp with
          | DK.Local  -> false (* a local definition *)
          | DK.Global -> true  (* a non-local one    *)
        )
    | "INDUCTIVE"       -> true   (* mutual inductive types are never local   *)
    | "VARIABLE"        -> false  (* variables are local, so no namesakes     *)
    | _                 -> false  (* uninteresting thing that won't be printed*)
;;


(* A SIMPLE DATA STRUCTURE AND SOME FUNCTIONS TO MANAGE THE CURRENT *)
(* ENVIRONMENT (= [(name1,l1); ...;(namen,ln)] WHERE li IS THE LIST *)
(* OF VARIABLES DECLARED IN THE i-th SUPER-SECTION OF THE CURRENT   *)
(* SECTION, WHOSE PATH IS namei                                     *)

let pvars =
 ref ([Names.id_of_string "",[]] : (Names.identifier * string list) list);;
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
   match !pvars with
      []       -> assert false
    | ((name,l)::tl) -> pvars := (name,v::l)::tl
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
          let t = List.map N.string_of_id (Declare.last_section_hyps dirpath) in
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

let filename_of_path ?(keep_sections=false) xml_library_root kn tag =
 let module N = Names in
  match xml_library_root with
     None -> None  (* stdout *)
   | Some xml_library_root' ->
      let tokens = Cic2acic.token_list_of_kernel_name ~keep_sections kn tag in
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
     let hd = List.hd toks in
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
    | T.Cast (te,ty) -> aux (aux l te) ty
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
    (Names.string_of_id id, unsharedbody,
     (Unshare.unshare (Term.body_of_type typ)), params)
;;

(* Unsharing is not performed on the body, that must be already unshared. *)
(* The evar map and the type, instead, are unshared by this function.     *)
let mk_current_proof_obj id bo ty evar_map env =
 let unshared_ty = Unshare.unshare (Term.body_of_type ty) in
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
         aux [] (List.rev evar_hyps)
       in
        (* We map the named context to a rel context and every Var to a Rel *)
        (n,context,Unshare.unshare (Term.subst_vars final_var_ids evar_concl))
   ) (Evd.non_instantiated evar_map)
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
     Acic.Constant (id',Some bo,unshared_ty,params)
   else
    Acic.CurrentProof (id',metasenv,bo,unshared_ty)
;;

let mk_constant_obj id bo ty variables hyps =
 let hyps = string_list_of_named_context_list hyps in
 let ty = Unshare.unshare (Term.body_of_type ty) in
 let params = filter_params variables hyps in
  match bo with
     None ->
      Acic.Constant (Names.string_of_id id,None,ty,params)
   | Some c ->
      Acic.Constant
       (Names.string_of_id id, Some (Unshare.unshare (Declarations.force c)),
         ty,params)
;;

let mk_inductive_obj sp packs variables hyps finite =
 let module D = Declarations in
  let hyps = string_list_of_named_context_list hyps in
  let params = filter_params variables hyps in
  let nparams = extract_nparams packs in
   let tys =
    let tyno = ref (Array.length packs) in
    Array.fold_right
     (fun p i ->
       decr tyno ;
       let {D.mind_consnames=consnames ;
            D.mind_typename=typename ;
            D.mind_nf_arity=arity} = p
       in
        let lc = Inductive.arities_of_constructors (Global.env ()) (sp,!tyno) in
        let cons =
         (Array.fold_right (fun (name,lc) i -> (name,lc)::i)
          (Array.mapi
           (fun j x ->(x,Unshare.unshare (Term.body_of_type lc.(j)))) consnames)
          []
         )
        in
         (typename,finite,Unshare.unshare arity,cons)::i
     ) packs []
   in
    Acic.InductiveDefinition (tys,params,nparams)
;;

(* The current channel for .theory files *)
let theory_channel = ref None;;

let theory_output_string s = 
  (* prepare for coqdoc post-processing *)
  let s = "(** #"^s^"\n#*)\n" in
  match !theory_channel with
     Some ch -> output_string ch s;
   | None -> print_string s; flush stdout
;;

let kind_of_object r =
  let module Ln = Libnames in
  let module DK = Decl_kinds in
  match r with
    Ln.IndRef kn -> "DEFINITION",
      if (fst (Global.lookup_inductive kn)).Declarations.mind_finite then
        try let _ = Recordops.find_structure kn in "Record"
        with Not_found -> "Inductive"
      else "CoInductive"
  | Ln.VarRef id ->
      (match Declare.variable_kind id with
      | DK.IsAssumption DK.Definitional -> "VARIABLE","Assumption"
      | DK.IsAssumption DK.Logical -> "VARIABLE","Hypothesis"
      | DK.IsAssumption DK.Conjectural -> "VARIABLE","Conjecture"
      | DK.IsDefinition -> "VARIABLE","LocalDefinition"
      | DK.IsConjecture -> "VARIABLE","Conjecture"
      | DK.IsProof DK.LocalStatement -> "VARIABLE","Hypothesis")
  | Ln.ConstRef sp ->
      (match Declare.constant_kind (Nametab.sp_of_global r) with
      | DK.IsAssumption DK.Definitional -> "AXIOM","Declaration"
      | DK.IsAssumption DK.Logical -> "AXIOM","Axiom"
      | DK.IsAssumption DK.Conjectural -> "AXIOM","Conjecture"
      | DK.IsDefinition -> "DEFINITION","Definition"
      | DK.IsConjecture -> "THEOREM","Conjecture"
      | DK.IsProof thm -> "THEOREM",
          match thm with
          | DK.Theorem -> "Theorem"
          | DK.Lemma -> "Lemma"
          | DK.Fact -> "Fact"
          | DK.Remark -> "Remark")
  | Ln.ConstructRef _ -> 
       Util.anomaly ("print: this should not happen")
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
let print glob_ref xml_library_root =
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
  let keep_sections,kn,tag,obj =
   match glob_ref with
      Ln.VarRef id ->
       let sp = Declare.find_section_variable id in
       (* this kn is fake since it is not provided by Coq *)
       let kn = 
        let (mod_path,dir_path) = Lib.current_prefix () in
        N.make_kn mod_path dir_path (N.label_of_id (Ln.basename sp))
       in
       let (_,body,typ) = G.lookup_named id in
        true,kn,Cic2acic.Variable,mk_variable_obj id body typ
    | Ln.ConstRef kn ->
       let id = N.id_of_label (N.label kn) in
       let {D.const_body=val0 ; D.const_type = typ ; D.const_hyps = hyps} =
        G.lookup_constant kn in
        false,kn,Cic2acic.Constant,mk_constant_obj id val0 typ variables hyps
    | Ln.IndRef (kn,_) ->
       let {D.mind_packets=packs ;
            D.mind_hyps=hyps;
            D.mind_finite=finite} = G.lookup_mind kn in
          false,kn,Cic2acic.Inductive,
           mk_inductive_obj kn packs variables hyps finite
    | Ln.ConstructRef _ ->
       Util.anomaly ("print: this should not happen")
  in
  let fn = filename_of_path ~keep_sections xml_library_root kn tag in
  let uri = Cic2acic.uri_of_kernel_name ~keep_sections kn tag in
   print_object_kind uri (kind_of_object glob_ref);
   print_object uri obj Evd.empty None fn
;;

(* show dest                                                  *)
(*  where dest is either None (for stdout) or (Some filename) *)
(* pretty prints via Xml.pp the proof in progress on dest     *)
let show_pftreestate fn pftst id =
 let str = Names.string_of_id id in
 let pf = Tacmach.proof_of_pftreestate pftst in
 let typ = (Proof_trees.goal_of_proof pf).Evd.evar_concl in
 let val0,evar_map,proof_tree_to_constr,proof_tree_to_flattened_proof_tree,
     unshared_pf
 =
  Proof2aproof.extract_open_pftreestate pftst in
 let kn = Lib.make_kn id in
 let env = Global.env () in
 let obj = mk_current_proof_obj id val0 typ evar_map env in
 let uri = Cic2acic.uri_of_kernel_name kn Cic2acic.Constant in
  print_object_kind uri  (kind_of_object (Libnames.ConstRef kn));
  print_object uri obj evar_map
   (Some (Tacmach.evc_of_pftreestate pftst,unshared_pf,proof_tree_to_constr,
    proof_tree_to_flattened_proof_tree)) fn
;;

let show fn =
 let pftst = Pfedit.get_pftreestate () in
 let id = Pfedit.get_current_proof_name () in
  show_pftreestate fn pftst id
;;

(*
(* FUNCTIONS TO PRINT AN ENTIRE SECTION OF COQ *)

(* list of (name, uncooked sp, most cooked sp, uncooked leaf object,  *)
(*          list of possible variables, directory name)               *)
(* used to collect informations on the uncooked and most cooked forms *)
(* of objects that could be cooked (have namesakes)                   *)
let printed = ref [];;

(* makes a filename from a directory name, a section path and an extension *)
let mkfilename dn sp ext =
(*CSC:
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
  let module L = Library in
  let module S = System in
  let module N = Names in
  let module No = Nameops in
   match dn with
      None         -> None
    | Some basedir ->
	let dir0 = No.extend_dirpath (No.dirpath sp) (No.basename sp) in
	let dir = List.map N.string_of_id (List.rev (N.repr_dirpath dir0)) in
       Some (join_dirs basedir dir ^ "." ^ ext)
*) match dn with None -> None | Some _ -> Some "/tmp/nonloso"
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
        "CONSTANT"  (* = Definition, Theorem, Axiom *)
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
            mk_inductive_obj sp packs fv hyps finite
      | "VARIABLE" ->
          let (_,(_,varentry,_)) = Declare.out_variable lobj in
           begin
            match varentry with
               Declare.SectionLocalDef (body,optt,opaq) ->
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
        let (_,section_name) = Nameops.split_dirpath dir in
         pvars := (section_name,[])::!pvars ;
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
  pvars := [Names.id_of_string "",[]] ;
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
*)


(*CSC: Ask Hugo for a better solution *)
(*
let ref_of_kernel_name kn =
 let module N = Names in
 let module Ln = Libnames in
  let (modpath,_,label) = N.repr_kn kn in
   match modpath with
      N.MPself _ -> Ln.Qualid (Ln.qualid_of_sp (Nametab.sp_of_global None kn))
    | _ ->
      Util.anomaly ("ref_of_kernel_name: the module path is not MPself")
;;
*)

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
      print (Libnames.VarRef (Libnames.basename sp)) xml_library_root)
;;

let _ =
  Declare.set_xml_declare_constant
   (function (sp,kn) ->
     match !proof_to_export with
        None ->
          print (Libnames.ConstRef kn) xml_library_root
      | Some pftreestate ->
         (* It is a proof. Let's export it starting from the proof-tree *)
         (* I saved in the Pfedit.set_xml_cook_proof callback.          *)
        let fn = filename_of_path xml_library_root kn Cic2acic.Constant in
         show_pftreestate fn pftreestate 
	  (Names.id_of_label (Names.label kn)) ;
         proof_to_export := None)
;;

let _ =
  Declare.set_xml_declare_inductive
   (function (sp,kn) ->
      print (Libnames.IndRef (kn,0)) xml_library_root)
;;

let _ =
  Vernac.set_xml_start_library
   (function () ->
     print_string "B";
     theory_channel :=
       Util.option_app (fun fn -> open_out (fn^".v"))
	 (theory_filename xml_library_root);
     print_string "C";
     theory_output_string "<?xml version=\"1.0\" encoding=\"latin1\"?>\n";
     theory_output_string "<html xmlns=\"http://www.w3.org/1999/xhtml\" xmlns:ht=\"http://www.cs.unibo.it/helm/namespaces/helm-theory\">\n";
     theory_output_string "<head>\n<style> A { text-decoration: none } </style>\n</head>\n")
;;

let _ =
  Vernac.set_xml_end_library
   (function () ->
      theory_output_string "</html>\n";
      Util.option_iter close_out !theory_channel;
      Util.option_iter 
	(fun fn ->
	  let coqdoc = Coq_config.bindir^"/coqdoc" in
	  let options = " --html -s --body-only --no-index --latin1 --raw-comments" in
	  let dir = Util.out_some xml_library_root in
          let command cmd =
           if Sys.command cmd <> 0 then
            Util.anomaly ("Error executing \"" ^ cmd ^ "\"")
          in
           command (coqdoc^options^" -d "^dir^" "^fn^".v");
           let dot = if fn.[0]='/' then "." else "" in
           command ("mv "^dir^"/"^dot^"*.html "^fn^".xml ");
           (*command ("rm "^fn^".v");*)
           print_string("\nWriting on file \"" ^ fn ^ ".xml\" was succesful\n"))
       (theory_filename xml_library_root))
;;

let _ =
  Lexer.set_xml_output_comment
    (fun s ->
      output_string (match !theory_channel with Some ch -> ch | _ -> stdout) s)
;;

let _ =
  Lib.set_xml_open_section
    (fun id ->
      print_string "A";
      let s = Names.string_of_id id in
      theory_output_string ("<ht:SECTION name=\""^s^"\">"))
;;

let _ =
  Lib.set_xml_close_section
    (fun _ -> theory_output_string "</ht:SECTION>")
;;
