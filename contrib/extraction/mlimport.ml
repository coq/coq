
(*i $Id$ i*)

open Pp

(* TODO : move this function to another file, like more_util. *)

let list0n = 
  let rec gen acc = function
      -1 -> acc
    | n  -> gen (n::acc) (n-1)
  in 
  gen []

(* get a fresh name if necessary *)
let rec next_global_ident id =
  if not (is_global id) then id else next_global_ident (lift_ident id)

(*s Importing ML objects, and linking axioms to terms. *)

(* A table to keep the ML imports. *)

let ml_import_tab = (Hashtabl.create 17 : (sorts oper, identifier) Hashtabl.t)

let mL_INDUCTIVES = ref ([] : section_path list)

let add_ml_inductive_import sp =
  if not (List.mem sp !mL_INDUCTIVES) then
    mL_INDUCTIVES := sp :: !mL_INDUCTIVES

let add_ml_import imp id =
  Hashtabl.add ml_import_tab imp id ;
  match imp with
    MutInd (sp,_) -> add_ml_inductive_import sp
  | _ -> ()

let find_ml_import imp = Hashtabl.find ml_import_tab imp

let is_ml_import op =
  try let _ = find_ml_import op in true with Not_found -> false

let sp_is_ml_import sp =
     (is_ml_import (Const sp))
  or (is_ml_import (MutInd (sp,0)))
  or (is_ml_import (MutConstruct ((sp,0),1)))

let sp_prod = path_of_string "#Datatypes#prod.fw"

let sp_is_ml_import_or_prod sp =
  (sp = sp_prod) or (sp_is_ml_import sp)

let inMLImport,outMLImport =
  declare_object ("MLIMPORT",
     {load_function = (fun _ -> ());
      cache_function         = (fun (_,(imp,id)) -> add_ml_import imp id) ;
      specification_function = (fun x -> x) })

(* A table to keep the extractions to ML objects *)

let ml_extract_tab = (Hashtabl.create 17 : (sorts oper, identifier) Hashtabl.t)

let add_ml_extract op id =
  Hashtabl.add ml_extract_tab op id;
  match op with 
      MutInd (sp,_) -> add_ml_inductive_import sp
    | _ -> ()

let find_ml_extract = Hashtabl.find ml_extract_tab

let is_ml_extract op = 
  try let _ = find_ml_extract op in true with Not_found -> false

let sp_is_ml_extract sp =
     (is_ml_extract (Const sp))
  or (is_ml_extract (MutInd (sp,0)))
  or (is_ml_extract (MutConstruct ((sp,0),1)))

let inMLExtract,outMLExtract =
  declare_object ("MLEXTRACT",
     {load_function = (fun _ -> ());
      cache_function         = (fun (_,(op,id)) -> add_ml_extract op id) ;
      specification_function = (fun x -> x) })

let is_import_or_extract sp = sp_is_ml_import sp or sp_is_ml_extract sp

(* Those two tables are rolled-back *)

let freeze () =
  (Hashtabl.freeze ml_import_tab, !mL_INDUCTIVES,
   Hashtabl.freeze ml_extract_tab)

let unfreeze (ft,stk,et) =
  Hashtabl.unfreeze ft ml_import_tab;
  mL_INDUCTIVES := stk;
  Hashtabl.unfreeze et ml_extract_tab

let _ = declare_summary "MLIMPORT-TABLE"
  { freeze_function   = freeze ;
    unfreeze_function = unfreeze ;
    init_function     = (fun () -> Hashtabl.clear ml_import_tab;
      	       	       	       	   mL_INDUCTIVES := [];
				   Hashtabl.clear ml_extract_tab) }

(* Replace CCI section_path with FW section_path in a term. *)

let whd_fwify = function
    DOPN(Const sp,cl)               -> DOPN(Const (fwsp_of sp),cl)
  | DOPN(MutInd(sp,i),cl)           -> DOPN(MutInd (fwsp_of sp,i),cl)
  | DOPN(MutConstruct((sp,j),i),cl) -> DOPN(MutConstruct((fwsp_of sp,j),i),cl)
  | x                               -> x

let fwify = strong whd_fwify

let fwsp_of_id id =
  try Nametab.fw_sp_of_id id
  with Not_found -> errorlabstrm "fwsp_of_id"
       [< 'sTR(string_of_id id) ; 'sTR" is not a defined informative object" >]


(**************************************************************************)
(*                      ML Import file__name : type.                      *)
(**************************************************************************)

(***** constants__make_parameter_body *****)
let make_fw_parameter_body (hyps,jt) =
  match level_of_type jt with
    (Prop Pos) | (Type _) ->
      {cONSTKIND = FW;
       cONSTHYPS=hyps;
       cONSTBODY=None;
       cONSTEVAL = None;
       cONSTOPAQUE = true;
       cONSTTYPE= jt;
       cONSTIMPARGS = NO_IMPL }
  | _ -> errorlabstrm "make_fw_parameter_body" 
         [< Printer.fprtype jt ; 'sTR " is not an informative term." >]


(***** constants__infexecute_parameter *****)
let fw_infexecute_parameter fhyps name t =
  let sp = Lib.make_path OBJ name in
  let (u,j) = fexecute_type_with_univ empty_evd fhyps sp t in
  let ids = auto_save_variables() in
  let fhyps' = thin_to_level fhyps (body_of_type j) in
    (u,[FW,make_fw_parameter_body (fhyps',j)])


(***** declare__machine_parameter *****)
let fw_machine_parameter fhyps (name,cty) =
  let (u',cmap) = fw_infexecute_parameter fhyps name cty in
    add_named_object (name,OBJ) (inConstant(cmap,NeverDischarge,u'))


(***** command__parameter_def_var *****)
let fw_parameter id com =
  let tcci = fconstr_of_com empty_evd (initial_fsign()) com in
  let tfw = fwify tcci in
  let _,fhyps = initial_assumptions() in
  fw_machine_parameter fhyps (id,tfw)


let ml_import id' id com =
  fw_parameter id com ;
  let sp = Lib.make_path FW id in
  add_anonymous_object (inMLImport (Const sp, id')) ;
  mSGNL [< 'sTR(string_of_id id) ; 'sTR" imported." >]


let id_of_varg = function
    VARG_IDENTIFIER id -> id
  | VARG_STRING s -> (try id_of_string s with _ -> id_of_string (" "^s))
  | _ -> invalid_arg "id_of_varg"

(*** TODO: remove overwriting ***)
let _ = overwriting_vinterp_add("ML_IMPORT", function
   [id'; VARG_IDENTIFIER id; VARG_COMMAND com] -> 
     (fun () -> ml_import (id_of_varg id') id com)
 | _ -> anomaly "ML_IMPORT called with bad arguments.")



(**************************************************************************)
(*                         Link ident := Fw-term.                         *)
(**************************************************************************)

let not_an_axiom id =
  errorlabstrm "ml_import__fw_link"
  [< 'sTR(string_of_id id) ; 'sTR" is not an FW axiom." >]


let not_have_type env cb' cb =
  let c = match cb'.cONSTBODY with
      Some {contents=COOKED x} -> x
    | _ -> anomaly "ml_import__not_have_type: should be a constant" in
    errorlabstrm "Ml_import.not_convertible"
  [< pENV [< 'sTR"In environment " >] env ; 'fNL ;
     'sTR"The term: " ; pFTERMINENV(env,c) ; 'sPC ; 
     'sTR"does not have type" ; 'sPC ; pFTYPEINENV(env,cb.cONSTTYPE) ;
     'sTR"." ; 'fNL ;
     'sTR"Actually, it has type" ; 'sPC ; pFTYPEINENV(env,cb'.cONSTTYPE) >]


let fw_infexecute_constant fhyps id c =
  let sp = Lib.make_path OBJ id in
  let (u,j) = fexecute_with_univ empty_evd fhyps sp c in
  let ids = auto_save_variables() in
  let fhyps' = thin_to_level fhyps j._KIND in
    (u,[FW, make_constant_body FW false (fhyps',j)])


let fw_link id com =

  (*** First we check that id corresponds to an informative axiom. ***)
  let sp = fwsp_of_id id in
  let osp = objsp_of sp in
  let (cmap,s,u) = match Lib.leaf_object_tag osp with
                     "CONSTANT" -> outConstant (Lib.map_leaf osp)
		   | _ -> not_an_axiom id in
  let cb = try Listmap.map cmap FW
           with Not_found -> not_an_axiom id in
  if cb.cONSTBODY <> None then not_an_axiom id ;

  (*** Then we execute the term com. ***)
  let (hyps,fhyps) = initial_assumptions() in
  let tcci = fconstr_of_com empty_evd hyps com in
  let tfw = fwify tcci in
  let (u',cmap') = fw_infexecute_constant fhyps id tfw in
  let cb' = Listmap.map cmap' FW in

  (*** We check that the type of com is convertible with cb.CONSTTYPE ***)
  if (not (conv empty_evd 
	     (body_of_type cb.cONSTTYPE) 
	     (body_of_type cb'.cONSTTYPE))) then
    not_have_type (gLOB fhyps) cb' cb ;

  (*** At last, we transform the original axiom into a constant. ***)
(**lib__remap (osp,lib__LEAF (inConstant(listmap__remap cmap FW cb',s,u))); **)
  cb.cONSTBODY <- cb'.cONSTBODY ;
  cb.cONSTOPAQUE <- false ;

  let c = match cb'.cONSTBODY with
      Some {contents=COOKED x} -> x
    | _ -> anomaly "ml_import__fw_link: should be a constant" in
  mSGNL (hOV 0 [< 'sTR"Constant " ; print_id id ; 'sTR" linked to" ; 'sPC ;
		  pFTERM c >])


(*** TODO: remove overwriting ***)
let _ = overwriting_vinterp_add("LINK", function
   [VARG_IDENTIFIER id; VARG_COMMAND com] -> (fun () -> fw_link id com)
 | _ -> anomaly "ML_IMPORT called with bad arguments.")



(**************************************************************************)
(*       ML Inductive name [ c1 ... cn ] == <Inductive Definition>.       *)
(**************************************************************************)
(*                     ML Inductive name1 [ c1,1 ... c1,n1 ]              *)
(*                                  ...                                   *)
(*                    	       	    namek [ ck,1 ... ck,nk ]              *)
(*                     == <Mutual Inductive Definition>.                  *)
(**************************************************************************)

(***** declare__machine_minductive *****)
let fw_machine_minductive fhyps nparams mispecvec finite = 
  if Array.length mispecvec = 0 then anomaly "fw_machine_minductive" 
  else 
   let mindidvec = 
     Array.map (fun  (indid,_,_,_,_) -> indid) mispecvec
   and arlcvec = 
     Array.map (fun  (_,_,indarity,indconstructors,_) ->
      	       	       	 (indarity,indconstructors)) mispecvec
   and namesvec = 
     Array.map (fun  (indid,indstamp,_,_,consnames) -> 
      	       	       	 (indstamp,indid,consnames)) mispecvec in

  let sp = Lib.make_path OBJ mindidvec.(0) in
  let (u',mimap) = with_universes 
      (execute_minductive fhyps nparams namesvec finite)
                               (sp,initial_universes,arlcvec) in

  (***  declare_minductive (mindidvec,mimap,u')  ***)
  add_named_object (mindidvec.(0),OBJ) (inMutualInductive (mimap,u'))
  (***  do_vect declare_eliminations mindidvec  ***)


(***** trad__fconstruct *****)
let fw_fconstruct sigma fsign com =
  let c = fconstr_of_com sigma fsign com in
  Mach.fexecute_type sigma fsign c


(***** command__build_mutual *****)
let fw_build_mutual lparams lnamearconstrs finite =

  let lrecnames = List.map (fun (x,_,_)->x)  lnamearconstrs
  and nparams = List.length lparams
  and sign0 = initial_fsign() in

  let (ind_sign,arityl) = List.fold_left 
    (fun (sign,arl) (recname,arityc,_) -> 
      let arity = fw_fconstruct empty_evd sign0 (mkProdCit lparams arityc) in
      (add_sign (recname,arity) sign, (arity::arl)))
      (sign0,[]) lnamearconstrs in

  let mispecvec = Array.of_list 
    (List.map2 (fun ar (name,_,lname_constr) -> 
    let consconstrl = List.map 
     (fun (_,constr) -> 
      	let c = fconstr_of_com empty_evd ind_sign 
		  (mkProdCit lparams constr)
      	in fwify c) lname_constr in
    (name,Anonymous,ar,
        put_DLAMSV_subst (List.rev lrecnames) (Array.of_list consconstrl),
              Array.of_list (List.map fst lname_constr)))
    (List.rev arityl) lnamearconstrs) in

  let _,fhyps = initial_assumptions() in
  fw_machine_minductive fhyps nparams mispecvec finite


let not_same_number_types () =
  errorlabstrm "ml_import__ml_import_inductive"
  [< 'sTR"Not the same number of types." >]

let not_same_number_constructors (id,id') =
  errorlabstrm "ml_import__ml_import_inductive"
    (hOV 0
       [< 'sTR"The ML type" ; 'sPC ; print_id id ;
          'sTR" and the FW type" ; 'sPC ; print_id id' ; 'sPC ;
          'sTR"do not have the same number" ;
      	  'sPC ; 'sTR"of constructors." >])

let ml_import_inductive names lparams lnamearconstrs finite =

  let assoc_list =
    if (List.length names) <> (List.length lnamearconstrs) then
      not_same_number_types ()
    else
      List.fold_right2 (fun (id,l) (id',_,l') acc ->
      	  if (List.length l)<>(List.length l') then
	    not_same_number_constructors (id,id')
	  else
	    ( (id,id'), List.combine l (List.map fst l') )::acc ) 
            names lnamearconstrs [] in

  fw_build_mutual lparams lnamearconstrs finite;

  List.iter
      (fun i ->
      	  let (mlid,id), l = List.nth assoc_list i in
      	  let sp = Lib.make_path FW id in
	  add_anonymous_object (inMLImport (MutInd (sp,i), mlid)) ;
	  List.iter (fun j ->
      	      let (mlid,id) = List.nth l (j-1) in
      	      add_anonymous_object
      	       	       	   (inMLImport (MutConstruct ((sp,i),j), mlid)) )
	  (List.tl (list0n (List.length l))) )
      (list0n ((List.length assoc_list) - 1)) ;

  pPNL [< 'sTR"ML inductive type(s) " ;
      	  prlist_with_sep (fun () -> [< 'sTR"," ; 'sPC >])
	                  (fun (id,_) -> [< 'sTR(string_of_id id) >]) names ;
         'sTR" imported." >]
  

(*** TODO: remove overwriting ***)
let _ = overwriting_vinterp_add("ML_ONEINDUCTIVE",
    function [VARG_VARGLIST nl;
         VARG_IDENTIFIER s;
         VARG_COMMAND c;
         VARG_BINDERLIST binders;
         VARG_BINDERLIST constructors] ->
        if List.length nl <> 1 then not_same_number_types () ;
	(match nl with
	     [VARG_VARGLIST (v::l)] ->
	       let cnames = List.map id_of_varg l in
               let la = join_binders binders in
               let li = List.map (fun (l,c) -> (List.hd l,c)) constructors in
        	 (function () -> ml_import_inductive [id_of_varg v,cnames] 
		      la [(s,c,li)] true)
	   | _ -> assert false)
      | _ -> anomaly "ML_ONEINDUCTIVE called with bad arguments.")


(*** TODO: remove overwriting ***)
let _ = overwriting_vinterp_add("ML_MUTUALINDUCTIVE",
    function [VARG_VARGLIST l;
      	 VARG_BINDERLIST binders;
      	 VARG_VARGLIST indl] ->
	let names = 
	  List.map (function (VARG_VARGLIST (v::ll)) ->
      	       	      id_of_varg v, List.map id_of_varg ll
		      | _ -> assert false) l in
        let la = join_binders binders in
        let lnamearconstructs = 
          List.map (function (VARG_VARGLIST [VARG_IDENTIFIER arid;
      	       	       	       	   VARG_COMMAND arc;
      	       	       	       	   VARG_BINDERLIST lconstr])
                	-> (arid,arc,
			    List.map (fun (l,c) -> (List.hd l,c)) lconstr)
		      | _ -> assert false)
      	      indl in
        (function () -> ml_import_inductive names la lnamearconstructs true)
      | _ -> anomaly "ML_MUTUALINDUCTIVE called with bad arguments.")



(**************************************************************************)
(*                       Extract Constant id => id                        *)
(*        Extract Inductive (id [id ... id])+ => (id [id ... id])+        *)
(**************************************************************************)

let extract_constant id id' =
  try
    let sp = Nametab.sp_of_id FW id in
      (match global_operator sp id with
	   Const _,_ -> add_anonymous_object (inMLExtract (Const sp,id'))
	 | _ -> raise Not_found)
  with Not_found ->
    errorlabstrm "Ml_import.extract_constant"
      [< pID id; 'sPC; 'sTR"is not an FW constant" >]


(*** TODO: remove overwriting ***)
let _ = overwriting_vinterp_add("EXTRACT_CONSTANT",
  function 
      [VARG_IDENTIFIER id; id'] -> 
	fun () -> extract_constant id (id_of_varg id')
    | _ -> assert false)


let extract_inductive id (id2,l2) =
  try
    let sp = Nametab.sp_of_id FW id in
      (match global_operator sp id with
	  MutInd (sp,i),_ -> 
	    add_anonymous_object (inMLExtract (MutInd (sp,i),id2));
	    (* TODO: verifier le nombre de constructeurs *)
	    List.iter
	      (fun (id,j) -> 
		 add_anonymous_object 
		   (inMLExtract (MutConstruct ((sp,i),j),id)))
	      (List.combine l2 (List.tl (list0n (List.length l2))))
	| _ -> raise Not_found)
  with Not_found ->
    errorlabstrm "Ml_import.extract_inductive"
      [< pID id; 'sPC; 'sTR"is not an FW inductive type" >]


(*** TODO: remove overwriting ***)
let _ = overwriting_vinterp_add("EXTRACT_INDUCTIVE",
  function 
      [VARG_IDENTIFIER id1; VARG_VARGLIST (id2::l2)] ->
	fun () -> extract_inductive id1 (id_of_varg id2,List.map id_of_varg l2)
    | _ -> assert false)


(**************************************************************************)
(*                            Fw Print ident.                             *)
(*                     To see FW constants or axioms.                     *)
(**************************************************************************)

let fprint_recipe = function
    Some{contents=COOKED c} -> pFTERM c
  | Some{contents=RECIPE _} -> [< 'sTR"<recipe>" >]
  | None -> [< 'sTR"<uncookable>" >]


let fprint_name id =
  try let sp = Nametab.sp_of_id FW id in
      let obj = Lib.map_leaf (objsp_of sp) in
      (match object_tag obj with
       	 "CONSTANT" ->
      	     let (cmap,_,_) = outConstant obj in
	     let {cONSTBODY=val_0;cONSTTYPE=typ} = Listmap.map cmap FW in
	     hOV 0 (match val_0 with
	        None -> [< 'sTR"*** [ "; 'sTR(string_of_id id);  'sTR " : ";
                           'cUT ; fprtype typ ; 'sTR" ]"; 'fNL >] 
	      | _    -> [< 'sTR(string_of_id id); 'sTR" = " ; 
                           fprint_recipe val_0 ;
	                   'fNL ; 'sTR "     : "; fprtype typ ; 'fNL >] )

       | "MUTUALINDUCTIVE" ->
       	     let (cmap,_) = outMutualInductive obj in
	     [< print_mutual FW (Listmap.map cmap FW) ; 'fNL >]
  
       | _ -> invalid_arg "fprint_name" )
  with Not_found | Invalid_argument _ -> errorlabstrm "ml_import__fprint_name"
                    [< 'sTR(string_of_id id) ; 'sTR" is not an FW constant." >]


(*** TODO: remove overwriting ***)
let _ = overwriting_vinterp_add("FWPRINT",
    function [VARG_IDENTIFIER id] -> (function () -> mSG(fprint_name id))
      | _ -> anomaly "FWPRINT called with bad arguments.")

