
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Constant
open Inductive
open Sign
open Reduction
open Environ
open Instantiate
open Declare
open Impargs
open Libobject
open Printer

let print_basename sp =
  let (_,id,k) = repr_path sp in
  try 
    if sp = Nametab.sp_of_id k id then 
      string_of_id id
    else 
      (string_of_id id)^"."^(string_of_kind k)
  with Not_found -> 
    warning "Undeclared constants in print_name";
    string_of_path sp

let print_basename_mind sp mindid =
  let (_,id,k) = repr_path sp in
  try 
    if sp = Nametab.sp_of_id k id then  
      string_of_id mindid
    else 
      (string_of_id mindid)^"."^(string_of_kind k)
  with Not_found ->
    warning "Undeclared constants in print_name";
    string_of_path_mind sp mindid

let print_closed_sections = ref false

let print_typed_value_in_env env (trm,typ) =
  let sign = Environ.var_context env in
  [< prterm_env (gLOB sign) trm ; 'fNL ;
     'sTR "     : "; prterm_env (gLOB sign) typ ; 'fNL >]

let print_typed_value x = print_typed_value_in_env (Global.env ()) x

let pkprinters = function
  | FW -> (fprterm,fprterm_env)
  | CCI -> (prterm,prterm_env)
  | _ -> anomaly "pkprinters"
			  		  
let print_recipe = function
  | Some { contents = Cooked c } -> prterm c
  | Some { contents = Recipe _ } -> [< 'sTR"<recipe>" >]
  | None -> [< 'sTR"<uncookable>" >]

(*
let fprint_recipe = function
  | Some c -> fprterm c
  | None -> [< 'sTR"<uncookable>" >]
*)

let print_typed_recipe (val_0,typ) =
  [< print_recipe val_0; 'fNL; 'sTR "     : "; prtype typ; 'fNL >]

let print_impl_args = function
  | []  -> [<>]
  | [i] -> [< 'sTR"Position ["; 'iNT i; 'sTR"] is implicit" >]
  | l   -> 
      [< 'sTR"Positions ["; 
         prlist_with_sep (fun () -> [< 'sTR";" >]) (fun i -> [< 'iNT i >]) l;
         'sTR"] are implicit" >]

(* To be improved; the type should be used to provide the types in the
   abstractions. This should be done recursively inside prterm, so that
   the pretty-print of a proposition (P:(nat->nat)->Prop)(P [u]u)
   synthesizes the type nat of the abstraction on u *)

let print_var name typ =
  [< 'sTR "*** [" ; 'sTR name ; 'sTR " : "; prtype typ; 'sTR "]"; 'fNL >]

let print_env pk = 
  let pterminenv = (* if pk = FW then fprterm_env else *) prterm_env in
  let pr_binder env (na,c) =
    match na with
      | Name id as name ->
          let pc = pterminenv env c in [< print_id id; 'sTR":"; pc >]
      | Anonymous -> anomaly "Anonymous variables in inductives" 
  in
  let rec prec env = function
    | [] -> [<>] 
    | [b] -> pr_binder env b
    | b::rest ->
        let pb = pr_binder env b in
        let penvtl = prec (add_rel b env) rest in
        [< pb; 'sTR";"; 'sPC; penvtl >]
  in 
  prec (gLOB nil_sign)

let assumptions_for_print lna =
  List.fold_right (fun na env -> add_rel (na,()) env) lna
    (ENVIRON(nil_sign,nil_dbsign))

let print_constructors_with_sep pk fsep mip = 
  let pterm,pterminenv = pkprinters pk in
  let (lna,lC) = decomp_all_DLAMV_name mip.mind_lc in
  let ass_name = assumptions_for_print lna in
  let lidC = Array.to_list 
               (array_map2 (fun id c -> (id,c)) mip.mind_consnames lC) in
  let prass (id,c) =
    let pc = pterminenv ass_name c in [< print_id id; 'sTR " : "; pc >]
  in
  prlist_with_sep fsep prass lidC

let implicit_args_id id l = 
  if l = [] then 
    [<>]
  else 
    [< 'sTR"For "; print_id id; 'sTR": "; print_impl_args l ; 'fNL >]

let implicit_args_msg sp mipv = 
  [< prvecti
       (fun i mip -> 
	  let imps = inductive_implicits (sp,i) in
          [< (implicit_args_id mip.mind_typename (list_of_implicits imps));
             prvecti 
	       (fun j idc ->
		  let imps = constructor_implicits ((sp,i),succ j) in
                  (implicit_args_id idc (list_of_implicits imps)))
               mip.mind_consnames 
          >])
       mipv >]

let print_mutual sp mib = 
  let pk = kind_of_path sp in
  let pterm,pterminenv = pkprinters pk in
  let env = Global.env () in
  let evd = Evd.empty in
  let {mind_packets=mipv; mind_nparams=nparams} = mib in 
  let (lpars,_) = decomp_n_prod env evd nparams (body_of_type mipv.(0).mind_arity) in
  let lparsname = List.map fst lpars in
  let lparsprint = assumptions_for_print lparsname in
  let prass ass_name (id,c) =
    let pc = pterminenv ass_name c in [< print_id id; 'sTR " : "; pc >] 
  in
  let print_constructors mip = 
    let (lna,lC) = decomp_all_DLAMV_name mip.mind_lc in
    let ass_name = assumptions_for_print (lparsname@lna) in
    let lidC =
      Array.to_list 
        (array_map2 (fun id c -> (id,snd (decomp_n_prod env evd nparams c)))
           mip.mind_consnames lC) in
    let plidC = prlist_with_sep (fun () -> [<'bRK(1,0); 'sTR "| " >])
                  (prass ass_name) lidC in
    (hV 0 [< 'sTR "  "; plidC >]) 
  in
  let print_oneind mip = 
    let (_,arity) = decomp_n_prod env evd nparams (body_of_type mip.mind_arity) in
      (hOV 0
         [< (hOV 0
	       [< print_id mip.mind_typename ; 'bRK(1,2);
		  if nparams = 0 then 
		    [<>] 
		  else
		    [< 'sTR "["; print_env pk (List.rev lpars); 
		       'sTR "]"; 'bRK(1,2) >]; 
	          'sTR ": "; pterminenv lparsprint arity; 'sTR " :=" >]);
            'bRK(1,2); print_constructors mip >]) 
  in 
  let mip = mipv.(0) in
  (* Case one [co]inductive *)
  if Array.length mipv = 1 then 
    let (_,arity) = decomp_n_prod env evd nparams (body_of_type mip.mind_arity) in 
    let sfinite = if mip.mind_finite then "Inductive " else "CoInductive " in
    (hOV 0 [< 'sTR sfinite ; print_id mip.mind_typename ;
              if nparams = 0 then 
		[<>] 
              else 
		[< 'sTR" ["; print_env pk (List.rev lpars); 'sTR "]">];
              'bRK(1,5); 'sTR": "; pterminenv lparsprint arity; 'sTR" :=";
              'bRK(0,4); print_constructors mip; 'fNL;
              implicit_args_msg sp mipv  >] )
  (* Mutual [co]inductive definitions *)
  else
    let (mipli,miplc) =
      List.fold_left 
        (fun (li,lc) mi ->
           if mi.mind_finite then (mi::li,lc) else (li,mi::lc))
        ([],[]) (Array.to_list mipv) 
    in 
    let strind =
      if mipli = [] then [<>] 
      else [< 'sTR "Inductive"; 'bRK(1,4);
              (prlist_with_sep
                 (fun () -> [< 'fNL; 'sTR"  with"; 'bRK(1,4) >])
                 print_oneind
                 (List.rev mipli)); 'fNL >]
    and strcoind =
      if miplc = [] then [<>] 
      else [< 'sTR "CoInductive"; 'bRK(1,4);
              (prlist_with_sep
                 (fun () -> [<'fNL; 'sTR "  with"; 'bRK(1,4) >]) 
                 print_oneind (List.rev miplc)); 'fNL >] 
    in
    (hV 0 [< 'sTR"Mutual " ; 
             if mip.mind_finite then 
	       [< strind; strcoind >] 
             else 
	       [<strcoind; strind>];
             implicit_args_msg sp mipv >])

let print_extracted_mutual sp = 
  let mib = Global.lookup_mind (ccisp_of sp) in
  match mib.mind_singl with 
    | None -> 
	let fwsp = fwsp_of sp in
	print_mutual fwsp (Global.lookup_mind fwsp)
    | Some a -> fprterm a

let print_variable sp =
  let (name,typ,_,_) = out_variable sp in
  let l = implicits_of_var name in
  [< print_var (string_of_id name) typ; print_impl_args l; 'fNL >]

let print_constant with_values sep sp =
  let cb = Global.lookup_constant sp in
  if kind_of_path sp = CCI then
    let val_0 = cb.const_body in
    let typ = cb.const_type in
    let l = constant_implicits sp in
    hOV 0 [< (match val_0 with 
		| None -> 
		    [< 'sTR"*** [ "; 
		       'sTR (print_basename (ccisp_of sp));  
		       'sTR " : "; 'cUT ; prtype typ ; 'sTR" ]"; 'fNL >]
		| _ -> 
		    [< 'sTR(print_basename (ccisp_of sp)) ; 
		       'sTR sep; 'cUT ;
		       if with_values then 
			 print_typed_recipe (val_0,typ) 
		       else 
			 [< prtype typ ; 'fNL >] >]); 
	     print_impl_args (list_of_implicits l); 'fNL >]
  else
    hOV 0 [< 'sTR"Fw constant " ; 
	     'sTR (print_basename (fwsp_of sp)) ; 'fNL>]

let print_inductive sp =
  let mib = Global.lookup_mind sp in
  if kind_of_path sp = CCI then
    [< print_mutual sp mib; 'fNL >]
  else
    hOV 0 [< 'sTR"Fw inductive definition "; 
	     'sTR (print_basename (fwsp_of sp)); 'fNL >]

let print_leaf_entry with_values sep (sp,lobj) =
  let tag = object_tag lobj in
  match (sp,tag) with
    | (_,"VARIABLE") ->
	print_variable sp
    | (_,("CONSTANT"|"PARAMETER")) ->
	print_constant with_values sep sp
    | (_,"INDUCTIVE") ->
	print_inductive sp
    | (_,"AUTOHINT") -> 
	[< 'sTR" Add Auto Marker"; 'fNL >]
    | (_,"GRAMMAR") -> 
	[< 'sTR" Grammar Marker"; 'fNL >]
    | (_,"SYNTAXCONSTANT") -> 
	let id = basename sp in
        [< 'sTR" Syntax Macro "; 
      	   print_id id ; 'sTR sep;  
           if with_values then 
             let c = Syntax_def.search_syntactic_definition id in 
	     [< pr_rawterm c >]
           else [<>]; 'fNL >]
    | (_,"PPSYNTAX") -> 
	[< 'sTR" Syntax Marker"; 'fNL >]
    | (_,"TOKEN") -> 
	[< 'sTR" Token Marker"; 'fNL >]
    | (_,"CLASS") -> 
	[< 'sTR" Class Marker"; 'fNL >]
    | (_,"COERCION") -> 
	[< 'sTR" Coercion Marker"; 'fNL >]
    | (_,s) -> 
	[< 'sTR(string_of_path sp); 'sTR" : ";
           'sTR"Unrecognized object "; 'sTR s; 'fNL >]

let rec print_library_entry with_values ent = 
  let sep = if with_values then " = " else " : " in 
  match ent with
    | (sp,Lib.Leaf lobj) -> 
	[< print_leaf_entry with_values sep (sp,lobj) >]
    | (_,Lib.OpenedSection str) -> 
        [< 'sTR(" >>>>>>> Section " ^ str); 'fNL >]
    | (_,Lib.ClosedSection (str,_)) -> 
        [< 'sTR(" >>>>>>> Closed Section " ^ str); 'fNL >]
    | (_,Lib.Module str) ->
	[< 'sTR(" >>>>>>> Module " ^ str); 'fNL >]
    | (_,Lib.FrozenState _) ->
	[< >]
	
and print_context with_values = 
  let rec prec = function
    | h::rest -> [< prec rest ; print_library_entry with_values h >]
    | [] -> [< >]
  in 
  prec

let print_full_context () = print_context true (Lib.contents_after None)

let print_full_context_typ () = print_context false (Lib.contents_after None)

(* For printing an inductive definition with
   its constructors and elimination,
   assume that the declaration of constructors and eliminations
   follows the definition of the inductive type *)

let rec head_const c = match strip_outer_cast c with
  | DOP2(Prod,_,DLAM(_,c)) -> head_const c
  | DOPN(AppL,cl)    -> head_const (array_hd cl)
  | def         -> def

let list_filter_vec f vec = 
  let rec frec n lf = 
    if n < 0 then lf 
    else if f vec.(n) then 
      frec (n-1) (vec.(n)::lf)
    else 
      frec (n-1) lf
  in 
  frec (Array.length vec -1) []

 (* The four functions print_constructors_head, print_all_constructors_head,
   print_constructors_rel and crible implement the behavior needed for the
   Coq Search command.  These functions take as first argument the procedure
   that will be called to treat each entry.  This procedure receives the name
   of the object, the assumptions that will make it possible to print its type,
   and the constr term that represent its type. *)

let print_constructors_head 
  (fn : string -> unit assumptions -> constr -> unit) c mip = 
  let (lna,lC) = decomp_all_DLAMV_name mip.mind_lc in
  let ass_name = assumptions_for_print lna in
  let lidC = array_map2 (fun id c_0 -> (id,c_0)) mip.mind_consnames lC in
  let flid = list_filter_vec (fun (_,c_0) -> head_const c_0 = c) lidC in
  List.iter
    (function (id,c_0) -> fn (string_of_id id) ass_name c_0) flid
    
let print_all_constructors_head fn c mib = 
  let mipvec = mib.mind_packets 
  and n = mib.mind_ntypes in 
  for i = 0 to n-1 do
    print_constructors_head fn c mipvec.(i)
  done

let print_constructors_rel fn mip = 
  let (lna,lC) = decomp_all_DLAMV_name mip.mind_lc in
  let ass_name = assumptions_for_print lna in
  let lidC = array_map2 (fun id c -> (id,c)) mip.mind_consnames lC in
  let flid = list_filter_vec (fun (_,c) -> isRel (head_const c)) lidC in
  List.iter (function (id,c) -> fn (string_of_id id) ass_name c) flid

let crible (fn : string -> unit assumptions -> constr -> unit) name =
  let hyps = gLOB (Global.var_context()) in
  let imported = Library.opened_modules() in
  let const = global_reference CCI name in 
  let rec crible_rec = function
    | (spopt,Lib.Leaf lobj)::rest ->
	(match (spopt,object_tag lobj) with
	   | (_,"VARIABLE") ->
	       let (namec,typ,_,_) = out_variable spopt in 
               if (head_const (body_of_type typ)) = const then  
                 fn (string_of_id namec) hyps (body_of_type typ);
               crible_rec rest
	   | (sp,("CONSTANT"|"PARAMETER")) ->
	       let {const_type=typ} = Global.lookup_constant sp in
               if (head_const (body_of_type typ)) = const then
                 fn (print_basename sp) hyps (body_of_type typ);
               crible_rec rest
	   | (sp,"INDUCTIVE") -> 
               let mib = Global.lookup_mind sp in 
               (match const with 
		  | (DOPN(MutInd(sp',tyi),_)) -> 
		      if sp = objsp_of sp' then print_constructors_rel fn
			(mind_nth_type_packet mib tyi) 
		  | _ -> print_all_constructors_head fn const mib); 
               crible_rec rest
	   | _ -> crible_rec rest)

    | (_, (Lib.OpenedSection _ | Lib.FrozenState _ | Lib.Module _))::rest -> 
	crible_rec rest
    | (_, Lib.ClosedSection _) :: rest ->
	crible_rec rest
    | []      -> ()
  in 
  try 
    crible_rec (Lib.contents_after None)
  with Not_found -> 
    error ((string_of_id name) ^ " not declared")

let print_crible name =
  crible (fun str ass_name constr -> 
            let pc = prterm_env ass_name constr in
            mSG[<'sTR str; 'sTR":"; pc; 'fNL >]) name

let read_sec_context sec =
  let rec get_cxt in_cxt = function
    | ((sp,Lib.OpenedSection str) as hd)::rest ->
        if str = sec then (hd::in_cxt) else get_cxt (hd::in_cxt) rest
    | [] -> []
    | hd::rest -> get_cxt (hd::in_cxt) rest 
  in
  let cxt = (Lib.contents_after None) in
  List.rev (get_cxt [] cxt)

let print_sec_context sec = print_context true (read_sec_context sec)

let print_sec_context_typ sec = print_context false (read_sec_context sec)

let print_val env {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env (trm,typ)
    
let print_type env {uj_val=trm;uj_type=typ} =
  print_typed_value_in_env env (trm, nf_betaiota env Evd.empty typ)
    
let print_eval red_fun env {uj_val=trm;uj_type=typ} =
  let ntrm = red_fun env Evd.empty trm
  and ntyp = nf_betaiota env Evd.empty typ in
  [< 'sTR "     = "; print_typed_value_in_env env (ntrm, ntyp) >]

let print_name name = 
  let str = string_of_id name in 
  try 
    let (sp,lobj) = 
      let (sp,entry) =
      	List.find (fun en -> basename (fst en) = name) 
	  (Lib.contents_after None)
      in
      match entry with
	| Lib.Leaf obj -> (sp,obj)
	| _ -> raise Not_found
    in
    print_leaf_entry true " = " (sp,lobj)
  with 
    | Not_found -> 
	(try 
	   (match Declare.global_reference CCI name with
	      | VAR _ ->
		  let (_,typ) = Global.lookup_var name in 
		  [< print_var str typ;
		     try print_impl_args (implicits_of_var name)
		     with _ -> [<>] >]
	      | DOPN(Const sp,_) ->
		  print_constant true " = " sp
	      | DOPN(MutInd (sp,_),_) ->
		  print_inductive sp
	      | DOPN (MutConstruct((sp,_),_),_) ->
		  print_inductive sp
	      | _ -> assert false)
	 with Not_found | Invalid_argument _ -> 
	   error (str ^ " not a defined object"))
    | Invalid_argument _ -> error (str ^ " not a defined object")

let print_opaque_name name = 
  let sigma = Evd.empty in
  let env = Global.env () in
  let sign = Global.var_context () in
  try 
    let x = global_reference CCI name in
    match kind_of_term x with
      | IsConst (sp,_ as cst) ->
	  let cb = Global.lookup_constant sp in
          if is_defined cb then
	    let typ = constant_type env Evd.empty cst in
            print_typed_value (constant_value env x, body_of_type typ)
          else 
	    anomaly "print_opaque_name"
      | IsMutInd ((sp,_),_) ->
          print_mutual sp (Global.lookup_mind sp)
      | IsMutConstruct cstr -> 
	  let ty = Typeops.type_of_constructor env sigma cstr in
	  print_typed_value(x, ty)
      | IsVar id ->
          let a = snd(lookup_sign id sign) in 
	  print_var (string_of_id id) a
      | _ -> failwith "print_name"
  with Not_found -> 
    error ((string_of_id name) ^ " not declared")

let print_local_context () =
  let env = Lib.contents_after None in
  let rec print_var_rec = function 
    | [] -> [< >]
    | (sp,Lib.Leaf lobj)::rest ->
	if "VARIABLE" = object_tag lobj then
          let (name,typ,_,_) = out_variable sp in 
	  [< print_var_rec rest;
             print_var (string_of_id name) typ >]
	else 
	  print_var_rec rest
    | _::rest -> print_var_rec rest

  and print_last_const = function
    | (sp,Lib.Leaf lobj)::rest -> 
        (match object_tag lobj with
           | "CONSTANT" | "PARAMETER" -> 
               let {const_body=val_0;const_type=typ} = 
		 Global.lookup_constant sp in
               [< print_last_const rest;
                  'sTR(print_basename sp) ;'sTR" = ";
                  print_typed_recipe (val_0,typ) >]
           | "INDUCTIVE" -> 
               let mib = Global.lookup_mind sp in 
               [< print_last_const rest;print_mutual sp mib; 'fNL >]
           | "VARIABLE" ->  [< >]
           | _          ->  print_last_const rest)
    | _ -> [< >]
  in 
  [< print_var_rec env;  print_last_const env >]

let fprint_var name typ =
  [< 'sTR ("*** [" ^ name ^ " :"); fprtype typ; 'sTR "]"; 'fNL >]

let fprint_judge {uj_val=trm;uj_type=typ} = 
  [< fprterm trm; 'sTR" : " ; fprterm typ >]

let unfold_head_fconst = 
  let rec unfrec = function
    | DOPN(Const _,_) as k -> constant_value (Global.env ()) k 
    | DOP2(Lambda,t,DLAM(na,b)) -> DOP2(Lambda,t,DLAM(na,unfrec b))
    | DOPN(AppL,v) -> DOPN(AppL,array_cons (unfrec (array_hd v)) (array_tl v))
    | x -> x
  in 
  unfrec

(***
let print_extracted_name name =
  let (sigma,(sign,fsign)) = initial_sigma_assumptions() in
  try
    match (Machops.global (gLOB sign) name) with
      | DOPN(Const _,_) as x ->
          let cont = snd(infexecute sigma (sign,fsign) x) in 
          (match cont with
             | Inf {_VAL=trm; _TYPE=typ} ->
                 (hOV 0
                    [< 'sTR (string_of_id name); 
                       if defined_const sigma x then 
                         begin
			   Constants.set_transparent_extraction name;
			   [< 'sTR " ==>";'bRK(1,4); 
                              fprterm (unfold_head_fconst sigma trm); 'fNL>]
			 end
                       else 
			 [< >]; 
		       'sTR " :  "; fprterm typ; 'fNL >])
             | _ -> error "Non informative term")
      | VAR id ->
	  (* Pourquoi on n'utilise pas fsign ? *)
          let a = snd(lookup_sign id sign) in
          let cont = snd(infexecute sigma (sign,fsign) a.body) in 
	  (match cont with  (* Cradingue *)
             | Inf {_VAL=t;_TYPE=k} -> 
		 (match whd_betadeltaiota sigma k with
		    | DOP0 (Sort s) ->
			fprint_var (string_of_id name) {body=t;typ=s})
             | _  -> error "Non informative term")
	  
      | DOPN(MutInd (sp,_),_) as x ->
          let cont = snd(infexecute sigma (sign,fsign) x) in 
	  (match cont with
             | Inf _ ->
                 (hOV 0 [< 'sTR (string_of_id name); 'sTR " ==>"; 'bRK(1,4);
                           print_extracted_mutual sp >])
             | _ -> error "Non informative term")
      | DOPN(MutConstruct _ ,_) as x ->
          let cont = snd(infexecute sigma (sign,fsign) x) in 
	  (match cont with
             | Inf d ->
                 [< 'sTR ((string_of_id name) ^" ==> ");
		    fprint_judge d ; 'fNL >]
             | _  -> error "Non informative term")
      | _ -> anomaly "should be a variable or constant"
  with Not_found -> 
    error ((string_of_id name) ^ " not declared")

let print_extraction () = 
  let rec print_rec = function
    | (sp,Lib.LEAF lobj)::rest ->
	(match (sp,object_tag lobj) with
	   | (sp,"CONSTANT") ->
	       (try 
		  let (_,{cONSTBODY=d}) = const_of_path (fwsp_of sp) in 
		  [< print_rec rest;
		     'sTR(print_basename sp) ; 'sTR" ==> ";  
		     fprint_recipe d; 'fNL >]
		with Not_found -> 
		  print_rec rest)
	   | (_,"VARIABLE") ->
	       let (name,(_,cont),_,_,_,_) = outVariable lobj in
               [< print_rec rest;
		  (match cont with 
		     | Some(t,_) -> fprint_var (string_of_id name) t
                     | _         -> [< >]) >]
	   | (sp,"INDUCTIVE") ->
	       [< print_rec rest; 
		  (try 
		     [< print_extracted_mutual sp ; 'fNL >] 
		   with Not_found -> [<>]) >]
	   | _ -> print_rec rest)
	
    | (sp,Lib.ClosedDir _)::rest -> print_rec rest
	  
    | _::rest -> print_rec rest
	  
    | [] -> [< 'fNL >]
  in 
  [< print_rec (Lib.contents_after None); 'fNL >]
 
let print_extracted_context () =
  let env = Lib.contents_after None in 
  let rec print_var_rec = function 
    | ((_,Lib.LEAF lobj))::rest ->
	if "VARIABLE" = object_tag lobj then
          let (name,(typ,cont),_,_,_,_) = outVariable lobj in
          [< print_var_rec rest ; 'fNL;
             match cont with
	       | Some(t,_) -> fprint_var (string_of_id name) t
               | _         -> [< >] >]
	else 
	  print_var_rec rest
    |  _::rest -> print_var_rec rest
    | [] -> [< 'fNL >]

  and print_last_constants = function 
    | (sp,Lib.LEAF lobj)::rest ->
	(match object_tag lobj with 
	   | "CONSTANT" -> 
	       let (_,{cONSTBODY=c;cONSTTYPE=typ}) = 
		 const_of_path (fwsp_of sp) in
               [< print_last_constants rest;
		  let s=print_basename sp	in 
		  (try 
		     let (_,{cONSTBODY = d}) = const_of_path (fwsp_of sp) in 
		     [< 'sTR (s ^" ==> "); fprint_recipe d; 'fNL >]
		   with Not_found -> 
		     [< >]) >]
	   | "INDUCTIVE" -> 
	       [< print_last_constants rest; 
		  try print_extracted_mutual sp with Not_found -> [<>] >]
	   | "VARIABLE" -> 
	       let (_,(_,cont),_,_,_,_) = outVariable lobj in
               (match cont with 
		  | Some _ -> [<>]
                  | None -> print_last_constants rest)
	   | _ ->  print_last_constants rest)
	
    |  (_,Lib.ClosedDir _)::rest -> print_last_constants rest
    | _ -> [< >]
  in 
  [< print_var_rec env; print_last_constants env >]

let print_extracted_vars () =
  let env = Lib.contents_after None in 
  let rec print_var_rec = function
    | ((_,Lib.LEAF lobj))::rest ->
	if "VARIABLE" = object_tag lobj then
          let (name,(_,cont),_,_,_,_) = outVariable lobj in
          [< print_var_rec rest ; 'fNL;
             match cont with
	       | Some (t,_) -> fprint_var (string_of_id name) t
               | _          -> [< >] >]
	else 
	  print_var_rec rest
    |  _::rest -> print_var_rec rest
    | [] -> [< 'fNL >]
  in 
  print_var_rec env
***)

(* for debug *)
let inspect depth = 
  let rec inspectrec n res env = 
    if n=0 or env=[] then 
      res
    else 
      inspectrec (n-1) (List.hd env::res) (List.tl env)
  in 
  let items = List.rev (inspectrec depth [] (Lib.contents_after None)) in
  print_context false items


(*************************************************************************)
(* Pretty-printing functions coming from classops.ml                     *)

open Classops

let string_of_strength = function 
  | NeverDischarge -> "(global)"
  | DischargeAt sp -> "(disch@"^(string_of_path sp)

let print_coercion_value v = prterm v.cOE_VALUE.uj_val

let print_index_coercion c = 
  let _,v = coercion_info_from_index c in
  print_coercion_value v

let print_class i =
  let cl,x = class_info_from_index i in
  [< 'sTR x.cL_STR >]
  
let print_path ((i,j),p) = 
  [< 'sTR"["; 
     prlist_with_sep (fun () -> [< 'sTR"; " >])
       (fun c ->  print_index_coercion c) p;
     'sTR"] : "; print_class i; 'sTR" >-> ";
     print_class j >]

let _ = Classops.install_path_printer print_path

let print_graph () = 
  [< prlist_with_sep pr_fnl print_path (inheritance_graph()) >]

let print_classes () = 
  [< prlist_with_sep pr_spc
       (fun (_,(cl,x)) -> 
          [< 'sTR x.cL_STR  (*; 'sTR(string_of_strength x.cL_STRE) *) >]) 
       (classes()) >]

let print_coercions () = 
  [< prlist_with_sep pr_spc
       (fun (_,(_,v)) -> [< print_coercion_value v >]) (coercions()) >]
  
let cl_of_id id = 
  match string_of_id id with
    | "FUNCLASS" -> CL_FUN
    | "SORTCLASS" -> CL_SORT
    | _ -> let v = Declare.global_reference CCI id in
	   let cl,_ = constructor_at_head v in 
	   cl

let index_cl_of_id id =
  try 
    let cl = cl_of_id id in
    let i,_=class_info cl in 
    i
  with _ -> 
    errorlabstrm "index_cl_of_id"
      [< 'sTR(string_of_id id); 'sTR" is not a defined class" >]

let print_path_between ids idt = 
  let i = (index_cl_of_id ids) in
  let j = (index_cl_of_id idt) in
  let p = 
    try 
      lookup_path_between (i,j) 
    with _ -> 
      errorlabstrm "index_cl_of_id"
        [< 'sTR"No path between ";'sTR(string_of_id ids); 
	   'sTR" and ";'sTR(string_of_id ids) >]
  in
  print_path ((i,j),p)

(*************************************************************************)
