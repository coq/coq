
(* $:Id$ *)

open Pp
open Util
open Names
(*i open Generic i*)
open Term
open Declarations
open Declare
open Coqast
open Ast
open Astterm
open Command

(********** definition d'un record (structure) **************)

let make_constructor fields appc =
  let rec aux fields =
    match fields with
      | [] -> appc
      | (id,ty)::l -> ope("PROD",[ty; slam(Some (string_of_id id), aux l)]) 
  in 
  aux fields

(* free_vars existe de'ja` dans ast.ml *)

let rec drop = function
  | [] -> []
  | (None::t) -> drop t
  | ((Some id)::t) -> id::(drop t)

let fold curriedf l base =
  List.fold_right (fun a -> fun b -> curriedf(a,b)) l base
    
let free_vars t = 
  let rec aux = function
    | (Nvar(_,s),accum) -> list_add_set (id_of_string s) accum
    | (Node(_,_,tl),accum) -> fold aux tl accum
    | (Slam(_,None,body),accum) -> (aux(body,[]))@accum
    | (Slam(_,Some id,body),accum) ->
	(list_subtract (aux(body,[])) [(id_of_string id)])@accum
    | (_,accum) -> accum
  in 
  aux(t,[]) 

let free_in_asts id l = 
  let rec aux =
    function 
      | [] -> true
      | a::l -> (not (List.mem id (free_vars a))) & (aux l) 
  in
  aux l

let all_vars t = 
  let rec aux = function
    | (Nvar(_,id),accum) -> list_add_set (id_of_string id) accum
    | (Node(_,_,tl),accum) -> fold aux tl accum
    | (Slam(_,None,body),accum) -> aux (body,accum)
    | (Slam(_,Some id,body),accum) ->
	aux (body,(list_union accum [(id_of_string id)]))
    | (_,accum) -> accum
  in 
  aux(t,[]) 
   
let print_id_list l =
  [< 'sTR "[" ; prlist (fun id -> [< 'sTR (string_of_id id) >]) l; 'sTR "]" >]

let typecheck_params_and_field ps fs =
  let env0 = Global.env () in
  let env1,newps =
    List.fold_left
      (fun (env,newps) (id,t) -> 
         let tj = type_judgment_of_rawconstr Evd.empty env t in
	 let ass = Typeops.assumption_of_type_judgment tj in
         (Environ.push_var_decl (id,ass) env,(id,tj.Environ.utj_val)::newps))
      (env0,[]) ps
  in
  let env2,newfs =
    List.fold_left
      (fun (env,newfs) (id,t) -> 
         let tj = type_judgment_of_rawconstr Evd.empty env t in
	 let ass = Typeops.assumption_of_type_judgment tj in
         (Environ.push_var_decl (id,ass) env,(id,tj.Environ.utj_val)::newfs)) (env1,[]) fs
  in
  List.rev(newps),List.rev(newfs)

let mk_LambdaCit = List.fold_right (fun (x,a) b -> mkNamedLambda x a b)

let warning_or_error coe st = 
  if coe then errorlabstrm "structure" st;
  pPNL [< 'sTR"Warning: "; st >] 

(* Fields have names [idfs] and types [tyfs]; [coers] is a boolean list 
   telling if the corresponding field must me a coercion *)

let definition_structure (is_coe,idstruc,ps,cfs,idbuild,s) =
  let coers,fs = List.split cfs in     
  let idps,typs = List.split ps in      
  let idfs,tyfs = List.split fs in
  if not (free_in_asts idstruc tyfs) then 
    message "Error: A record cannot be recursive";
  let newps,newfs = typecheck_params_and_field ps fs in
  let app_constructor = 
    ope("APPLISTEXPL",
        (nvar (string_of_id idstruc))::
        List.map (fun id -> nvar(string_of_id id)) idps) in
  let type_constructor = make_constructor fs app_constructor in 
  let _ = build_mutual ps [(idstruc,s,[(idbuild,type_constructor)])] true in
  let r = global_reference CCI idstruc in
  let rsp = op_of_mind r in
  let x = Environ.named_hd (Global.env()) r Anonymous in
  let lp = List.length idps in
  let rp1 = applist (r,(rel_list 0 lp)) in
  let rp2 = applist (r,(rel_list 1 lp)) in

  (* We build projections *)
  let (sp_projs,_,_) =
    List.fold_left2
      (fun (sp_projs,ids_not_ok,subst) coe (fi,ti) -> 
	 let fv_ti = global_vars ti in
	 let bad_projs = (list_intersect ids_not_ok fv_ti) in
	 if bad_projs <> [] then begin 
	   (warning_or_error coe
              [< 'sTR(string_of_id fi); 
		 'sTR" cannot be defined. The projections ";
                 print_id_list bad_projs; 'sTR " were not defined" >]);
           (None::sp_projs,fi::ids_not_ok,subst)
         end else 
	   let p = mkLambda (x, rp2, replace_vars subst ti) in
	   let branch = mk_LambdaCit newfs (VAR fi) in
	   let ci = Inductive.make_case_info
		      (Global.lookup_mind_specif (destMutInd r))
		      (Some PrintLet) [| RegularPat |] in
	   let proj = mk_LambdaCit newps 
			(mkLambda (x, rp1,
				   mkMutCaseA ci p (Rel 1) [|branch|])) in
	   let ok = 
	     try
	       let cie =
		 { const_entry_body = Cooked proj;
		   const_entry_type = None } in
	       (declare_constant fi (cie,NeverDischarge); true)
             with UserError(s,pps) ->
               ((warning_or_error coe 
                   [<'sTR (string_of_id fi); 
                     'sTR" cannot be defined. "; pps >]);false) in
	   if not ok then 
	     (None::sp_projs,fi::ids_not_ok,subst)
	   else begin
             if coe then
	       Class.try_add_new_coercion_record fi NeverDischarge idstruc;
             let constr_fi = global_reference CCI fi in
             let constr_fip = (* Rel 1 refers to "x" *)
               applist (constr_fi,(List.map (fun id -> VAR id) idps)@[Rel 1])
             in (Some(path_of_const constr_fi)::sp_projs,
		 ids_not_ok, (fi,constr_fip)::subst)
	   end)
      ([],[],[]) coers newfs
  in 
  if is_coe then Class.try_add_new_coercion idbuild NeverDischarge;
  Recordops.add_new_struc (rsp,idbuild,lp,List.rev sp_projs)
