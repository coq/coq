
(* $:Id$ *)

open Util;;
open Names;;
open Term;;
(*
open Generic;;
open Mach;;
open Command;;
open More_util;;
open Pp;;

open Constrtypes;;
open Termenv;;
open Trad;;
open Ast;;
open CoqAst;;

open Machops;;
open Classops;;
open Recordops;;
*)

(********** definition d'un record (structure) **************)

let make_constructor fields appc =
 let rec aux fields =
  match fields with
     [] -> appc
   | (id,ty)::l -> ope("PROD",[ty; slam(Some (string_of_id id), aux l)]) 
 in aux fields;;

(* free_vars existe de'ja` dans ast.ml *)

let rec drop = function
    [] -> []
  | (None::t) -> drop t
  | ((Some id)::t) -> id::(drop t)
;;

let fold curriedf l base =
  List.fold_right (fun a -> fun b -> curriedf(a,b)) l base
;;

let free_vars t = 
 let rec aux = function
  (Nvar(_,s),accum) -> add_set (id_of_string s) accum
| (Node(_,_,tl),accum) -> fold aux tl accum
| (Slam(_,None,body),accum) ->
        (aux(body,[]))@accum
| (Slam(_,Some id,body),accum) ->
        (subtract (aux(body,[])) [(id_of_string id)])@accum
| (_,accum) -> accum
 in aux(t,[]) 
;;

let free_in_asts id l = 
  let rec aux =
    function [] -> true
      | a::l -> (not (List.mem id (free_vars a))) & (aux l) in
  aux l;;

let all_vars t = 
 let rec aux = function
  (Nvar(_,id),accum) -> add_set (id_of_string id) accum
| (Node(_,_,tl),accum) -> fold aux tl accum
| (Slam(_,None,body),accum) -> aux (body,accum)
| (Slam(_,Some id,body),accum) ->
    aux (body,(union accum [(id_of_string id)]))
| (_,accum) -> accum
 in aux(t,[]) 
;;
   
let print_id_list l =
  [< 'sTR "[" ; prlist (fun id -> [< 'sTR (string_of_id id) >]) l; 'sTR "]" >]
;; 

let typecheck_params_and_field ps fs =
  let sign0 = initial_sign() in
  let sign1,newps =
    List.fold_left
      (fun (sign,newps) (id,t) -> 
         let tj = type_of_com sign t in
           (add_sign (id,tj) sign,(id,tj.body)::newps))
      (sign0,[]) ps in
  let sign2,newfs =
    List.fold_left
      (fun (sign,newfs) (id,t) -> 
         let tj = type_of_com sign t in
           (add_sign (id,tj) sign,(id,tj.body)::newfs)) (sign1,[]) fs
  in List.rev(newps),List.rev(newfs)
;;


let mk_LambdaCit = List.fold_right (fun (x,a) b -> mkNamedLambda x a b);;


let definition_structure (coe_constr,struc,ps,cfs,const,s) =

 let (sign,fsign) = initial_assumptions() in
 let fs = List.map snd cfs in     
 let coers = List.map fst cfs in  
 let idps = List.map fst ps in      
 let typs = List.map snd ps in
 let idfs = List.map fst fs in
 let tyfs = List.map snd fs in
 let _ = if not (free_in_asts struc tyfs)
            then message "Error: A record cannot be recursive" in
 let newps,newfs = typecheck_params_and_field ps fs in
 let app_constructor = ope("APPLIST",
                           (ope("XTRA",[str "!";(nvar (string_of_id struc))]))::
                           List.map (fun id -> nvar(string_of_id id)) idps) in
 let type_constructor = make_constructor fs app_constructor in 
 let _ = build_mutual ps [(struc,s,[(const,type_constructor)])] true in

 let x = next_ident_away (id_of_string "x") 
               (List.fold_left (fun l ty -> union (all_vars ty) l) 
               (union idps (fst sign)) tyfs) in
 let r = Machops.global (gLOB sign) struc in
 let (rsp,_,_) = destMutInd r in
 let rid = basename rsp in
 let lp = length idps in
 let rp1 = applist (r,(rel_list 0 lp)) in
 let rp2 = applist (r,(rel_list 1 lp)) in
 let warning_or_error coe st = if coe then (errorlabstrm "structure" st)
                               else pPNL [< 'sTR"Warning: "; st >] in
        
 let (sp_projs,_,_,_,_) =
   List.fold_left 
   (fun (sp_projs,ids_ok,ids_not_ok,sigma,coes) (fi,ti) -> 
      let fv_ti = global_vars ti in
      let bad_projs = (intersect ids_not_ok fv_ti) in
      if bad_projs <> []
      then begin (warning_or_error (hd coes)
                   [< 'sTR(string_of_id fi); 
                      'sTR" cannot be defined. The projections ";
                         print_id_list bad_projs; 'sTR " were not defined" >]);
                 (None::sp_projs,ids_ok,fi::ids_not_ok,sigma,(tl coes))
           end
      else 

      let p = mkNamedLambda x rp2 (replace_vars sigma ti) in
      let branch = mk_LambdaCit newfs (VAR fi) in
      let proj = mk_LambdaCit newps 
             (mkNamedLambda x rp1 (mkMutCaseA (ci_of_mind r) p (Rel 1) [|branch|])) in
      let ok = try (Declare.machine_constant (sign,fsign)
                    ((fi,false,NeverDischarge),proj); true)
               with UserError(s,pps) ->
                 ((warning_or_error (hd coes) 
                     [<'sTR (string_of_id fi); 
                       'sTR" cannot be defined. "; pps >]);false) in
      if not ok
      then (None::sp_projs,ids_ok,fi::ids_not_ok,sigma,(tl coes))
      else begin
        if List.hd coes then
           Class.try_add_new_coercion_record fi NeverDischarge rsp;
        let constr_fi = Machops.global (gLOB sign) fi in
        let constr_fip =
          applist (constr_fi,(List.map (fun id -> VAR id) idps)@[VAR x])
        in (Some(path_of_const constr_fi)::sp_projs,fi::ids_ok,ids_not_ok,
            (fi,{sinfo=Closed;sit=constr_fip})::sigma,(tl coes))
      end)
     ([],[],[],[],coers) newfs
   in (if coe_constr="COERCION" 
     then Class.try_add_new_coercion const NeverDischarge);
          add_new_struc (rsp,const,lp,rev sp_projs)
;;
         
(* $Id$ *)
