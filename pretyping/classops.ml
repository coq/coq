

open Std;;
open Names;;
open Vectops;;
open Pp;;
open Vartab;;
open Libobject;;
open Constrtypes;;
open Vectops;;
open List;;
open Library;;
open Term;;
open More_util;;
open Generic;;
open Initial;;
open Printer;;


(* usage qque peu general: utilise aussi dans record *)

type cte_typ = NAM_Var of identifier | NAM_SP of section_path | NAM_Construct of section_path*int*int
;;

let cte_of_constr = function  
    (DOPN(Const sp,l)) -> NAM_SP sp
  | (DOPN(MutInd (sp,_),l)) -> NAM_SP sp
  | (VAR(id)) -> NAM_Var id
  | (DOPN(MutConstruct ((sp,i),j) ,l)) -> NAM_Construct (sp,i,j)
  |  _ -> raise Not_found
;;

type cl_typ = CL_SORT | CL_FUN | CL_Var of identifier | CL_SP of section_path 
            | CL_IND of section_path*int
;;

type cl_info_typ = {cL_STR : string;
                    cL_STRE : strength;
                    cL_PARAM : int}
;;

type coe_typ = cte_typ
;;

type coe_info_typ = {cOE_VALUE : judgement;
                     cOE_STRE : strength;
                     cOE_ISID : bool;
                     cOE_PARAM : int}
;;

type inheritance_path = int list
;;

(* table des classes, des coercions et graphe d'heritage *)

let cLASSES = (ref [] : (int * (cl_typ * cl_info_typ)) list ref);;

let cOERCIONS = (ref [] : (int * (coe_typ * coe_info_typ)) list ref);;

let iNHERITANCE_GRAPH = (ref [] : ((int * int) * inheritance_path) list ref);; 

let freeze () = (!cLASSES,!cOERCIONS,
                 !iNHERITANCE_GRAPH)
;;

let unfreeze (fcl,fco,fig) = (cLASSES:=fcl;
                              cOERCIONS:=fco;
                              iNHERITANCE_GRAPH:=fig)
;;

(* ajout de nouveaux "objets" *)

let newNum_class = 
 let num = ref 0 in
 function () -> (num:=!num+1;!num)
;;

let newNum_coercion = 
 let num = ref 0 in
 function () -> (num:=!num+1;!num)
;;

let add_new_class_num (n,(cl,s)) = 
cLASSES := (n,(cl,s))::(!cLASSES)
;;

let add_new_class1 (cl,s) = 
add_new_class_num (newNum_class(),(cl,s))
;;

let add_new_coercion_num (n,(coe,s)) = 
cOERCIONS := (n,(coe,s))::(!cOERCIONS)
;;

let add_new_coercion (coe,s) = 
let n = newNum_coercion() in 
add_new_coercion_num (n,(coe,s));n
;;

let add_new_path x =
iNHERITANCE_GRAPH := x::(!iNHERITANCE_GRAPH)
;;

let init () = (cLASSES:= []; 
               add_new_class1 (CL_FUN,{cL_STR="FUNCLASS";cL_PARAM=0;cL_STRE=NeverDischarge});
               add_new_class1 (CL_SORT,{cL_STR="SORTCLASS";cL_PARAM=0;cL_STRE=NeverDischarge});
               cOERCIONS:= [];
               iNHERITANCE_GRAPH:= [])
;;

init();;

(* fonction de recherche *)

let search_info x l = 
let rec aux = function [] -> raise Not_found
                     | (n,(x1,r))::l -> if x=x1 then (n,r)
                                        else aux l
in aux l
;;

(* class_info : cl_typ -> int * cl_info_typ *)

let class_info cl = search_info cl (!cLASSES)
;;

(* class_info_from_index : int -> cl_typ * cl_info_typ *)

let class_info_from_index i = List.assoc i (!cLASSES)
;;

(* coercion_info : coe_typ -> int * coe_info_typ *)

let coercion_info coe = search_info coe (!cOERCIONS)
;;

(* coercion_info_from_index : int -> coe_typ * coe_info_typ *)

let coercion_info_from_index i = List.assoc i (!cOERCIONS)
;;

let lookup_path_between (s,t) = List.assoc (s,t) (!iNHERITANCE_GRAPH);;

let lookup_path_to_fun_from s = lookup_path_between (s,fst(class_info CL_FUN))
;;

let lookup_path_to_sort_from s = lookup_path_between (s,fst(class_info CL_SORT))
;;


(* library, summary *)

(*val inClass : (cl_typ * cl_info_typ) -> Libobject.object = <fun>
 val outClass : Libobject.object -> (cl_typ * cl_info_typ) = <fun> *)

let (inClass,outClass) =
    declare_object ("CLASS",
                    {load_function = (fun _ -> ());
                     cache_function = (function  (_,x) -> add_new_class1 x);
                     specification_function = (function x -> x)});;

let add_new_class (cl,s,stre,p) = 
add_anonymous_object (inClass ((cl,{cL_STR=s;cL_STRE=stre;cL_PARAM=p})))
;;

Library.declare_summary "inh_graph"
{Summary.freeze_function = freeze;
 Summary.unfreeze_function = unfreeze;
 Summary.init_function = init}
;;

(* classe d'un terme *)

(* constructor_at_head : constr -> cl_typ * int *)

let constructor_at_head t = 
let rec aux t' = match t' with
    (DOPN(Const sp,_)) -> CL_SP sp,0
  | (DOPN(MutInd (sp,i),_)) -> CL_IND (sp,i),0
  | (VAR(id)) -> CL_Var id,0
  | (DOP2(Cast,c,_)) -> aux (collapse_appl c)
  | (DOPN(AppL,cl)) -> let c,_ = aux (hd_vect cl) 
                        in c,Array.length(cl)-1
  | DOP2(Prod,_,DLAM(_,c)) -> CL_FUN,0
  | DOP0(Sort(_)) -> CL_SORT,0
  |  _ -> raise Not_found
in aux (collapse_appl t)
;;

(* class_of : Term.constr -> int *)


let class_of sigma t = 
let t,n,n1,i = (try let (cl,n) = constructor_at_head t in
               let (i,{cL_PARAM=n1}) = class_info cl in
               t,n,n1,i              
              with _ -> let t = Reduction.hnf_constr sigma t in
                        let (cl,n) = constructor_at_head t in
                        let (i,{cL_PARAM=n1}) = class_info cl in
                        t,n,n1,i) in
if n = n1 then t,i 
else raise Not_found
;;

(*

let class_of t = 
let (cl,n) = constructor_at_head t in
let (i,{cL_PARAM=n1}) = class_info cl in
if n = n1 then i 
else raise Not_found
;;
*)

let rec class_args_of c = 
let aux = function (DOP2(Cast,c,_)) -> class_args_of c
                 | (DOPN(AppL,cl)) -> Array.to_list(tl_vect(cl))
                 | _ -> []
in aux (collapse_appl c)
;;

(* verfications pour l'ajout d'une classe *)

let fully_applied id p p1 =
if p <> p1
then  errorlabstrm "fully_applied" 
          [< 'sTR"Wrong number of parameters for ";'sTR(string_of_id id) >]
;;

let rec arity_sort = function
    DOP0(Sort(Prop(_))) -> 0
  | DOP0(Sort(Type(_))) -> 0
  | DOP2(Prod,_,DLAM(_,c)) -> (arity_sort c) +1
  | DOP2(Cast,c,_) -> arity_sort c
  | _ -> raise Not_found
;;

let stre_of_cl = 
  function CL_SP sp ->
                    (match Lib.leaf_object_tag (objsp_of sp) with
                      "CONSTANT" ->
                       let (_,stre,_) = Environ.outConstant(Lib.map_leaf (objsp_of sp)) in stre
                      | _ -> NeverDischarge)
          | CL_Var id -> stre_of_var id
          | _ -> NeverDischarge
;;

(* coe_value : int -> Term.constr * bool *)

let coe_value i = 
let (_,{cOE_VALUE=v;cOE_ISID=b}) = coercion_info_from_index i in
v,b
;;

(* fonction de print *)

let string_of_strength = function NeverDischarge -> "(global)"
                                | DischargeAt sp -> "(disch@"^(string_of_path sp)
;;

let print_coercion_value v = (prterm v.cOE_VALUE._VAL);;

let print_index_coercion c = 
 let _,v = coercion_info_from_index c in
 print_coercion_value v;;

(*
let string_of_cl = function CL_Var id -> string_of_id id
                          | CL_SP sp -> string_of_id (basename sp)
                          | CL_IND (sp,i,s) -> s
                          | CL_FUN -> "FUNCLASS"
                          | CL_SORT -> "SORTCLASS";;
*)

let print_class i =
 let cl,x = class_info_from_index i in
 [< 'sTR x.cL_STR >];;

let print_path ((i,j),p) = [< 'sTR"["; 
                                   prlist_with_sep (fun () -> [< 'sTR"; " >])
                                   (fun c ->  print_index_coercion c) p;
                                   'sTR"] : "; print_class i; 'sTR" >-> ";
                                   print_class j >];;

let print_graph () = 
  [< prlist_with_sep pr_fnl print_path (!iNHERITANCE_GRAPH) >];;

let print_classes () = 
  [< prlist_with_sep pr_spc
     (fun (_,(cl,x)) -> 
        [< 'sTR x.cL_STR  (*; 'sTR(string_of_strength x.cL_STRE) *) >]) 
        (!cLASSES) >];;

let print_coercions () = 
  [< prlist_with_sep pr_spc
     (fun (_,(_,v)) -> [< (print_coercion_value v)
              (* ;'sTR(string_of_strength v.cOE_STRE)*) >]) (!cOERCIONS) >];;

let cl_of_id id = 
match (string_of_id id) with
 "FUNCLASS" -> CL_FUN
| "SORTCLASS" -> CL_SORT
| _ -> let v = Machops.global (gLOB(initial_sign())) id in
       let cl,_ = constructor_at_head v in cl
;;

let index_cl_of_id id =
try let cl = cl_of_id id in
    let i,_=class_info cl in i
with _ -> errorlabstrm "index_cl_of_id"
          [< 'sTR(string_of_id id); 'sTR" is not a defined class" >]
;;

let print_path_between ids idt = 
let i = (index_cl_of_id ids) in
let j = (index_cl_of_id idt) in
let p = (try lookup_path_between (i,j) 
         with _ -> errorlabstrm "index_cl_of_id"
           [< 'sTR"No path between ";'sTR(string_of_id ids); 'sTR" and ";'sTR(string_of_id ids) >]) in
print_path ((i,j),p);;

(* rajouter une coercion dans le graphe *)
 
let message_ambig l =
    [< 'sTR"Ambiguous paths : ";
       prlist_with_sep pr_fnl (fun ijp -> print_path ijp) l >];;

(* add_coercion_in_graph : int * int * int -> unit 
                         coercion,source,target *)

let add_coercion_in_graph (ic,source,target) =
let old_iNHERITANCE_GRAPH = (!iNHERITANCE_GRAPH) in
let ambig_paths = (ref []:((int * int) * inheritance_path) list ref) in

let try_add_new_path (p,i,j) =
    try (if i=j 
         then (if (snd (class_info_from_index i)).cL_PARAM > 0
               then (lookup_path_between (i,j);
                     ambig_paths := ((i,j),p)::!ambig_paths))
         else
          (lookup_path_between (i,j);
          ambig_paths := ((i,j),p)::!ambig_paths);false)
    with Not_found -> (add_new_path ((i,j),p);true)
in
let try_add_new_path1 (p,i,j) = (try_add_new_path (p,i,j);())
in
        (if try_add_new_path ([ic],source,target)
           then 
             (iter (fun ((s,t),p) ->
                if s<>t 
                then ((if (t = source)
                       then begin
                            try_add_new_path1 (p @ [ ic ],s,target);
                            (iter (fun ((u,v),q) ->
                                    if u<>v 
                                    then if (u = target) & (p <> q)
                                         then try_add_new_path1 (p @ [ ic ] @ q,s,v))
                                              old_iNHERITANCE_GRAPH)
                            end);
                       if (s = target)
                       then try_add_new_path1 (ic::p,source,t)))
                 old_iNHERITANCE_GRAPH);

if ((!ambig_paths) <> []) & is_mes_ambig()
then pPNL (message_ambig (!ambig_paths)))
;;


let add_new_coercion_in_graph ((coef,xf),cls,clt) =
let is,_ = class_info cls in
let it,_ = class_info clt in
let jf = add_new_coercion (coef,xf) in
add_coercion_in_graph (jf,is,it)
;;





(* val inCoercion : (coe_typ * coe_info_typ) * cl_typ * cl_typ  ->
                    -> Libobject.object 
   val outCoercion : Libobject.object -> (coe_typ * coe_info_typ) 
                         * cl_typ * cl_typ *)

let (inCoercion,outCoercion) =
    declare_object ("COERCION",
                    {load_function = (fun _ -> ());
                     cache_function =
                       (function  (_,x) -> add_new_coercion_in_graph x);
                     specification_function = (function x -> x)});;


