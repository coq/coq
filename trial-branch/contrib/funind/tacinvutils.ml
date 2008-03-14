(* tacinvutils.ml *)
(*s utilities *)

(*i*)
open Names
open Util
open Term
open Termops
open Coqlib
open Pp
open Printer
open Inductiveops
open Environ
open Declarations
open Nameops
open Evd
open Sign
open Reductionops
(*i*)

(*s printing of constr -- debugging *)

(* comment this line to see debug msgs *)
let msg x = () ;; let pr_lconstr c = str ""
  (* uncomment this to see debugging *)
let prconstr c =  msg (str"  " ++ pr_lconstr c ++ str"\n")
let prlistconstr lc = List.iter prconstr lc
let prstr s = msg(str s)

let prchr () = msg (str" (ret) \n")
let prNamedConstr s c = 
  begin
    msg(str "");
    msg(str(s^"==>\n ") ++ pr_lconstr c ++ str "\n<==\n");
    msg(str "");
  end

let prNamedLConstr_aux lc = 
  List.iter (prNamedConstr "#>") lc

let prNamedLConstr s lc = 
  begin
    prstr s;
    prNamedLConstr_aux lc
  end


(* FIXME: ref 1, pas bon, si? *)
let evarcpt = ref 0
let metacpt = ref 0
let mknewexist ()= 
  begin
    evarcpt := !evarcpt+1;
    !evarcpt,[||]
  end

let resetexist ()= evarcpt := 0

let mknewmeta ()= 
  begin
    metacpt := !metacpt+1;
    mkMeta (!metacpt)
  end

let resetmeta () = metacpt := 0

let  rec mkevarmap_from_listex lex =
  match lex with
	 | [] -> Evd.empty
	 | ((ex,_),typ)::lex' -> 
(*		  let _ = prstr "mkevarmap" in
		  let _ = prstr ("evar n. " ^ string_of_int ex ^ " ") in
		  let _ = prstr "OF TYPE: " in
		  let _ = prconstr typ in*)
		  let info = {
			 evar_concl = typ;
			 evar_hyps = empty_named_context_val;
			 evar_body = Evar_empty;
		         evar_extra = None} in
		  Evd.add (mkevarmap_from_listex lex') ex info

let mkEq typ c1 c2 = 
  mkApp (build_coq_eq(),[| typ; c1; c2|])

let mkRefl typ c1 = 
  mkApp ((build_coq_eq_data()).refl, [| typ; c1|])

let rec popn i c = if i<=0 then c else pop (popn (i-1) c)


(* Operations on names *)
let id_of_name = function
    Anonymous -> id_of_string "H"
  | Name id   -> id;;
let string_of_name nme = string_of_id (id_of_name nme)
let name_of_string str = Name (id_of_string str)
let newname_append nme str = 
  Name(id_of_string ((string_of_id (id_of_name nme))^str))

(* Substitutions in constr *)

let compare_constr_nosub t1 t2 =
  if compare_constr (fun _ _ -> false) t1 t2 
  then true
  else false

let rec compare_constr' t1 t2 =
  if compare_constr_nosub t1 t2 
  then true
  else (compare_constr (compare_constr') t1 t2)

let rec substitterm prof t by_t in_u =
  if (compare_constr' (lift prof t) in_u)
  then (lift prof by_t)
  else map_constr_with_binders succ 
    (fun i -> substitterm i t by_t) prof in_u


let apply_eqtrpl eq t =
  let r,(tb,b,by_t) = eq in
  substitterm 0 b by_t t

let apply_eqtrpl_lt lt eq =  List.map (apply_eqtrpl eq) lt

let apply_leqtrpl_t t leq =
  List.fold_left (fun x y -> apply_eqtrpl y x) t leq


let apply_refl_term eq t =
  let _,arr = destApp eq in
  let reli= (Array.get arr 1) in
  let by_t= (Array.get arr 2) in
  substitterm 0 reli by_t t

let apply_eq_leqtrpl leq eq =
  List.map 
    (function (r,(tb,b,t)) ->
		r,(tb, 
		(if isRel b then b else (apply_refl_term eq b)), apply_refl_term eq t))
	 leq



(* [(a b c) a] -> true *)
let constr_head_match u t=
  if isApp u 
  then 
	 let uhd,args= destApp u in
    uhd=t
  else false

(* My operations on constr *)
let lift1L l = (List.map (lift 1) l)
let mkArrow_lift t1 t2 = mkArrow t1 (lift 1 t2)
let mkProd_liftc nme c1 c2 = mkProd (nme,c1,(lift 1 c2))
(* prod_it_lift x [a1 a2 ...] *)
let prod_it_lift ini lcpl =
  List.fold_right (function a,b -> (fun c -> mkProd_liftc a b c)) ini lcpl;;

let prod_it_anonym_lift trm lst = List.fold_right mkArrow_lift lst trm

let lam_it_anonymous trm lst =
  List.fold_right 
	 (fun elt res -> mkLambda(Name(id_of_string "Hrec"),elt,res)) lst trm

let lambda_id id typeofid cstr =
  let cstr' = mkNamedLambda (id_of_string "FUNX") typeofid cstr in
  substitterm 0 id (mkRel 0) cstr'

let prod_id id typeofid cstr =
  let cstr' = mkNamedProd (id_of_string "FUNX") typeofid cstr in
  substitterm 0 id (mkRel 0) cstr'





let nth_dep_constructor indtype n =
  let sigma = Evd.empty and env = Global.env() in
  let indtypedef = find_rectype env sigma indtype in
  let indfam,_ = dest_ind_type indtypedef in
  let arr_cstr_summary = get_constructors env indfam in
  let cstr_sum = Array.get arr_cstr_summary n in
  build_dependent_constructor cstr_sum,  cstr_sum.cs_nargs


let rec buildrefl_from_eqs eqs = 
  match eqs with 
    | []  ->  []
    | cstr::eqs' -> 
        let eq,args = destApp cstr in
        (mkRefl (Array.get args 0) (Array.get args 2))
	:: (buildrefl_from_eqs eqs')




(* list of occurrences of a term inside another *)
(* Cofix will be wrong, not sure Fix is correct too *)
let rec hdMatchSub u t=
  let subres = 
    match kind_of_term u with
      | Lambda (nm,tp,cstr) | Prod (nm,tp,cstr) -> hdMatchSub (lift 1 cstr) t
      | Fix (_,(lna,tl,bl))  -> 
	  Array.fold_left 
	    (fun acc cstr -> acc @ hdMatchSub (lift (Array.length tl) cstr) t) 
	    [] bl
      | LetIn _  -> assert false
	  (* Correct? *)
      | _ -> fold_constr (fun l cstr -> l @ hdMatchSub cstr t) [] u
  in 
  if constr_head_match u t then u :: subres else subres


(* let hdMatchSub_list u lt = List.flatten (List.map (hdMatchSub u) lt) *)
let hdMatchSub_cpl u (d,f) = 
  let res = ref [] in
  begin
    for i = d to f do res := hdMatchSub u (mkRel i) @ !res done;
    !res
  end


(* destApplication raises an exception if [t] is not an application *)      
let exchange_hd_prod subst_hd t =
  let hd,args= destApplication t in mkApp (subst_hd,args)

(* substitute t by by_t in head of products inside in_u, reduces each
	product found  *)
let rec substit_red prof t by_t in_u =
  if constr_head_match in_u (lift prof t) 
  then
    let x = whd_beta (exchange_hd_prod (lift prof by_t) in_u) in
    x
  else
    map_constr_with_binders succ (fun i u -> substit_red i t by_t u) prof in_u

(* [exchange_reli_arrayi t=(reli x y ...) tarr (d,f)] exchange each
	reli by tarr.(f-i). *) 
let exchange_reli_arrayi tarr (d,f) t =
  let hd,args= destApp t in 
  let i = destRel hd in
  let res = whd_beta (mkApp (tarr.(f-i) ,args)) in
  res

let exchange_reli_arrayi_L tarr (d,f) = 
  List.map (exchange_reli_arrayi tarr (d,f))


(* expand all letins in a term, before building the principle. *)
let rec expand_letins mimick =
  match kind_of_term mimick with
    | LetIn(nme,cstr1, typ, cstr) ->
        let cstr' = substitterm 0 (mkRel 1) (lift 1 cstr1) cstr in
        expand_letins (pop cstr')
    | x -> map_constr expand_letins mimick
	  

(* Valeur d'une constante, or identity *)
let def_of_const t =
  match kind_of_term t with
    | Const sp -> 
		  (try 
			 match Global.lookup_constant sp with
              {const_body=Some c} -> force c
 				|_ -> assert false
			 with _ -> assert false)
    | _ -> t

(* nom d'une constante. Must be a constante. x*)
let name_of_const t =
    match (kind_of_term t) with
        Const cst -> Names.string_of_label (Names.con_label cst)
		|_ -> assert false
 ;;


(*i
***  Local Variables:
***  compile-command: "make -k tacinvutils.cmo"
***  test-tactic: "../../bin/coqtop -translate -q -batch -load-vernac-source ../../test-suite/success/Funind.v"
***  End:
i*)

