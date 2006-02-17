open Names
open Pp

open Libnames

let mk_prefix pre id = id_of_string (pre^(string_of_id id))
let mk_rel_id = mk_prefix "R_"

let msgnl m =
  ()

let invalid_argument s = raise (Invalid_argument s)

(* let idtbl = Hashtbl.create 29 *)
(* let reset_name () = Hashtbl.clear idtbl *)

(* let fresh_id s = *)
(*   try *)
(*     let id = Hashtbl.find idtbl s in *)
(*     incr id; *)
(*     id_of_string (s^(string_of_int !id)) *)
(*   with Not_found -> *)
(*     Hashtbl.add idtbl s (ref (-1)); *)
(*     id_of_string s *)

(* let fresh_name s = Name (fresh_id s) *)
(* let get_name ?(default="H") = function *)
(*   | Anonymous -> fresh_name default *)
(*   | Name n -> Name n *)



let fresh_id avoid s = Termops.next_global_ident_away true (id_of_string s) avoid

let fresh_name avoid s = Name (fresh_id avoid s)

let get_name avoid ?(default="H") = function
  | Anonymous -> fresh_name avoid default
  | Name n -> Name n

let array_get_start a =
  try 
    Array.init
      (Array.length a - 1)
      (fun i -> a.(i))
  with Invalid_argument "index out of bounds" -> 
    invalid_argument "array_get_start"
      
let id_of_name = function
    Name id -> id
  | _ -> raise Not_found

let locate  ref =
    let (loc,qid) = qualid_of_reference ref in
    Nametab.locate qid

let locate_ind ref =
  match locate ref with
    | IndRef x -> x
    | _ -> raise Not_found

let locate_constant ref =
  match locate ref with
    | ConstRef x -> x
    | _ -> raise Not_found


let locate_with_msg msg f x =
  try
    f x
  with
    | Not_found -> raise (Util.UserError("", msg))
    | e -> raise e


let filter_map filter f =
  let rec it = function
    | [] -> []
    | e::l ->
	if filter e
	then
	  (f e) :: it l
	else it l
  in
  it


let chop_rlambda_n  =
  let rec chop_lambda_n acc n rt =
      if n == 0
      then List.rev acc,rt
      else
	match rt with
	  | Rawterm.RLambda(_,name,t,b) -> chop_lambda_n ((name,t)::acc) (n-1) b
	  | _ -> raise (Util.UserError("chop_rlambda_n",str "chop_rlambda_n: Not enough Lambdas"))
  in
  chop_lambda_n []

let chop_rprod_n  =
  let rec chop_prod_n acc n rt =
      if n == 0
      then List.rev acc,rt
      else
	match rt with
	  | Rawterm.RProd(_,name,t,b) -> chop_prod_n ((name,t)::acc) (n-1) b
	  | _ -> raise (Util.UserError("chop_rprod_n",str "chop_rprod_n: Not enough products"))
  in
  chop_prod_n []



let list_union_eq eq_fun l1 l2 =
  let rec urec = function
    | [] -> l2
    | a::l -> if List.exists (eq_fun a) l2 then urec l else a::urec l
  in
  urec l1

let list_add_set_eq eq_fun x l =
  if List.exists (eq_fun x) l then l else x::l

  


let const_of_id id =
  let _,princ_ref = 
    qualid_of_reference (Libnames.Ident (Util.dummy_loc,id))
  in
  try Nametab.locate_constant princ_ref
  with Not_found -> Util.error ("cannot find "^ string_of_id id)

let def_of_const t =
   match (Term.kind_of_term t) with
    Term.Const sp -> 
      (try (match (Global.lookup_constant sp) with
             {Declarations.const_body=Some c} -> Declarations.force c
	     |_ -> assert false)
       with _ -> assert false)
    |_ -> assert false

let coq_constant s =
  Coqlib.gen_constant_in_modules "RecursiveDefinition" 
    (Coqlib.init_modules @ Coqlib.arith_modules) s;;

let constant sl s =
  constr_of_reference
    (Nametab.locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let find_reference sl s =
    (Nametab.locate (make_qualid(Names.make_dirpath 
			   (List.map id_of_string (List.rev sl)))
	       (id_of_string s)));;

let eq = lazy(coq_constant "eq")
let refl_equal = lazy(coq_constant "refl_equal")


(* (\************************************************\)  *)
(* (\* Should be removed latter                     *\) *)
(* (\* Comes from new induction  (cf Pierre)        *\) *)
(* (\************************************************\)  *)

(* open Sign *)
(* open Term *)

(* type elim_scheme =  *)

(* (\* { (\\* lists are in reverse order! *\\) *\) *)
(* (\*   params: rel_context;     (\\* (prm1,tprm1);(prm2,tprm2)...(prmp,tprmp) *\\) *\) *)
(* (\*   predicates: rel_context; (\\* (Qq, (Tq_1 -> Tq_2 ->...-> Tq_nq)), (Q1,...) *\\) *\) *)
(* (\*   branches: rel_context;    (\\* branchr,...,branch1 *\\) *\) *)
(* (\*   args: rel_context;       (\\* (xni, Ti_ni) ... (x1, Ti_1) *\\) *\) *)
(* (\*   indarg: rel_declaration option; (\\* Some (H,I prm1..prmp x1...xni) if present, None otherwise *\\) *\) *)
(* (\*   concl: types;            (\\* Qi x1...xni HI, some prmis may not be present *\\) *\) *)
(* (\*   indarg_in_concl:bool;    (\\* true if HI appears at the end of conclusion (dependent scheme) *\\) *\) *)
(* (\* } *\) *)



(* let occur_rel n c =  *)
(*   let res = not (noccurn n c) in *)
(*   res *)

(* let list_filter_firsts f l = *)
(*   let rec list_filter_firsts_aux f acc l = *)
(*     match l with *)
(*       | e::l' when f e -> list_filter_firsts_aux f (acc@[e]) l' *)
(*       | _ -> acc,l *)
(*   in *)
(*   list_filter_firsts_aux f [] l *)

(* let count_rels_from n c = *)
(*   let rels = Termops.free_rels c in *)
(*   let cpt,rg = ref 0, ref n in *)
(*   while Util.Intset.mem !rg rels do *)
(*     cpt:= !cpt+1; rg:= !rg+1; *)
(*   done; *)
(*   !cpt *)

(* let count_nonfree_rels_from n c = *)
(*   let rels = Termops.free_rels c in *)
(*   if Util.Intset.exists (fun x -> x >= n) rels then *)
(*     let cpt,rg = ref 0, ref n in *)
(*     while not (Util.Intset.mem !rg rels) do *)
(*       cpt:= !cpt+1; rg:= !rg+1; *)
(*     done; *)
(*     !cpt *)
(*   else raise Not_found *)

(* (\* cuts a list in two parts, first of size n. Size must be greater than n *\) *)
(* let cut_list n l = *)
(*   let rec cut_list_aux acc n l = *)
(*     if n<=0 then acc,l *)
(*     else match l with *)
(*       | [] -> assert false *)
(*       | e::l' -> cut_list_aux (acc@[e]) (n-1) l' in *)
(*   let res = cut_list_aux [] n l in *)
(*   res *)

(* let exchange_hd_prod subst_hd t = *)
(*   let hd,args= decompose_app t in mkApp (subst_hd,Array.of_list args) *)

(* let compute_elim_sig elimt  = *)
(*   (\* conclusion is the final (Qi ...) *\) *)
(*   let hyps,conclusion = decompose_prod_assum elimt in *)
(*   (\* ccl is conclusion where Qi (that is rel <something>) is replaced *)
(*      by a constant (Prop) to avoid it being counted as an arg or *)
(* parameter in the following. *\) *)
(*   let ccl = exchange_hd_prod mkProp conclusion in *)
(*   (\* indarg is the inductive argument if it exists. If it exists it is *)
(* the last hyp before the conclusion, so it is the first element of *)
(*      hyps. To know the first elmt is an inductive arg, we check if the *)
(*      it appears in the conclusion (as rel 1). If yes, then it is not *)
(*      an inductive arg, otherwise it is. There is a pathological case *)
(*      with False_inf where Qi is rel 1, so we first get rid of Qi in *)
(*      ccl. *\) *)
(*   (\* if last arg of ccl is an application then this a functional ind *)
(* principle *\) let last_arg_ccl =  *)
(*     try List.hd (List.rev (snd (decompose_app ccl)))  *)
(*     with Failure "hd" -> mkProp in (\* dummy constr that is not an app *)
(* *\) let hyps',indarg,dep =  *)
(*     if isApp last_arg_ccl  *)
(*     then  *)
(*       hyps,None , false (\* no HI at all *\) *)
(*     else  *)
(*       try  *)
(* 	if noccurn 1 ccl (\* rel 1 does not occur in ccl *\) *)
(* 	then *)
(* 	  List.tl hyps , Some (List.hd hyps), false (\* it does not *)
(* occur in concl *\) else *)
(* 	  List.tl hyps , Some (List.hd hyps) , true (\* it does occur in concl *\)  *)
(*       with Failure s -> Util.error "cannot recognise an induction schema" *)
(*   in *)

(*   (\* Arguments [xni...x1] must appear in the conclusion, so we count *)
(*      successive rels appearing in conclusion **Qi is not considered a *)
(* rel** *\) let nargs = count_rels_from  *)
(*     (match indarg with *)
(*       | None -> 1 *)
(*       | Some _ -> 2) ccl in *)
(*   let args,hyps'' = cut_list nargs hyps' in *)
(*   let rel_is_pred (_,_,c) = isSort (snd(decompose_prod_assum c)) in *)
(*   let branches,hyps''' =  *)
(*     list_filter_firsts (function x -> not (rel_is_pred x)) hyps'' *)
(*   in *)
(*   (\* Now we want to know which hyps remaining are predicates and which *)
(*      are parameters *\) *)
(*   (\* We rebuild  *)
     
(*      forall (x1:Ti_1) (xni:Ti_ni) (HI:I prm1..prmp x1...xni), DUMMY *)
(* x1...xni HI ^^^^^^^^^^^^^^^^^^^^^^^^^                  ^^ *)
(*                                           optional *)
(* opt *)

(*      Free rels appearing in this term are parameters. We catch all of *)
(*      them if HI is present. In this case the number of parameters is *)
(*      the number of free rels. Otherwise (principle generated by *)
(*      functional induction or by hand) WE GUESS that all parameters *)
(*      appear in Ti_js, IS THAT TRUE??. *)

(*      TODO: if we want to generalize to the case where arges are merged *)
(*      with branches (?) and/or where several predicates are cited in *)
(*      the conclusion, we should do something more precise than just *)
(*      counting free rels. *)
(*  *\) *)
(*   let concl_with_indarg =  *)
(*     match indarg with *)
(*     | None -> ccl *)
(*     | Some c -> it_mkProd_or_LetIn ccl [c] in *)
(*   let concl_with_args = it_mkProd_or_LetIn concl_with_indarg args in *)
(* (\*   let nparams2 = Util.Intset.cardinal (Termops.free_rels concl_with_args) in *\) *)
(*   let nparams =  *)
(*     try List.length (hyps'''@branches) - count_nonfree_rels_from 1 *)
(*       concl_with_args with Not_found -> 0 in *)
(*   let preds,params = cut_list (List.length hyps''' - nparams) hyps''' in *)
(*   let elimscheme = { *)
(*     params = params; *)
(*     predicates = preds; *)
(*     branches = branches; *)
(*     args = args; *)
(*     indarg = indarg; *)
(*     concl = conclusion; *)
(*     indarg_in_concl = dep; *)
(*   } *)
(*   in *)
(*   elimscheme *)

(* let get_params elimt =  *)
(*   (compute_elim_sig elimt).params *)
(* (\************************************************\)  *)
(* (\* end of Should be removed latter              *\) *)
(* (\* Comes from new induction  (cf Pierre)        *\) *)
(* (\************************************************\)  *)

