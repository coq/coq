(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Merging of induction principles. *)

(*i $Id: i*)

open Util
open Topconstr
open Vernacexpr
open Pp
open Names
open Term
open Declarations
open Environ
open Rawterm
open Rawtermops

(** {1 Utilities}  *)

(** {2 Useful operations on constr and rawconstr} *)

(** Substitutions in constr *)
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

let lift_ldecl n ldecl = List.map (fun (x,y) -> x,lift n y) ldecl

let understand = Pretyping.Default.understand Evd.empty (Global.env())

(** Operations on names *)
let id_of_name = function
    Anonymous -> id_of_string "H"
  | Name id   -> id;;
let name_of_string str = Name (id_of_string str)
let string_of_name nme = string_of_id (id_of_name nme)

(** [isVarf f x] returns [true] if term [x] is of the form [(Var f)]. *)
let isVarf f x = 
    match x with
      | RVar (_,x) -> x = f 
      | _ -> false


(** {2 Debugging} *)
(* comment this line to see debug msgs *)
(* let msg x = () ;; let pr_lconstr c = str "" *)
(* uncomment this to see debugging *)
let prconstr c =  msg (str"  " ++ Printer.pr_lconstr c ++ str"\n")
let prlistconstr lc = List.iter prconstr lc
let prstr s = msg(str s)
let prNamedConstr s c = 
  begin
    msg(str "");
    msg(str(s^"==>\n ") ++ Printer.pr_lconstr c ++ str "\n<==\n");
    msg(str "");
  end
let prNamedRConstr s c = 
  begin
    msg(str "");
    msg(str(s^"==>\n ") ++ Printer.pr_rawconstr c ++ str "\n<==\n");
    msg(str "");
  end
let prNamedLConstr_aux lc = 
  List.iter (prNamedConstr "#>") lc
let prNamedLConstr s lc = 
  begin
    prstr s;
    prNamedLConstr_aux lc
  end
let prNamedLDecl s lc = 
  begin
    prstr s; prstr "\n";
    List.iter (fun (nm,_,tp) -> prNamedConstr (string_of_name nm) tp) lc;
    prstr "\n";
  end

let showind (id:identifier) =
  let cstrid = Tacinterp.constr_of_id (Global.env()) id in
  let ind1,cstrlist = Inductiveops.find_inductive (Global.env()) Evd.empty cstrid in
  let mib1,ib1 = Inductive.lookup_mind_specif (Global.env()) ind1 in
  List.iter (fun (nm, optcstr, tp) -> 
    print_string (string_of_name nm^":");
    prconstr tp; print_string "\n") 
    ib1.mind_arity_ctxt;
  (match ib1.mind_arity with
    | Monomorphic x ->
        Printf.printf "arity :"; prconstr x.mind_user_arity
    | Polymorphic x -> 
        Printf.printf "arity : universe?");
  Array.iteri 
    (fun i x -> Printf.printf"type constr %d :" i ; prconstr x)
    ib1.mind_user_lc

(** {2 Misc} *)

exception Found of int

(* Array scanning *)
let array_find (arr: 'a array) (pred: int -> 'a -> bool): int option = 
  try
    for i=0 to Array.length arr - 1 do if pred i (arr.(i)) then raise (Found i) done;
    None
  with Found i -> Some i

let array_prfx (arr: 'a array) (pred: int -> 'a -> bool): int =
  try
    for i=0 to Array.length arr - 1 do if pred i (arr.(i)) then raise (Found i) done;
    Array.length arr (* all elt are positive *)
  with Found i -> i

let array_fold_lefti (f: int -> 'a -> 'b -> 'a) (acc:'a) (arr:'b array): 'a = 
  let i = ref 0 in 
  Array.fold_left 
    (fun acc x -> 
      let res = f !i acc x in i := !i + 1; res)
    acc arr

(* Like list_chop but except that [i] is the size of the suffix of [l]. *)
let list_chop_end i l =
  let size_prefix = List.length l -i in
  if size_prefix < 0 then failwith "list_chop_end"
  else list_chop size_prefix l

let list_fold_lefti (f: int -> 'a -> 'b -> 'a) (acc:'a) (arr:'b list): 'a = 
  let i = ref 0 in 
  List.fold_left 
    (fun acc x -> 
      let res = f !i acc x in i := !i + 1; res)
    acc arr

let list_filteri (f: int -> 'a -> bool) (l:'a list):'a list = 
  let i = ref 0 in 
  List.filter (fun x -> let res = f !i x in i := !i + 1; res) l


(** Iteration module *)
module For = 
struct
  let rec map i j (f: int -> 'a)  = if i>j then [] else f i :: (map (i+1) j f)
  let rec foldup i j (f: 'a -> int -> 'a) acc = 
    if i>j then acc else let newacc = f acc i in foldup (i+1) j f newacc
  let rec folddown i j (f: 'a -> int -> 'a) acc = 
    if i>j then acc else let newacc = f acc j in folddown i (j-1) f newacc
  let fold i j = if i<j then foldup i j else folddown i j
end


(** {1 Parameters shifting and linking information} *)

(** This type is used to deal with debruijn linked indices. When a
    variable is linked to a previous one, we will ignore it and refer
    to previous one. *)
type linked_var =
    | Linked of int
    | Unlinked

(** When merging two graphs, parameters may become regular arguments,
    and thus be shifted. This type describe the result of computing
    the changes. *)
type 'a shifted_params =
    {
      nprm1:'a;
      nprm2:'a;
      prm2_unlinked:'a list; (* ranks of unlinked params in nprms2 *)
      nuprm1:'a;
      nuprm2:'a;
      nargs1:'a;
      nargs2:'a;
    }


let prlinked x =
  match x with
    | Linked i -> Printf.sprintf "Linked %d" i
    | Unlinked -> Printf.sprintf "Unlinked"

let linkmonad f lnkvar = 
  match lnkvar with
    | Linked i -> Linked (f i)
    | Unlinked -> Unlinked

let linklift lnkvar i = linkmonad (fun x -> x+i) lnkvar

(* This map is used to deal with debruijn linked indices. *)
module Link = Map.Make (struct type t = int let compare = Pervasives.compare end)

let pr_links l = 
  Printf.printf "links:\n";
  Link.iter (fun k e -> Printf.printf "%d : %s\n" k (prlinked e)) l;
  Printf.printf "_____________\n"

type 'a merged_arg =
    | Prm_stable of 'a
    | Prm_linked of 'a
    | Prm_arg of 'a
    | Arg_stable of 'a
    | Arg_linked of 'a

type merge_infos =
    {
      ident:identifier; (* new inductive name *)
      mib1: mutual_inductive_body;
      oib1: one_inductive_body; 
      mib2: mutual_inductive_body;
      oib2: one_inductive_body; 
      (* Array of links of the first inductive (should be all stable) *)
      lnk1: int merged_arg array;
      (* Array of links of the second inductive (point to the first ind param/args) *)
      lnk2: int merged_arg array;
      (* number of rec params of ind1 which remai rec param in merge *)
      nrecprms1: int;
      (* number of other rec params of ind1 (which become non parm) *)
      notherprms1:int;
      (* list of decl of rec parms from ind1 which remain parms *)
      recprms1: rel_declaration list;
      (* List of other rec parms from ind1 *)
      otherprms1: rel_declaration list; (* parms that became args *)
      (* number of rec params of ind2 which remain rec param in merge (and not linked) *)
      nrecprms2: int;
      (* number of other rec params of ind2 (which become non parm) *)
      notherprms2:int;
      (* list of decl of rec parms from ind2 which remain parms (and not linked) *)
      recprms2: rel_declaration list;
      (* List of other rec parms from ind2 (which are linked or become non parm) *)
      otherprms2: rel_declaration list;      
      (* list of decl of ordinary args from ind1 which remain args in merge *)
(*      args1:rel_declaration list;
      (* list of decl of ordinary args from ind2 which remain args in merge *)
      args2:rel_declaration list;
      nargs1:int;
      nargs2:int*)
    }


let pr_merginfo x =
  let i,s=
    match x with 
      | Prm_linked i -> i,"Prm_linked"
      | Arg_linked i -> i,"Arg_linked"
      | Prm_stable i ->  i,"Prm_stable"
      | Prm_arg i ->  i,"Prm_arg"
      | Arg_stable i ->  i,"Arg_stable" in
  (Printf.sprintf "%s(%d)" s i)

let isPrm_stable x = match x with Prm_stable _ -> true | _ -> false

let isArg_stable x = match x with Arg_stable _ -> true | _ -> false

let filter_shift_stable (lnk:int merged_arg array) (l:'a list): 'a list =
  let prms = list_filteri (fun i _ -> isPrm_stable lnk.(i)) l in
  let args = list_filteri (fun i _ -> isArg_stable lnk.(i)) l in
  prms@args

(** Reverse the link map, keeping only linked vars, elements are list
    of int as several vars may be linked to the same var. *)
let revlinked lnk =
  For.fold 0 (Array.length lnk - 1)
    (fun acc k -> 
      match lnk.(k) with 
        | Unlinked -> acc 
        | Linked i -> 
            let old = try Link.find i acc with Not_found -> [] in
            Link.add i (k::old) acc)
    Link.empty





(** {1 Utilities for merging} *)

let ind1name = id_of_string "__ind1"
let ind2name = id_of_string "__ind2"

(** Performs verifications on two graphs before merging: they must not
    be co-inductive, and for the moment they must not be mutual
    either. *)
let verify_inds mib1 mib2 =
  if not mib1.mind_finite then error "First argument is coinductive";
  if not mib2.mind_finite then error "Second argument is coinductive";
  if mib1.mind_ntypes <> 1 then error "First argument is mutual";
  if mib2.mind_ntypes <> 1 then error "Second argument is mutual";
  ()

(** [apply_link lnk typ] returns the type [type] in which each
     debruijn index linked in [lnk] has been lifted to its
     correpsonding new index. *)
let apply_link lnk typ = 
  Link.fold 
    (fun k x acc -> 
      match x with
        | Linked i -> substitterm 0 (mkRel k) (mkRel i) acc
        | Unlinked -> acc) 
    lnk typ 


(** {1 Merging function graphs} *)

(** [shift_linked_params mib1 mib2 lnk] Computes how many recursively
    uniform parameters of mutual inductives mib1 and mib2 remain
    uniform when linked by [lnk].
    
    Explanation: The two inductives have parameters, some of the first
    are recursively uniform.

   (I x1 x2 ... xk ... xn)
   (J y1 y2 ... xl ... ym)

   Problem is, if some rec unif params are linked to non rec unif
   ones, they become non rec (and the following too). This function
   computes how many rec unif params we get from both inductives. *)
let shift_linked_params mib1 mib2 (lnk1:linked_var array) (lnk2:linked_var array) id =
  let linked_targets = revlinked lnk2 in
  let is_param_of_mib1 x = x < mib1.mind_nparams_rec in
  let is_param_of_mib2 x = x < mib2.mind_nparams_rec in
  let is_targetted_by_non_recparam_lnk1 i = 
    try 
      let targets = Link.find i linked_targets in 
      List.exists (fun x -> not (is_param_of_mib2 x)) targets
    with Not_found -> false in
  let mlnk1 = 
    Array.mapi
      (fun i lkv -> 
        let isprm = is_param_of_mib1 i in
        let prmlost = is_targetted_by_non_recparam_lnk1 i in
        match isprm , prmlost with
          | true , true -> Prm_arg i (* recparam becoming ordinary *)
          | true , false -> Prm_stable i (* recparam remains recparam*)
          | false , _ -> Arg_stable i) (* Args of lnk1 are not linked *)
      lnk1 in
  let mlnk2 = 
    Array.mapi
      (fun i lkv -> 
        let isprm = is_param_of_mib2 i in
        (* FIXME: should use mlnk1.(i) instead of lnk2.(i) *)
        match isprm , lnk2.(i) with
          | true , Linked j when not (is_param_of_mib1 j) -> 
              Prm_arg j (* recparam becoming ordinary *)
          | true , Linked j -> Prm_linked j (*recparam linked to recparam*)
          | true , Unlinked -> Prm_stable i (* recparam remains recparam*)
          | false , Linked j -> Arg_linked j (* Args of lnk2 lost *)
          | false , Unlinked -> Arg_stable i) (* Args of lnk2 remains *)
      lnk2 in

  let oib1 = mib1.mind_packets.(0) in
  let oib2 = mib2.mind_packets.(0) in
  (* count params remaining params *)
  let n_params1 = array_prfx mlnk1 (fun i x -> not (isPrm_stable x)) in
  let n_params2 = array_prfx mlnk2 (fun i x -> not (isPrm_stable x)) in

  let recprms1,otherprms1 = 
    list_fold_lefti
      (fun i (acc1,acc2) x -> 
        match mlnk1.(i) with
          | Prm_stable _ -> x::acc1 , acc2 
          | Prm_arg _ | Arg_stable _ -> acc1 , x::acc2 
          | _ -> acc1 , acc2) (* Prm_linked and Arg_xxx = forget it *)
      ([],[])
      (List.rev oib1.mind_arity_ctxt)
  in
  let recprms2,otherprms2 = 
    list_fold_lefti
      (fun i (acc1,acc2) x -> 
        match mlnk2.(i) with
          | Prm_stable _ -> x::acc1 , acc2 
          | Prm_arg _ | Arg_stable _ -> acc1 , x::acc2 
          | _ -> acc1 , acc2) (* Prm_linked and Arg_xxx = forget it *)
      ([],[])
      (List.rev oib2.mind_arity_ctxt)
  in
  
  {
    ident=id;
    mib1=mib1;
    oib1 = oib1;
    mib2=mib2;
    oib2 = oib2;
    lnk1 = mlnk1;
    lnk2 = mlnk2;
    nrecprms1 = n_params1;
    recprms1 = recprms1;
    otherprms1 = otherprms1;
    notherprms1 = Array.length mlnk1 - n_params1;
    nrecprms2 = n_params2;
    recprms2 = recprms2;
    otherprms2 = otherprms2;
    notherprms2 = Array.length mlnk2 - n_params2;
  }




(** {1 Merging functions} *)

exception NoMerge

(* lnk is an link array of *all* args (from 1 and 2) *)
let merge_app c1 c2 id1 id2 shift = 
  let lnk = Array.append shift.lnk1 shift.lnk2 in
  match c1 , c2 with
    | RApp(_,f1, arr1), RApp(_,f2,arr2) when isVarf id1 f1 && isVarf id2 f2 -> 
        let args = filter_shift_stable lnk (arr1 @ arr2) in
        RApp (dummy_loc,RVar (dummy_loc,shift.ident) , args)
    | RApp(_,f1, arr1), RApp(_,f2,arr2)  -> raise NoMerge
    | _ -> raise NoMerge

let merge_app_unsafe c1 c2 shift = 
  let lnk = Array.append shift.lnk1 shift.lnk2 in
  match c1 , c2 with
    | RApp(_,f1, arr1), RApp(_,f2,arr2) -> 
        let args = filter_shift_stable lnk (arr1 @ arr2) in
        RApp (dummy_loc,RVar(dummy_loc,shift.ident) , args)
    | _ -> raise NoMerge

let onefoud = ref false

(* Heuristic when merging two lists of hypothesis: merge every rec
   calls of nrach 1 with all rec calls of branch 2. *)
let rec merge_rec_hyps shift accrec (ltyp:(Names.name * Rawterm.rawconstr) list) =
  match ltyp with
    | [] -> []
    | (nme,(RApp(_,f, largs) as t)) :: lt when isVarf ind2name f -> 
        let _ = onefoud := true in
        let rechyps = 
          List.map 
            (fun (nme,ind) -> 
              match ind with
                | RApp(_,i,args) -> nme, merge_app_unsafe t ind shift
                | _ -> assert false)
            accrec in
        rechyps @ merge_rec_hyps shift accrec lt
    | e::lt -> e :: merge_rec_hyps shift accrec lt


let rec build_suppl_reccall (accrec:(name * rawconstr) list) concl2 shift = 
  List.map (fun (nm,tp) -> (nm,merge_app_unsafe tp concl2 shift)) accrec

(* TODO: reecrire cette heuristique *)
let rec merge_types shift accrec1 (ltyp1:(name * rawconstr) list)
    concl1 (ltyp2:(name * rawconstr) list) concl2
    : (name * rawconstr) list * rawconstr = 
  let res = 
  match ltyp1 with
    | [] -> 
        let _ = onefoud := false in
        let rechyps =(*If accrec1 is empty, use conlusion instead of accrec1 
                       to merge rec calls*)
          merge_rec_hyps shift
            (if accrec1<>[] then accrec1 else [name_of_string "concl1",concl1])
            ltyp2 in
        (* If no reccalls has been found in ltyp2 and accrec1 is not
           empty, create one with accrec1 + concl2  *)
        let suppl_rechyps = 
          if accrec1 = [] || !onefoud then []
          else build_suppl_reccall accrec1 concl2 shift in
        rechyps @ suppl_rechyps , merge_app concl1 concl2 ind1name ind2name shift
    | (nme,t1)as e ::lt1 -> 
        match t1 with
          | RApp(_,f,carr) when isVarf ind1name f -> 
              merge_types shift (e::accrec1) lt1 concl1 ltyp2 concl2
          | _ -> 
              let recres, recconcl2 =
                merge_types shift accrec1 lt1 concl1 ltyp2 concl2 in
              ((nme,t1) :: recres) , recconcl2
  in
  res


(** [build_link_map_aux allargs1 allargs2 shift] returns the mapping of
    linked args [allargs2] to target args of [allargs1] as specified
    in [shift]. [allargs1] and [allargs2] are in reverse order.  Also
    returns the list of unlinked vars of [allargs2]. *)
let build_link_map_aux (allargs1:identifier array) (allargs2:identifier array)
    (lnk:int merged_arg array) =
  array_fold_lefti
    (fun i acc e -> 
      if i = Array.length lnk - 1 then acc (* functional arg, not in allargs *)
      else 
        match e with 
          | Prm_linked j | Arg_linked j -> Idmap.add allargs2.(i) allargs1.(j) acc
          | _ -> acc)
    Idmap.empty lnk

let build_link_map allargs1 allargs2 lnk =
  let allargs1 =
    Array.of_list (List.rev (List.map (fun (x,y) -> id_of_name x) allargs1)) in
  let allargs2 =
    Array.of_list (List.rev (List.map (fun (x,y) -> id_of_name x) allargs2)) in
  build_link_map_aux allargs1 allargs2 lnk


(** [merge_one_constructor lnk shift typcstr1 typcstr2] merges the two
    constructor rawtypes [typcstr1] and [typcstr2].  [typcstr1] and
    [typcstr2] contain all parameters (including rec. unif. ones) of
    their inductive.

    if  [typcstr1] and [typcstr2] are of the form:

    forall recparams1, forall ordparams1, H1a -> H2a... (I1 x1 y1 ... z1)
    forall recparams2, forall ordparams2, H2b -> H2b... (I2 x2 y2 ... z2)

    we build:

    forall recparams1 (recparams2 without linked params),
     forall ordparams1 (ordparams2 without linked params),
      H1a' -> H2a' -> ...  -> H2a' -> H2b' -> ... 
        -> (newI x1 ... z1 x2 y2 ...z2 without linked params)

    where Hix' have been adapted, ie: 
      - linked vars have been changed,
      - rec calls to I1 and I2 have been replaced by rec calls to
        newI. More precisely calls to I1 and I2 have been merge by an
        experimental heuristic (in particular if n o rec calls for I1
        or I2 is found, we use the conclusion as a rec call). See
        [merge_types] above.

    Precond: vars sets of [typcstr1] and [typcstr2] must be disjoint.

    TODO: return nothing if equalities (after linking) are contradictory. *)
let merge_one_constructor (shift:merge_infos) (typcstr1:rawconstr)
    (typcstr2:rawconstr) : rawconstr =
  (* -1 because last arg is functional result ?? *)
  (* FIXME: les noms des parametres corerspondent en principe au
     parametres du niveau mib, mais il faudrait s'en assurer *)
  let nargs1 = shift.mib1.mind_nparams + shift.oib1.mind_nrealargs -1 in
  let nargs2 = shift.mib2.mind_nparams + shift.oib2.mind_nrealargs -1 in
  let allargs1,rest1 = raw_decompose_prod_n nargs1 typcstr1 in
  let allargs2,rest2 = raw_decompose_prod_n nargs2 typcstr2 in  
  (* Build map of linked args of [typcstr2], and apply it to [typcstr2]. *)
  let linked_map = build_link_map allargs1 allargs2 shift.lnk2 in
  let rest2 = change_vars linked_map rest2 in
  let hyps1,concl1 = raw_decompose_prod rest1 in
  let hyps2,concl2' = raw_decompose_prod rest2 in
  let ltyp,concl2 = merge_types shift [] (List.rev hyps1) concl1 (List.rev hyps2) concl2' in
  let typ = raw_compose_prod concl2 (List.rev ltyp) in
  let revargs1 = 
    list_filteri (fun i _ -> isArg_stable shift.lnk1.(i)) (List.rev allargs1) in
  let revargs2 = 
    list_filteri (fun i _ -> isArg_stable shift.lnk2.(i)) (List.rev allargs2) in
(*  let args1 , _ = list_chop_end shift.nrecprms1 allargs1 in
  let args2 , _ = list_chop_end shift.nrecprms2 allargs2_filtered in *)
  let typwithprms = raw_compose_prod typ (List.rev revargs2 @ List.rev revargs1) in
  typwithprms (* useless *)

let merge_constructor_id id1 id2:identifier = 
  let s1 = string_of_id id1 in
  let s2 = string_of_id id2 in
  id_of_string (s1^s2)

(** [merge_constructors lnk shift avoid] merges the two list of
    constructor [(name*type)]. These are translated to rawterms
    first, each of them having distinct var names. *)
let rec merge_constructors (shift:merge_infos) (avoid:Idset.t)
    (typcstr1:(identifier * types) list) 
    (typcstr2:(identifier * types) list) : (identifier * rawconstr) list =
  List.flatten 
    (List.map
        (fun (id1,typ1) -> 
          let typ1 = substitterm 0 (mkRel 1) (mkVar ind1name) typ1 in
          let rawtyp1 = Detyping.detype false (Idset.elements avoid) [] typ1 in
          let idsoftyp1:Idset.t = ids_of_rawterm rawtyp1 in
          List.map
            (fun (id2,typ2) -> 
              let typ2 = substitterm 0 (mkRel 1) (mkVar ind2name) typ2 in
              (* Avoid also rawtyp1 names *)
              let avoid2 = Idset.union avoid idsoftyp1 in
              let rawtyp2 = Detyping.detype false (Idset.elements avoid2) [] typ2 in
              let typ = merge_one_constructor shift rawtyp1 rawtyp2 in
              let newcstror_id = merge_constructor_id id1 id2 in
              newcstror_id , typ)
            typcstr2)
        typcstr1)
    
(** [merge_inductive_body lnk shift avoid oib1 oib2] merges two
    inductive bodies [oib1] and [oib2], linking with [lnk], params
    info in [shift], avoiding identifiers in [avoid]. *)
let rec merge_inductive_body (shift:merge_infos) avoid (oib1:one_inductive_body)
    (oib2:one_inductive_body) : (identifier * rawconstr) list =
  let lcstr1 = Array.to_list oib1.mind_user_lc in
  let lcstr2 = Array.to_list oib2.mind_user_lc in
  let lcstr1 = List.combine (Array.to_list oib1.mind_consnames) lcstr1 in
  let lcstr2 = List.combine (Array.to_list oib2.mind_consnames) lcstr2 in
  let newshift = shift (* { shift with
    nargs1 = oib1.mind_nrealargs;
    nargs2 = oib2.mind_nrealargs; } *) in
  let res = merge_constructors newshift avoid lcstr1 lcstr2 in
  res

(** [build_raw_params prms_decl avoid] returns a list of variables
    attributed to the list of decl [prms_decl], avoiding names in
    [avoid]. *)
let build_raw_params prms_decl avoid =
  let dummy_constr = compose_prod prms_decl mkProp in
  let dummy_rawconstr = Detyping.detype false avoid [] dummy_constr in
  let res,_ = raw_decompose_prod dummy_rawconstr in
  res , (avoid @ (Idset.elements (ids_of_rawterm dummy_rawconstr)))

(** [merge_mutual_inductive_body lnk mib1 mib2 shift] merge mutual
    inductive bodies [mib1] and [mib2] linking vars with
    [lnk]. [shift] information on parameters of the new inductive.
    For the moment, inductives are supposed to be non mutual.
*)
let rec merge_mutual_inductive_body
    (mib1:mutual_inductive_body) (mib2:mutual_inductive_body) 
    (shift:merge_infos) =
  (* Mutual not treated, we take first ind body of each. *)
  let nprms1 = mib1.mind_nparams_rec in (* n# of rec uniform parms of mib1 *)
  let prms1 = (* rec uniform parms of mib1 *)
    List.map (fun (x,_,y) -> x,y) (fst (list_chop nprms1 mib1.mind_params_ctxt)) in

  (* useless: *)
  let prms1_named,avoid' = build_raw_params prms1 [] in
  let prms2_named,avoid = build_raw_params prms1 avoid' in
  let avoid:Idset.t = List.fold_right Idset.add avoid Idset.empty in  
  (* *** *)

  merge_inductive_body shift avoid mib1.mind_packets.(0) mib2.mind_packets.(0) 

  

(* TODO: Define and use everywhere needed a function [is_linked i lnk] *)
(* TODO: Define and use everywhere needed a function List.filteri,
   List.fold_lefti... Probably with a initial int for the counter. *)
let merge_rec_params_and_arity params1 params2 shift (concl:constr) = 
  let params = shift.recprms1 @ shift.recprms2 in
  let resparams, _ =
    List.fold_left
      (fun (acc,env) (nme,_,tp) -> 
        let typ = Constrextern.extern_constr false env tp in
        let newenv = Environ.push_rel (nme,None,tp) env in
        LocalRawAssum ([(dummy_loc,nme)] , typ) :: acc , newenv)
      ([],Global.env())
      params in
  let concl = Constrextern.extern_constr false (Global.env()) concl in
  let arity,_ = 
    List.fold_left 
      (fun (acc,env) (nm,_,c) -> 
        let typ = Constrextern.extern_constr false env c in
        let newenv = Environ.push_rel (nm,None,c) env in
        CProdN (dummy_loc, [[(dummy_loc,nm)],typ] , acc) , newenv)
      (concl,Global.env())
      (shift.otherprms1@shift.otherprms2) in  
  resparams,arity

  

(** [rawterm_list_to_inductive_expr ident rawlist] returns the
    induct_expr corresponding to the the list of constructor types
    [rawlist], named ident.
    FIXME: params et cstr_expr (arity) *)
let rawterm_list_to_inductive_expr mib1 mib2 shift
    (rawlist:(identifier * rawconstr) list):inductive_expr =
  let rawterm_to_constr_expr = (* build a constr_expr from a rawconstr *)
    Options.with_option Options.raw_print (Constrextern.extern_rawtype Idset.empty) in
  let lident = dummy_loc, shift.ident in
  let bindlist , cstr_expr = (* params , arities  , FIXME: verify this *)
    merge_rec_params_and_arity 
      mib1.mind_params_ctxt mib2.mind_params_ctxt shift mkSet in
  let cstor_cpt = ref 0 in
  let bld_cor_name id =
    cstor_cpt := !cstor_cpt + 1;
    id_of_string (string_of_id id ^ string_of_int !cstor_cpt) in
  let lcstor_expr : (bool * (lident * constr_expr)) list  = 
    List.map (* zeta_normalize t ? *)
      (fun (id,t) -> false, ((dummy_loc,bld_cor_name id),rawterm_to_constr_expr t))
      rawlist in  
  lident , bindlist , cstr_expr , lcstor_expr

(** [merge_inductive ind1 ind2 lnk] merges two graphs, linking
    variables specified in [lnk]. Graphs are not supposed to be mutual
    inductives for the moment. *)
let merge_inductive (ind1: inductive) (ind2: inductive) 
    (lnk1: linked_var array) (lnk2: linked_var array) id =
  let env = Global.env() in
  let mib1,_ = Inductive.lookup_mind_specif env ind1 in
  let mib2,_ = Inductive.lookup_mind_specif env ind2 in
  let _ = verify_inds mib1 mib2 in (* raises an exception if something wrong *)
  (* compute params that become ordinary args (because linked to ord. args) *)
  let shift_prm = shift_linked_params mib1 mib2 lnk1 lnk2 id in
  let rawlist = merge_mutual_inductive_body mib1 mib2 shift_prm in
  let indexpr = rawterm_list_to_inductive_expr mib1 mib2 shift_prm rawlist in
  (* Declare inductive *)
  Command.build_mutual [(indexpr,None)] true (* means: not coinductive *)



let merge (cstr1:constr) (cstr2:constr) (args1:constr array) (args2:constr array) id =
  let env = Global.env() in
  let ind1,_cstrlist1 = Inductiveops.find_inductive env Evd.empty cstr1 in
  let ind2,_cstrlist2 = Inductiveops.find_inductive env Evd.empty cstr2 in
  let lnk1 = (* args1 are unlinked. FIXME? mergescheme (G x x) ?? *)
    Array.mapi (fun i c -> Unlinked) args1 in
  let lnk2 = (* args2 may be linked to args1 members. FIXME: same 
                   as above: vars may be linked inside args2?? *)
    Array.mapi
      (fun i c -> 
        match array_find args1 (fun i x -> x=c) with
          | Some j -> (Linked j)
          | None -> Unlinked) 
      args2 in
  let resa = merge_inductive ind1 ind2 lnk1 lnk2 id in
  resa





(* @article{ bundy93rippling,
    author = "Alan Bundy and Andrew Stevens and Frank van Harmelen and Andrew Ireland and Alan Smaill",
    title = "Rippling: A Heuristic for Guiding Inductive Proofs",
    journal = "Artificial Intelligence",
    volume = "62",
    number = "2",
    pages = "185-253",
    year = "1993",
    url = "citeseer.ist.psu.edu/bundy93rippling.html" }

 *)
(* 
*** Local Variables: ***
*** compile-command: "make -C ../.. contrib/funind/merge.cmo" ***
*** indent-tabs-mode: nil ***
*** End: ***
*)
