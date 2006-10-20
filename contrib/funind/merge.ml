(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Merging of induction principles. *)

(*i $Id: i*)

(*i*)
open Names
open Term
open Declarations
open Environ
(*i*)



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

(* Parameters shifting information. *)
type 'a shifted_params =
    {
      nprm1:'a;
      nprm2:'a;
      nuprm1:'a;
      nuprm2:'a;
    }

(* This type is used to deal with debruijn linked indices. When a
   variable is linke to a previous one, we will ignore it and refer to
   previous one. *)
type linked_var =
    | Linked of int
    | Unlinked of int

let prlinked x =
  match x with
    | Linked i -> Printf.sprintf "Linked %d" i
    | Unlinked i -> Printf.sprintf "Unlinked %d" i

let linkmonad f lnkvar = 
  match lnkvar with
    | Linked i -> Linked (f i)
    | Unlinked i -> Unlinked (f i)

let linklift lnkvar i = linkmonad (fun x -> x+i) lnkvar

(* This map is used to deal with debruijn linked indices. *)
module Link = Map.Make (struct type t = int let compare = Pervasives.compare end)
let poplink n l: 'a Link.t = 
  Link.fold 
    (fun k e acc -> Link.add (k-n) (linklift e (-k)) acc)
    l Link.empty 


let liftlink n l: 'a Link.t =
   Link.fold 
    (fun k e acc -> Link.add (k+n) (linklift e k) acc)
    l Link.empty 


(* Reverse the link map, keeping only linked vars, elements are list
   of int as several vars may be linked to the same var. *)
let revlinked lnk =
  Link.fold 
    (fun k x acc -> 
      match x with 
        | Unlinked _ -> acc 
        | Linked i -> 
            let old = try Link.find i acc with Not_found -> [] in
            Link.add i (k::old) acc)
    lnk Link.empty


let verify_inds mib1 mib2 =
  if not mib1.mind_finite then Util.error "First argument is coinductive";
  if not mib2.mind_finite then Util.error "Second argument is coinductive";
  if mib1.mind_ntypes <> 1 then Util.error "First argument is mutual";
  if mib2.mind_ntypes <> 1 then Util.error "Second argument is mutual";
  ()

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
let shift_linked_params mib1 mib2 lnk =
  let linked_targets = revlinked lnk in
  let is_param_of_mib2 x = 
    x >= mib1.mind_nparams && x - mib1.mind_nparams < mib2.mind_nparams_rec in
  let is_param_of_mib2 x = 
    x >= mib1.mind_nparams && x - mib1.mind_nparams < mib2.mind_nparams_rec in
  let i = ref 0 in
  let found = ref false in
  while !i < mib1.mind_nparams_rec && not !found do 
    let linked = try Link.find !i linked_targets with Not_found -> [] in
    if List.exists (fun x -> not (is_param_of_mib2 x)) linked then found := true;
    i:=!i+1;
  done; (* i should be (fst unparam or last rec param) + 1 (starting from 0) *)
  let n_params1,n_unparams1 = 
    if !found then !i-1,mib1.mind_nparams_rec+1-(!i) else mib1.mind_nparams_rec,0 in
  i:=mib1.mind_nparams;
  found := false;
  while !i < mib1.mind_nparams + mib2.mind_nparams_rec && not !found do 
    let linked = try Link.find !i lnk with Not_found -> assert false in
    (match linked with
      | Linked k -> if not (is_param_of_mib2 k) then found := true
      | Unlinked _ -> ());
    i:=!i+1;
  done;
  let n_params2,n_unparams2 = 
    if not !found then mib2.mind_nparams_rec, 0
    else
      let unp = mib1.mind_nparams_rec + mib2.mind_nparams_rec - !i + 1 in
      mib2.mind_nparams_rec - unp , unp in
  { nprm1=n_params1; nuprm1=n_unparams1; nprm2=n_params2; nuprm2=n_unparams2}



let rec listmapsome f l = 
  match l with
    | [] -> []
    | e::l' -> 
        match f e with
          | None -> listmapsome f l'
          | Some res -> res::listmapsome f l'


let apply_link lnk typ = 
  Link.fold 
    (fun k x acc -> 
      match x with
        | Linked i -> substitterm 0 (mkRel k) (mkRel i) acc
        | Unlinked _ -> acc) 
    lnk typ 

let ind1name = "__ind1"
let ind2name = "__ind2"
let newindname = "__newind"
(* Operations on names *)
let id_of_name = function
    Anonymous -> id_of_string "H"
  | Name id   -> id;;
let name_of_string str = Name (id_of_string str)
let string_of_name nme = string_of_id (id_of_name nme)


let lift_ldecl n ldecl = List.map (fun (x,y) -> x,lift n y) ldecl

let isAppf f x = 
  try
    let _ = Printf.printf "isreccall %s\n" (string_of_id (destVar x) ) in
    string_of_id (destVar x) = f with _ -> false

exception NoMerge

let merge_app c1 c2 id1 id2 newid = 
  match kind_of_term c1 , kind_of_term c2 with
    | App(f1, arr1), App(f2,arr2) 
        when isAppf id1 f1 && isAppf id2 f2 -> 
        mkApp (mkVar (id_of_string newid) , Array.append arr1 arr2)
    | App(f1, arr1), App(f2,arr2)  -> 
        let _ = Printf.printf "id1 = %s ; id1 = %s" id1 id2 in
        let _ = Tacinvutils.prNamedConstr "f1" f1 in
        let _ = Tacinvutils.prNamedConstr "f2" f2 in
        raise NoMerge
    | _ -> 
        let _ = Printf.printf "Not an App" in
        raise NoMerge


let rec merge_rec_hyps accrec ltyp =
  match ltyp with
    | [] -> []
    | (nme,t) as e ::lt -> 
        match kind_of_term t with
          | App(f, arr) when isAppf ind2name f -> 
              let rechyps = 
                List.map 
                  (fun (nme,ind) -> 
                  match kind_of_term ind with
                    | App(i,args) -> 
                        nme, 
                        mkApp(mkVar(id_of_string newindname), (Array.append args arr))
                    | _ -> assert false)
                  accrec in
              let nhyps = List.length rechyps in
              (List.fold_left (fun acc x -> x :: lift_ldecl 1 acc) [] rechyps)
              @ merge_rec_hyps (lift_ldecl nhyps accrec) (lift_ldecl nhyps lt)
          | _ -> e :: merge_rec_hyps (lift_ldecl 1 accrec) lt
              

let rec merge_types accrec1 (ltyp1:(name * constr) list)
    concl1 (ltyp2:(name * constr) list) concl2: (name * constr) list * constr = 
  let res = 
  match ltyp1 with
    | [] -> 
        let rechyps = merge_rec_hyps accrec1 ltyp2 in
        let suppl_hyps = List.length rechyps - List.length ltyp2 in
        rechyps 
          , merge_app (lift (List.length rechyps) concl1) (lift suppl_hyps concl2) 
            ind1name ind2name newindname
    | (nme,t1)as e ::lt1 -> 
        match kind_of_term t1 with
          | App(f,carr) when isAppf ind1name f -> 
              merge_types (e::accrec1) (lift_ldecl (-1) lt1)
                (lift (-1) concl1) ltyp2 concl2
          | _ -> 
              let recres, recconcl2 =
                merge_types (lift_ldecl 1 accrec1) lt1 concl1 ltyp2 concl2 in
              ((nme,t1) :: recres) , recconcl2
  in
  res


(* Return a type if the 2 constructors are not incompatible *)
let merge_one_constructor lnk shift (typcstr1:types) (typcstr2:types):types list =
  let prms1,rest1 = decompose_prod_n shift.nprm1 typcstr1 in
  let prms2,rest2 = decompose_prod_n shift.nprm2 typcstr2 in
  let newlnk = liftlink shift.nprm1 lnk in
  let hyps1,concl1 = decompose_prod (lift shift.nprm2 rest1) in
  let hyps2,concl2' = decompose_prod (apply_link newlnk rest2) in
  let ltyp,concl2 = merge_types [] (List.rev hyps1) concl1 (List.rev hyps2) concl2' in
  let typ = compose_prod (List.rev ltyp) concl2 (* FIXME *) in
  
  let _ = Tacinvutils.prNamedConstr "rest1 = " rest1 in
  let _ = Tacinvutils.prNamedConstr "rest2 = " rest2 in
  let _ = Tacinvutils.prNamedConstr "TYP" typ in
  let typwithprms = compose_prod (prms1@prms2) typ in
  let _ = Tacinvutils.prNamedConstr "TYPWTHP" typwithprms in
  let _ = print_string "\n***\n" in
  [typwithprms]

let rec merge_constructors lnk shift (typcstr1:types list) (typcstr2:types list) =
  List.flatten 
    (List.map
        (fun typ1 -> 
          List.map
            (fun typ2 -> 
              let typ1 =
                substitterm 0 (mkRel 1) (mkVar (id_of_string ind1name)) typ1 in
              let typ2 =
                substitterm 0 (mkRel 1) (mkVar (id_of_string ind2name)) typ2 in
              let _ = Tacinvutils.prNamedConstr "Whole typ1 = " typ1 in
              let _ = Tacinvutils.prNamedConstr "Wholetyp2 = " typ2 in
              let _ = print_string "\n\n" in
              merge_one_constructor lnk shift typ1 typ2)
            typcstr2) 
        typcstr1) 
    
let rec merge_inductive_body (lnk: linked_var Link.t) (shift:int shifted_params)
    (oib1:one_inductive_body) (oib2:one_inductive_body)  =
  let lcstr1 = Array.to_list oib1.mind_user_lc in
  let lcstr2 = Array.to_list oib2.mind_user_lc in
  let types_of_cstrs = merge_constructors lnk shift lcstr1 lcstr2 in
  ()

let rec merge_mutual_inductive_body (lnk: linked_var Link.t)
    (mib1:mutual_inductive_body) (mib2:mutual_inductive_body) 
    (shift:int shifted_params) =
  merge_inductive_body lnk shift mib1.mind_packets.(0) mib2.mind_packets.(0) 




let merge_inductive (ind1: inductive) (ind2: inductive) (lnk: linked_var Link.t) =
  let env = Global.env() in
  let mib1,ib1 = Inductive.lookup_mind_specif env ind1 in
  let mib2,ib2 = Inductive.lookup_mind_specif env ind2 in
  let _ = verify_inds mib1 mib2 in
  let shift_prm = shift_linked_params mib1 mib2 lnk in
  merge_mutual_inductive_body lnk mib1 mib2 shift_prm


let merge (cstr1:constr) (cstr2:constr) (args1:constr array) (args2:constr array) =
  let env = Global.env() in
  let ind1,_cstrlist1 = Inductiveops.find_inductive env Evd.empty cstr1 in
  let ind2,_cstrlist2 = Inductiveops.find_inductive env Evd.empty cstr2 in
  let arrmem arr e = 
    let x = ref 0 in
    let found = ref false in
    while not !found & !x < Array.length arr do
      if arr.(!x)=e then found := true else x:=!x+1
    done;
    if not !found  then None else Some !x in
  let i = ref (-1) in
  let lnk_partial = 
    Array.fold_left (fun acc c -> i:=!i+1; Link.add !i (Unlinked !i) acc) Link.empty args2 in
  let ilinked = ref !i in
  let lnk_all = 
    Array.fold_left (
        fun acc c -> 
          match arrmem args1 c with
            | Some j -> i:=!i+1;Link.add !i (Linked j) acc
            | None -> i:=!i+1; ilinked:=!ilinked+1;Link.add !i (Unlinked !ilinked) acc)
      lnk_partial args2 in
(*  let _ = print_string "\n\n Links =      " in
  let _ = Link.iter (fun k e -> Printf.printf "%d -> %s, " k (prlinked e)) lnk_all in *)
  merge_inductive ind1 ind2 lnk_all

let id_of_name = function
    Anonymous -> id_of_string "H"
  | Name id   -> id;;
let string_of_name nme = string_of_id (id_of_name nme)

let showind (id:identifier) =
  let cstrid = Tacinterp.constr_of_id (Global.env()) id in
  let ind1,cstrlist = Inductiveops.find_inductive (Global.env()) Evd.empty cstrid in
  let mib1,ib1 = Inductive.lookup_mind_specif (Global.env()) ind1 in
  List.iter (fun (nm, optcstr, tp) -> 
    print_string (string_of_name nm^":");
    Tacinvutils.prconstr tp; print_string "\n") 
    ib1.mind_arity_ctxt;
  (match ib1.mind_arity with
    | Monomorphic x ->
        Printf.printf "arity :"; Tacinvutils.prconstr x.mind_user_arity
    | Polymorphic x -> 
        Printf.printf "arity : universe?");
  Array.iteri 
    (fun i x -> Printf.printf"type constr %d :" i ; Tacinvutils.prconstr x)
    ib1.mind_user_lc
;;



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
