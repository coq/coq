(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Tacmach
open Proof_type
open Libobject
open Reductionops
open Term
open Termops
open Names
open Entries
open Libnames
open Nameops
open Util
open Pp
open Printer
open Environ
open Tactics 
open Tacticals
open Vernacexpr
open Safe_typing
open Nametab
open Decl_kinds
open Constrintern

let replace = ref (fun _ _ -> assert false)
let register_replace f = replace := f

type setoid =
    { set_a : constr;
      set_aeq : constr;
      set_th : constr
    }

type 'a setoid_class =
   ACSetoid  of 'a      (*the equivalence relation of the setoid or the setoid*)
 | ACLeibniz of constr  (*the carrier of the setoid*)

type 'a morphism =
    { lem : constr;
      args : 'a setoid_class list;
      output : 'a setoid_class;
      lem2 : constr option
    }

type funct =
    { f_args : constr list;
      f_output : constr
    }

type morphism_class =
   ACMorphism of setoid morphism
 | ACFunction of funct

let subst_mps_in_setoid_class subst =
 function
    ACSetoid  t -> ACSetoid  (subst_mps subst t)
  | ACLeibniz t -> ACLeibniz (subst_mps subst t) 

let constr_setoid_class_of_setoid_setoid_class =
 function
    ACSetoid setoid -> ACSetoid setoid.set_aeq
  | ACLeibniz t -> ACLeibniz t
 

let constr_of c = Constrintern.interp_constr Evd.empty (Global.env()) c

let constant dir s = Coqlib.gen_constant "Setoid_replace" ("Setoids"::dir) s

let global_constant dir s =Coqlib.gen_constant "Setoid_replace" ("Init"::dir) s

let current_constant id =
  try
    global_reference id
  with Not_found ->
    anomaly ("Setoid: cannot find " ^ (string_of_id id))

(* Setoid_theory *)

let coq_Setoid_Theory = lazy(constant ["Setoid"] "Setoid_Theory")

let coq_seq_refl = lazy(constant ["Setoid"] "Seq_refl")
let coq_seq_sym = lazy(constant ["Setoid"] "Seq_sym")
let coq_seq_trans = lazy(constant ["Setoid"] "Seq_trans")

let coq_fleche = lazy(constant ["Setoid"] "fleche")

(* Coq constants *)

let coqiff = lazy(global_constant ["Logic"] "iff")

let coqeq = lazy(global_constant ["Logic"] "eq")

let coqconj = lazy(global_constant ["Logic"] "conj")
let coqand = lazy(global_constant ["Logic"] "and")
let coqproj1 = lazy(global_constant ["Logic"] "proj1")
let coqproj2 = lazy(global_constant ["Logic"] "proj2")

(************************* Table of declared setoids **********************)


(* Setoids are stored in a table which is synchronised with the Reset mechanism. *)

let setoid_table = ref Gmap.empty

let setoid_table_add (s,th) = setoid_table := Gmap.add s th !setoid_table
let setoid_table_find s = Gmap.find s !setoid_table
let setoid_table_mem s = Gmap.mem s !setoid_table

let prsetoid s =
 str "(" ++ prterm s.set_a ++ str "," ++ prterm s.set_aeq ++ str ")"

let prsetoid_class =
 function
    ACSetoid eq  ->
     (try prsetoid (setoid_table_find eq)
      with Not_found ->
       str "[[ Error: setoid on equality " ++ prterm eq ++ str " not found! ]]")
  | ACLeibniz ty -> prterm ty

let prmorphism k m =
  prterm k ++ str ": " ++
  prlist_with_sep (fun () -> str " -> ") prsetoid_class m.args ++
  str " -> " ++ prsetoid_class m.output


(* A function that gives back the only setoid on a given carrier *)
(*CSC: this implementation is really inefficient. I should define a new
  map to make it efficient. However, is this really worth of? *)
let default_setoid_for_carrier a =
 let rng = Gmap.rng !setoid_table in
 match List.filter (fun {set_a=set_a} -> set_a = a) rng with
    [] -> ACLeibniz a
  | setoid::tl ->
     if tl <> [] then
      msg_warning
       (str "There are several setoids whose carrier is " ++ prterm a ++
         str ". The setoid " ++ prsetoid setoid ++
         str " is randomly chosen.") ;
     ACSetoid setoid

let setoid_morphism_of_constr_morphism =
 let setoid_setoid_class_of_constr_setoid_class =
  function
     ACLeibniz t -> ACLeibniz t
   | ACSetoid aeq ->
      ACSetoid (try setoid_table_find aeq with Not_found -> assert false)
 in
  function mor ->
   let args' = List.map setoid_setoid_class_of_constr_setoid_class mor.args in
   let output' = setoid_setoid_class_of_constr_setoid_class mor.output in
    {mor with args=args' ; output=output'}

let subst_setoid subst setoid = 
  let set_a' = subst_mps subst setoid.set_a in
  let set_aeq' = subst_mps subst setoid.set_aeq in
  let set_th' = subst_mps subst setoid.set_th in
    if set_a' == setoid.set_a
      && set_aeq' == setoid.set_aeq
      && set_th' == setoid.set_th
    then
      setoid
    else
      { set_a = set_a' ;
	set_aeq = set_aeq' ;
	set_th = set_th' ;
      }
      
let equiv_list () = List.map (fun x -> x.set_aeq) (Gmap.rng !setoid_table)

let _ = 
  Summary.declare_summary "setoid-table"
    { Summary.freeze_function = (fun () -> !setoid_table);
      Summary.unfreeze_function = (fun t -> setoid_table := t);
      Summary.init_function = (fun () -> setoid_table := Gmap .empty);
      Summary.survive_module = true;
      Summary.survive_section = false }

(* Declare a new type of object in the environment : "setoid-theory". *)

let (setoid_to_obj, obj_to_setoid)=
  let cache_set (_,(s, th)) =
   if setoid_table_mem s then
    begin
     let old_setoid = setoid_table_find s in
      msg_warning
       (str "The setoid " ++ prsetoid th ++ str " is redeclared. " ++
        str "The new declaration justified by " ++
         prterm th.set_th ++ str " replaces the old declaration justified by "++
         prterm old_setoid.set_th ++ str ".")
    end ;
   setoid_table_add (s,th)
  and subst_set (_,subst,(s,th as obj)) =
    let s' = subst_mps subst s in
    let th' = subst_setoid subst th in
      if s' == s && th' == th then obj else
	(s',th')
  and export_set x = Some x 
  in 
    declare_object {(default_object "setoid-theory") with
		      cache_function = cache_set;
		      load_function = (fun i o -> cache_set o);
		      subst_function = subst_set;
		      classify_function = (fun (_,x) -> Substitute x);
		      export_function = export_set}

(******************************* Table of declared morphisms ********************)

(* Setoids are stored in a table which is synchronised with the Reset mechanism. *)

let morphism_table = ref Gmap.empty

let morphism_table_find m = Gmap.find m !morphism_table
let morphism_table_add (m,c) =
 let old =
  try
   morphism_table_find m
  with
   Not_found -> []
 in
  try
   let old_morph =
    List.find
     (function mor -> mor.args = c.args && mor.output = c.output) old
   in
    msg_warning
     (str "The morphism " ++ prmorphism m old_morph ++ str " is redeclared. " ++
      str "The new declaration whose compatibility is granted by " ++
       prterm c.lem ++
       (match c.lem2 with None -> str "" | Some t-> str " and " ++ prterm t)
       ++ str " replaces the old declaration whose" ++
       str " compatibility was granted by " ++
       prterm old_morph.lem ++
       (match old_morph.lem2 with
          None -> str ""
        | Some t-> str " and "++ prterm t) ++ str ".")
  with
   Not_found -> morphism_table := Gmap.add m (c::old) !morphism_table

let find_morphism_fleche () =
 let fleche_constr = (Lazy.force coq_fleche) in
 try
  let mor =
   List.find
    (function {args=args; output=output} as morphism ->
      output = ACSetoid (Lazy.force coqiff) &&
      List.for_all (function c -> c = ACSetoid (Lazy.force coqiff)) args)
     (morphism_table_find fleche_constr)
  in
   setoid_morphism_of_constr_morphism mor
 with
  Not_found -> assert false

let subst_morph subst morph = 
  let lem' = subst_mps subst morph.lem in
  let args' = list_smartmap (subst_mps_in_setoid_class subst) morph.args in
  let output' = subst_mps_in_setoid_class subst morph.output in
  let lem2' = option_smartmap (subst_mps subst) morph.lem2 in
    if lem' == morph.lem
      && args' == morph.args
      && output' == morph.output
      && lem2' == morph.lem2
    then
      morph
    else
      { lem = lem' ;
	args = args' ;
	output = output' ;
	lem2 = lem2'
      }


let _ = 
  Summary.declare_summary "morphism-table"
    { Summary.freeze_function = (fun () -> !morphism_table);
      Summary.unfreeze_function = (fun t -> morphism_table := t);
      Summary.init_function = (fun () -> morphism_table := Gmap .empty);
      Summary.survive_module = true;
      Summary.survive_section = false }

(* Declare a new type of object in the environment : "morphism-definition". *)

let (morphism_to_obj, obj_to_morphism)=
  let cache_set (_,(m, c)) = morphism_table_add (m, c)
  and subst_set (_,subst,(m,c as obj)) = 
    let m' = subst_mps subst m in
    let c' = subst_morph subst c in
      if m' == m && c' == c then obj else
	(m',c')
  and export_set x = Some x 
  in 
    declare_object {(default_object "morphism-definition") with
		      cache_function = cache_set;
		      load_function = (fun i o -> cache_set o);
		      subst_function = subst_set;
		      classify_function = (fun (_,x) -> Substitute x);
		      export_function = export_set}

(************************** Printing setoids and morphisms **********************)

let print_setoids () =
  Gmap.iter
   (fun k setoid ->
     assert (k=setoid.set_aeq) ;
     ppnl (str"Setoid " ++ prsetoid setoid ++ str"; equivalence relation properties granted by " ++
      prterm setoid.set_th))
   !setoid_table ;
  Gmap.iter
   (fun k l ->
     List.iter
      (fun ({lem=lem ; lem2=lem2} as mor) ->
        ppnl (str "Morphism " ++ prmorphism k mor ++
        str ". Compatibility granted by " ++
        prterm lem ++ 
         (match lem2 with None -> str"" | Some t -> str " and " ++ prterm t) ++
        str "."))
      l) !morphism_table
;;

(************************** Adding a setoid to the database *********************)

(* Add a Setoid to the database after a type verification. *)

let eq_lem_common_sign env a eq =
  let na = named_hd env a Anonymous in
  let ne = named_hd env eq Anonymous in
  [(ne,None,mkApp (eq, [|(mkRel 3);(mkRel 2)|]));
   (ne,None,mkApp (eq, [|(mkRel 4);(mkRel 3)|]));
   (na,None,a);(na,None,a);(na,None,a);(na,None,a)]

(* Proof of (a,b,c,d:A)(eq a b)->(eq c d)->(eq a c)->(eq b d) *)
let eq_lem_proof env a eq sym trans = 
  let sign = eq_lem_common_sign env a eq in
  let ne = named_hd env eq Anonymous in
  let sign = (ne,None,mkApp (eq, [|(mkRel 6);(mkRel 4)|]))::sign in
  let ccl = mkApp (eq, [|(mkRel 6);(mkRel 4)|]) in
  let body =
    mkApp (trans,
      [|(mkRel 6);(mkRel 7);(mkRel 4);
        (mkApp (sym, [|(mkRel 7);(mkRel 6);(mkRel 3)|]));
	  (mkApp (trans,
	    [|(mkRel 7);(mkRel 5);(mkRel 4);(mkRel 1);(mkRel 2)|]))|]) in
  let p = it_mkLambda_or_LetIn body sign in
  let t = it_mkProd_or_LetIn ccl sign in
  (p,t)

(* Proof of (a,b,c,d:A)(eq a b)->(eq c d)->((eq a c)<->(eq b d)) *)
let eq_lem2_proof env a eq sym trans =
  let sign = eq_lem_common_sign env a eq in
  let ccl1 =
    mkArrow
      (mkApp (eq, [|(mkRel 6);(mkRel 4)|]))
      (mkApp (eq, [|(mkRel 6);(mkRel 4)|])) in
  let ccl2 =
    mkArrow
      (mkApp (eq, [|(mkRel 5);(mkRel 3)|]))
      (mkApp (eq, [|(mkRel 7);(mkRel 5)|])) in
  let ccl = mkApp (Lazy.force coqand, [|ccl1;ccl2|]) in
  let body =
    mkApp ((Lazy.force coqconj),
    [|ccl1;ccl2;
      lambda_create env
	(mkApp (eq, [|(mkRel 6);(mkRel 4)|]),
	(mkApp (trans,
	  [|(mkRel 6);(mkRel 7);(mkRel 4);
	    (mkApp (sym, [|(mkRel 7);(mkRel 6);(mkRel 3)|]));
	    (mkApp (trans,
	      [|(mkRel 7);(mkRel 5);(mkRel 4);(mkRel 1);(mkRel 2)|]))|])));
      lambda_create env
        (mkApp (eq, [|(mkRel 5);(mkRel 3)|]),
        (mkApp (trans,
          [|(mkRel 7);(mkRel 6);(mkRel 5);(mkRel 3);
            (mkApp (trans,
              [|(mkRel 6);(mkRel 4);(mkRel 5);(mkRel 1);
                (mkApp (sym, [|(mkRel 5);(mkRel 4);(mkRel 2)|]))|]))|])))|])
  in
  let p = it_mkLambda_or_LetIn body sign in
  let t = it_mkProd_or_LetIn ccl sign in
  (p,t)

let gen_eq_lem_name =
  let i = ref 0 in
    function () -> 
      incr i;
      make_ident "setoid_eq_ext" (Some !i)

let add_setoid a aeq th =
  let env = Global.env () in
    if (is_conv env Evd.empty (Typing.type_of env Evd.empty th)
	  (mkApp ((Lazy.force coq_Setoid_Theory), [| a; aeq |])))
    then (Lib.add_anonymous_leaf 
	    (setoid_to_obj 
	       (aeq, { set_a = a;
		     set_aeq = aeq;
		     set_th = th}));
	  let sym = mkApp ((Lazy.force coq_seq_sym), [|a; aeq; th|]) in
	  let trans = mkApp ((Lazy.force coq_seq_trans), [|a; aeq; th|]) in
	  let (eq_morph, eq_morph_typ) = eq_lem_proof env a aeq sym trans in
	  let (eq_morph2, eq_morph2_typ) = eq_lem2_proof env a aeq sym trans in
	    Options.if_verbose ppnl (prterm a ++str " is registered as a setoid");
	    let eq_ext_name = gen_eq_lem_name () in 
	    let eq_ext_name2 = gen_eq_lem_name () in 
	    let _ = Declare.declare_constant eq_ext_name
		      ((DefinitionEntry {const_entry_body = eq_morph; 
		                       const_entry_type = Some eq_morph_typ;
                                       const_entry_opaque = true}),
		       IsProof Lemma) in
	    let _ = Declare.declare_constant eq_ext_name2
		      ((DefinitionEntry {const_entry_body = eq_morph2; 
				       const_entry_type = Some eq_morph2_typ;
                                       const_entry_opaque = true}),
		       IsProof Lemma) in
	    let eqmorph = (current_constant eq_ext_name) in
	    let eqmorph2 = (current_constant eq_ext_name2) in
	      (Lib.add_anonymous_leaf
		 (morphism_to_obj (aeq,
				   { lem = eqmorph;
                                     args = [ACSetoid aeq; ACSetoid aeq];
                                     output = ACSetoid (Lazy.force coqiff);
				     lem2 = (Some eqmorph2)})));
	      Options.if_verbose ppnl (prterm aeq ++str " is registered as a morphism"))
    else errorlabstrm "Add Setoid" (str "Not a valid setoid theory")

(* The vernac command "Add Setoid" *)
let add_setoid a aeq th =
  add_setoid (constr_of a) (constr_of aeq) (constr_of th)

(***************** Adding a morphism to the database ****************************)

(* We maintain a table of the currently edited proofs of morphism lemma
   in order to add them in the morphism_table when the user does Save *)

let edited = ref Gmap.empty

let new_edited id m = 
  edited := Gmap.add id m !edited

let is_edited id =
  Gmap.mem id !edited

let no_more_edited id =
  edited := Gmap.remove id !edited

let what_edited id =
  Gmap.find id !edited

let check_is_dependent t n =
  let rec aux t i n =
    if (i<n)
    then (dependent (mkRel i) t) || (aux t (i+1) n)
    else false
  in aux t 0 n

let gen_lem_name m = match kind_of_term m with 
  | Var id -> add_suffix id "_ext"
  | Const kn -> add_suffix (id_of_label (label kn)) "_ext"
  | Ind (kn, i) -> add_suffix (id_of_label (label kn)) ((string_of_int i)^"_ext")
  | Construct ((kn,i),j) -> add_suffix
      (id_of_label (label kn)) ((string_of_int i)^(string_of_int j)^"_ext")
  | _ -> errorlabstrm "New Morphism" (str "The term " ++ prterm m ++ str "is not a known name")

let gen_lemma_tail m args body n =
  let l = (List.length args) in
  let a1 = Array.create l (mkRel 0) in
  let a2 = Array.create l (mkRel 0) in
  let rec aux i n = function
    | (ACSetoid _)::tl -> 
	a1.(i) <- (mkRel n);
	a2.(i) <- (mkRel (n-1));
	aux (i+1) (n-2) tl
    | (ACLeibniz _)::tl ->
	a1.(i) <- (mkRel n);
	a2.(i) <- (mkRel n);
	aux (i+1) (n-1) tl
    | [] -> () in 
    aux 0 n args;
    if (match body with ACSetoid setoid when setoid.set_aeq = Lazy.force coqiff -> true | _ -> false)
    then mkArrow (mkApp (m,a1)) (lift 1 (mkApp (m, a2)))
    else
     match body with
        ACSetoid setoid ->
         mkApp (setoid.set_aeq, [|(mkApp (m, a1)); (mkApp (m, a2))|])
      | ACLeibniz t ->
         mkApp ((Lazy.force coqeq), [|t; (mkApp (m, a1)); (mkApp (m, a2))|])

let gen_lemma_middle m args body n =
  let rec aux i n =
   function
    | [] -> gen_lemma_tail m args body n
    | (ACSetoid setoid)::tl ->
        let t = setoid.set_a in
	mkArrow (mkApp (setoid.set_aeq, 
			[|(mkRel i); (mkRel (i-1))|])) (aux (i-1) (n+1) tl)
    | (ACLeibniz t)::tl -> aux (i-1) n tl
  in aux n n args

let gen_compat_lemma env m body args = 
  let rec aux n =
   function
      (ACSetoid setoid)::tl ->
        let t = setoid.set_a in
	 prod_create env (t,(prod_create env (t, (aux (n+2) tl))))
    | (ACLeibniz t)::tl ->
	prod_create env (t, (aux (n+1) tl))
    | [] -> gen_lemma_middle m args body n
  in aux 0 args

let new_morphism m id hook =
  let env = Global.env() in
  let typeofm = (Typing.type_of env Evd.empty m) in
  let typ = (nf_betaiota typeofm) in  (* nf_bdi avant, mais bug *)
  let (argsrev, output) = (decompose_prod typ) in
  let args_ty = (List.map snd (List.rev argsrev)) in
    if (args_ty=[])
    then errorlabstrm "New Morphism"
     (str "The term " ++ prterm m ++ str " is not a product")
    else if (check_is_dependent typ (List.length args_ty))
    then  errorlabstrm "New Morphism"
     (str "The term " ++ prterm m ++ str" should not be a dependent product")
    else (
     let args = List.map default_setoid_for_carrier args_ty in
     let output = default_setoid_for_carrier output in
     let lem = (gen_compat_lemma env m output args) in
      new_edited id (m,args,output);
      Pfedit.start_proof id (IsGlobal (Proof Lemma)) 
       (Declare.clear_proofs (Global.named_context ()))
       lem hook;
      (Options.if_verbose msg (Pfedit.pr_open_subgoals ())))

let rec sub_bool n = function
  | [] -> []
  | (ACSetoid setoid)::tl -> (setoid, n)::(sub_bool (n-2) tl)
  | (ACLeibniz _)::tl -> (sub_bool (n-1) tl)

let gen_lemma_iff_tail m mext args n k =
  let a1 = Array.create k (mkRel 0) in
  let a2 = Array.create k (mkRel 0) in
  let nb = List.length args in
  let b1 = Array.create nb (mkRel 0) in
  let b2 = Array.create nb (mkRel 0) in
  let rec aux i j = function
    |[] -> ()
    |(ACSetoid _)::tl ->
       (a1.(i) <- (mkRel j);
	a1.(i+1) <- (mkRel (j-1));
	a2.(i) <- (mkRel (j-1));
	a2.(i+1) <- (mkRel j);
	aux (i+2) (j-2) tl)
    |(ACLeibniz _)::tl ->
       (a1.(i) <- (mkRel j);
	a2.(i) <- (mkRel j);
	aux (i+1) (j-1) tl) in
  let rec aux2 i j = function
    | ({set_a=a; set_th=th; set_aeq=aeq},p)::tl -> 
	a1.(i) <- (mkRel j);
	a2.(i) <- mkApp ((Lazy.force coq_seq_sym),
		   [|a; aeq; th; (mkRel p); (mkRel (p-1)); (mkRel j)|]);
	aux2 (i+1) (j-1) tl
    | [] -> () in
  let rec aux3 i j = function
    | (ACSetoid _)::tl -> 
	b1.(i) <- (mkRel j);
	b2.(i) <- (mkRel (j-1));
	aux3 (i+1) (j-2) tl
    | (ACLeibniz _)::tl ->
	b1.(i) <- (mkRel j);
	b2.(i) <- (mkRel j);
	aux3 (i+1) (j-1) tl
    | [] -> () in 
    aux 0 k args;
    aux2 n (k-n) (sub_bool k args);
    aux3 0 k args;
    mkApp ((Lazy.force coqconj),
	   [|(mkArrow (mkApp (m,b1)) (lift 1 (mkApp (m, b2))));
	     (mkArrow (mkApp (m,b2)) (lift 1 (mkApp (m, b1))));
	     (mkApp (mext, a1));(mkApp (mext, a2))|])

let gen_lemma_iff_middle env m mext args n =
  let rec aux i k =
   function
      [] -> gen_lemma_iff_tail m mext args n k
    | (ACSetoid setoid)::tl ->
	lambda_create env
         ((mkApp (setoid.set_aeq, [|(mkRel i); (mkRel (i-1))|])),
          (aux (i-1) (k+1) tl))
    | (ACLeibniz t)::tl -> aux (i-1) k tl
  in aux n n args

let gen_lem_iff env m mext args =
  let rec aux n =
   function
      (ACSetoid setoid)::tl ->
        let t = setoid.set_a in
	lambda_create env (t,(lambda_create env (t, (aux (n+2) tl))))
    | (ACLeibniz t)::tl ->
	lambda_create env (t, (aux (n+1) tl))
    | [] -> gen_lemma_iff_middle env m mext args n
  in aux 0 args

let add_morphism lem_name (m,args,output) =
 let env = Global.env() in
 let mext = (current_constant lem_name) in
 let args_constr= List.map constr_setoid_class_of_setoid_setoid_class args in
 let output_constr = constr_setoid_class_of_setoid_setoid_class output in
   (if (match output with ACSetoid setoid when setoid.set_aeq = Lazy.force coqiff -> true | _ -> false)
    then
     (let lem_2 = gen_lem_iff env m mext args in
      let lem2_name = add_suffix lem_name "2" in
      let _ = Declare.declare_constant lem2_name
	    ((DefinitionEntry {const_entry_body = lem_2; 
			     const_entry_type = None;
                                    const_entry_opaque = true}),
	     IsProof Lemma) in
      let lem2 = (current_constant lem2_name) in
	    (Lib.add_anonymous_leaf
	       (morphism_to_obj (m, 
				 { lem = mext;
                                   args = args_constr;
                                   output = output_constr;
				   lem2 = (Some lem2)})));
	    Options.if_verbose message ((string_of_id lem2_name) ^ " is defined"))
    else
     (Lib.add_anonymous_leaf
      (morphism_to_obj (m, 
        { lem = mext;
          args = args_constr;
          output = output_constr;
	  lem2 = None}))));
      Options.if_verbose ppnl (prterm m ++str " is registered as a morphism")   

let morphism_hook stre ref =
  let pf_id = id_of_global ref in
  if (is_edited pf_id)
  then 
    (add_morphism pf_id (what_edited pf_id); no_more_edited pf_id)

let new_named_morphism id m = new_morphism (constr_of m) id morphism_hook

(****************************** The tactic itself *******************************)

type constr_with_marks =
  | MApp of morphism_class Lazy.t * constr_with_marks array 
  | Toreplace of setoid
  | Tokeep
  | Mimp of constr_with_marks * constr_with_marks

let is_to_replace = function
 | Tokeep -> false
 | Toreplace _ -> true
 | MApp _ -> true
 | Mimp _ -> true

let get_mark a = 
  Array.fold_left (||) false (Array.map is_to_replace a)

exception Use_replace

let mark_occur gl hyp =
 let rec aux t in_c =
  if (eq_constr t in_c) then
   let sa =
    match hyp with
       None ->
        (match default_setoid_for_carrier (pf_type_of gl t) with
            ACSetoid sa -> sa
          | ACLeibniz _ -> raise Use_replace)
     | Some h ->
        let hypt = pf_type_of gl h in
        let (heq, hargs) = decompose_app hypt in
        let rec get_all_but_last_two =
         function
            []
          | [_] -> assert false
          | [_;_] -> []
          | he::tl -> he::(get_all_but_last_two tl) in
        let aeq = mkApp (heq,(Array.of_list (get_all_but_last_two hargs))) in
         try setoid_table_find aeq with Not_found -> assert false
   in
    Toreplace sa
  else
    match kind_of_term in_c with
      | App (c,al) -> 
	  let a = Array.map (aux t) al in
	  let mor =
           lazy
            (try
              begin
               match morphism_table_find c with
                  [] -> assert false
                | morphism::tl ->
                   if tl <> [] then
                    msg_warning
                     (str "There are several morphisms declared for " ++
                       prterm c ++
                       str ". The morphism " ++ prmorphism c morphism ++
                       str " is randomly chosen.") ;
                   ACMorphism (setoid_morphism_of_constr_morphism morphism)
              end
             with Not_found ->
              let env = Global.env() in
              let typeofc = (Typing.type_of env Evd.empty c) in
              let typ = nf_betaiota typeofc in
              let (argsrev, output) = decompose_prod typ in
              ACFunction
               {f_args=List.rev (List.map snd argsrev); f_output=output})
          in
	   if (get_mark a) then MApp (mor,a) else Tokeep
      | Prod (_, c1, c2) -> 
	  if (dependent (mkRel 1) c2)
	  then Tokeep
	  else 
	    let c1m = aux t c1 in
	    let c2m = aux t c2 in
	      if ((is_to_replace c1m)||(is_to_replace c2m))
	      then (Mimp (c1m, c2m))
	      else Tokeep
      | _ -> Tokeep
 in aux

let create_args ca ma args c1 c2 = 
  let rec aux i = function
    | [] -> []
    | (ACSetoid _)::tl -> 
	if is_to_replace ma.(i)
	then (replace_term c1 c2 ca.(i))::ca.(i)::(aux (i+1) tl)
	else ca.(i)::ca.(i)::(aux (i+1) tl)
    | (ACLeibniz _)::tl ->
        if is_to_replace ma.(i)
        then
         let newarg = replace_term c1 c2 ca.(i) in
          newarg::(aux (i+1) tl)
        else ca.(i)::(aux (i+1) tl)
  in
    aux 0 args

let res_tac sa c hyp glll =
  let fin = match hyp with
    | None -> Auto.full_trivial
    | Some h -> 
	tclORELSE (tclTHEN (tclTRY (apply h)) (tclFAIL 0 "")) 
	(tclORELSE (tclTHEN (tclTRY (tclTHEN (apply (mkApp ((Lazy.force coq_seq_sym), [|sa.set_a; sa.set_aeq; sa.set_th|]))) (apply h))) (tclFAIL 0 ""))
	   Auto.full_trivial)
  in
    tclORELSE (tclTHEN (tclTRY (apply (mkApp ((Lazy.force coq_seq_refl), [|sa.set_a; sa.set_aeq; sa.set_th;c|])))) (tclFAIL 0 ""))
      (tclORELSE assumption
	 (tclORELSE (tclTHEN (tclTRY (apply (mkApp ((Lazy.force coq_seq_sym), [|sa.set_a; sa.set_aeq; sa.set_th|])))) assumption)
	    fin))

let id_res_tac (*c*) sa = 
 (apply (mkApp ((Lazy.force coq_seq_refl), [|sa.set_a; sa.set_aeq; sa.set_th(*; c*)|])))

(* An exception to catchs errors *)

exception Nothing_found of constr;;

(* special case of replace_where_needed_gen where all the arguments
   are of class (ACLeibniz _) *)
let rec replace_where_needed hyp ca ma c1 c2 = 
  let rec aux i = function
    | [] -> tclIDTAC
    | he::tl ->
      if is_to_replace he then
       let dummy = mkProp in (* dummy will never be used *)
       tclTHENS
        (!replace ca.(i) (replace_term c1 c2 ca.(i)))
        [aux (i+1) tl; zapply (Some(ACLeibniz dummy)) false ca.(i) he c1 c2 hyp]
      else
       (aux (i+1) tl)
  in
   aux 0 ma
and replace_where_needed_gen hyp ca ma args c1 c2 =
  let rec aux i = function
    | [] -> tclIDTAC
    | ((ACLeibniz _) as he)::tl ->
       if is_to_replace ma.(i) then
        tclTHENS
         (!replace ca.(i) (replace_term c1 c2 ca.(i)))
         [aux (i+1) tl ; zapply (Some he) false ca.(i) ma.(i) c1 c2 hyp ]
       else
        aux (i+1) tl
    | (ACSetoid _)::tl -> aux (i+1) tl
  in
   aux 0 args
and create_tac_list i a al c1 c2 hyp = function
  | [] -> []
  | (ACLeibniz _)::tl -> create_tac_list (i+1) a al c1 c2 hyp tl
  | ((ACSetoid setoid) as he)::tl -> 
      if (is_to_replace a.(i))
      then (zapply (Some he) false al.(i) a.(i) c1 c2 hyp)::(create_tac_list (i+1) a al c1 c2 hyp tl)
      else (id_res_tac (*al.(i)*) setoid)::(create_tac_list (i+1) a al c1 c2 hyp tl)

and zapply close is_r gl gl_m c1 c2 hyp glll =
 (match ((kind_of_term gl), gl_m) with
  | ((App (c,al)),(MApp (m,a))) ->
     (match Lazy.force m with
         ACMorphism m ->
	  let args = Array.of_list (create_args al a m.args c1 c2) in
           tclTHENS
            (replace_where_needed_gen hyp al a m.args c1 c2)
	    [if is_r
	     then tclTHENS (apply (mkApp (m.lem, args)))
	       ((create_tac_list 0 a al c1 c2 hyp m.args)@[tclIDTAC])
 	     else
              match m.lem2 with
                 None -> 
                  tclTHENS (apply (mkApp (m.lem, args)))
                   (create_tac_list 0 a al c1 c2 hyp m.args)
               | Some xom -> 
                  tclTHENS (apply (mkApp (xom, args)))
                   (create_tac_list 0 a al c1 c2 hyp m.args)]
       | ACFunction f ->
          tclTHENS
           (replace_where_needed hyp al (Array.to_list a) c1 c2)
           [match close with
               None -> tclIDTAC
             | Some (ACLeibniz _) -> reflexivity
             | Some (ACSetoid setoid) -> id_res_tac setoid])
  | ((Prod (_,hh, cc)),(Mimp (hhm, ccm))) ->
      let al = [|hh; cc|] in
      let a = [|hhm; ccm|] in
      let fleche_constr = (Lazy.force coq_fleche) in
      let fleche_cp = destConst fleche_constr in
      let new_concl = (mkApp (fleche_constr, al)) in
      let m = find_morphism_fleche () in
	if is_r 
	then
	  let args = Array.of_list (create_args al a m.args c1 c2) in  
	    tclTHEN (change_in_concl None new_concl)
	      (tclTHENS (apply (mkApp (m.lem, args)))
		 ((create_tac_list 0 a al c1 c2 hyp m.args)@[unfold_constr (ConstRef fleche_cp)]))
	else
         (zapply (Some m.output) is_r new_concl
           (MApp (lazy (ACMorphism m),a)) c1 c2 hyp)
  | (_, Toreplace setoid) -> 
      if is_r 
      then (match hyp with
	      | None -> errorlabstrm "Setoid_replace"
		  (str "You should use the tactic Replace here")
	      | Some h ->
		  let hypt = pf_type_of glll h in
		  let (heq, hargs) = decompose_app hypt in
		  let rec get_last_two = function
		    | [c1;c2] -> (c1, c2)
		    | x::y::z -> get_last_two (y::z)
		    | _ -> assert false in
		  let (hc1,hc2) = get_last_two hargs in
		    if c1 = hc1
		    then 				     
		      apply (mkApp (Lazy.force coqproj2,[|(mkArrow hc1 hc2);(mkArrow hc2 hc1);h|]))
		    else 
		      apply (mkApp (Lazy.force coqproj1,[|(mkArrow hc1 hc2);(mkArrow hc2 hc1);h|]))
	   )
      else (res_tac setoid gl hyp glll)
  | (_, Tokeep) -> (match hyp with 
		      | None -> errorlabstrm "Setoid_replace"
			  (str "No replacable occurence of " ++ prterm c1 ++ str " found")
		      | Some _ ->errorlabstrm "Setoid_replace"
			  (str "No rewritable occurence of " ++ prterm c1 ++ str " found"))
  | _ -> assert false) glll

let setoid_replace c1 c2 hyp gl =
  let but = (pf_concl gl) in
   try
    (zapply None true but (mark_occur gl hyp c1 but) c1 c2 hyp) gl
   with
    Use_replace -> (!replace c1 c2) gl

let general_s_rewrite lft2rgt c gl =
  let ctype = pf_type_of gl c in
  let (equiv, args) = decompose_app ctype in
  let rec get_last_two = function
    | [c1;c2] -> (c1, c2)
    | x::y::z -> get_last_two (y::z)
    | _ -> error "The term provided is not an equivalence" in 
  let (c1,c2) = get_last_two args in
    if lft2rgt
    then setoid_replace c1 c2 (Some c) gl
    else setoid_replace c2 c1 (Some c) gl

let setoid_replace c1 c2 = setoid_replace c1 c2 None

let setoid_rewriteLR = general_s_rewrite true

let setoid_rewriteRL = general_s_rewrite false
