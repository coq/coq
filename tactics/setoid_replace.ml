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
open Clenv
open Unification
open Tactics 
open Tacticals
open Vernacexpr
open Safe_typing
open Nametab
open Decl_kinds
open Constrintern

let replace = ref (fun _ _ -> assert false)
let register_replace f = replace := f

let general_rewrite = ref (fun _ _ -> assert false)
let register_general_rewrite f = general_rewrite := f

(* util function; it should be in util.mli *)
let prlist_with_sepi sep elem =
 let rec aux n =
  function
   | []   -> mt ()
   | [h]  -> elem n h
   | h::t ->
      let e = elem n h and s = sep() and r = aux (n+1) t in
      e ++ s ++ r
 in
  aux 1

type relation =
   { rel_a: constr ;
     rel_aeq: constr;
     rel_refl: constr option;
     rel_sym: constr option
   }

type 'a relation_class =
   Relation of 'a     (* the rel_aeq of the relation or the relation*)
 | Leibniz of constr  (* the carrier *)

type 'a morphism =
    { args : (bool option * 'a relation_class) list;
      output : 'a relation_class;
      lem : constr;
    }

type funct =
    { f_args : constr list;
      f_output : constr
    }

type morphism_class =
   ACMorphism of relation morphism
 | ACFunction of funct

let subst_mps_in_relation_class subst =
 function
    Relation  t -> Relation  (subst_mps subst t)
  | Leibniz t -> Leibniz (subst_mps subst t) 

let subst_mps_in_argument_class subst (variance,rel) =
 variance, subst_mps_in_relation_class subst rel

let constr_relation_class_of_relation_relation_class =
 function
    Relation relation -> Relation relation.rel_aeq
  | Leibniz t -> Leibniz t
 

let constr_of c = Constrintern.interp_constr Evd.empty (Global.env()) c

let constant dir s = Coqlib.gen_constant "Setoid_replace" ("Setoids"::dir) s
let gen_constant dir s = Coqlib.gen_constant "Setoid_replace" dir s
let reference dir s = Coqlib.gen_reference "Setoid_replace" ("Setoids"::dir) s
let eval_reference dir s = EvalConstRef (destConst (constant dir s))
let eval_init_reference dir s = EvalConstRef (destConst (gen_constant ("Init"::dir) s))

let current_constant id =
  try
    global_reference id
  with Not_found ->
    anomaly ("Setoid: cannot find " ^ (string_of_id id))

(* From Setoid.v *)

let coq_reflexive =
 lazy(gen_constant ["Relations"; "Relation_Definitions"] "reflexive")
let coq_symmetric =
 lazy(gen_constant ["Relations"; "Relation_Definitions"] "symmetric")
let coq_relation =
 lazy(gen_constant ["Relations"; "Relation_Definitions"] "relation")

let coq_Relation_Class = lazy(constant ["Setoid"] "Relation_Class")
let coq_Argument_Class = lazy(constant ["Setoid"] "Argument_Class")
let coq_Setoid_Theory = lazy(constant ["Setoid"] "Setoid_Theory")
let coq_Morphism_Theory = lazy(constant ["Setoid"] "Morphism_Theory")
let coq_Build_Morphism_Theory= lazy(constant ["Setoid"] "Build_Morphism_Theory")

let coq_AsymmetricReflexive = lazy(constant ["Setoid"] "AsymmetricReflexive")
let coq_SymmetricReflexive = lazy(constant ["Setoid"] "SymmetricReflexive")
let coq_SymmetricAreflexive = lazy(constant ["Setoid"] "SymmetricAreflexive")
let coq_AsymmetricAreflexive = lazy(constant ["Setoid"] "AsymmetricAreflexive")
let coq_Leibniz = lazy(constant ["Setoid"] "Leibniz")

let coq_RAsymmetric = lazy(constant ["Setoid"] "RAsymmetric")
let coq_RSymmetric = lazy(constant ["Setoid"] "RSymmetric")
let coq_RLeibniz = lazy(constant ["Setoid"] "RLeibniz")

let coq_ASymmetric = lazy(constant ["Setoid"] "ASymmetric")
let coq_AAsymmetric = lazy(constant ["Setoid"] "AAsymmetric")

let coq_seq_refl = lazy(constant ["Setoid"] "Seq_refl")
let coq_seq_sym = lazy(constant ["Setoid"] "Seq_sym")
let coq_seq_trans = lazy(constant ["Setoid"] "Seq_trans")

let coq_variance = lazy(constant ["Setoid"] "variance")
let coq_Covariant = lazy(constant ["Setoid"] "Covariant")
let coq_Contravariant = lazy(constant ["Setoid"] "Contravariant")
let coq_Left2Right = lazy(constant ["Setoid"] "Left2Right")
let coq_Right2Left = lazy(constant ["Setoid"] "Right2Left")
let coq_MSNone = lazy(constant ["Setoid"] "MSNone")
let coq_MSCovariant = lazy(constant ["Setoid"] "MSCovariant")
let coq_MSContravariant = lazy(constant ["Setoid"] "MSContravariant")

let coq_singl = lazy(constant ["Setoid"] "singl")
let coq_cons = lazy(constant ["Setoid"] "cons")

let coq_equality_morphism_of_setoid_theory =
 lazy(constant ["Setoid"] "equality_morphism_of_setoid_theory")
let coq_make_compatibility_goal =
 lazy(constant ["Setoid"] "make_compatibility_goal")
let coq_make_compatibility_goal_ref =
 lazy(reference ["Setoid"] "make_compatibility_goal")
let coq_make_compatibility_goal_aux_ref =
 lazy(reference ["Setoid"] "make_compatibility_goal_aux")

let coq_App = lazy(constant ["Setoid"] "App")
let coq_ToReplace = lazy(constant ["Setoid"] "ToReplace")
let coq_ToKeep = lazy(constant ["Setoid"] "ToKeep")
let coq_ProperElementToKeep = lazy(constant ["Setoid"] "ProperElementToKeep")
let coq_fcl_singl = lazy(constant ["Setoid"] "fcl_singl")
let coq_fcl_cons = lazy(constant ["Setoid"] "fcl_cons")

let coq_setoid_rewrite = lazy(constant ["Setoid"] "setoid_rewrite")
let coq_proj1 = lazy(gen_constant ["Init"; "Logic"] "proj1")
let coq_proj2 = lazy(gen_constant ["Init"; "Logic"] "proj2")
let coq_unit = lazy(gen_constant ["Init"; "Datatypes"] "unit")
let coq_tt = lazy(gen_constant ["Init"; "Datatypes"] "tt")
let coq_eq = lazy(gen_constant ["Init"; "Logic"] "eq")

let coq_morphism_theory_of_function =
 lazy(constant ["Setoid"] "morphism_theory_of_function")
let coq_morphism_theory_of_predicate =
 lazy(constant ["Setoid"] "morphism_theory_of_predicate")
let coq_relation_of_relation_class =
 lazy(eval_reference ["Setoid"] "relation_of_relation_class")
let coq_directed_relation_of_relation_class =
 lazy(eval_reference ["Setoid"] "directed_relation_of_relation_class")
let coq_interp = lazy(eval_reference ["Setoid"] "interp")
let coq_Morphism_Context_rect2 =
 lazy(eval_reference ["Setoid"] "Morphism_Context_rect2")
let coq_iff = lazy(eval_init_reference ["Logic"] "iff")

let coq_impl = lazy(constant ["Setoid"] "impl")
let coq_prop_relation =
 lazy (
  Relation {
     rel_a = mkProp ;
     rel_aeq = gen_constant ["Init"; "Logic"] "iff" ;
     rel_refl = Some (gen_constant ["Init"; "Logic"] "iff_refl");
     rel_sym = Some (gen_constant ["Init"; "Logic"] "iff_sym")
   })

let coq_prop_relation2 =
 lazy (
  Relation {
     rel_a = mkProp ;
     rel_aeq = Lazy.force coq_impl ;
     rel_refl = Some (constant ["Setoid"] "impl_refl") ;
     rel_sym = None
   })


(************************* Table of declared relations **********************)


(* Relations are stored in a table which is synchronised with the Reset mechanism. *)

let relation_table = ref Gmap.empty

let relation_table_add (s,th) = relation_table := Gmap.add s th !relation_table
let relation_table_find s = Gmap.find s !relation_table
let relation_table_mem s = Gmap.mem s !relation_table

let prrelation s =
 str "(" ++ prterm s.rel_a ++ str "," ++ prterm s.rel_aeq ++ str ")"

let prrelation_class =
 function
    Relation eq  ->
     (try prrelation (relation_table_find eq)
      with Not_found ->
       (*CSC: still "setoid" in the error message *)
       str "[[ Error: setoid on equality " ++ prterm eq ++ str " not found! ]]")
  | Leibniz ty -> prterm ty

let prmorphism_argument_gen prrelation (variance,rel) =
 prrelation rel ++
  match variance with
     None -> str " ==> "
   | Some true -> str " ++> "
   | Some false -> str " --> "

let prargument_class = prmorphism_argument_gen prrelation_class

let pr_morphism_signature (l,c) =
 prlist (prmorphism_argument_gen Ppconstrnew.pr_constr) l ++
  Ppconstrnew.pr_constr c

let prmorphism k m =
  prterm k ++ str ": " ++
  prlist prargument_class m.args ++
  prrelation_class m.output


(* A function that gives back the only relation_class on a given carrier *)
(*CSC: this implementation is really inefficient. I should define a new
  map to make it efficient. However, is this really worth of? *)
let default_relation_for_carrier a =
 let rng = Gmap.rng !relation_table in
 match List.filter (fun {rel_a=rel_a} -> rel_a = a) rng with
    [] -> Leibniz a
  | relation::tl ->
     if tl <> [] then
      ppnl
       (*CSC: still "setoid" in the error message *)
       (str "Warning: There are several setoids whose carrier is "++ prterm a ++
         str ". The setoid " ++ prrelation relation ++
         str " is randomly chosen.") ;
     Relation relation

let find_relation_class rel =
 try Relation (relation_table_find rel)
 with
  Not_found ->
   match kind_of_term (Reduction.whd_betadeltaiota (Global.env ()) rel) with
    | App (eq,[|ty|]) when eq_constr eq (Lazy.force coq_eq) -> Leibniz ty
    | _ -> raise Not_found

let relation_morphism_of_constr_morphism =
 let relation_relation_class_of_constr_relation_class =
  function
     Leibniz t -> Leibniz t
   | Relation aeq ->
      Relation (try relation_table_find aeq with Not_found -> assert false)
 in
  function mor ->
   let args' =
    List.map
     (fun (variance,rel) ->
       variance, relation_relation_class_of_constr_relation_class rel
     ) mor.args in
   let output' = relation_relation_class_of_constr_relation_class mor.output in
    {mor with args=args' ; output=output'}

let subst_relation subst relation = 
  let rel_a' = subst_mps subst relation.rel_a in
  let rel_aeq' = subst_mps subst relation.rel_aeq in
  let rel_refl' = option_app (subst_mps subst) relation.rel_refl in
  let rel_sym' = option_app (subst_mps subst) relation.rel_sym in
    if rel_a' == relation.rel_a
      && rel_aeq' == relation.rel_aeq
      && rel_refl' == relation.rel_refl
      && rel_sym' == relation.rel_sym
    then
      relation
    else
      { rel_a = rel_a' ;
        rel_aeq = rel_aeq' ;
        rel_refl = rel_refl' ;
        rel_sym = rel_sym'
      }
      
let equiv_list () = List.map (fun x -> x.rel_aeq) (Gmap.rng !relation_table)

let _ = 
  Summary.declare_summary "relation-table"
    { Summary.freeze_function = (fun () -> !relation_table);
      Summary.unfreeze_function = (fun t -> relation_table := t);
      Summary.init_function = (fun () -> relation_table := Gmap .empty);
      Summary.survive_module = true;
      Summary.survive_section = false }

(* Declare a new type of object in the environment : "relation-theory". *)

let (relation_to_obj, obj_to_relation)=
  let cache_set (_,(s, th)) =
   let th' =
    if relation_table_mem s then
     begin
      let old_relation = relation_table_find s in
       let th' =
        {th with rel_sym =
          match th.rel_sym with
             None -> old_relation.rel_sym
           | Some t -> Some t} in
        (*CSC: still "setoid" in the error message *)
        ppnl
         (str "Warning: The setoid " ++ prrelation th' ++
          str " is redeclared. The new declaration" ++
           (match th'.rel_refl with
              None -> str ""
            | Some t -> str " (reflevity proved by " ++ prterm t) ++
           (match th'.rel_sym with
               None -> str ""
             | Some t ->
                (if th'.rel_refl = None then str " (" else str " and ") ++
                str "symmetry proved by " ++ prterm t) ++
           (if th'.rel_refl <> None && th'.rel_sym <> None then
             str ")" else str "") ++
           str " replaces the old declaration" ++
           (match old_relation.rel_refl with
              None -> str ""
            | Some t -> str " (reflevity proved by " ++ prterm t) ++
           (match old_relation.rel_sym with
               None -> str ""
             | Some t ->
                (if old_relation.rel_refl = None then
                  str " (" else str " and ") ++
                str "symmetry proved by " ++ prterm t) ++
           (if old_relation.rel_refl <> None && old_relation.rel_sym <> None
            then str ")" else str "") ++
           str ".");
        th'
     end
    else
     th
   in
    relation_table_add (s,th')
  and subst_set (_,subst,(s,th as obj)) =
    let s' = subst_mps subst s in
    let th' = subst_relation subst th in
      if s' == s && th' == th then obj else
        (s',th')
  and export_set x = Some x 
  in 
    declare_object {(default_object "relation-theory") with
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
    ppnl
     (str "Warning: The morphism " ++ prmorphism m old_morph ++
      str " is redeclared. " ++
      str "The new declaration whose compatibility is granted by " ++
       prterm c.lem ++ str " replaces the old declaration whose" ++
       str " compatibility was granted by " ++
       prterm old_morph.lem ++ str ".")
  with
   Not_found -> morphism_table := Gmap.add m (c::old) !morphism_table

let subst_morph subst morph = 
  let lem' = subst_mps subst morph.lem in
  let args' = list_smartmap (subst_mps_in_argument_class subst) morph.args in
  let output' = subst_mps_in_relation_class subst morph.output in
    if lem' == morph.lem
      && args' == morph.args
      && output' == morph.output
    then
      morph
    else
      { args = args' ;
        output = output' ;
        lem = lem'
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

(************************** Printing relations and morphisms **********************)

(*CSC: still "setoids" in the name *)
let print_setoids () =
  Gmap.iter
   (fun k relation ->
     assert (k=relation.rel_aeq) ;
     (*CSC: still "Setoid" in the error message *)
     ppnl (str"Setoid " ++ prrelation relation ++ str";" ++
      (match relation.rel_refl with
          None -> str ""
        | Some t -> str" reflexivity granted by " ++ prterm t) ++
      (match relation.rel_sym with
          None -> str ""
        | Some t -> str " symmetry granted by " ++ prterm t)))
   !relation_table ;
  Gmap.iter
   (fun k l ->
     List.iter
      (fun ({lem=lem} as mor) ->
        ppnl (str "Morphism " ++ prmorphism k mor ++
        str ". Compatibility granted by " ++
        prterm lem ++ str "."))
      l) !morphism_table
;;

(************************** Adding a relation to the database *********************)

let check_eq env a aeq =
 let typ = mkApp (Lazy.force coq_relation, [| a |]) in
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty aeq) typ)
 then
  errorlabstrm "Add Relation Class"
   (prterm aeq ++ str " should have type (" ++ prterm typ ++ str ")")

let check_refl env a aeq refl =
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty refl)
     (mkApp ((Lazy.force coq_reflexive), [| a; aeq |])))
 then
  errorlabstrm "Add Relation Class"
   (str "Not a valid proof of reflexivity")

let check_sym env a aeq sym =
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty sym)
     (mkApp ((Lazy.force coq_symmetric), [| a; aeq |])))
 then
  errorlabstrm "Add Relation Class"
   (str "Not a valid proof of symmetry")

let int_add_relation a aeq refl sym =
 let env = Global.env () in
  check_eq env a aeq ;
  option_iter (check_refl env a aeq) refl ;
  option_iter (check_sym env a aeq) sym ;
  Lib.add_anonymous_leaf 
   (relation_to_obj 
    (aeq, { rel_a = a;
            rel_aeq = aeq;
            rel_refl = refl;
            rel_sym = sym}))

(* The vernac command "Add Relation ..." *)
let add_relation a aeq refl sym =
 int_add_relation (constr_of a) (constr_of aeq) (option_app constr_of refl)
  (option_app constr_of sym)

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

let cic_relation_class_of_X_relation_class typ value =
 function
    Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=None}
    ->
     mkApp ((Lazy.force coq_AsymmetricReflexive),
      [| Lazy.force typ ; Lazy.force value ; rel_a ; rel_aeq; refl |])
  | Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=Some sym}
    ->
     mkApp ((Lazy.force coq_SymmetricReflexive),
      [| Lazy.force typ ; rel_a ; rel_aeq; sym ; refl |])
  | Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=None}
    ->
     mkApp ((Lazy.force coq_AsymmetricAreflexive),
      [| Lazy.force typ ; Lazy.force value ; rel_a ; rel_aeq |])
  | Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=Some sym}
    ->
     mkApp ((Lazy.force coq_SymmetricAreflexive),
      [| Lazy.force typ ; rel_a ; rel_aeq; sym |])
  | Leibniz t -> mkApp ((Lazy.force coq_Leibniz), [| Lazy.force typ ; t |])

let cic_precise_relation_class_of_relation_class =
 function
    Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=None}
    ->
     rel_aeq,
      mkApp ((Lazy.force coq_RAsymmetric), [| rel_a ; rel_aeq; refl |]), true
  | Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=Some sym}
    ->
     rel_aeq,
      mkApp ((Lazy.force coq_RSymmetric), [| rel_a ; rel_aeq; sym ; refl |]),
      true
  | Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=None}
    ->
     rel_aeq, mkApp ((Lazy.force coq_AAsymmetric), [| rel_a ; rel_aeq |]), false
  | Relation
     {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=Some sym}
    ->
     rel_aeq, mkApp ((Lazy.force coq_ASymmetric), [| rel_a ; rel_aeq; sym |]),
      false
  | Leibniz t ->
     mkApp ((Lazy.force coq_eq), [| t |]),
      mkApp ((Lazy.force coq_RLeibniz), [| t |]), true

let cic_relation_class_of_relation_class =
 cic_relation_class_of_X_relation_class coq_unit coq_tt

let cic_argument_class_of_argument_class (variance,arg) =
 let coq_variant_value =
  match variance with
     None -> coq_Covariant (* dummy value, it won't be used *)
   | Some true -> coq_Covariant
   | Some false -> coq_Contravariant
 in
  cic_relation_class_of_X_relation_class coq_variance coq_variant_value arg

let gen_compat_lemma_statement output args m =
 let rec mk_signature =
  function
     [] -> assert false
   | [last] ->
      mkApp ((Lazy.force coq_singl), [| Lazy.force coq_Argument_Class; last |])
   | he::tl ->
      mkApp ((Lazy.force coq_cons),
       [| Lazy.force coq_Argument_Class; he ; mk_signature tl |])
 in
  let output = cic_relation_class_of_relation_class output in
  let args= mk_signature (List.map cic_argument_class_of_argument_class args) in
   args, output,
    mkApp ((Lazy.force coq_make_compatibility_goal), [| args ; output ; m |])

let check_if_signature_is_well_typed c typ args output =
 let carrier_of_relation =
  function
     Leibniz t -> t
   | Relation {rel_a = a} -> a in
 let rev_args' =
  List.rev_map (fun (_,t) -> Anonymous,carrier_of_relation t) args  in
 let output' = carrier_of_relation output in
 let typ' = compose_prod rev_args' output' in
 let env = Global.env () in
  if not (is_conv env Evd.empty typ typ') then
   errorlabstrm "New Morphism"
    (str "The signature provided is for a function of type " ++ prterm typ' ++
     str ". The function " ++ prterm c ++ str " has type " ++ prterm typ)

let new_morphism m signature id hook =
 if Nametab.exists_cci (Lib.make_path id) or is_section_variable id then
  errorlabstrm "New Morphism" (pr_id id ++ str " already exists")
 else
  let env = Global.env() in
  let typeofm = (Typing.type_of env Evd.empty m) in
  let typ = (nf_betaiota typeofm) in
  let (argsrev, output) = (decompose_prod typ) in
  let args_ty = (List.map snd (List.rev argsrev)) in
    if (args_ty=[])
    then errorlabstrm "New Morphism"
     (str "The term " ++ prterm m ++ str " is not a product")
    else if (check_is_dependent typ (List.length args_ty))
    then  errorlabstrm "New Morphism"
     (str "The term " ++ prterm m ++ str" should not be a dependent product")
    else
     begin
      let args,output =
       match signature with
          None ->
           List.map (fun ty -> None,default_relation_for_carrier ty) args_ty,
           default_relation_for_carrier output
        | Some (args,output) ->
           let find_relation_class t =
            try find_relation_class t
            with Not_found ->
             errorlabstrm "Add Morphism"
              (str "Not a valid signature: " ++ prterm t ++
               str " is neither a registered relation nor the Leibniz " ++
               str " equality partially applied to a type.")
           in
           let find_relation_class_v (variance,t) =
            let relation = find_relation_class t in
             match find_relation_class t, variance with
                Leibniz _, None
              | Relation {rel_sym = Some _}, None
              | Relation {rel_sym = None}, Some _ -> variance,relation
              | Relation {rel_sym = None},None ->
                 errorlabstrm "Add Morphism"
                  (str "You must specify the variance in each argument " ++
                   str "whose relation is asymmetric.")
              | Leibniz _, Some _
              | Relation {rel_sym = Some _}, Some _ ->
                 errorlabstrm "Add Morphism"
                  (str "You cannot specify the variance of an argument " ++
                   str "whose relation is symmetric.")
           in
            let args = List.map find_relation_class_v args in
            let output = find_relation_class output in
             check_if_signature_is_well_typed m typ args output ;
             args, output
      in
      let argsconstr,outputconstr,lem =
       gen_compat_lemma_statement output args m
      in
       new_edited id (m,args,argsconstr,output,outputconstr);
       Pfedit.start_proof id (IsGlobal (Proof Lemma)) 
        (Declare.clear_proofs (Global.named_context ()))
        lem hook;
       (* "unfold make_compatibility_goal" *)
       Pfedit.by
        (Tactics.unfold_constr
         (Lazy.force coq_make_compatibility_goal_ref)) ;
       (* "unfold make_compatibility_goal_aux" *)
       Pfedit.by
        (Tactics.unfold_constr
         (Lazy.force coq_make_compatibility_goal_aux_ref)) ;
       (* "simpl" *)
       Pfedit.by Tactics.simpl_in_concl ;
       Options.if_verbose msg (Printer.pr_open_subgoals ());
     end

let add_morphism lemma_infos mor_name (m,args,output) =
 let env = Global.env() in
 begin
  match lemma_infos with
     None -> () (* the Morphism_Theory object has alrady been created *)
   | Some (lem_name,argsconstr,outputconstr) ->
      (* only the compatibility has been proved; we need to declare the
         Morphism_Theory object *)
     let mext = current_constant lem_name in
     ignore (
      Declare.declare_constant mor_name
       (DefinitionEntry
         {const_entry_body =
           mkApp ((Lazy.force coq_Build_Morphism_Theory),
            [| argsconstr; outputconstr; m ; mext |]);
          const_entry_type = None;
          const_entry_opaque = false},
           IsDefinition))
  end ;
  let mmor = current_constant mor_name in
  let args_constr =
   List.map
    (fun (variance,arg) ->
      variance, constr_relation_class_of_relation_relation_class arg) args in
  let output_constr = constr_relation_class_of_relation_relation_class output in
   Lib.add_anonymous_leaf
    (morphism_to_obj (m, 
      { args = args_constr;
        output = output_constr;
        lem = mmor }));
   Options.if_verbose ppnl (prterm m ++ str " is registered as a morphism")   

let morphism_hook stre ref =
  let pf_id = id_of_global ref in
  let mor_id = id_of_string (string_of_id pf_id ^ "_morphism_theory") in
  let (m,args,argsconstr,output,outputconstr) = what_edited pf_id in
  if (is_edited pf_id)
  then 
    add_morphism (Some (pf_id,argsconstr,outputconstr)) mor_id
     (m,args,output); no_more_edited pf_id

type morphism_signature =
 (bool option * Topconstr.constr_expr) list * Topconstr.constr_expr

let new_named_morphism id m sign =
 let sign =
  match sign with
     None -> None
   | Some (args,out) ->
      Some
       (List.map (fun (variance,ty) -> variance, constr_of ty) args,
        constr_of out)
 in
  new_morphism (constr_of m) sign id morphism_hook

(************************ Add Setoid ******************************************)

(*CSC: I do not like this. I would prefer more self-describing constant names *)
let gen_morphism_name =
  let i = ref 0 in
    function () -> 
      incr i;
      make_ident "morphism_of_setoid_equality" (Some !i)

(* The vernac command "Add Setoid" *)
let add_setoid a aeq th =
 let a = constr_of a in
 let aeq = constr_of aeq in
 let th = constr_of th in
 let env = Global.env () in
  if is_conv env Evd.empty (Typing.type_of env Evd.empty th)
    (mkApp ((Lazy.force coq_Setoid_Theory), [| a; aeq |]))
  then
   begin
    let refl = mkApp ((Lazy.force coq_seq_refl), [| a; aeq; th |]) in
    let sym = mkApp ((Lazy.force coq_seq_sym), [| a; aeq; th |]) in
    int_add_relation a aeq (Some refl) (Some sym) ;
    let mor_name = gen_morphism_name () in
    let _ =
     Declare.declare_constant mor_name
      (DefinitionEntry
        {const_entry_body =
          mkApp
           ((Lazy.force coq_equality_morphism_of_setoid_theory),
            [| a; aeq; th |]) ;
         const_entry_type = None;
         const_entry_opaque = false},
        IsDefinition) in
    let aeq_rel =
     None,
      Relation
       {rel_a = a ; rel_aeq = aeq ; rel_refl = Some refl ; rel_sym = Some sym}
    in
     add_morphism None mor_name
      (aeq,[aeq_rel;aeq_rel],Lazy.force coq_prop_relation)
   end
  else
   errorlabstrm "Add Setoid" (str "Not a valid setoid theory")


(****************************** The tactic itself *******************************)

type direction =
   Left2Right
 | Right2Left

let prdirection =
 function
    Left2Right -> str "->"
  | Right2Left -> str "<-"

type constr_with_marks =
  | MApp of constr * morphism_class * constr_with_marks array * direction
  | ToReplace
  | ToKeep of constr * relation relation_class * direction

let is_to_replace = function
 | ToKeep _ -> false
 | ToReplace -> true
 | MApp _ -> true

let get_mark a = 
  Array.fold_left (||) false (Array.map is_to_replace a)

let cic_direction_of_direction =
 function
    Left2Right -> Lazy.force coq_Left2Right
  | Right2Left -> Lazy.force coq_Right2Left

let opposite_direction =
 function
    Left2Right -> Right2Left
  | Right2Left -> Left2Right

let direction_of_constr_with_marks hole_direction =
 function
    MApp (_,_,_,dir) -> cic_direction_of_direction dir
  | ToReplace -> hole_direction
  | ToKeep (_,_,dir) -> cic_direction_of_direction dir

type argument =
   Toapply of constr         (* apply the function to the argument *)
 | Toexpand of name * types  (* beta-expand the function w.r.t. an argument
                                of this type *)
let beta_expand c args_rev =
 let rec to_expand =
  function
     [] -> []
   | (Toapply _)::tl -> to_expand tl
   | (Toexpand (name,s))::tl -> (name,s)::(to_expand tl) in
 let rec aux n =
  function
     [] -> []
   | (Toapply arg)::tl -> arg::(aux n tl)
   | (Toexpand _)::tl -> (mkRel n)::(aux (n + 1) tl)
 in
  compose_lam (to_expand args_rev)
   (mkApp (c, Array.of_list (List.rev (aux 1 args_rev))))

exception Use_rewrite

let relation_of_hypothesis_and_term_to_rewrite new_goals gl (_,h) t =
 let hypt = pf_type_of gl h in
 let (heq, hargs) = decompose_app hypt in
 let rec get_all_but_last_two =
  function
     []
   | [_] -> assert false
   | [_;_] -> []
   | he::tl -> he::(get_all_but_last_two tl) in
 let aeq = mkApp (heq,(Array.of_list (get_all_but_last_two hargs))) in
  try
   let rel = find_relation_class aeq in
   match rel,new_goals with
      Leibniz _,[] -> raise Use_rewrite (* let's optimize the proof term size *)
    | _,_ -> rel
  with Not_found ->
   (*CSC: still "setoid" in the error message *)
   errorlabstrm "Setoid_rewrite"
    (prterm aeq ++ str " is not a setoid equality.")

(* rel1 is a subrelation of rel2 whenever 
    forall x1 x2, rel1 x1 x2 -> rel2 x1 x2
   The Coq part of the tactic, however, needs rel1 == rel2.
   Hence the third case commented out.
   Note: accepting user-defined subtrelations seems to be the last
   useful generalization that does not go against the original spirit of
   the tactic.
*)
let subrelation rel1 rel2 =
 match rel1,rel2 with
    Relation {rel_aeq=rel_aeq1}, Relation {rel_aeq=rel_aeq2} ->
     eq_constr rel_aeq1 rel_aeq2
  | Leibniz t1, Leibniz t2 ->
     eq_constr t1 t2
(* This is the commented out case (see comment above)
  | Leibniz t1, Relation {rel_a=t2; rel_refl = Some _} ->
     eq_constr t1 t2
*)
  | _,_ -> false

(* this function returns the list of new goals opened by a constr_with_marks *)
let rec collect_new_goals =
 function
   MApp (_,_,a,_) -> List.concat (List.map collect_new_goals (Array.to_list a))
 | ToReplace
 | ToKeep (_,Leibniz _,_)
 | ToKeep (_,Relation {rel_refl=Some _},_) -> []
 | ToKeep (c,Relation {rel_aeq=aeq; rel_refl=None},_) -> [mkApp(aeq,[|c ; c|])]

(* two marked_constr are equivalent if they produce the same set of new goals *)
let marked_constr_equiv_or_more_complex to_marked_constr c1 c2 =
  let glc1 = collect_new_goals (to_marked_constr c1) in
  let glc2 = collect_new_goals (to_marked_constr c2) in
   List.for_all (fun c -> List.exists (fun c' -> eq_constr c c') glc1) glc2

let pr_new_goals i c =
 let glc = collect_new_goals c in
  str " " ++ int i ++ str ") side conditions:" ++
   (if glc = [] then str " no side conditions"
    else
     (pr_fnl () ++ str "   " ++
       prlist_with_sep (fun () -> str "\n   ")
        (fun c -> str " ... |- " ++ prterm c) glc))

(* given a list of constr_with_marks, it returns the list where
   constr_with_marks than open more goals than simpler ones in the list
   are got rid of *)
let elim_duplicates to_marked_constr =
 let rec aux =
  function
     [] -> []
   | he:: tl ->
      if List.exists(marked_constr_equiv_or_more_complex to_marked_constr he) tl
      then aux tl
      else he::aux tl
 in
  aux

let filter_superset_of_new_goals new_goals l =
 List.filter
  (fun (_,_,c) ->
    List.for_all
     (fun g -> List.exists (eq_constr g) (collect_new_goals c)) new_goals) l

(* given the array of lists [| l1 ; ... ; ln |] it returns the list of arrays
   [ c1 ; ... ; cn ] that is the cartesian product of the sets l1, ..., ln *)
let cartesian_product a =
 let rec aux =
  function
     [] -> assert false
   | [he] -> List.map (fun e -> [e]) he
   | he::tl ->
      let tl' = aux tl in
       List.flatten
        (List.map (function e -> List.map (function l -> e :: l) tl') he)
 in
  List.map Array.of_list
   (aux (List.map (elim_duplicates identity) (Array.to_list a)))

let mark_occur gl ~new_goals t in_c input_relation input_direction =
 let rec aux output_relation output_direction in_c =
  if eq_constr t in_c then
   if input_direction = output_direction
   && subrelation input_relation output_relation then
    [ToReplace]
   else []
  else
    match kind_of_term in_c with
      | App (c,al) -> 
         let mors =
          try
           let morphisms =
            List.map relation_morphism_of_constr_morphism
             (morphism_table_find c)
           in
            List.filter
             (fun mor -> subrelation mor.output output_relation) morphisms
          with Not_found -> []
         in
          (* First we look for well typed morphisms *)
          let res_mors =
           List.fold_left
            (fun res mor ->
              let a =
               let arguments = Array.of_list mor.args in
               let apply_variance_to_direction default_dir =
                function
                   None -> default_dir
                 | Some true -> output_direction
                 | Some false -> opposite_direction output_direction
               in
                Util.array_map2
                 (fun a (variance,relation) ->
                   (aux relation
                     (apply_variance_to_direction Left2Right variance) a) @
                   (aux relation
                     (apply_variance_to_direction Right2Left variance) a)
                 ) al arguments
              in
               let a' = cartesian_product a in
                (List.map
                  (function a ->
                    if not (get_mark a) then
                     ToKeep (in_c,output_relation,output_direction)
                    else
                     MApp (c,ACMorphism mor,a,output_direction)) a') @ res
            ) [] mors in
          (* Then we look for well typed functions *)
          let res_functions =
           (* the tactic works only if the function type is
               made of non-dependent products only. However, here we
               can cheat a bit by partially istantiating c to match
               the requirement when the arguments to be replaced are
               bound by non-dependent products only. *)
            let typeofc = Tacmach.pf_type_of gl c in
            let typ = nf_betaiota typeofc in
            let rec find_non_dependent_function env c c_args_rev typ f_args_rev
                     a_rev
            =
             function
                [] ->
                 if a_rev = [] then
                  [ToKeep (in_c,output_relation,output_direction)]
                 else
                  let a' = cartesian_product (Array.of_list (List.rev a_rev)) in
                   List.fold_left
                    (fun res a ->
                      if not (get_mark a) then
                       (ToKeep (in_c,output_relation,output_direction))::res
                      else
                       let err =
                        match output_relation with
                           Leibniz typ' when eq_constr typ typ' -> false
                         | _ when output_relation = Lazy.force coq_prop_relation
                             -> false
                         | _ -> true
                       in
                        if err then res
                        else
                         let mor =
                          ACFunction{f_args=List.rev f_args_rev;f_output=typ} in
                         let func = beta_expand c c_args_rev in
                          (MApp (func,mor,a,output_direction))::res
                    ) [] a'
              | (he::tl) as a->
                 let typnf = Reduction.whd_betadeltaiota env typ in
                  match kind_of_term typnf with
                    Cast (typ,_) ->
                     find_non_dependent_function env c c_args_rev typ
                      f_args_rev a_rev a
                  | Prod (name,s,t) ->
                     let env' = push_rel (name,None,s) env in
                     let he =
                      (aux (Leibniz s) Left2Right he) @
                      (aux (Leibniz s) Right2Left he) in
                     if he = [] then []
                     else
                      let he0 = List.hd he in
                      begin
                       match noccurn 1 t, he0 with
                          _, ToKeep (arg,_,_) ->
                           (* invariant: if he0 = ToKeep (t,_,_) then every
                              element in he is = ToKeep (t,_,_) *)
                           assert
                            (List.for_all
                              (function
                                  ToKeep (arg',_,_) when eq_constr arg arg' ->
                                    true
                                | _ -> false) he) ;
                           (* generic product, to keep *)
                           find_non_dependent_function
                            env' c ((Toapply arg)::c_args_rev)
                            (subst1 arg t) f_args_rev a_rev tl
                        | true, _ ->
                           (* non-dependent product, to replace *)
                           find_non_dependent_function
                            env' c ((Toexpand (name,s))::c_args_rev)
                             (lift 1 t) (s::f_args_rev) (he::a_rev) tl
                        | false, _ ->
                           (* dependent product, to replace *)
                           (* This limitation is due to the reflexive
                             implementation and it is hard to lift *)
                           errorlabstrm "Setoid_replace"
                            (str "Cannot rewrite in the argument of a " ++
                             str "dependent product. If you need this " ++
                             str "feature, please report to the author.")
                      end
                  | _ -> assert false
            in
             find_non_dependent_function (Tacmach.pf_env gl) c [] typ [] []
              (Array.to_list al)
          in
           elim_duplicates identity (res_functions @ res_mors)
      | Prod (_, c1, c2) -> 
          if (dependent (mkRel 1) c2)
          then
           errorlabstrm "Setoid_replace"
            (str "Cannot rewrite in the type of a variable bound " ++
             str "in a dependent product.")
          else 
           let typeofc1 = Tacmach.pf_type_of gl c1 in
            if not (Tacmach.pf_conv_x gl typeofc1 mkProp) then
             (* to avoid this error we should introduce an impl relation
                whose first argument is Type instead of Prop. However,
                the type of the new impl would be Type -> Prop -> Prop
                that is no longer a Relation_Definitions.relation. Thus
                the Coq part of the tactic should be heavily modified. *)
             errorlabstrm "Setoid_replace"
              (str "Rewriting in a product A -> B is possible only when A " ++
               str "is a proposition (i.e. A is of type Prop). The type " ++
               prterm c1 ++ str " has type " ++ prterm typeofc1 ++
               str " that is not convertible to Prop.")
            else
             aux output_relation output_direction
              (mkApp ((Lazy.force coq_impl), [| c1 ; c2 |]))
      | _ -> [ToKeep (in_c,output_relation,output_direction)]
 in
  let aux2 output_relation output_direction =
   List.map
    (fun res -> output_relation,output_direction,res)
     (aux output_relation output_direction in_c) in
  let res =
   (aux2 (Lazy.force coq_prop_relation) Right2Left) @
   (* This is the case of a proposition of signature A ++> iff or B --> iff *)
   (aux2 (Lazy.force coq_prop_relation) Left2Right) @
   (aux2 (Lazy.force coq_prop_relation2) Right2Left) in
  let res = elim_duplicates (function (_,_,t) -> t) res in
  let res' = filter_superset_of_new_goals new_goals res in
  match res' with
     [] when res = [] ->
      errorlabstrm "Setoid_rewrite"
       (str "Either the term " ++ prterm in_c ++ str " that must be " ++
        str "rewritten occurs in a covariant position or the goal is not " ++
        str "made of morphism applications only. You can replace only " ++
        str "occurrences that are in a contravariant position and such that " ++
        str "the context obtained by abstracting them is made of morphism " ++
        str "applications only.")
   | [] ->
      errorlabstrm "Setoid_rewrite"
       (str "No generated set of side conditions is a superset of those " ++
        str "requested by the user. The generated sets of side conditions " ++
        str "are: " ++
         pr_fnl () ++
         prlist_with_sepi pr_fnl
          (fun i (_,_,mc) -> pr_new_goals i mc) res)
   | [he] -> he
   | he::_ ->
      ppnl
       (str "Warning: The application of the tactic is subject to one of " ++
        str "the \nfollowing set of side conditions that the user needs " ++
        str "to prove:" ++
         pr_fnl () ++
         prlist_with_sepi pr_fnl
          (fun i (_,_,mc) -> pr_new_goals i mc) res' ++ pr_fnl () ++
         str "The first set is randomly chosen. Use the syntax " ++
         str "\"setoid_rewrite ... generate side conditions ...\" to choose " ++
         str "a different set.") ;
      he

let cic_morphism_context_list_of_list hole_relation hole_direction out_direction
=
 let check =
  function
     (None,dir,dir') -> 
      mkApp ((Lazy.force coq_MSNone), [| dir ; dir' |])
   | (Some true,dir,dir') ->
      assert (dir = dir');
      mkApp ((Lazy.force coq_MSCovariant), [| dir |])
   | (Some false,dir,dir') ->
      assert (dir <> dir');
      mkApp ((Lazy.force coq_MSContravariant), [| dir |]) in
 let rec aux =
  function
     [] -> assert false
   | [(variance,out),(value,direction)] ->
      mkApp ((Lazy.force coq_singl), [| Lazy.force coq_Argument_Class ; out |]),
      mkApp ((Lazy.force coq_fcl_singl),
       [| hole_relation; hole_direction ; out ;
          direction ; out_direction ;
          check (variance,direction,out_direction) ; value |])
   | ((variance,out),(value,direction))::tl ->
      let outtl, valuetl = aux tl in
       mkApp ((Lazy.force coq_cons),
        [| Lazy.force coq_Argument_Class ; out ; outtl |]),
       mkApp ((Lazy.force coq_fcl_cons),
        [| hole_relation ; hole_direction ; out ; outtl ;
           direction ; out_direction ;
           check (variance,direction,out_direction) ;
           value ; valuetl |])
 in aux

let rec cic_type_nelist_of_list =
 function
    [] -> assert false
  | [value] ->
      mkApp ((Lazy.force coq_singl), [| mkType (Termops.new_univ ()) ; value |])
  | value::tl ->
     mkApp ((Lazy.force coq_cons),
      [| mkType (Termops.new_univ ()); value; cic_type_nelist_of_list tl |])

let syntactic_but_representation_of_marked_but hole_relation hole_direction =
 let rec aux out (rel_out,precise_out,is_reflexive) =
  function
     MApp (f, m, args, direction) ->
      let direction = cic_direction_of_direction direction in
      let morphism_theory, relations =
       match m with
          ACMorphism { args = args ; lem = lem } -> lem,args
        | ACFunction { f_args = f_args ; f_output = f_output } ->
           let mt =
            if eq_constr out (cic_relation_class_of_relation_class
              (Lazy.force coq_prop_relation))
            then
              mkApp ((Lazy.force coq_morphism_theory_of_predicate),
               [| cic_type_nelist_of_list f_args; f|])
            else
              mkApp ((Lazy.force coq_morphism_theory_of_function),
               [| cic_type_nelist_of_list f_args; f_output; f|])
           in
            mt,List.map (fun x -> None,Leibniz x) f_args in
      let cic_relations =
       List.map
        (fun (variance,r) ->
          variance,
          r,
          cic_relation_class_of_relation_class r,
          cic_precise_relation_class_of_relation_class r
        ) relations in
      let cic_args_relations,argst =
       cic_morphism_context_list_of_list hole_relation hole_direction direction
        (List.map2
         (fun (variance,trel,t,precise_t) v ->
           (variance,cic_argument_class_of_argument_class (variance,trel)),
             (aux t precise_t v,
               direction_of_constr_with_marks hole_direction v)
         ) cic_relations (Array.to_list args))
      in
       mkApp ((Lazy.force coq_App),
        [|hole_relation ; hole_direction ;
          cic_args_relations ; out ; direction ;
          morphism_theory ; argst|])
   | ToReplace ->
      mkApp ((Lazy.force coq_ToReplace), [| hole_relation ; hole_direction |])
   | ToKeep (c,_,direction) ->
      let direction = cic_direction_of_direction direction in
       if is_reflexive then
        mkApp ((Lazy.force coq_ToKeep),
         [| hole_relation ; hole_direction ; precise_out ; direction ; c |])
       else
        let c_is_proper =
         let typ = mkApp (rel_out, [| c ; c |]) in
          mkCast (Evarutil.mk_new_meta (),typ)
        in
         mkApp ((Lazy.force coq_ProperElementToKeep),
          [| hole_relation ; hole_direction; precise_out ;
             direction; c ; c_is_proper |])
 in aux

let apply_coq_setoid_rewrite hole_relation prop_relation c1 c2 (direction,h)
 prop_direction m
=
 let hole_relation = cic_relation_class_of_relation_class hole_relation in
 let hyp,hole_direction = h,cic_direction_of_direction direction in
 let cic_prop_relation = cic_relation_class_of_relation_class prop_relation in
 let precise_prop_relation =
  cic_precise_relation_class_of_relation_class prop_relation
 in
  mkApp ((Lazy.force coq_setoid_rewrite),
   [| hole_relation ; hole_direction ; cic_prop_relation ;
      prop_direction ; c1 ; c2 ;
      syntactic_but_representation_of_marked_but hole_relation hole_direction
       cic_prop_relation precise_prop_relation m ; hyp |])

let relation_rewrite c1 c2 (input_direction,cl) ~new_goals gl =
 let but = pf_concl gl in
 let (hyp,c1,c2) =
   let (env',c1) =
    try
     (* ~mod_delta:false to allow to mark occurences that must not be
        rewritten simply by replacing them with let-defined definitions
        in the context *)
     w_unify_to_subterm ~mod_delta:false (pf_env gl) (c1,but) cl.env
    with
     Pretype_errors.PretypeError _ ->
      (* ~mod_delta:true to make Ring work (since it really
          exploits conversion) *)
      w_unify_to_subterm ~mod_delta:true (pf_env gl) (c1,but) cl.env
   in
   let cl' = {cl with env = env' } in
   let c2 = Clenv.clenv_nf_meta cl' c2 in
    (input_direction,Clenv.clenv_value cl'), c1, c2
 in
  try
   let input_relation =
    relation_of_hypothesis_and_term_to_rewrite new_goals gl hyp c1 in
   let output_relation,output_direction,marked_but =
    mark_occur gl ~new_goals c1 but input_relation input_direction in
   let cic_output_direction = cic_direction_of_direction output_direction in
   let if_output_relation_is_iff gl =
    let th =
     apply_coq_setoid_rewrite input_relation output_relation c1 c2 hyp
      cic_output_direction marked_but
    in
     let new_but = Termops.replace_term c1 c2 but in
     let hyp1,hyp2,proj =
      match output_direction with
         Right2Left -> new_but, but, Lazy.force coq_proj1
       | Left2Right -> but, new_but, Lazy.force coq_proj2
     in
     let impl1 = mkProd (Anonymous, hyp2, lift 1 hyp1) in
     let impl2 = mkProd (Anonymous, hyp1, lift 1 hyp2) in
      let th' = mkApp (proj, [|impl2; impl1; th|]) in
       Tactics.refine
        (mkApp (th', [| mkCast (Evarutil.mk_new_meta(), new_but) |])) gl in
   let if_output_relation_is_if gl =
    let th =
     apply_coq_setoid_rewrite input_relation output_relation c1 c2 hyp
      cic_output_direction marked_but
    in
     let new_but = Termops.replace_term c1 c2 but in
      Tactics.refine
       (mkApp (th, [| mkCast (Evarutil.mk_new_meta(), new_but) |])) gl
   in
    if output_relation = (Lazy.force coq_prop_relation) then
     if_output_relation_is_iff gl
    else
     if_output_relation_is_if gl
  with
   Use_rewrite ->
    !general_rewrite (input_direction = Left2Right) (snd hyp) gl

let general_s_rewrite lft2rgt c ~new_goals gl =
 let direction = if lft2rgt then Left2Right else Right2Left in
 let ctype = pf_type_of gl c in
 let eqclause  = Clenv.make_clenv_binding gl (c,ctype) Rawterm.NoBindings in
 let (equiv, args) = decompose_app (Clenv.clenv_type eqclause) in
 let rec get_last_two = function
   | [c1;c2] -> (c1, c2)
   | x::y::z -> get_last_two (y::z)
   | _ -> error "The term provided is not an equivalence" in
 let (c1,c2) = get_last_two args in
  match direction with
     Left2Right -> relation_rewrite c1 c2 (direction,eqclause) ~new_goals gl
   | Right2Left -> relation_rewrite c2 c1 (direction,eqclause) ~new_goals gl

exception Use_replace

(*CSC: still setoid in the name *)
let setoid_replace relation c1 c2 ~new_goals gl =
 try
  let relation =
   match relation with
      Some rel ->
       (try
         match find_relation_class rel with
            Relation sa -> sa
          | Leibniz _ -> raise Use_replace
        with
         Not_found ->
          errorlabstrm "Setoid_rewrite"
           (prterm rel ++ str " is not a setoid equality."))
    | None ->
       match default_relation_for_carrier (pf_type_of gl c1) with
          Relation sa -> sa
        | Leibniz _ -> raise Use_replace
  in
   let eq_left_to_right = mkApp (relation.rel_aeq, [| c1 ; c2 |]) in
   let eq_right_to_left = mkApp (relation.rel_aeq, [| c2 ; c1 |]) in
   let replace dir eq =
    tclTHENS (assert_tac false Anonymous eq)
      [onLastHyp (fun id ->
        tclTHEN
          (general_s_rewrite dir (mkVar id) ~new_goals)
          (clear [id]));
       Tacticals.tclIDTAC]
   in
    tclORELSE
     (replace true eq_left_to_right) (replace false eq_right_to_left) gl
 with
  Use_replace -> (!replace c1 c2) gl
