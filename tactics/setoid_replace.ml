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
open Mod_subst

let replace = ref (fun _ _ _ -> assert false)
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
     rel_sym: constr option;
     rel_trans : constr option;
     rel_quantifiers_no: int  (* it helps unification *);
     rel_X_relation_class: constr;
     rel_Xreflexive_relation_class: constr
   }

type 'a relation_class =
   Relation of 'a            (* the rel_aeq of the relation or the relation   *)
 | Leibniz of constr option  (* the carrier (if eq is partially instantiated) *)

type 'a morphism =
    { args : (bool option * 'a relation_class) list;
      output : 'a relation_class;
      lem : constr;
      morphism_theory : constr
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
  | Leibniz t -> Leibniz (Option.map (subst_mps subst) t) 

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
    anomalylabstrm ""
      (str "Setoid: cannot find " ++ pr_id id ++
       str "(if loading Setoid.v under coqtop, use option \"-top Coq.Setoids.Setoid_tac\")")

(* From Setoid.v *)

let coq_reflexive =
 lazy(gen_constant ["Relations"; "Relation_Definitions"] "reflexive")
let coq_symmetric =
 lazy(gen_constant ["Relations"; "Relation_Definitions"] "symmetric")
let coq_transitive =
 lazy(gen_constant ["Relations"; "Relation_Definitions"] "transitive")
let coq_relation =
 lazy(gen_constant ["Relations"; "Relation_Definitions"] "relation")

let coq_Relation_Class = lazy(constant ["Setoid_tac"] "Relation_Class")
let coq_Argument_Class = lazy(constant ["Setoid_tac"] "Argument_Class")
let coq_Setoid_Theory = lazy(constant ["Setoid"] "Setoid_Theory")
let coq_Morphism_Theory = lazy(constant ["Setoid_tac"] "Morphism_Theory")
let coq_Build_Morphism_Theory= lazy(constant ["Setoid_tac"] "Build_Morphism_Theory")
let coq_Compat = lazy(constant ["Setoid_tac"] "Compat")

let coq_AsymmetricReflexive = lazy(constant ["Setoid_tac"] "AsymmetricReflexive")
let coq_SymmetricReflexive = lazy(constant ["Setoid_tac"] "SymmetricReflexive")
let coq_SymmetricAreflexive = lazy(constant ["Setoid_tac"] "SymmetricAreflexive")
let coq_AsymmetricAreflexive = lazy(constant ["Setoid_tac"] "AsymmetricAreflexive")
let coq_Leibniz = lazy(constant ["Setoid_tac"] "Leibniz")

let coq_RAsymmetric = lazy(constant ["Setoid_tac"] "RAsymmetric")
let coq_RSymmetric = lazy(constant ["Setoid_tac"] "RSymmetric")
let coq_RLeibniz = lazy(constant ["Setoid_tac"] "RLeibniz")

let coq_ASymmetric = lazy(constant ["Setoid_tac"] "ASymmetric")
let coq_AAsymmetric = lazy(constant ["Setoid_tac"] "AAsymmetric")

let coq_seq_refl = lazy(constant ["Setoid"] "Seq_refl")
let coq_seq_sym = lazy(constant ["Setoid"] "Seq_sym")
let coq_seq_trans = lazy(constant ["Setoid"] "Seq_trans")

let coq_variance = lazy(constant ["Setoid_tac"] "variance")
let coq_Covariant = lazy(constant ["Setoid_tac"] "Covariant")
let coq_Contravariant = lazy(constant ["Setoid_tac"] "Contravariant")
let coq_Left2Right = lazy(constant ["Setoid_tac"] "Left2Right")
let coq_Right2Left = lazy(constant ["Setoid_tac"] "Right2Left")
let coq_MSNone = lazy(constant ["Setoid_tac"] "MSNone")
let coq_MSCovariant = lazy(constant ["Setoid_tac"] "MSCovariant")
let coq_MSContravariant = lazy(constant ["Setoid_tac"] "MSContravariant")

let coq_singl = lazy(constant ["Setoid_tac"] "singl")
let coq_cons = lazy(constant ["Setoid_tac"] "necons")

let coq_equality_morphism_of_asymmetric_areflexive_transitive_relation =
 lazy(constant ["Setoid_tac"]
  "equality_morphism_of_asymmetric_areflexive_transitive_relation")
let coq_equality_morphism_of_symmetric_areflexive_transitive_relation =
 lazy(constant ["Setoid_tac"]
  "equality_morphism_of_symmetric_areflexive_transitive_relation")
let coq_equality_morphism_of_asymmetric_reflexive_transitive_relation =
 lazy(constant ["Setoid_tac"]
  "equality_morphism_of_asymmetric_reflexive_transitive_relation")
let coq_equality_morphism_of_symmetric_reflexive_transitive_relation =
 lazy(constant ["Setoid_tac"]
  "equality_morphism_of_symmetric_reflexive_transitive_relation")
let coq_make_compatibility_goal =
 lazy(constant ["Setoid_tac"] "make_compatibility_goal")
let coq_make_compatibility_goal_eval_ref =
 lazy(eval_reference ["Setoid_tac"] "make_compatibility_goal")
let coq_make_compatibility_goal_aux_eval_ref =
 lazy(eval_reference ["Setoid_tac"] "make_compatibility_goal_aux")

let coq_App = lazy(constant ["Setoid_tac"] "App")
let coq_ToReplace = lazy(constant ["Setoid_tac"] "ToReplace")
let coq_ToKeep = lazy(constant ["Setoid_tac"] "ToKeep")
let coq_ProperElementToKeep = lazy(constant ["Setoid_tac"] "ProperElementToKeep")
let coq_fcl_singl = lazy(constant ["Setoid_tac"] "fcl_singl")
let coq_fcl_cons = lazy(constant ["Setoid_tac"] "fcl_cons")

let coq_setoid_rewrite = lazy(constant ["Setoid_tac"] "setoid_rewrite")
let coq_proj1 = lazy(gen_constant ["Init"; "Logic"] "proj1")
let coq_proj2 = lazy(gen_constant ["Init"; "Logic"] "proj2")
let coq_unit = lazy(gen_constant ["Init"; "Datatypes"] "unit")
let coq_tt = lazy(gen_constant ["Init"; "Datatypes"] "tt")
let coq_eq = lazy(gen_constant ["Init"; "Logic"] "eq")

let coq_morphism_theory_of_function =
 lazy(constant ["Setoid_tac"] "morphism_theory_of_function")
let coq_morphism_theory_of_predicate =
 lazy(constant ["Setoid_tac"] "morphism_theory_of_predicate")
let coq_relation_of_relation_class =
 lazy(eval_reference ["Setoid_tac"] "relation_of_relation_class")
let coq_directed_relation_of_relation_class =
 lazy(eval_reference ["Setoid_tac"] "directed_relation_of_relation_class")
let coq_interp = lazy(eval_reference ["Setoid_tac"] "interp")
let coq_Morphism_Context_rect2 =
 lazy(eval_reference ["Setoid_tac"] "Morphism_Context_rect2")
let coq_iff = lazy(gen_constant ["Init";"Logic"] "iff")
let coq_impl = lazy(constant ["Setoid_tac"] "impl")


(************************* Table of declared relations **********************)


(* Relations are stored in a table which is synchronised with the
   Reset mechanism. The table maps the term denoting the relation to
   the data of type relation that characterises the relation *)

let relation_table = ref Gmap.empty

let relation_table_add (s,th) = relation_table := Gmap.add s th !relation_table
let relation_table_find s = Gmap.find s !relation_table
let relation_table_mem s = Gmap.mem s !relation_table

let prrelation s =
 str "(" ++ pr_lconstr s.rel_a ++ str "," ++ pr_lconstr s.rel_aeq ++ str ")"

let prrelation_class =
 function
    Relation eq  ->
     (try prrelation (relation_table_find eq)
      with Not_found ->
       str "[[ Error: " ++ pr_lconstr eq ++
        str " is not registered as a relation ]]")
  | Leibniz (Some ty) -> pr_lconstr ty
  | Leibniz None -> str "_"

let prmorphism_argument_gen prrelation (variance,rel) =
 prrelation rel ++
  match variance with
     None -> str " ==> "
   | Some true -> str " ++> "
   | Some false -> str " --> "

let prargument_class = prmorphism_argument_gen prrelation_class

let pr_morphism_signature (l,c) =
 prlist (prmorphism_argument_gen Ppconstr.pr_constr_expr) l ++
  Ppconstr.pr_constr_expr c

let prmorphism k m =
  pr_lconstr k ++ str ": " ++
  prlist prargument_class m.args ++
  prrelation_class m.output


(* A function that gives back the only relation_class on a given carrier *)
(*CSC: this implementation is really inefficient. I should define a new
  map to make it efficient. However, is this really worth of? *)
let default_relation_for_carrier ?(filter=fun _ -> true) a =
 let rng = Gmap.rng !relation_table in
 match List.filter (fun ({rel_a=rel_a} as r) -> rel_a = a && filter r) rng with
    [] -> Leibniz (Some a)
  | relation::tl ->
     if tl <> [] then
      Flags.if_warn msg_warning
       (str "There are several relations on the carrier \"" ++
         pr_lconstr a ++ str "\". The relation " ++ prrelation relation ++
         str " is chosen.") ;
     Relation relation

let find_relation_class rel =
 try Relation (relation_table_find rel)
 with
  Not_found ->
   let rel = Reduction.whd_betadeltaiota (Global.env ()) rel in
   match kind_of_term rel with
    | App (eq,[|ty|]) when eq_constr eq (Lazy.force coq_eq) -> Leibniz (Some ty)
    | _ when eq_constr rel (Lazy.force coq_eq) -> Leibniz None
    | _ -> raise Not_found

let coq_iff_relation = lazy (find_relation_class (Lazy.force coq_iff))
let coq_impl_relation = lazy (find_relation_class (Lazy.force coq_impl))

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
  let rel_refl' = Option.map (subst_mps subst) relation.rel_refl in
  let rel_sym' = Option.map (subst_mps subst) relation.rel_sym in
  let rel_trans' = Option.map (subst_mps subst) relation.rel_trans in
  let rel_X_relation_class' = subst_mps subst relation.rel_X_relation_class in
  let rel_Xreflexive_relation_class' =
   subst_mps subst relation.rel_Xreflexive_relation_class
  in
    if rel_a' == relation.rel_a
      && rel_aeq' == relation.rel_aeq
      && rel_refl' == relation.rel_refl
      && rel_sym' == relation.rel_sym
      && rel_trans' == relation.rel_trans
      && rel_X_relation_class' == relation.rel_X_relation_class
      && rel_Xreflexive_relation_class'==relation.rel_Xreflexive_relation_class
    then
      relation
    else
      { rel_a = rel_a' ;
        rel_aeq = rel_aeq' ;
        rel_refl = rel_refl' ;
        rel_sym = rel_sym';
        rel_trans = rel_trans';
        rel_quantifiers_no = relation.rel_quantifiers_no;
        rel_X_relation_class = rel_X_relation_class';
        rel_Xreflexive_relation_class = rel_Xreflexive_relation_class'
      }
      
let equiv_list () = List.map (fun x -> x.rel_aeq) (Gmap.rng !relation_table)

let _ = 
  Summary.declare_summary "relation-table"
    { Summary.freeze_function = (fun () -> !relation_table);
      Summary.unfreeze_function = (fun t -> relation_table := t);
      Summary.init_function = (fun () -> relation_table := Gmap .empty);
      Summary.survive_module = false;
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
        Flags.if_warn msg_warning 
         (strbrk "The relation " ++ prrelation th' ++
          strbrk " is redeclared. The new declaration" ++
           (match th'.rel_refl with
              None -> mt ()
            | Some t -> strbrk " (reflexivity proved by " ++ pr_lconstr t) ++
           (match th'.rel_sym with
               None -> mt ()
             | Some t ->
                (if th'.rel_refl = None then strbrk " (" else strbrk " and ")
		++ strbrk "symmetry proved by " ++ pr_lconstr t) ++
           (if th'.rel_refl <> None && th'.rel_sym <> None then
             str ")" else str "") ++
           strbrk " replaces the old declaration" ++
           (match old_relation.rel_refl with
              None -> str ""
            | Some t -> strbrk " (reflexivity proved by " ++ pr_lconstr t) ++
           (match old_relation.rel_sym with
               None -> str ""
             | Some t ->
                (if old_relation.rel_refl = None then
                  strbrk " (" else strbrk " and ") ++
                strbrk "symmetry proved by " ++ pr_lconstr t) ++
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
    Flags.if_warn msg_warning
     (strbrk "The morphism " ++ prmorphism m old_morph ++
      strbrk " is redeclared. " ++
      strbrk "The new declaration whose compatibility is proved by " ++
       pr_lconstr c.lem ++ strbrk " replaces the old declaration whose" ++
       strbrk " compatibility was proved by " ++
       pr_lconstr old_morph.lem ++ str ".")
  with
   Not_found -> morphism_table := Gmap.add m (c::old) !morphism_table

let default_morphism ?(filter=fun _ -> true) m =
  match List.filter filter (morphism_table_find m) with
      [] -> raise Not_found
    | m1::ml ->
        if ml <> [] then
          Flags.if_warn msg_warning
            (strbrk "There are several morphisms associated to \"" ++
            pr_lconstr m ++ strbrk "\". Morphism " ++ prmorphism m m1 ++
            strbrk " is randomly chosen.");
        relation_morphism_of_constr_morphism m1

let subst_morph subst morph = 
  let lem' = subst_mps subst morph.lem in
  let args' = list_smartmap (subst_mps_in_argument_class subst) morph.args in
  let output' = subst_mps_in_relation_class subst morph.output in
  let morphism_theory' = subst_mps subst morph.morphism_theory in
    if lem' == morph.lem
      && args' == morph.args
      && output' == morph.output
      && morphism_theory' == morph.morphism_theory
    then
      morph
    else
      { args = args' ;
        output = output' ;
        lem = lem' ;
        morphism_theory = morphism_theory'
      }


let _ = 
  Summary.declare_summary "morphism-table"
    { Summary.freeze_function = (fun () -> !morphism_table);
      Summary.unfreeze_function = (fun t -> morphism_table := t);
      Summary.init_function = (fun () -> morphism_table := Gmap .empty);
      Summary.survive_module = false;
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

let print_setoids () =
  Gmap.iter
   (fun k relation ->
     assert (k=relation.rel_aeq) ;
     ppnl (str"Relation " ++ prrelation relation ++ str";" ++
      (match relation.rel_refl with
          None -> str ""
        | Some t -> str" reflexivity proved by " ++ pr_lconstr t) ++
      (match relation.rel_sym with
          None -> str ""
        | Some t -> str " symmetry proved by " ++ pr_lconstr t) ++
      (match relation.rel_trans with
          None -> str ""
        | Some t -> str " transitivity proved by " ++ pr_lconstr t)))
   !relation_table ;
  Gmap.iter
   (fun k l ->
     List.iter
      (fun ({lem=lem} as mor) ->
        ppnl (str "Morphism " ++ prmorphism k mor ++
        str ". Compatibility proved by " ++
        pr_lconstr lem ++ str "."))
      l) !morphism_table
;;

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

(* also returns the triple (args_ty_quantifiers_rev,real_args_ty,real_output)
   where the args_ty and the output are delifted *)
let check_is_dependent n args_ty output =
 let m = List.length args_ty - n in
 let args_ty_quantifiers, args_ty = Util.list_chop n args_ty in
  let rec aux m t =
   match kind_of_term t with
      Prod (n,s,t) when m > 0 ->
       if not (dependent (mkRel 1) t) then
        let args,out = aux (m - 1) (subst1 (mkRel 1) (* dummy *) t) in
         s::args,out
       else
        errorlabstrm "New Morphism"
         (str "The morphism is not a quantified non dependent product.")
    | _ -> [],t
  in
   let ty = compose_prod (List.rev args_ty) output in
   let args_ty, output = aux m ty in
   List.rev args_ty_quantifiers, args_ty, output

let cic_relation_class_of_X_relation typ value =
 function
    {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=None} ->
     mkApp ((Lazy.force coq_AsymmetricReflexive),
      [| typ ; value ; rel_a ; rel_aeq; refl |])
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=Some sym} ->
     mkApp ((Lazy.force coq_SymmetricReflexive),
      [| typ ; rel_a ; rel_aeq; sym ; refl |])
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=None} ->
     mkApp ((Lazy.force coq_AsymmetricAreflexive),
      [| typ ; value ; rel_a ; rel_aeq |])
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=Some sym} ->
     mkApp ((Lazy.force coq_SymmetricAreflexive),
      [| typ ; rel_a ; rel_aeq; sym |])

let cic_relation_class_of_X_relation_class typ value =
 function
    Relation {rel_X_relation_class=x_relation_class} ->
     mkApp (x_relation_class, [| typ ; value |])
  | Leibniz (Some t) ->
     mkApp ((Lazy.force coq_Leibniz), [| typ ; t |])
  | Leibniz None -> assert false


let cic_precise_relation_class_of_relation =
 function
    {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=None} ->
      mkApp ((Lazy.force coq_RAsymmetric), [| rel_a ; rel_aeq; refl |])
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=Some refl; rel_sym=Some sym} ->
      mkApp ((Lazy.force coq_RSymmetric), [| rel_a ; rel_aeq; sym ; refl |])
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=None} ->
      mkApp ((Lazy.force coq_AAsymmetric), [| rel_a ; rel_aeq |])
  | {rel_a=rel_a; rel_aeq=rel_aeq; rel_refl=None; rel_sym=Some sym} ->
      mkApp ((Lazy.force coq_ASymmetric), [| rel_a ; rel_aeq; sym |])

let cic_precise_relation_class_of_relation_class =
 function
    Relation
     {rel_aeq=rel_aeq; rel_Xreflexive_relation_class=lem; rel_refl=rel_refl }
     ->
      rel_aeq,lem,not(rel_refl=None)
  | Leibniz (Some t) ->
     mkApp ((Lazy.force coq_eq), [| t |]),
      mkApp ((Lazy.force coq_RLeibniz), [| t |]), true
  | Leibniz None -> assert false

let cic_relation_class_of_relation_class rel =
 cic_relation_class_of_X_relation_class
  (Lazy.force coq_unit) (Lazy.force coq_tt) rel

let cic_argument_class_of_argument_class (variance,arg) =
 let coq_variant_value =
  match variance with
     None -> (Lazy.force coq_Covariant) (* dummy value, it won't be used *)
   | Some true -> (Lazy.force coq_Covariant)
   | Some false -> (Lazy.force coq_Contravariant)
 in
  cic_relation_class_of_X_relation_class (Lazy.force coq_variance)
   coq_variant_value arg

let cic_arguments_of_argument_class_list args =
 let rec aux =
  function
     [] -> assert false
   | [last] ->
      mkApp ((Lazy.force coq_singl), [| Lazy.force coq_Argument_Class; last |])
   | he::tl ->
      mkApp ((Lazy.force coq_cons),
       [| Lazy.force coq_Argument_Class; he ; aux tl |])
 in
  aux (List.map cic_argument_class_of_argument_class args)

let gen_compat_lemma_statement quantifiers_rev output args m =
 let output = cic_relation_class_of_relation_class output in
 let args = cic_arguments_of_argument_class_list args in
  args, output,
   compose_prod quantifiers_rev
    (mkApp ((Lazy.force coq_make_compatibility_goal), [| args ; output ; m |]))

let morphism_theory_id_of_morphism_proof_id id =
 id_of_string (string_of_id id ^ "_morphism_theory")

(* apply_to_rels c [l1 ; ... ; ln] returns (c Rel1 ... reln) *)
let apply_to_rels c l =
 if l = [] then c
 else
  let len = List.length l in
   applistc c (Util.list_map_i (fun i _ -> mkRel (len - i)) 0 l)

let apply_to_relation subst rel =
 if Array.length subst = 0 then rel
 else
  let new_quantifiers_no = rel.rel_quantifiers_no - Array.length subst in
   assert (new_quantifiers_no >= 0) ;
   { rel_a = mkApp (rel.rel_a, subst) ;
     rel_aeq = mkApp (rel.rel_aeq, subst) ;
     rel_refl = Option.map (fun c -> mkApp (c,subst)) rel.rel_refl ; 
     rel_sym = Option.map (fun c -> mkApp (c,subst)) rel.rel_sym;
     rel_trans = Option.map (fun c -> mkApp (c,subst)) rel.rel_trans;
     rel_quantifiers_no = new_quantifiers_no;
     rel_X_relation_class = mkApp (rel.rel_X_relation_class, subst);
     rel_Xreflexive_relation_class =
      mkApp (rel.rel_Xreflexive_relation_class, subst) }

let add_morphism lemma_infos mor_name (m,quantifiers_rev,args,output) =
 let lem =
  match lemma_infos with
     None ->
      (* the Morphism_Theory object has already been created *)
      let applied_args =
       let len = List.length quantifiers_rev in
       let subst =
        Array.of_list
         (Util.list_map_i (fun i _ -> mkRel (len - i)) 0 quantifiers_rev)
       in
        List.map
         (fun (v,rel) ->
           match rel with
              Leibniz (Some t) ->
               assert (subst=[||]);
               v, Leibniz (Some t)
            | Leibniz None ->
               assert (Array.length subst = 1);
               v, Leibniz (Some (subst.(0)))
            | Relation rel -> v, Relation (apply_to_relation subst rel)) args
      in
       compose_lam quantifiers_rev
        (mkApp (Lazy.force coq_Compat,
          [| cic_arguments_of_argument_class_list applied_args;
             cic_relation_class_of_relation_class output;
             apply_to_rels (current_constant mor_name) quantifiers_rev |]))
   | Some (lem_name,argsconstr,outputconstr) ->
      (* only the compatibility has been proved; we need to declare the
         Morphism_Theory object *)
     let mext = current_constant lem_name in
     ignore (
      Declare.declare_internal_constant mor_name
       (DefinitionEntry
         {const_entry_body =
           compose_lam quantifiers_rev
            (mkApp ((Lazy.force coq_Build_Morphism_Theory),
              [| argsconstr; outputconstr; apply_to_rels m quantifiers_rev ;
                  apply_to_rels mext quantifiers_rev |]));
          const_entry_type = None;
          const_entry_opaque = false;
          const_entry_boxed = Flags.boxed_definitions()},
	IsDefinition Definition)) ;
     mext 
 in
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
        lem = lem;
        morphism_theory = mmor }));
   Flags.if_verbose ppnl (pr_lconstr m ++ str " is registered as a morphism")

let error_cannot_unify_signature env k t t' =
  errorlabstrm "New Morphism"
   (str "One morphism argument or its output has type" ++ spc() ++
    pr_lconstr_env env t ++ strbrk " but the signature requires an argument" ++
    (if k = 0 then strbrk " of type " else
    strbrk "whose type is an instance of ") ++ pr_lconstr_env env t' ++
    str ".")

(* first order matching with a bit of conversion *)
let unify_relation_carrier_with_type env rel t =
 let args =
  match kind_of_term t with
     App (he',args') ->
      let argsno = Array.length args' - rel.rel_quantifiers_no in
      let args1 = Array.sub args' 0 argsno in
      let args2 = Array.sub args' argsno rel.rel_quantifiers_no in
       if is_conv env Evd.empty rel.rel_a (mkApp (he',args1)) then
        args2
       else
	error_cannot_unify_signature env rel.rel_quantifiers_no t rel.rel_a
   | _  ->
       try
       let args =
         Clenv.clenv_conv_leq env Evd.empty t rel.rel_a rel.rel_quantifiers_no
       in
       Array.of_list args
       with Reduction.NotConvertible -> 
	error_cannot_unify_signature env rel.rel_quantifiers_no t rel.rel_a
 in
  apply_to_relation args rel

let unify_relation_class_carrier_with_type env rel t =
 match rel with
    Leibniz (Some t') ->
     if is_conv env Evd.empty t t' then
      rel
     else
      error_cannot_unify_signature env 0 t t'
  | Leibniz None -> Leibniz (Some t)
  | Relation rel -> Relation (unify_relation_carrier_with_type env rel t)

exception Impossible

(* first order matching with a bit of conversion *)
(* Note: the type checking operations performed by the function could  *)
(* be done once and for all abstracting the morphism structure using   *)
(* the quantifiers. Would the new structure be more suited than the    *)
(* existent one for other tasks to? (e.g. pretty printing would expose *)
(* much more information: is it ok or is it too much information?)     *)
let unify_morphism_with_arguments gl (c,av)
     {args=args; output=output; lem=lem; morphism_theory=morphism_theory} t
=
 let avlen = Array.length av in 
 let argsno = List.length args in
 if avlen < argsno then raise Impossible; (* partial application *)
 let al = Array.to_list av in
 let quantifiers,al' = Util.list_chop (avlen - argsno) al in
 let quantifiersv = Array.of_list quantifiers in
 let c' = mkApp (c,quantifiersv) in
 if dependent t c' then raise Impossible; 
 (* these are pf_type_of we could avoid *)
 let al'_type = List.map (Tacmach.pf_type_of gl) al' in
 let args' =
   List.map2
     (fun (var,rel) ty ->
	var,unify_relation_class_carrier_with_type (pf_env gl) rel ty)
     args al'_type in
 (* this is another pf_type_of we could avoid *)
 let ty = Tacmach.pf_type_of gl (mkApp (c,av)) in
 let output' = unify_relation_class_carrier_with_type (pf_env gl) output ty in
 let lem' = mkApp (lem,quantifiersv) in
 let morphism_theory' = mkApp (morphism_theory,quantifiersv) in
 ({args=args'; output=output'; lem=lem'; morphism_theory=morphism_theory'},
  c',Array.of_list al')

let new_morphism m signature id hook =
 if Nametab.exists_cci (Lib.make_path id) or is_section_variable id then
  errorlabstrm "New Morphism" (pr_id id ++ str " already exists")
 else
  let env = Global.env() in
  let typeofm = Typing.type_of env Evd.empty m in
  let typ = clos_norm_flags Closure.betaiotazeta empty_env Evd.empty typeofm in
  let argsrev, output =
    match signature with
	None -> decompose_prod typ
      | Some (_,output') ->
	  (* the carrier of the relation output' can be a Prod ==>
             we must uncurry on the fly output.
             E.g: A -> B -> C vs        A -> (B -> C)
             args   output     args     output
	  *)
	  let rel = 
	    try find_relation_class output' 
	    with Not_found -> errorlabstrm "Add Morphism"
	      (str "Not a valid signature: " ++ pr_lconstr output' ++
		 str " is neither a registered relation nor the Leibniz " ++
		 str " equality.") in
	  let rel_a,rel_quantifiers_no =
            match rel with
		Relation rel -> rel.rel_a, rel.rel_quantifiers_no
              | Leibniz (Some t) -> t, 0
              | Leibniz None -> let _,t = decompose_prod typ in t, 0 in
	  let rel_a_n =
            clos_norm_flags Closure.betaiotazeta empty_env Evd.empty rel_a 
	  in
	    try
              let _,output_rel_a_n = decompose_lam_n rel_quantifiers_no rel_a_n in
              let argsrev,_ = decompose_prod output_rel_a_n in
              let n = List.length argsrev in
              let argsrev',_ = decompose_prod typ in
              let m = List.length argsrev' in
		decompose_prod_n (m - n) typ
	    with UserError(_,_) ->
              (* decompose_lam_n failed. This may happen when rel_a is an axiom,
		 a constructor, an inductive type, etc. *)
              decompose_prod typ
  in
  let args_ty = List.rev argsrev in
  let args_ty_len = List.length (args_ty) in
  let args_ty_quantifiers_rev,args,args_instance,output,output_instance =
    match signature with
	None ->
	  if args_ty = [] then
            errorlabstrm "New Morphism"
              (str "The term " ++ pr_lconstr m ++ str " has type " ++
		  pr_lconstr typeofm ++ str " that is not a product.") ;
	  ignore (check_is_dependent 0 args_ty output) ;
	  let args =
            List.map
              (fun (_,ty) -> None,default_relation_for_carrier ty) args_ty in
	  let output = default_relation_for_carrier output in
            [],args,args,output,output
      | Some (args,output') ->
	  assert (args <> []);
	  let number_of_arguments = List.length args in
	  let number_of_quantifiers = args_ty_len - number_of_arguments in
	    if number_of_quantifiers < 0 then
              errorlabstrm "New Morphism"
		(str "The morphism " ++ pr_lconstr m ++ str " has type " ++
		    pr_lconstr typeofm ++ str " that expects at most " ++ int args_ty_len ++
		    str " arguments. The signature that you specified requires " ++
		    int number_of_arguments ++ str " arguments.")
	    else
              begin
		(* the real_args_ty returned are already delifted *)
		let args_ty_quantifiers_rev, real_args_ty, real_output =
		  check_is_dependent number_of_quantifiers args_ty output in
		let quantifiers_rel_context =
		  List.map (fun (n,t) -> n,None,t) args_ty_quantifiers_rev in
		let env = push_rel_context quantifiers_rel_context env in
		let find_relation_class t real_t =
		  try
		    let rel = find_relation_class t in
		      rel, unify_relation_class_carrier_with_type env rel real_t
		  with Not_found ->
		    errorlabstrm "Add Morphism"
		      (str "Not a valid signature: " ++ pr_lconstr t ++
			  str " is neither a registered relation nor the Leibniz " ++
			  str " equality.")
		in
		let find_relation_class_v (variance,t) real_t =
		  let relation,relation_instance = find_relation_class t real_t in
		    match relation, variance with
			Leibniz _, None
		      | Relation {rel_sym = Some _}, None
		      | Relation {rel_sym = None}, Some _ ->
			  (variance, relation), (variance, relation_instance)
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
		let args, args_instance =
		  List.split
		    (List.map2 find_relation_class_v args real_args_ty) in
		let output,output_instance= find_relation_class output' real_output in
		  args_ty_quantifiers_rev, args, args_instance, output, output_instance
              end
  in
  let argsconstr,outputconstr,lem =
    gen_compat_lemma_statement args_ty_quantifiers_rev output_instance
      args_instance (apply_to_rels m args_ty_quantifiers_rev) in
    (* "unfold make_compatibility_goal" *)
  let lem =
    Reductionops.clos_norm_flags
      (Closure.unfold_red (Lazy.force coq_make_compatibility_goal_eval_ref))
      env Evd.empty lem in
    (* "unfold make_compatibility_goal_aux" *)
  let lem =
    Reductionops.clos_norm_flags
      (Closure.unfold_red(Lazy.force coq_make_compatibility_goal_aux_eval_ref))
      env Evd.empty lem in
    (* "simpl" *)
  let lem = Tacred.simpl env Evd.empty lem in
    if Lib.is_modtype () then
      begin
	ignore
	  (Declare.declare_internal_constant id
              (ParameterEntry (lem,false), IsAssumption Logical)) ;
	let mor_name = morphism_theory_id_of_morphism_proof_id id in
	let lemma_infos = Some (id,argsconstr,outputconstr) in
	  add_morphism lemma_infos mor_name
            (m,args_ty_quantifiers_rev,args,output)
      end
    else
      begin
	new_edited id
	  (m,args_ty_quantifiers_rev,args,argsconstr,output,outputconstr);
	Pfedit.start_proof id (Global, Proof Lemma) 
	  (Decls.clear_proofs (Global.named_context ()))
	  lem hook;
	Flags.if_verbose msg (Printer.pr_open_subgoals ());
      end

let morphism_hook _ ref =
  let pf_id = id_of_global ref in
  let mor_id = morphism_theory_id_of_morphism_proof_id pf_id in
  let (m,quantifiers_rev,args,argsconstr,output,outputconstr) =
   what_edited pf_id in
  if (is_edited pf_id)
  then 
   begin
    add_morphism (Some (pf_id,argsconstr,outputconstr)) mor_id
     (m,quantifiers_rev,args,output) ;
    no_more_edited pf_id
   end

type morphism_signature =
 (bool option * Topconstr.constr_expr) list * Topconstr.constr_expr

let new_named_morphism id m sign =
  Coqlib.check_required_library ["Coq";"Setoids";"Setoid_tac"];
 let sign =
  match sign with
     None -> None
   | Some (args,out) ->
      if args = [] then
	error "Morphism signature expects at least one argument.";
      Some
       (List.map (fun (variance,ty) -> variance, constr_of ty) args,
        constr_of out)
 in
  new_morphism (constr_of m) sign id morphism_hook

(************************** Adding a relation to the database *********************)

let check_a env a =
 let typ = Typing.type_of env Evd.empty a in
 let a_quantifiers_rev,_ = Reduction.dest_arity env typ in
  a_quantifiers_rev

let check_eq env a_quantifiers_rev a aeq =
 let typ =
  Sign.it_mkProd_or_LetIn
   (mkApp ((Lazy.force coq_relation),[| apply_to_rels a a_quantifiers_rev |]))
   a_quantifiers_rev in
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty aeq) typ)
 then
  errorlabstrm "Add Relation Class"
   (pr_lconstr aeq ++ str " should have type (" ++ pr_lconstr typ ++ str ")")

let check_property env a_quantifiers_rev a aeq strprop coq_prop t =
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty t)
    (Sign.it_mkProd_or_LetIn
     (mkApp ((Lazy.force coq_prop),
       [| apply_to_rels a   a_quantifiers_rev ;
          apply_to_rels aeq a_quantifiers_rev |])) a_quantifiers_rev))
 then
  errorlabstrm "Add Relation Class"
   (str "Not a valid proof of " ++ str strprop ++ str ".")

let check_refl env a_quantifiers_rev a aeq refl =
 check_property env a_quantifiers_rev a aeq "reflexivity" coq_reflexive refl

let check_sym env a_quantifiers_rev a aeq sym =
 check_property env a_quantifiers_rev a aeq "symmetry" coq_symmetric sym

let check_trans env a_quantifiers_rev a aeq trans =
 check_property env a_quantifiers_rev a aeq "transitivity" coq_transitive trans

let check_setoid_theory env a_quantifiers_rev a aeq th =
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty th)
    (Sign.it_mkProd_or_LetIn
     (mkApp ((Lazy.force coq_Setoid_Theory),
       [| apply_to_rels a   a_quantifiers_rev ;
          apply_to_rels aeq a_quantifiers_rev |])) a_quantifiers_rev))
 then
  errorlabstrm "Add Relation Class"
   (str "Not a valid proof of symmetry")

let int_add_relation id a aeq refl sym trans =
 let env = Global.env () in
 let a_quantifiers_rev = check_a env a in
  check_eq env a_quantifiers_rev a aeq  ;
  Option.iter (check_refl env a_quantifiers_rev a aeq) refl ;
  Option.iter (check_sym env a_quantifiers_rev a aeq) sym ;
  Option.iter (check_trans env a_quantifiers_rev a aeq) trans ;
  let quantifiers_no = List.length a_quantifiers_rev in
  let aeq_rel =
   { rel_a = a;
     rel_aeq = aeq;
     rel_refl = refl;
     rel_sym = sym;
     rel_trans = trans;
     rel_quantifiers_no = quantifiers_no;
     rel_X_relation_class = mkProp; (* dummy value, overwritten below *)
     rel_Xreflexive_relation_class = mkProp (* dummy value, overwritten below *)
   } in
  let x_relation_class =
   let subst =
    let len = List.length a_quantifiers_rev in
    Array.of_list
     (Util.list_map_i (fun i _ -> mkRel (len - i + 2)) 0 a_quantifiers_rev) in
   cic_relation_class_of_X_relation
    (mkRel 2) (mkRel 1) (apply_to_relation subst aeq_rel) in
  let _ =
   Declare.declare_internal_constant id
    (DefinitionEntry
      {const_entry_body =
        Sign.it_mkLambda_or_LetIn x_relation_class
         ([ Name (id_of_string "v"),None,mkRel 1;
            Name (id_of_string "X"),None,mkType (Termops.new_univ ())] @
            a_quantifiers_rev);
       const_entry_type = None;
       const_entry_opaque = false;
       const_entry_boxed = Flags.boxed_definitions()},
      IsDefinition Definition) in
  let id_precise = id_of_string (string_of_id id ^ "_precise_relation_class") in
  let xreflexive_relation_class =
   let subst =
    let len = List.length a_quantifiers_rev in
    Array.of_list
     (Util.list_map_i (fun i _ -> mkRel (len - i)) 0 a_quantifiers_rev)
   in
    cic_precise_relation_class_of_relation (apply_to_relation subst aeq_rel) in
  let _ =
   Declare.declare_internal_constant id_precise
    (DefinitionEntry
      {const_entry_body =
        Sign.it_mkLambda_or_LetIn xreflexive_relation_class a_quantifiers_rev;
       const_entry_type = None;
       const_entry_opaque = false;
       const_entry_boxed = Flags.boxed_definitions() },
      IsDefinition Definition) in
  let aeq_rel =
   { aeq_rel with
      rel_X_relation_class = current_constant id;
      rel_Xreflexive_relation_class = current_constant id_precise } in
  Lib.add_anonymous_leaf (relation_to_obj (aeq, aeq_rel)) ;
  Flags.if_verbose ppnl (pr_lconstr aeq ++ str " is registered as a relation");
  match trans with
     None -> ()
   | Some trans ->
      let mor_name = id_of_string (string_of_id id ^ "_morphism") in
      let a_instance = apply_to_rels a a_quantifiers_rev in
      let aeq_instance = apply_to_rels aeq a_quantifiers_rev in
      let sym_instance =
       Option.map (fun x -> apply_to_rels x a_quantifiers_rev) sym in
      let refl_instance =
       Option.map (fun x -> apply_to_rels x a_quantifiers_rev) refl in
      let trans_instance = apply_to_rels trans a_quantifiers_rev in
      let aeq_rel_class_and_var1, aeq_rel_class_and_var2, lemma, output =
       match sym_instance, refl_instance with
          None, None ->
           (Some false, Relation aeq_rel),
           (Some true, Relation aeq_rel),
            mkApp
             ((Lazy.force
                coq_equality_morphism_of_asymmetric_areflexive_transitive_relation),
              [| a_instance ; aeq_instance ; trans_instance |]),
            Lazy.force coq_impl_relation
        | None, Some refl_instance ->
           (Some false, Relation aeq_rel),
           (Some true, Relation aeq_rel),
            mkApp
             ((Lazy.force
                coq_equality_morphism_of_asymmetric_reflexive_transitive_relation),
              [| a_instance ; aeq_instance ; refl_instance ; trans_instance |]),
            Lazy.force coq_impl_relation
        | Some sym_instance, None ->
           (None, Relation aeq_rel),
           (None, Relation aeq_rel),
            mkApp
             ((Lazy.force
                coq_equality_morphism_of_symmetric_areflexive_transitive_relation),
              [| a_instance ; aeq_instance ; sym_instance ; trans_instance |]),
            Lazy.force coq_iff_relation
        | Some sym_instance, Some refl_instance ->
           (None, Relation aeq_rel),
           (None, Relation aeq_rel),
            mkApp
             ((Lazy.force
                coq_equality_morphism_of_symmetric_reflexive_transitive_relation),
              [| a_instance ; aeq_instance ; refl_instance ; sym_instance ;
                 trans_instance |]),
            Lazy.force coq_iff_relation in
      let _ =
       Declare.declare_internal_constant mor_name
        (DefinitionEntry
          {const_entry_body = Sign.it_mkLambda_or_LetIn lemma a_quantifiers_rev;
           const_entry_type = None;
           const_entry_opaque = false;
          const_entry_boxed = Flags.boxed_definitions()},
          IsDefinition Definition)
      in
       let a_quantifiers_rev =
        List.map (fun (n,b,t) -> assert (b = None); n,t) a_quantifiers_rev in
       add_morphism None mor_name
        (aeq,a_quantifiers_rev,[aeq_rel_class_and_var1; aeq_rel_class_and_var2],
          output)

(* The vernac command "Add Relation ..." *)
let add_relation id a aeq refl sym trans =
  Coqlib.check_required_library ["Coq";"Setoids";"Setoid_tac"];
  int_add_relation id (constr_of a) (constr_of aeq) (Option.map constr_of refl)
    (Option.map constr_of sym) (Option.map constr_of trans)

(************************ Add Setoid ******************************************)

(* The vernac command "Add Setoid" *)
let add_setoid id a aeq th =
  Coqlib.check_required_library ["Coq";"Setoids";"Setoid_tac"];
  let a = constr_of a in
  let aeq = constr_of aeq in
  let th = constr_of th in
  let env = Global.env () in
  let a_quantifiers_rev = check_a env a in
  check_eq env a_quantifiers_rev a aeq  ;
  check_setoid_theory env a_quantifiers_rev a aeq  th ;
  let a_instance = apply_to_rels a a_quantifiers_rev in
   let aeq_instance = apply_to_rels aeq a_quantifiers_rev in
   let th_instance = apply_to_rels th a_quantifiers_rev in
   let refl =
    Sign.it_mkLambda_or_LetIn
     (mkApp ((Lazy.force coq_seq_refl),
       [| a_instance; aeq_instance; th_instance |])) a_quantifiers_rev in
   let sym =
    Sign.it_mkLambda_or_LetIn
     (mkApp ((Lazy.force coq_seq_sym),
       [| a_instance; aeq_instance; th_instance |])) a_quantifiers_rev in
   let trans =
    Sign.it_mkLambda_or_LetIn
     (mkApp ((Lazy.force coq_seq_trans),
       [| a_instance; aeq_instance; th_instance |])) a_quantifiers_rev in
   int_add_relation id a aeq (Some refl) (Some sym) (Some trans)


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

exception Optimize (* used to fall-back on the tactic for Leibniz equality *)

let relation_class_that_matches_a_constr caller_name new_goals hypt =
 let (heq, hargs) = decompose_app hypt in
 let rec get_all_but_last_two =
  function
     []
   | [_] ->
      errorlabstrm caller_name (pr_lconstr hypt ++
       str " is not a registered relation.")
   | [_;_] -> []
   | he::tl -> he::(get_all_but_last_two tl) in
 let all_aeq_args = get_all_but_last_two hargs in
 let rec find_relation l subst =
  let aeq = mkApp (heq,(Array.of_list l)) in
  try
   let rel = find_relation_class aeq in
   match rel,new_goals with
      Leibniz _,[] ->
       assert (subst = []);
       raise Optimize (* let's optimize the proof term size *)
    | Leibniz (Some _), _ ->
       assert (subst = []);
       rel
    | Leibniz None, _ ->
       (* for well-typedness reasons it should have been catched by the
          previous guard in the previous iteration. *)
       assert false
    | Relation rel,_ -> Relation (apply_to_relation (Array.of_list subst) rel)
  with Not_found ->
   if l = [] then
    errorlabstrm caller_name
     (pr_lconstr (mkApp (aeq, Array.of_list all_aeq_args)) ++
      str " is not a registered relation.")
   else
    let last,others = Util.list_sep_last l in
    find_relation others (last::subst)
 in
  find_relation all_aeq_args []

(* rel1 is a subrelation of rel2 whenever 
    forall x1 x2, rel1 x1 x2 -> rel2 x1 x2
   The Coq part of the tactic, however, needs rel1 == rel2.
   Hence the third case commented out.
   Note: accepting user-defined subrelations seems to be the last
   useful generalization that does not go against the original spirit of
   the tactic.
*)
let subrelation gl rel1 rel2 =
 match rel1,rel2 with
    Relation {rel_aeq=rel_aeq1}, Relation {rel_aeq=rel_aeq2} ->
     Tacmach.pf_conv_x gl rel_aeq1 rel_aeq2
  | Leibniz (Some t1), Leibniz (Some t2) ->
     Tacmach.pf_conv_x gl t1 t2
  | Leibniz None, _
  | _, Leibniz None -> assert false
(* This is the commented out case (see comment above)
  | Leibniz (Some t1), Relation {rel_a=t2; rel_refl = Some _} ->
     Tacmach.pf_conv_x gl t1 t2
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
let marked_constr_equiv_or_more_complex to_marked_constr gl c1 c2 =
  let glc1 = collect_new_goals (to_marked_constr c1) in
  let glc2 = collect_new_goals (to_marked_constr c2) in
   List.for_all (fun c -> List.exists (fun c' -> pf_conv_x gl c c') glc1) glc2

let pr_new_goals i c =
 let glc = collect_new_goals c in
  str " " ++ int i ++ str ") side conditions:" ++
   (if glc = [] then str " no side conditions"
    else
     (pr_fnl () ++ str "   " ++
       prlist_with_sep (fun () -> str "\n   ")
        (fun c -> str " ... |- " ++ pr_lconstr c) glc))

(* given a list of constr_with_marks, it returns the list where
   constr_with_marks than open more goals than simpler ones in the list
   are got rid of *)
let elim_duplicates gl to_marked_constr =
 let rec aux =
  function
     [] -> []
   | he:: tl ->
      if List.exists
          (marked_constr_equiv_or_more_complex to_marked_constr gl he) tl
      then aux tl
      else he::aux tl
 in
  aux

let filter_superset_of_new_goals gl new_goals l =
 List.filter
  (fun (_,_,c) ->
    List.for_all
     (fun g -> List.exists (pf_conv_x gl g) (collect_new_goals c)) new_goals) l

(* given the array of lists [| l1 ; ... ; ln |] it returns the list of arrays
   [ c1 ; ... ; cn ] that is the cartesian product of the sets l1, ..., ln *)
let cartesian_product gl a =
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
   (aux (List.map (elim_duplicates gl identity) (Array.to_list a)))

let mark_occur gl ~new_goals t in_c input_relation input_direction =
 let rec aux output_relation output_directions in_c =
  if eq_constr t in_c then
   if List.mem input_direction output_directions
   && subrelation gl input_relation output_relation then
    [ToReplace]
   else []
  else
    match kind_of_term in_c with
      | App (c,al) -> 
         let mors_and_cs_and_als =
          let mors_and_cs_and_als =
           let morphism_table_find c =
            try morphism_table_find c with Not_found -> [] in
           let rec aux acc =
            function
               [] ->
                let c' = mkApp (c, Array.of_list acc) in
                let al' = [||] in
                List.map (fun m -> m,c',al') (morphism_table_find c')
             | (he::tl) as l ->
                let c' = mkApp (c, Array.of_list acc) in
                let al' = Array.of_list l in
                let acc' = acc @ [he] in
                 (List.map (fun m -> m,c',al') (morphism_table_find c')) @
                  (aux acc' tl)
           in
            aux [] (Array.to_list al) in
          let mors_and_cs_and_als =
           List.map
            (function (m,c,al) ->
              relation_morphism_of_constr_morphism m, c, al)
             mors_and_cs_and_als in
          let mors_and_cs_and_als =
           List.fold_left
            (fun l (m,c,al) ->
	       try (unify_morphism_with_arguments gl (c,al) m t) :: l
	       with Impossible -> l
	    ) [] mors_and_cs_and_als
          in
           List.filter
            (fun (mor,_,_) -> subrelation gl mor.output output_relation)
            mors_and_cs_and_als
         in
          (* First we look for well typed morphisms *)
          let res_mors =
           List.fold_left
            (fun res (mor,c,al) ->
              let a =
               let arguments = Array.of_list mor.args in
               let apply_variance_to_direction =
                function
                   None -> [Left2Right;Right2Left]
                 | Some true -> output_directions
                 | Some false -> List.map opposite_direction output_directions
               in
                Util.array_map2
                 (fun a (variance,relation) ->
                   (aux relation (apply_variance_to_direction variance) a)
                 ) al arguments
              in
               let a' = cartesian_product gl a in
	       List.flatten (List.map (fun output_direction ->
                (List.map
                  (function a ->
                    if not (get_mark a) then
                     ToKeep (in_c,output_relation,output_direction)
                    else
                     MApp (c,ACMorphism mor,a,output_direction)) a'))
		 output_directions) @ res
            ) [] mors_and_cs_and_als in
          (* Then we look for well typed functions *)
          let res_functions =
           (* the tactic works only if the function type is
               made of non-dependent products only. However, here we
               can cheat a bit by partially instantiating c to match
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
		  List.map (fun output_direction ->
                   ToKeep (in_c,output_relation,output_direction))
		   output_directions
                 else
                  let a' =
                   cartesian_product gl (Array.of_list (List.rev a_rev))
                  in
                   List.fold_left
                    (fun res a ->
                      if not (get_mark a) then
			List.map (fun output_direction ->
			 (ToKeep (in_c,output_relation,output_direction)))
			 output_directions @ res
                      else
                       let err =
                        match output_relation with
                           Leibniz (Some typ') when pf_conv_x gl typ typ' ->
                            false
                         | Leibniz None -> assert false
                         | _ when output_relation = Lazy.force coq_iff_relation
                             -> false
                         | _ -> true
                       in
                        if err then res
                        else
                         let mor =
                          ACFunction{f_args=List.rev f_args_rev;f_output=typ} in
                         let func = beta_expand c c_args_rev in
			 List.map (fun output_direction ->
                          (MApp (func,mor,a,output_direction)))
			  output_directions @ res
                    ) [] a'
              | (he::tl) ->
                 let typnf = Reduction.whd_betadeltaiota env typ in
                  match kind_of_term typnf with
                  | Prod (name,s,t) ->
                     let env' = push_rel (name,None,s) env in
                     let he =
                      (aux (Leibniz (Some s)) [Left2Right;Right2Left] he) in
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
                                  ToKeep(arg',_,_) when pf_conv_x gl arg arg' ->
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
           elim_duplicates gl identity (res_functions @ res_mors)
      | Prod (_, c1, c2) -> 
          if (dependent (mkRel 1) c2)
          then
            if (occur_term t c2)
	    then errorlabstrm "Setoid_replace"
              (str "Cannot rewrite in the type of a variable bound " ++
		  str "in a dependent product.")
	    else
	      List.map (fun output_direction ->
	       ToKeep (in_c,output_relation,output_direction)) 
	       output_directions
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
		      pr_lconstr c1 ++ str " has type " ++ pr_lconstr typeofc1 ++
		      str " that is not convertible to Prop.")
              else
		aux output_relation output_directions
		  (mkApp ((Lazy.force coq_impl),
			 [| c1 ; subst1 (mkRel 1 (*dummy*)) c2 |]))
      | _ ->
          if occur_term t in_c then
            errorlabstrm "Setoid_replace"
              (str "Trying to replace " ++ pr_lconstr t ++ str " in " ++ pr_lconstr in_c ++
		  str " that is not an applicative context.")
          else
	    List.map (fun output_direction ->
             ToKeep (in_c,output_relation,output_direction))
	      output_directions
 in
  let aux2 output_relation output_direction =
   List.map
    (fun res -> output_relation,output_direction,res)
     (aux output_relation [output_direction] in_c) in
  let res =
   (aux2 (Lazy.force coq_iff_relation) Right2Left) @
   (* [Left2Right] is the case of a prop of signature A ++> iff or B --> iff *)
   (aux2 (Lazy.force coq_iff_relation) Left2Right) @
   (aux2 (Lazy.force coq_impl_relation) Right2Left) in
  let res = elim_duplicates gl (function (_,_,t) -> t) res in
  let res' = filter_superset_of_new_goals gl new_goals res in
  match res' with
     [] when res = [] ->
      errorlabstrm "Setoid_rewrite"
       (strbrk "Either the term " ++ pr_lconstr t ++ strbrk " that must be " ++
        strbrk "rewritten occurs in a covariant position or the goal is not" ++
        strbrk " made of morphism applications only. You can replace only " ++
        strbrk "occurrences that are in a contravariant position and such " ++
        strbrk "that the context obtained by abstracting them is made of " ++
        strbrk "morphism applications only.")
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
      Flags.if_warn msg_warning
       (strbrk "The application of the tactic is subject to one of " ++
        strbrk "the following set of side conditions that the user needs " ++
        strbrk "to prove:" ++
         pr_fnl () ++
         prlist_with_sepi pr_fnl
          (fun i (_,_,mc) -> pr_new_goals i mc) res' ++ pr_fnl () ++
         strbrk "The first set is randomly chosen. Use the syntax " ++
         strbrk "\"setoid_rewrite ... generate side conditions ...\" to choose " ++
         strbrk "a different set.") ;
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
          ACMorphism { args = args ; morphism_theory = morphism_theory } ->
           morphism_theory,args
        | ACFunction { f_args = f_args ; f_output = f_output } ->
           let mt =
            if eq_constr out (cic_relation_class_of_relation_class
              (Lazy.force coq_iff_relation))
            then
              mkApp ((Lazy.force coq_morphism_theory_of_predicate),
               [| cic_type_nelist_of_list f_args; f|])
            else
              mkApp ((Lazy.force coq_morphism_theory_of_function),
               [| cic_type_nelist_of_list f_args; f_output; f|])
           in
            mt,List.map (fun x -> None,Leibniz (Some x)) f_args in
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
          mkCast (Evarutil.mk_new_meta (),DEFAULTcast, typ)
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

let check_evar_map_of_evars_defs evd =
 let metas = Evd.meta_list evd in
 let check_freemetas_is_empty rebus =
  Evd.Metaset.iter
   (fun m ->
     if Evd.meta_defined evd m then () else
      raise (Logic.RefinerError (Logic.UnresolvedBindings [Evd.meta_name evd m])))
 in
  List.iter
   (fun (_,binding) ->
     match binding with
        Evd.Cltyp (_,{Evd.rebus=rebus; Evd.freemetas=freemetas}) ->
         check_freemetas_is_empty rebus freemetas
      | Evd.Clval (_,({Evd.rebus=rebus1; Evd.freemetas=freemetas1},_),
                 {Evd.rebus=rebus2; Evd.freemetas=freemetas2}) ->
         check_freemetas_is_empty rebus1 freemetas1 ;
         check_freemetas_is_empty rebus2 freemetas2
   ) metas

(* For a correct meta-aware "rewrite in", we split unification 
   apart from the actual rewriting (Pierre L, 05/04/06) *)
   
(* [unification_rewrite] searchs a match for [c1] in [but] and then 
   returns the modified objects (in particular [c1] and [c2]) *)  

let rewrite_unif_flags = {
  modulo_conv_on_closed_terms = None;
  use_metas_eagerly = true;
  modulo_delta = empty_transparent_state;
}

let rewrite2_unif_flags = {
  modulo_conv_on_closed_terms = Some full_transparent_state;
  use_metas_eagerly = true;
  modulo_delta = empty_transparent_state;
}

let unification_rewrite c1 c2 cl but gl = 
  let (env',c1) =
    try
      (* ~flags:(false,true) to allow to mark occurences that must not be
         rewritten simply by replacing them with let-defined definitions
         in the context *)
      w_unify_to_subterm ~flags:rewrite_unif_flags (pf_env gl) (c1,but) cl.evd
    with
	Pretype_errors.PretypeError _ ->
	  (* ~flags:(true,true) to make Ring work (since it really
             exploits conversion) *)
	  w_unify_to_subterm ~flags:rewrite2_unif_flags
	    (pf_env gl) (c1,but) cl.evd
  in
  let cl' = {cl with evd = env' } in
  let c2 = Clenv.clenv_nf_meta cl' c2 in
  check_evar_map_of_evars_defs env' ;
  env',Clenv.clenv_value cl', c1, c2

(* no unification is performed in this function. [sigma] is the 
 substitution obtained from an earlier unification. *)

let relation_rewrite_no_unif c1 c2 hyp ~new_goals sigma gl = 
  let but = pf_concl gl in 
  try
   let input_relation =
    relation_class_that_matches_a_constr "Setoid_rewrite"
     new_goals (Typing.mtype_of (pf_env gl) sigma (snd hyp)) in
   let output_relation,output_direction,marked_but =
    mark_occur gl ~new_goals c1 but input_relation (fst hyp) in
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
        (mkApp (th',[|mkCast (Evarutil.mk_new_meta(), DEFAULTcast, new_but)|]))
	gl in
   let if_output_relation_is_if gl =
    let th =
     apply_coq_setoid_rewrite input_relation output_relation c1 c2 hyp
      cic_output_direction marked_but
    in
     let new_but = Termops.replace_term c1 c2 but in
      Tactics.refine
       (mkApp (th, [|mkCast (Evarutil.mk_new_meta(), DEFAULTcast, new_but)|]))
       gl in
   if output_relation = (Lazy.force coq_iff_relation) then
     if_output_relation_is_iff gl
   else
     if_output_relation_is_if gl
  with
    Optimize ->
      !general_rewrite (fst hyp = Left2Right) all_occurrences (snd hyp) gl

let relation_rewrite c1 c2 (input_direction,cl) ~new_goals gl =
 let (sigma,cl,c1,c2) = unification_rewrite c1 c2 cl (pf_concl gl) gl in 
 relation_rewrite_no_unif c1 c2 (input_direction,cl) ~new_goals sigma gl 

let analyse_hypothesis gl c =
 let ctype = pf_type_of gl c in
 let eqclause  = Clenv.make_clenv_binding gl (c,ctype) Rawterm.NoBindings in
 let (equiv, args) = decompose_app (Clenv.clenv_type eqclause) in
 let rec split_last_two = function
   | [c1;c2] -> [],(c1, c2)
   | x::y::z ->
      let l,res = split_last_two (y::z) in x::l, res
   | _ -> error "The term provided is not an equivalence" in
 let others,(c1,c2) = split_last_two args in
  eqclause,mkApp (equiv, Array.of_list others),c1,c2

let general_s_rewrite lft2rgt occs c ~new_goals gl =
  if occs <> all_occurrences then
    warning "Rewriting at selected occurrences not supported";
  let eqclause,_,c1,c2 = analyse_hypothesis gl c in
  if lft2rgt then 
    relation_rewrite c1 c2 (Left2Right,eqclause) ~new_goals gl
  else 
    relation_rewrite c2 c1 (Right2Left,eqclause) ~new_goals gl

let relation_rewrite_in id c1 c2 (direction,eqclause) ~new_goals gl = 
 let hyp = pf_type_of gl (mkVar id) in
 (* first, we find a match for c1 in the hyp *)
 let (sigma,cl,c1,c2) = unification_rewrite c1 c2 eqclause hyp gl in 
 (* since we will actually rewrite in the opposite direction, we also need
    to replace every occurrence of c2 (resp. c1) in hyp with something that
    is convertible but not syntactically equal. To this aim we introduce a
    let-in and then we will use the intro tactic to get rid of it.
    Quite tricky to do properly since c1 can occur in c2 or vice-versa ! *)
 let mangled_new_hyp = 
   let hyp = lift 2 hyp in 
   (* first, we backup every occurences of c1 in newly allocated (Rel 1) *)
   let hyp = Termops.replace_term (lift 2 c1) (mkRel 1) hyp in 
   (* then, we factorize every occurences of c2 into (Rel 2) *)
   let hyp = Termops.replace_term (lift 2 c2) (mkRel 2) hyp in 
   (* Now we substitute (Rel 1) (i.e. c1) for c2 *)
   let hyp = subst1 (lift 1 c2) hyp in 
   (* Since subst1 has killed Rel 1 and decreased the other Rels, 
      Rel 1 is now coding for c2, we can build the let-in factorizing c2 *)
   mkLetIn (Anonymous,c2,pf_type_of gl c2,hyp) 
 in 
 let new_hyp = Termops.replace_term c1 c2 hyp in 
 let oppdir = opposite_direction direction in 
 cut_replacing id new_hyp
   (tclTHENLAST
      (tclTHEN (change_in_concl None mangled_new_hyp)
         (tclTHEN intro
            (relation_rewrite_no_unif c2 c1 (oppdir,cl) ~new_goals sigma))))
   gl

let general_s_rewrite_in id lft2rgt occs c ~new_goals gl =
  if occs <> all_occurrences then
    warning "Rewriting at selected occurrences not supported";
  let eqclause,_,c1,c2 = analyse_hypothesis gl c in
  if lft2rgt then 
    relation_rewrite_in id c1 c2 (Left2Right,eqclause) ~new_goals gl
  else 
    relation_rewrite_in id c2 c1 (Right2Left,eqclause) ~new_goals gl


(* 
   [general_setoid_replace rewrite_tac try_prove_eq_tac_opt relation c1 c2 ~new_goals ]
   common part of [setoid_replace] and [setoid_replace_in]  (distinction is done using rewrite_tac). 

   Algorith sketch: 
   1- find the (setoid) relation [rel] between [c1] and [c2] using [relation]
   2- assert [H:rel c2 c1] 
   3- replace [c1] with [c2] using [rewrite_tac] (should be [general_s_rewrite] if we want to replace in the 
      goal, and [general_s_rewrite_in id] if we want to replace in the hypothesis [id]). Possibly generate
      new_goals if asked (cf general_s_rewrite)
   4- if [try_prove_eq_tac_opt] is [Some tac] try to complete [rel c2 c1] using tac and do nothing if 
      [try_prove_eq_tac_opt] is [None]
*)
let general_setoid_replace rewrite_tac try_prove_eq_tac_opt relation c1 c2 ~new_goals gl =
  let try_prove_eq_tac = 
    match try_prove_eq_tac_opt with 
      | None -> Tacticals.tclIDTAC
      | Some tac ->  Tacticals.tclTRY (Tacticals.tclCOMPLETE tac )
  in 
  try
    let carrier,args = decompose_app (pf_type_of gl c1) in
    let relation =
      match relation with
	  Some rel ->
	    (try
		match find_relation_class rel with
		    Relation sa -> if not (eq_constr carrier sa.rel_a) then 		    
			errorlabstrm "Setoid_rewrite"
			  (str "the carrier of " ++ pr_lconstr rel ++ 
			      str " does not match the type of " ++ pr_lconstr c1);
		      sa
		  | Leibniz _ -> raise Optimize
              with
		  Not_found ->
		    errorlabstrm "Setoid_rewrite"
		      (pr_lconstr rel ++ str " is not a registered relation."))
	| None ->
	    match default_relation_for_carrier (pf_type_of gl c1) with
		Relation sa -> sa
              | Leibniz _ -> raise Optimize
    in
    let eq_left_to_right = mkApp (relation.rel_aeq, Array.of_list (List.append args [ c1 ; c2 ])) in
    let eq_right_to_left = mkApp (relation.rel_aeq, Array.of_list (List.append args [ c2 ; c1 ])) in
    let replace dir eq =
      tclTHENS (assert_tac false Anonymous eq)
	[onLastHyp (fun id ->
          tclTHEN
            (rewrite_tac dir all_occurrences (mkVar id) ~new_goals)
            (clear [id]));
	 try_prove_eq_tac]
    in
      tclORELSE
	(replace true eq_left_to_right) (replace false eq_right_to_left) gl
  with
      Optimize -> (* (!replace tac_opt c1 c2) gl *)
	let eq =  mkApp (Lazy.force  coq_eq, [| pf_type_of gl c1;c2 ; c1 |]) in 
	  tclTHENS (assert_tac false Anonymous eq)
	    [onLastHyp (fun id ->
	      tclTHEN
		(rewrite_tac false all_occurrences (mkVar id) ~new_goals)
		(clear [id]));
	     try_prove_eq_tac] gl
      
let setoid_replace = general_setoid_replace general_s_rewrite
let setoid_replace_in  tac_opt id relation c1 c2 ~new_goals gl = 
  general_setoid_replace (general_s_rewrite_in id)  tac_opt relation c1 c2 ~new_goals gl
 
(* [setoid_]{reflexivity,symmetry,transitivity} tactics *)

let setoid_reflexivity gl =
 try
  let relation_class =
   relation_class_that_matches_a_constr "Setoid_reflexivity"
    [] (pf_concl gl) in
  match relation_class with
     Leibniz _ -> assert false (* since [] is empty *)
   | Relation rel ->
      match rel.rel_refl with
         None ->
          errorlabstrm "Setoid_reflexivity"
           (str "The relation " ++ prrelation rel ++ str " is not reflexive.")
       | Some refl -> apply refl gl
 with
  Optimize -> reflexivity_red true gl

let setoid_symmetry gl =
 try
  let relation_class =
   relation_class_that_matches_a_constr "Setoid_symmetry"
    [] (pf_concl gl) in
  match relation_class with
     Leibniz _ -> assert false (* since [] is empty *)
   | Relation rel ->
      match rel.rel_sym with
         None ->
          errorlabstrm "Setoid_symmetry"
           (str "The relation " ++ prrelation rel ++ str " is not symmetric.")
       | Some sym -> apply sym gl
 with
  Optimize -> symmetry_red true gl

let setoid_symmetry_in id gl =
  let ctype = pf_type_of gl (mkVar id) in
  let binders,concl = Sign.decompose_prod_assum ctype in
  let (equiv, args) = decompose_app concl in
  let rec split_last_two = function
    | [c1;c2] -> [],(c1, c2)
    | x::y::z -> let l,res = split_last_two (y::z) in x::l, res
    | _ -> error "The term provided is not an equivalence" 
  in
  let others,(c1,c2) = split_last_two args in
  let he,c1,c2 =  mkApp (equiv, Array.of_list others),c1,c2 in
  let new_hyp' =  mkApp (he, [| c2 ; c1 |]) in
  let new_hyp = it_mkProd_or_LetIn new_hyp'  binders in
  tclTHENS (cut new_hyp)
    [ intro_replacing id;
      tclTHENLIST [ intros; setoid_symmetry; apply (mkVar id); assumption ] ]
    gl

let setoid_transitivity c gl =
 try
  let relation_class =
   relation_class_that_matches_a_constr "Setoid_transitivity"
    [] (pf_concl gl) in
  match relation_class with
     Leibniz _ -> assert false (* since [] is empty *)
   | Relation rel ->
      let ctyp = pf_type_of gl c in
      let rel' = unify_relation_carrier_with_type (pf_env gl) rel ctyp in
       match rel'.rel_trans with
          None ->
           errorlabstrm "Setoid_transitivity"
            (str "The relation " ++ prrelation rel ++ str " is not transitive.")
        | Some trans ->
           let transty = nf_betaiota (pf_type_of gl trans) in
           let argsrev, _ =
            Reductionops.decomp_n_prod (pf_env gl) Evd.empty 2 transty in
           let binder =
            match List.rev argsrev with
               _::(Name n2,None,_)::_ -> Rawterm.NamedHyp n2
             | _ -> assert false
           in
            apply_with_bindings
             (trans, Rawterm.ExplicitBindings [ dummy_loc, binder, c ]) gl
 with
  Optimize -> transitivity_red true c gl
;;

