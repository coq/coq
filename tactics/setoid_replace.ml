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

type relation =
   { rel_a: constr ;
     rel_aeq: constr;
     rel_refl: constr option;
     rel_sym: constr option
   }

type 'a relation_class =
   Relation of 'a     (* the rel_aeq of the relation
                           or the relation*)
 | Leibniz of constr  (* the carrier *)

type 'a morphism =
    { args : 'a relation_class list;
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
let coq_Left2Right = lazy(constant ["Setoid"] "Left2Right")
let coq_MSNone = lazy(constant ["Setoid"] "MSNone")
let coq_MSCovariant = lazy(constant ["Setoid"] "MSCovariant")

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

let prmorphism k m =
  prterm k ++ str ": " ++
  prlist_with_sep (fun () -> str " -> ") prrelation_class m.args ++
  str " -> " ++ prrelation_class m.output


(* A function that gives back the only relation_class on a given carrier *)
(*CSC: this implementation is really inefficient. I should define a new
  map to make it efficient. However, is this really worth of? *)
let default_relation_for_carrier a =
 let rng = Gmap.rng !relation_table in
 match List.filter (fun {rel_a=rel_a} -> rel_a = a) rng with
    [] -> Leibniz a
  | relation::tl ->
     if tl <> [] then
      msg_warning
       (*CSC: still "setoid" in the error message *)
       (str "There are several setoids whose carrier is " ++ prterm a ++
         str ". The setoid " ++ prrelation relation ++
         str " is randomly chosen.") ;
     Relation relation

let relation_morphism_of_constr_morphism =
 let relation_relation_class_of_constr_relation_class =
  function
     Leibniz t -> Leibniz t
   | Relation aeq ->
      Relation (try relation_table_find aeq with Not_found -> assert false)
 in
  function mor ->
   let args' = List.map relation_relation_class_of_constr_relation_class mor.args in
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
        msg_warning
         (str "The setoid " ++ prrelation th' ++ str " is redeclared. " ++
          str "The new declaration" ++
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
    msg_warning
     (str "The morphism " ++ prmorphism m old_morph ++ str " is redeclared. " ++
      str "The new declaration whose compatibility is granted by " ++
       prterm c.lem ++ str " replaces the old declaration whose" ++
       str " compatibility was granted by " ++
       prterm old_morph.lem ++ str ".")
  with
   Not_found -> morphism_table := Gmap.add m (c::old) !morphism_table

let subst_morph subst morph = 
  let lem' = subst_mps subst morph.lem in
  let args' = list_smartmap (subst_mps_in_relation_class subst) morph.args in
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

let check_refl env a aeq refl =
 if
  not
   (is_conv env Evd.empty (Typing.type_of env Evd.empty refl)
     (mkApp ((Lazy.force coq_reflexive), [| a; aeq |])))
 then
  errorlabstrm "Add Relation Class"
   (str "Not a valid proof of reflexivity")
 else ()

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

let cic_argument_class_of_argument_class =
 cic_relation_class_of_X_relation_class coq_variance coq_Covariant

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

let new_morphism m signature id hook =
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
           List.map default_relation_for_carrier args_ty,
           default_relation_for_carrier output
        | Some (args,output) ->
           let relation_table_find t =
            try Relation (relation_table_find t)
            with Not_found ->
             errorlabstrm "Add Morphism"
              (str "Not a valid signature: " ++ prterm t ++
               str " is not a registered relation")
           in
            List.map relation_table_find args,
            relation_table_find output
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
       Options.if_verbose msg (Pfedit.pr_open_subgoals ());
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
   List.map constr_relation_class_of_relation_relation_class args in
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

let new_named_morphism id m sign =
 let sign =
  match sign with
     None -> None
   | Some (args,out) ->
      Some (List.map constr_of args, constr_of out)
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
     Relation
      {rel_a = a ; rel_aeq = aeq ; rel_refl = Some refl ; rel_sym = Some sym}
    in
     add_morphism None mor_name
      (aeq,[aeq_rel;aeq_rel],Lazy.force coq_prop_relation)
   end
  else
   errorlabstrm "Add Setoid" (str "Not a valid setoid theory")


(****************************** The tactic itself *******************************)

type constr_with_marks =
  | MApp of constr * morphism_class * constr_with_marks array 
  | ToReplace
  | ToKeep of constr

let is_to_replace = function
 | ToKeep _ -> false
 | ToReplace -> true
 | MApp _ -> true

let get_mark a = 
  Array.fold_left (||) false (Array.map is_to_replace a)

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

let relation_of_hypothesis_and_term_to_rewrite gl (_,h) t =
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
   relation_table_find aeq
  with Not_found ->
   (*CSC: still "setoid" in the error message *)
   errorlabstrm "Setoid_rewrite"
    (prterm aeq ++ str " is not a setoid equality.")

let mark_occur t in_c =
 let rec aux in_c =
  if eq_constr t in_c then
    ToReplace
  else
    match kind_of_term in_c with
      | App (c,al) -> 
          let a = Array.map aux al in
           if not (get_mark a) then ToKeep in_c
           else
            let mor =
              try
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
                     Some
                      (ACMorphism
                       (relation_morphism_of_constr_morphism morphism))
                end
               with Not_found -> None
            in
             (match mor with
                 Some mor -> MApp (c,mor,a)
               | None ->
                 (* the tactic works only if the function type is
                    made of non-dependent products only. However, here we
                    can cheat a bit by partially istantiating c to match
                    the requirement when the arguments to be replaced are
                    bound by non-dependent products only. *)
                 let env = Global.env() in
                 let typeofc = (Typing.type_of env Evd.empty c) in
                 let typ = nf_betaiota typeofc in
                 let rec find_non_dependent_function env c c_args_rev typ
                          f_args_rev a_rev=
                  function
                     [] ->
                      let mor =
                       ACFunction {f_args=List.rev f_args_rev ; f_output=typ} in
                      let func = beta_expand c c_args_rev in
                       MApp (func,mor,Array.of_list (List.rev a_rev))
                   | (he::tl) as a->
                      let typnf = Reduction.whd_betadeltaiota env typ in
                       match kind_of_term typnf with
                         Cast (typ,_) ->
                          find_non_dependent_function env c c_args_rev typ
                           f_args_rev a_rev a
                       | Prod (name,s,t) ->
                          let env' = push_rel (name,None,s) env in
                          begin
                           match noccurn 1 t, he with
                              _, ToKeep arg ->
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
                               (*CSC: this limitation is due to the reflexive
                                 implementation and it is hard to lift *)
                               errorlabstrm "Setoid_replace"
                                (str "Cannot rewrite in the argument of a " ++
                                 str "dependent product. If you need this " ++
                                 str "feature, please report to the authors.")
                          end
                       | _ -> assert false
                 in
                  find_non_dependent_function env c [] typ [] []
                   (Array.to_list a))
      | Prod (_, c1, c2) -> 
          if (dependent (mkRel 1) c2)
          then ToKeep in_c
          else 
            let c1m = aux c1 in
            let c2m = aux c2 in
              if ((is_to_replace c1m)||(is_to_replace c2m))
              then
               (* this can be optimized since c1 and c2 will be *)
               (* processed again                               *)
               aux (mkApp ((Lazy.force coq_impl), [| c1 ; c2 |]))
              else ToKeep in_c
      | _ -> ToKeep in_c
 in aux in_c

let cic_morphism_context_list_of_list hole_relation =
 let check =
  function
     Relation {rel_sym=None} ->
      mkApp ((Lazy.force coq_MSCovariant), [| Lazy.force coq_Left2Right |])
   | Relation {rel_sym=Some _}
   | Leibniz _ ->
      mkApp ((Lazy.force coq_MSNone),
       [| Lazy.force coq_Left2Right ; Lazy.force coq_Left2Right |]) in
 let rec aux =
  function
     [] -> assert false
   | [(outrel,out),value] ->
      mkApp ((Lazy.force coq_singl), [| Lazy.force coq_Argument_Class ; out |]),
      mkApp ((Lazy.force coq_fcl_singl),
       [| hole_relation; Lazy.force coq_Left2Right ; out ;
          Lazy.force coq_Left2Right ; Lazy.force coq_Left2Right ;
          check outrel ; value |])
   | ((outrel,out),value)::tl ->
      let outtl, valuetl = aux tl in
       mkApp ((Lazy.force coq_cons),
        [| Lazy.force coq_Argument_Class ; out ; outtl |]),
       mkApp ((Lazy.force coq_fcl_cons),
        [| hole_relation ; Lazy.force coq_Left2Right ; out ; outtl ;
           Lazy.force coq_Left2Right ; Lazy.force coq_Left2Right ;
           check outrel ; value ; valuetl |])
 in aux

let rec cic_type_nelist_of_list =
 function
    [] -> assert false
  | [value] ->
      mkApp ((Lazy.force coq_singl), [| mkType (Termops.new_univ ()) ; value |])
  | value::tl ->
     mkApp ((Lazy.force coq_cons),
      [| mkType (Termops.new_univ ()); value; cic_type_nelist_of_list tl |])

let syntactic_but_representation_of_marked_but hole_relation =
 let rec aux out (rel_out,precise_out,is_reflexive) =
  function
     MApp (f, m, args) ->
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
            mt,List.map (fun x -> Leibniz x) f_args in
      let cic_relations =
       List.map
        (fun r ->
          cic_relation_class_of_relation_class r,
          cic_precise_relation_class_of_relation_class r
        ) relations in
      let cic_arguments =
       List.map
        (fun rel -> rel,cic_argument_class_of_argument_class rel) relations in
      let cic_args_relations,argst =
       cic_morphism_context_list_of_list hole_relation
        (List.combine cic_arguments
          (List.map2 (fun (t,precise_t) v -> aux t precise_t v) cic_relations
           (Array.to_list args)))
      in
       mkApp ((Lazy.force coq_App),
        [|hole_relation ; Lazy.force coq_Left2Right ;
          cic_args_relations ; out ; Lazy.force coq_Left2Right ;
          morphism_theory ; argst|])
   | ToReplace ->
      mkApp ((Lazy.force coq_ToReplace),
       [| hole_relation ; Lazy.force coq_Left2Right |])
   | ToKeep c ->
       if is_reflexive then
        mkApp ((Lazy.force coq_ToKeep),
         [| hole_relation ; Lazy.force coq_Left2Right ; precise_out ;
            Lazy.force coq_Left2Right ; c |])
       else
        let c_is_proper =
         let typ = mkApp (rel_out, [| c ; c |]) in
          mkCast (mkMeta (Clenv.new_meta ()),typ)
        in
         mkApp ((Lazy.force coq_ProperElementToKeep),
          [| hole_relation ; Lazy.force coq_Left2Right; precise_out ;
             Lazy.force coq_Left2Right; c ; c_is_proper |])
 in aux

let apply_coq_setoid_rewrite hole_relation c1 c2 (lft2rgt,h) m =
 let {rel_aeq=hole_equality; rel_sym=hole_symmetry} = hole_relation in
 let hole_relation =
  cic_relation_class_of_relation_class (Relation hole_relation) in
 let prop_relation =
  cic_relation_class_of_relation_class (Lazy.force coq_prop_relation) in
 let precise_prop_relation =
  cic_precise_relation_class_of_relation_class
   (Lazy.force coq_prop_relation) in
 let hyp =
  if lft2rgt then h else
   match hole_symmetry with
      Some sym ->
       mkApp (sym, [| c2 ; c1 ; h |])
    | None ->
       errorlabstrm "Setoid_rewrite"
        (str "Rewriting from right to left not permitted since the " ++
         str "relation " ++ prterm hole_equality ++ str " is not known " ++
         str "to be symmetric. Either declare it as a symmetric " ++
         str "relation or use setoid_replace or (setoid_)rewrite from " ++
         str "left to right only.")
 in
  mkApp ((Lazy.force coq_setoid_rewrite),
   [| hole_relation ; Lazy.force coq_Left2Right ; prop_relation ;
      Lazy.force coq_Left2Right ; c1 ; c2 ;
      syntactic_but_representation_of_marked_but hole_relation
       prop_relation precise_prop_relation m ; hyp |])

let relation_rewrite c1 c2 (lft2rgt,cl) gl =
 let but = pf_concl gl in
 let (hyp,c1,c2) =
   let cl' =
     Clenv.clenv_wtactic
       (fun evd-> fst (Unification.w_unify_to_subterm (pf_env gl) (c1,but) evd))
       cl in
   let c1 = Clenv.clenv_instance_term cl' c1 in
   let c2 = Clenv.clenv_instance_term cl' c2 in
   (lft2rgt,Clenv.clenv_instance_template cl'), c1, c2
 in
  let input_relation = relation_of_hypothesis_and_term_to_rewrite gl hyp c1 in
  let marked_but = mark_occur c1 but in
  let th = apply_coq_setoid_rewrite input_relation c1 c2 hyp marked_but in
   let hyp1 = Termops.replace_term c1 c2 but in
   let hyp2 = but in
   let impl1 = mkProd (Anonymous, hyp2, lift 1 hyp1) in
   let impl2 = mkProd (Anonymous, hyp1, lift 1 hyp2) in
    let th' = mkApp ((Lazy.force coq_proj2), [|impl1; impl2; th|]) in
     Tactics.refine
      (mkApp (th', [| mkCast (mkMeta (Clenv.new_meta()), hyp1) |])) gl

let general_s_rewrite lft2rgt c gl =
 let ctype = pf_type_of gl c in
 let eqclause  = Clenv.make_clenv_binding gl (c,ctype) Rawterm.NoBindings in
 let (equiv, args) =
  decompose_app (Clenv.clenv_instance_template_type eqclause) in
 let rec get_last_two = function
   | [c1;c2] -> (c1, c2)
   | x::y::z -> get_last_two (y::z)
   | _ -> error "The term provided is not an equivalence" in
 let (c1,c2) = get_last_two args in
   if lft2rgt
   then relation_rewrite c1 c2 (lft2rgt,eqclause) gl
   else relation_rewrite c2 c1 (lft2rgt,eqclause) gl

exception Use_replace

(*CSC: the name should be changed *)
let setoid_replace c1 c2 gl =
 try
  let relation =
   match default_relation_for_carrier (pf_type_of gl c1) with
      Relation sa -> sa
    | Leibniz _ -> raise Use_replace
  in
   let eq = mkApp (relation.rel_aeq, [| c1 ; c2 |]) in
    tclTHENS (assert_tac false Anonymous eq)
      [onLastHyp (fun id ->
        tclTHEN
          (general_s_rewrite true (mkVar id))
          (clear [id]));
       Tacticals.tclIDTAC] gl
 with
  Use_replace -> (!replace c1 c2) gl

let setoid_rewriteLR = general_s_rewrite true

let setoid_rewriteRL = general_s_rewrite false
