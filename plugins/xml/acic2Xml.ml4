(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *   The HELM Project         /   The EU MoWGLI Project       *)
(*         *   University of Bologna                                    *)
(************************************************************************)
(*          This file is distributed under the terms of the             *)
(*           GNU Lesser General Public License Version 2.1              *)
(*                                                                      *)
(*                 Copyright (C) 2000-2004, HELM Team.                  *)
(*                       http://helm.cs.unibo.it                        *)
(************************************************************************)

(*CSC codice cut & paste da cicPp e xmlcommand *)

exception ImpossiblePossible;;
exception NotImplemented;;
let dtdname = "http://mowgli.cs.unibo.it/dtd/cic.dtd";;
let typesdtdname = "http://mowgli.cs.unibo.it/dtd/cictypes.dtd";;

let rec find_last_id =
 function
    [] -> Util.anomaly "find_last_id: empty list"
  | [id,_,_] -> id
  | _::tl -> find_last_id tl
;;

let export_existential = string_of_int

let print_term ids_to_inner_sorts =
 let rec aux =
  let module A = Acic in
  let module N = Names in
  let module X = Xml in
    function
       A.ARel (id,n,idref,b) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_empty "REL"
          ["value",(string_of_int n) ; "binder",(N.string_of_id b) ;
           "id",id ; "idref",idref; "sort",sort]
     | A.AVar (id,uri) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_empty "VAR" ["uri", uri ; "id",id ; "sort",sort]
     | A.AEvar (id,n,l) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "META"
	   ["no",(export_existential n) ; "id",id ; "sort",sort]
          (List.fold_left
            (fun i t ->
              [< i ; X.xml_nempty "substitution" [] (aux t) >]
            ) [< >] (List.rev l))
     | A.ASort (id,s) ->
        let string_of_sort =
         match Term.family_of_sort s with
            Term.InProp -> "Prop"
          | Term.InSet  -> "Set"
          | Term.InType -> "Type"
        in
         X.xml_empty "SORT" ["value",string_of_sort ; "id",id]
     | A.AProds (prods,t) ->
        let last_id = find_last_id prods in
        let sort = Hashtbl.find ids_to_inner_sorts last_id in
         X.xml_nempty "PROD" ["type",sort]
          [< List.fold_left
              (fun i (id,binder,s) ->
                let sort =
                 Hashtbl.find ids_to_inner_sorts (Cic2acic.source_id_of_id id)
                in
                 let attrs =
                  ("id",id)::("type",sort)::
                  match binder with
                     Names.Anonymous -> []
                   | Names.Name b -> ["binder",Names.string_of_id b]
                 in
                  [< X.xml_nempty "decl" attrs (aux s) ; i >]
              ) [< >] prods ;
             X.xml_nempty "target" [] (aux t)
          >]
     | A.ACast (id,v,t) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "CAST" ["id",id ; "sort",sort]
          [< X.xml_nempty "term" [] (aux v) ;
             X.xml_nempty "type" [] (aux t)
          >]
     | A.ALambdas (lambdas,t) ->
        let last_id = find_last_id lambdas in
        let sort = Hashtbl.find ids_to_inner_sorts last_id in
         X.xml_nempty "LAMBDA" ["sort",sort]
          [< List.fold_left
              (fun i (id,binder,s) ->
                let sort =
                 Hashtbl.find ids_to_inner_sorts (Cic2acic.source_id_of_id id)
                in
                 let attrs =
                  ("id",id)::("type",sort)::
                  match binder with
                     Names.Anonymous -> []
                   | Names.Name b -> ["binder",Names.string_of_id b]
                 in
                  [< X.xml_nempty "decl" attrs (aux s) ; i >]
              ) [< >] lambdas ;
             X.xml_nempty "target" [] (aux t)
          >]
     | A.ALetIns (letins,t) ->
        let last_id = find_last_id letins in
        let sort = Hashtbl.find ids_to_inner_sorts last_id in
         X.xml_nempty "LETIN" ["sort",sort]
          [< List.fold_left
              (fun i (id,binder,s) ->
                let sort =
                 Hashtbl.find ids_to_inner_sorts (Cic2acic.source_id_of_id id)
                in
                 let attrs =
                  ("id",id)::("sort",sort)::
                  match binder with
                     Names.Anonymous -> assert false
                   | Names.Name b -> ["binder",Names.string_of_id b]
                 in
                  [< X.xml_nempty "def" attrs (aux s) ; i >]
              ) [< >] letins ;
             X.xml_nempty "target" [] (aux t)
          >]
     | A.AApp (id,li) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "APPLY" ["id",id ; "sort",sort]
          [< (List.fold_left (fun i x -> [< i ; (aux x) >]) [<>] li)
          >]
     | A.AConst (id,subst,uri) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        let attrs = ["uri", uri ; "id",id ; "sort",sort] in
         aux_subst (X.xml_empty "CONST" attrs) subst
     | A.AInd (id,subst,uri,i) ->
        let attrs = ["uri", uri ; "noType",(string_of_int i) ; "id",id] in
         aux_subst (X.xml_empty "MUTIND" attrs) subst
     | A.AConstruct (id,subst,uri,i,j) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
        let attrs =
         ["uri", uri ;
          "noType",(string_of_int i) ; "noConstr",(string_of_int j) ;
          "id",id ; "sort",sort]
        in
         aux_subst (X.xml_empty "MUTCONSTRUCT" attrs) subst
     | A.ACase (id,uri,typeno,ty,te,patterns) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "MUTCASE"
          ["uriType", uri ;
           "noType", (string_of_int typeno) ;
           "id", id ; "sort",sort]
          [< X.xml_nempty "patternsType" [] [< (aux ty) >] ;
             X.xml_nempty "inductiveTerm" [] [< (aux te) >] ;
             List.fold_left
              (fun i x -> [< i ; X.xml_nempty "pattern" [] [< aux x >] >])
              [<>] patterns
          >]
     | A.AFix (id, no, funs) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "FIX"
          ["noFun", (string_of_int no) ; "id",id ; "sort",sort]
          [< List.fold_left
              (fun i (id,fi,ai,ti,bi) ->
                [< i ;
                   X.xml_nempty "FixFunction"
                    ["id",id ; "name", (Names.string_of_id fi) ;
                     "recIndex", (string_of_int ai)]
                    [< X.xml_nempty "type" [] [< aux ti >] ;
                       X.xml_nempty "body" [] [< aux bi >]
                    >]
                >]
              ) [<>] funs
          >]
     | A.ACoFix (id,no,funs) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "COFIX"
          ["noFun", (string_of_int no) ; "id",id ; "sort",sort]
          [< List.fold_left
              (fun i (id,fi,ti,bi) ->
                [< i ;
                   X.xml_nempty "CofixFunction"
                    ["id",id ; "name", Names.string_of_id fi]
                    [< X.xml_nempty "type" [] [< aux ti >] ;
                       X.xml_nempty "body" [] [< aux bi >]
                    >]
                >]
              ) [<>] funs
          >]
 and aux_subst target (id,subst) =
  if subst = [] then
   target
  else
   Xml.xml_nempty "instantiate"
    (match id with None -> [] | Some id -> ["id",id])
    [< target ;
       List.fold_left
        (fun i (uri,arg) ->
          [< i ; Xml.xml_nempty "arg" ["relUri", uri] (aux arg) >]
        ) [<>] subst
    >]
 in
  aux
;;

let param_attribute_of_params params =
 List.fold_right
  (fun (path,l) i ->
    List.fold_right
     (fun x i ->path ^ "/" ^ x ^ ".var" ^ match i with "" -> "" | i' -> " " ^ i'
     ) l "" ^ match i with "" -> "" | i' -> " " ^ i'
  ) params ""
;;

let print_object uri ids_to_inner_sorts =
 let rec aux =
  let module A = Acic in
  let module X = Xml in
    function
       A.ACurrentProof (id,n,conjectures,bo,ty) ->
        let xml_for_current_proof_body =
(*CSC: Should the CurrentProof also have the list of variables it depends on? *)
(*CSC: I think so. Not implemented yet.                                       *)
         X.xml_nempty "CurrentProof" ["of",uri ; "id", id]
          [< List.fold_left
              (fun i (cid,n,canonical_context,t) ->
                [< i ;
                   X.xml_nempty "Conjecture"
                    ["id", cid ; "no",export_existential n]
                    [< List.fold_left
                        (fun i (hid,t) ->
                          [< (match t with
                                n,A.Decl t ->
                                 X.xml_nempty "Decl"
                                  ["id",hid;"name",Names.string_of_id n]
                                  (print_term ids_to_inner_sorts t)
                              | n,A.Def (t,_) ->
                                 X.xml_nempty "Def"
                                  ["id",hid;"name",Names.string_of_id n]
                                  (print_term ids_to_inner_sorts t)
                             ) ;
                             i
                          >]
                        ) [< >] canonical_context ;
                       X.xml_nempty "Goal" []
                        (print_term ids_to_inner_sorts t)
                    >]
                >])
              [<>] (List.rev conjectures) ;
             X.xml_nempty "body" [] (print_term ids_to_inner_sorts bo) >]
        in
        let xml_for_current_proof_type =
         X.xml_nempty "ConstantType" ["name",n ; "id", id]
          (print_term ids_to_inner_sorts ty)
        in
        let xmlbo =
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE CurrentProof SYSTEM \""^dtdname ^"\">\n");
            xml_for_current_proof_body
         >] in
        let xmlty =
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata
             ("<!DOCTYPE ConstantType SYSTEM \"" ^ dtdname ^ "\">\n");
            xml_for_current_proof_type
         >]
        in
         xmlty, Some xmlbo
     | A.AConstant (id,n,bo,ty,params) ->
        let params' = param_attribute_of_params params in
        let xmlbo =
         match bo with
            None -> None
          | Some bo ->
             Some
              [< X.xml_cdata
                  "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
                 X.xml_cdata
                  ("<!DOCTYPE ConstantBody SYSTEM \"" ^ dtdname ^ "\">\n") ;
                 X.xml_nempty "ConstantBody"
                  ["for",uri ; "params",params' ; "id", id]
                  [< print_term ids_to_inner_sorts bo >]
              >]
        in
        let xmlty =
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE ConstantType SYSTEM \""^dtdname ^"\">\n");
             X.xml_nempty "ConstantType"
              ["name",n ; "params",params' ; "id", id]
              [< print_term ids_to_inner_sorts ty >]
         >]
        in
         xmlty, xmlbo
     | A.AVariable (id,n,bo,ty,params) ->
        let params' = param_attribute_of_params params in
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE Variable SYSTEM \"" ^ dtdname ^ "\">\n") ;
            X.xml_nempty "Variable" ["name",n ; "params",params' ; "id", id]
             [< (match bo with
                    None -> [<>]
                  | Some bo ->
                     X.xml_nempty "body" []
                      (print_term ids_to_inner_sorts bo)
                ) ;
                X.xml_nempty "type" [] (print_term ids_to_inner_sorts ty)
             >]
         >], None
     | A.AInductiveDefinition (id,tys,params,nparams) ->
        let params' = param_attribute_of_params params in
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE InductiveDefinition SYSTEM \"" ^
             dtdname ^ "\">\n") ;
            X.xml_nempty "InductiveDefinition"
             ["noParams",string_of_int nparams ;
              "id",id ;
              "params",params']
             [< (List.fold_left
                  (fun i (id,typename,finite,arity,cons) ->
                    [< i ;
                       X.xml_nempty "InductiveType"
                        ["id",id ; "name",Names.string_of_id typename ;
                         "inductive",(string_of_bool finite)
                        ]
                        [< X.xml_nempty "arity" []
                            (print_term ids_to_inner_sorts arity) ;
                           (List.fold_left
                            (fun i (name,lc) ->
                              [< i ;
                                 X.xml_nempty "Constructor"
                                  ["name",Names.string_of_id name]
                                  (print_term ids_to_inner_sorts lc)
                              >]) [<>] cons
                           )
                        >]
                    >]
                  ) [< >] tys
                )
             >]
         >], None
 in
  aux
;;

let print_inner_types curi ids_to_inner_sorts ids_to_inner_types =
 let module C2A = Cic2acic in
 let module X = Xml in
  [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
     X.xml_cdata ("<!DOCTYPE InnerTypes SYSTEM \"" ^ typesdtdname ^"\">\n");
      X.xml_nempty "InnerTypes" ["of",curi]
       (Hashtbl.fold
         (fun id {C2A.annsynthesized = synty ; C2A.annexpected = expty} x ->
           [< x ;
              X.xml_nempty "TYPE" ["of",id]
               [< X.xml_nempty "synthesized" []
                   (print_term ids_to_inner_sorts synty) ;
                  match expty with
                     None -> [<>]
                   | Some expty' ->
                      X.xml_nempty "expected" []
                       (print_term ids_to_inner_sorts expty')
               >]
           >]
         ) ids_to_inner_types [<>]
       )
  >]
;;
