(* Copyright (C) 2000, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

(*CSC codice cut & paste da cicPp e xmlcommand *)

exception ImpossiblePossible;;
exception NotImplemented;;
let dtdname = "http://localhost:8081/getdtd?url=cic.dtd";;
let typesdtdname = "http://localhost:8081/getdtd?url=cictypes.dtd";;

(*CSC ottimizzazione: al posto di curi cdepth (vedi codice) *)
let print_term curi ids_to_inner_sorts =
 let rec aux =
  let module A = Acic in
  let module N = Names in
  let module X = Xml in
    function
       A.ARel (id,n,b) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_empty "REL"
          ["value",(string_of_int n) ; "binder",(N.string_of_id b) ;
           "id",id ; "sort",sort]
     | A.AVar (id,uri) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_empty "VAR"
          ["relUri", uri ;
           "id",id ; "sort",sort]
     | A.AEvar (id,n,l) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "META" ["no",(string_of_int n) ; "id",id ; "sort",sort]
          (List.fold_left
            (fun i t ->
              [< i ; X.xml_nempty "substitution" [] (aux t) >]
            ) [< >] l)
     | A.ASort (id,s) ->
        let string_of_sort =
         match Term.family_of_sort s with
            Term.InProp -> "Prop"
          | Term.InSet  -> "Set"
          | Term.InType -> "Type"
        in
         X.xml_empty "SORT" ["value",string_of_sort ; "id",id]
     | A.AProd (id,Names.Anonymous,s,t) ->
        let ty = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "PROD" ["id",id ; "type",ty]
          [< X.xml_nempty "source" [] (aux s) ;
             X.xml_nempty "target" [] (aux t)
          >]
     | A.AProd (xid,Names.Name id,s,t) ->
        let ty = Hashtbl.find ids_to_inner_sorts xid in
         X.xml_nempty "PROD" ["id",xid ; "type",ty]
          [< X.xml_nempty "source" [] (aux s) ;
             X.xml_nempty "target" ["binder",Names.string_of_id id] (aux t)
          >]
     | A.ACast (id,v,t) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "CAST" ["id",id ; "sort",sort]
          [< X.xml_nempty "term" [] (aux v) ;
             X.xml_nempty "type" [] (aux t)
          >]
     | A.ALambda (id,Names.Anonymous,s,t) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "LAMBDA" ["id",id ; "sort",sort]
          [< X.xml_nempty "source" [] (aux s) ;
             X.xml_nempty "target" [] (aux t)
          >]
     | A.ALambda (xid,Names.Name id,s,t) ->
        let sort = Hashtbl.find ids_to_inner_sorts xid in
         X.xml_nempty "LAMBDA" ["id",xid ; "sort",sort]
          [< X.xml_nempty "source" [] (aux s) ;
             X.xml_nempty "target" ["binder",Names.string_of_id id] (aux t)
          >]
     | A.ALetIn (xid,Names.Anonymous,s,t) ->
       assert false
     | A.ALetIn (xid,Names.Name id,s,t) ->
        let sort = Hashtbl.find ids_to_inner_sorts xid in
         X.xml_nempty "LETIN" ["id",xid ; "sort",sort]
          [< X.xml_nempty "term" [] (aux s) ;
             X.xml_nempty "letintarget" ["binder",Names.string_of_id id] (aux t)
          >]
     | A.AApp (id,li) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_nempty "APPLY" ["id",id ; "sort",sort]
          [< (List.fold_left (fun i x -> [< i ; (aux x) >]) [<>] li)
          >]
     | A.AConst (id,uri) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_empty "CONST"
          ["uri", uri ; "id",id ; "sort",sort]
     | A.AInd (id,uri,i) ->
        X.xml_empty "MUTIND"
         ["uri", uri ;
          "noType",(string_of_int i) ;
          "id",id]
     | A.AConstruct (id,uri,i,j) ->
        let sort = Hashtbl.find ids_to_inner_sorts id in
         X.xml_empty "MUTCONSTRUCT"
          ["uri", uri ;
           "noType",(string_of_int i) ; "noConstr",(string_of_int j) ;
           "id",id ; "sort",sort]
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
              (fun i (fi,ai,ti,bi) ->
                [< i ;
                   X.xml_nempty "FixFunction"
                    ["name", (Names.string_of_id fi);
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
              (fun i (fi,ti,bi) ->
                [< i ;
                   X.xml_nempty "CofixFunction" ["name", Names.string_of_id fi]
                    [< X.xml_nempty "type" [] [< aux ti >] ;
                       X.xml_nempty "body" [] [< aux bi >]
                    >]
                >]
              ) [<>] funs
          >]
 in
  aux
;;

let param_attribute_of_params params =
 List.fold_right
  (fun (_,x) i ->
    List.fold_right
     (fun x i ->
       x ^ match i with "" -> "" | i' -> " " ^ i'
     ) x "" ^ match i with "" -> "" | i' -> " " ^ i'
  ) params ""
;;

(*CSC ottimizzazione: al posto di curi cdepth (vedi codice) *)
let print_object curi ids_to_inner_sorts =
 let rec aux =
  let module A = Acic in
  let module X = Xml in
    function
       A.ACurrentProof (id,n,conjectures,bo,ty) ->
        X.xml_nempty "CurrentProof" ["name",n ; "id", id]
         [< List.fold_left
             (fun i (cid,n,canonical_context,t) ->
               [< i ;
                  X.xml_nempty "Conjecture"
                   ["id", cid ; "no",(string_of_int n)]
                   [< List.fold_left
                       (fun i (hid,t) ->
                         [< (match t with
                               n,A.Decl t ->
                                X.xml_nempty "Decl"
                                 ["id",hid;"name",Names.string_of_id n]
                                 (print_term curi ids_to_inner_sorts t)
                             | n,A.Def t ->
                                X.xml_nempty "Def"
                                 ["id",hid;"name",Names.string_of_id n]
                                 (print_term curi ids_to_inner_sorts t)
                            ) ;
                            i
                         >]
                       ) [< >] canonical_context ;
                      X.xml_nempty "Goal" []
                       (print_term curi ids_to_inner_sorts t)
                   >]
               >])
             [<>] conjectures ;
            X.xml_nempty "body" [] (print_term curi ids_to_inner_sorts bo) ;
            X.xml_nempty "type" [] (print_term curi ids_to_inner_sorts ty)  >]
     | A.ADefinition (id,n,bo,ty,params) ->
        let params' = param_attribute_of_params params in
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE Definition SYSTEM \"" ^ dtdname ^"\">\n\n");
             X.xml_nempty "Definition" ["name",n ; "params",params' ; "id", id]
              [< X.xml_nempty "body" [] (print_term curi ids_to_inner_sorts bo);
                 X.xml_nempty "type" [] (print_term curi ids_to_inner_sorts ty)
               >]
         >]
     | A.AAxiom (id,n,ty,params) ->
        let params' = param_attribute_of_params params in
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE Axiom SYSTEM \"" ^ dtdname ^ "\">\n\n") ;
            X.xml_nempty "Axiom"
             ["name",n ; "id",id ; "params",params']
             (X.xml_nempty "type" [] (print_term curi ids_to_inner_sorts ty))
         >]
     | A.AVariable (id,n,bo,ty) ->
        [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
           X.xml_cdata ("<!DOCTYPE Variable SYSTEM \"" ^ dtdname ^ "\">\n\n") ;
           X.xml_nempty "Variable" ["name",n ; "id", id]
            [< (match bo with
                   None -> [<>]
                 | Some bo ->
                    X.xml_nempty "body" []
                     (print_term curi ids_to_inner_sorts bo)
               ) ;
               X.xml_nempty "type" [] (print_term curi ids_to_inner_sorts ty)
            >]
        >]
     | A.AInductiveDefinition (id,tys,params,nparams) ->
        let params' = param_attribute_of_params params in
         [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
            X.xml_cdata ("<!DOCTYPE InductiveDefinition SYSTEM \"" ^
             dtdname ^ "\">\n\n") ;
            X.xml_nempty "InductiveDefinition"
             ["noParams",string_of_int nparams ;
              "id",id ;
              "params",params']
             [< (List.fold_left
                  (fun i (typename,finite,arity,cons) ->
                    [< i ;
                       X.xml_nempty "InductiveType"
                        ["name",Names.string_of_id typename ;
                         "inductive",(string_of_bool finite)
                        ]
                        [< X.xml_nempty "arity" []
                            (print_term curi ids_to_inner_sorts arity) ;
                           (List.fold_left
                            (fun i (name,lc) ->
                              [< i ;
                                 X.xml_nempty "Constructor"
                                  ["name",Names.string_of_id name]
                                  (print_term curi ids_to_inner_sorts lc)
                              >]) [<>] cons
                           )
                        >]
                    >]
                  ) [< >] tys
                )
             >]
         >]
 in
  aux
;;

let print_inner_types curi ids_to_inner_sorts ids_to_inner_types =
 let module C2A = Cic2acic in
 let module X = Xml in
  [< X.xml_cdata "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?>\n" ;
     X.xml_cdata ("<!DOCTYPE InnerTypes SYSTEM \"" ^ typesdtdname ^"\">\n\n");
      X.xml_nempty "InnerTypes" ["of",curi]
       (Hashtbl.fold
         (fun id {C2A.annsynthesized = synty ; C2A.annexpected = expty} x ->
           [< x ;
              X.xml_nempty "TYPE" ["of",id]
               [< print_term curi ids_to_inner_sorts synty ;
                  match expty with
                     None -> [<>]
                   | Some expty' -> print_term curi ids_to_inner_sorts expty'
               >]
           >]
         ) ids_to_inner_types [<>]
       )
  >]
;;
