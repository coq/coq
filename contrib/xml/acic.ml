open Names
open Term

(* Maps fron \em{unshared} [constr] to ['a]. *)
module CicHash =
 Hashtbl.Make
  (struct
    type t = Term.constr
    let equal = (==)
    let hash = Hashtbl.hash
   end)
;;

type id = string  (* the type of the (annotated) node identifiers *)
type uri = string

type 'constr context_entry =
   Decl of 'constr   (* Declaration *)
 | Def  of 'constr   (* Definition  *)
type 'constr hypothesis = identifier * 'constr context_entry
type context = constr hypothesis list

type conjecture = int * context * constr
type metasenv = conjecture list

(* list of couples section path -- variables defined in that section *)
type params = (string * uri list) list

type obj =
   Definition of string *                          (* id,           *)
    constr * constr *                              (*  value, type, *)
    params                                         (*  parameters   *)
 | Axiom of string * constr *                      (* id, type    *)
    params                                         (*  parameters *)
 | Variable of
    string * constr option * constr                (* name, body, type *)
 | CurrentProof of
    string * metasenv *                            (*  name, conjectures, *)
    constr * constr                                (*  value, type        *)
 | InductiveDefinition of
    inductiveType list *                           (* inductive types ,      *)
    params * int                                   (*  parameters,n ind. pars*)
and inductiveType = 
 identifier * bool * constr *                 (* typename, inductive, arity *)
  constructor list                            (*  constructors              *)
and constructor =
 identifier * constr                          (* id, type *)

type aconstr =
  | ARel       of id * int * identifier
  | AVar       of id * uri
  | AEvar      of id * int * aconstr list
  | ASort      of id * sorts
  | ACast      of id * aconstr * aconstr
  | AProd      of id * name * aconstr * aconstr
  | ALambda    of id * name * aconstr * aconstr
  | ALetIn     of id * name * aconstr * aconstr
  | AApp       of id * aconstr list
  | AConst     of id * uri
  | AInd       of id * uri * int
  | AConstruct of id * uri * int * int
  | ACase      of id * uri * int * aconstr * aconstr * aconstr list
  | AFix       of id * int * ainductivefun list
  | ACoFix     of id * int * acoinductivefun list
and ainductivefun = 
 identifier * int * aconstr * aconstr
and acoinductivefun = 
 identifier * aconstr * aconstr

type acontext = (id * aconstr hypothesis) list
type aconjecture = id * int * acontext * aconstr
type ametasenv = aconjecture list

type aobj =
   ADefinition of id * string *                    (* id,           *)
    aconstr * aconstr *                            (*  value, type, *)
    params                                         (*  parameters   *)
 | AAxiom of id * string * aconstr *               (* id, type    *)
    params                                         (*  parameters *)
 | AVariable of id *
    string * aconstr option * aconstr              (* name, body, type *)
 | ACurrentProof of id *
    string * ametasenv *                           (*  name, conjectures, *)
    aconstr * aconstr                              (*  value, type        *)
 | AInductiveDefinition of id *
    anninductiveType list *                        (* inductive types ,      *)
    params * int                                   (*  parameters,n ind. pars*)
and anninductiveType = 
 identifier * bool * aconstr *                (* typename, inductive, arity *)
  annconstructor list                         (*  constructors              *)
and annconstructor =
 identifier * aconstr                         (* id, type *)
