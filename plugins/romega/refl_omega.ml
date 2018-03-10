(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

open Pp
open Util
open Constr
open Const_omega
module OmegaSolver = Omega_plugin.Omega.MakeOmegaSolver (Bigint)
open OmegaSolver

module Id = Names.Id
module IntSet = Int.Set
module IntHtbl = Hashtbl.Make(Int)

(* \section{Useful functions and flags} *)
(* Especially useful debugging functions *)
let debug = ref false

let show_goal = Tacticals.New.tclIDTAC

let pp i = print_int i; print_newline (); flush stdout

(* More readable than the prefix notation *)
let (>>) = Tacticals.New.tclTHEN

(* \section{Types}
  \subsection{How to walk in a term}
  To represent how to get to a proposition. Only choice points are
  kept (branch to choose in a disjunction  and identifier of the disjunctive
  connector) *)
type direction = Left of int | Right of int

(* Step to find a proposition (operators are at most binary). A list is
   a path *)
type occ_step = O_left | O_right | O_mono
type occ_path = occ_step list

(* chemin identifiant une proposition sous forme du nom de l'hypothèse et
   d'une liste de pas à partir de la racine de l'hypothèse *)
type occurrence = {o_hyp : Id.t; o_path : occ_path}

type atom_index = int

(* \subsection{reifiable formulas} *)
type oformula =
    (* integer *)
  | Oint of Bigint.bigint
    (* recognized binary and unary operations *)
  | Oplus of oformula * oformula
  | Omult of oformula * oformula (* Invariant : one side is [Oint] *)
  | Ominus of oformula * oformula
  | Oopp of  oformula
    (* an atom in the environment *)
  | Oatom of atom_index

(* Operators for comparison recognized by Omega *)
type comparaison = Eq | Leq | Geq | Gt | Lt | Neq

(* Representation of reified predicats (fragment of propositional calculus,
   no quantifier here). *)
(* Note : in [Pprop p], the non-reified constr [p] should be closed
   (it could contains some [Term.Var] but no [Term.Rel]). So no need to
   lift when breaking or creating arrows. *)
type oproposition =
    Pequa of EConstr.t * oequation (* constr = copy of the Coq formula *)
  | Ptrue
  | Pfalse
  | Pnot of oproposition
  | Por of int * oproposition * oproposition
  | Pand of int * oproposition * oproposition
  | Pimp of int * oproposition * oproposition
  | Pprop of EConstr.t

(* The equations *)
and oequation = {
    e_comp: comparaison;		(* comparaison *)
    e_left: oformula;			(* formule brute gauche *)
    e_right: oformula;			(* formule brute droite *)
    e_origin: occurrence;		(* l'hypothèse dont vient le terme *)
    e_negated: bool;			(* vrai si apparait en position nié
					   après normalisation *)
    e_depends: direction list;		(* liste des points de disjonction dont
					   dépend l'accès à l'équation avec la
					   direction (branche) pour y accéder *)
    e_omega: OmegaSolver.afine (* normalized formula *)
  }

(* \subsection{Proof context}
  This environment codes
  \begin{itemize}
  \item the terms and propositions that are given as
  parameters of the reified proof (and are represented as variables in the
  reified goals)
  \item translation functions linking the decision procedure and the Coq proof
  \end{itemize} *)

type environment = {
  (* La liste des termes non reifies constituant l'environnement global *)
  mutable terms : EConstr.t list;
  (* La meme chose pour les propositions *)
  mutable props : EConstr.t list;
  (* Traduction des indices utilisés ici en les indices finaux utilisés par
   * la tactique Omega après dénombrement des variables utiles *)
  real_indices : int IntHtbl.t;
  mutable cnt_connectors : int;
  equations : oequation IntHtbl.t;
  constructors : occurrence IntHtbl.t
}

(* \subsection{Solution tree}
   Définition d'une solution trouvée par Omega sous la forme d'un identifiant,
   d'un ensemble d'équation dont dépend la solution et d'une trace *)

type solution = {
  s_index : int;
  s_equa_deps : IntSet.t;
  s_trace : OmegaSolver.action list }

(* Arbre de solution résolvant complètement un ensemble de systèmes *)
type solution_tree =
    Leaf of solution
    (* un noeud interne représente un point de branchement correspondant à
       l'élimination d'un connecteur générant plusieurs buts
       (typ. disjonction). Le premier argument
       est l'identifiant du connecteur *)
  | Tree of int * solution_tree * solution_tree

(* Représentation de l'environnement extrait du but initial sous forme de
   chemins pour extraire des equations ou d'hypothèses *)

type context_content =
    CCHyp of occurrence
  | CCEqua of int

(** Some dedicated equality tests *)

let occ_step_eq s1 s2 = match s1, s2 with
| O_left, O_left | O_right, O_right | O_mono, O_mono -> true
| _ -> false

let rec oform_eq f f' = match f,f' with
  | Oint i, Oint i' -> Bigint.equal i i'
  | Oplus (f1,f2), Oplus (f1',f2')
  | Omult (f1,f2), Omult (f1',f2')
  | Ominus (f1,f2), Ominus (f1',f2') -> oform_eq f1 f1' && oform_eq f2 f2'
  | Oopp f, Oopp f' -> oform_eq f f'
  | Oatom a, Oatom a' -> Int.equal a a'
  | _ -> false

let dir_eq d d' = match d, d' with
  | Left i, Left i' | Right i, Right i' -> Int.equal i i'
  | _ -> false

(* \section{Specific utility functions to handle base types} *)
(* Nom arbitraire de l'hypothèse codant la négation du but final *)
let id_concl = Id.of_string "__goal__"

(* Initialisation de l'environnement de réification de la tactique *)
let new_environment () = {
  terms = []; props = []; cnt_connectors = 0;
  real_indices = IntHtbl.create 7;
  equations = IntHtbl.create 7;
  constructors = IntHtbl.create 7;
}

(* Génération d'un nom d'équation *)
let new_connector_id env =
   env.cnt_connectors <- succ env.cnt_connectors; env.cnt_connectors

(* Calcul de la branche complémentaire *)
let barre = function Left x -> Right x | Right x -> Left x

(* Identifiant associé à une branche *)
let indice = function Left x | Right x -> x

(* Affichage de l'environnement de réification (termes et propositions) *)
let print_env_reification env =
  let rec loop c i = function
      [] ->  str "  ===============================\n\n"
    | t :: l ->
      let sigma, env = Pfedit.get_current_context () in
      let s = Printf.sprintf "(%c%02d)" c i in
      spc () ++ str s ++ str " := " ++ Printer.pr_econstr_env env sigma t ++ fnl () ++
      loop c (succ i) l
  in
  let prop_info = str "ENVIRONMENT OF PROPOSITIONS :" ++ fnl () ++ loop 'P' 0 env.props in
  let term_info = str "ENVIRONMENT OF TERMS :" ++ fnl () ++ loop 'V' 0 env.terms in
  Feedback.msg_debug (prop_info ++ fnl () ++ term_info)

(* \subsection{Gestion des environnements de variable pour Omega} *)
(* generation d'identifiant d'equation pour Omega *)

let new_omega_eq, rst_omega_eq =
  let cpt = ref (-1) in
  (function () -> incr cpt; !cpt),
  (function () -> cpt:=(-1))

(* generation d'identifiant de variable pour Omega *)

let new_omega_var, rst_omega_var, set_omega_maxvar =
  let cpt = ref (-1) in
  (function () -> incr cpt; !cpt),
  (function () -> cpt:=(-1)),
  (function n -> cpt:=n)

(* Affichage des variables d'un système *)

let display_omega_var i = Printf.sprintf "OV%d" i

(* \subsection{Gestion des environnements de variable pour la réflexion}
   Gestion des environnements de traduction entre termes des constructions
   non réifiés et variables des termes reifies. Attention il s'agit de
   l'environnement initial contenant tout. Il faudra le réduire après
   calcul des variables utiles. *)

let add_reified_atom sigma t env =
  try List.index0 (EConstr.eq_constr sigma) t env.terms
  with Not_found ->
    let i = List.length env.terms in
    env.terms <- env.terms @ [t]; i

let get_reified_atom env =
  try List.nth env.terms with Invalid_argument _ -> failwith "get_reified_atom"

(** When the omega resolution has created a variable [v], we re-sync
    the environment with this new variable. To be done in the right order. *)

let set_reified_atom v t env =
  assert (Int.equal v (List.length env.terms));
  env.terms <- env.terms @ [t]

(* \subsection{Gestion de l'environnement de proposition pour Omega} *)
(* ajout d'une proposition *)
let add_prop sigma env t =
  try List.index0 (EConstr.eq_constr sigma) t env.props
  with Not_found ->
    let i = List.length env.props in  env.props <- env.props @ [t]; i

(* accès a une proposition *)
let get_prop v env =
  try List.nth v env with Invalid_argument _ -> failwith "get_prop"

(* \subsection{Gestion du nommage des équations} *)
(* Ajout d'une equation dans l'environnement de reification *)
let add_equation env e =
  let id = e.e_omega.id in
  if IntHtbl.mem env.equations id then () else IntHtbl.add env.equations id e

(* accès a une equation *)
let get_equation env id =
  try IntHtbl.find env.equations id
  with Not_found as e ->
    Printf.printf "Omega Equation %d non trouvée\n" id; raise e

(* Affichage des termes réifiés *)
let rec oprint ch = function
  | Oint n -> Printf.fprintf ch "%s" (Bigint.to_string n)
  | Oplus (t1,t2) -> Printf.fprintf ch "(%a + %a)" oprint t1 oprint t2
  | Omult (t1,t2) -> Printf.fprintf ch "(%a * %a)" oprint t1 oprint t2
  | Ominus(t1,t2) -> Printf.fprintf ch "(%a - %a)" oprint t1 oprint t2
  | Oopp t1 ->Printf.fprintf ch "~ %a" oprint t1
  | Oatom n -> Printf.fprintf ch "V%02d" n

let print_comp = function
  | Eq -> "=" | Leq -> "<=" | Geq -> ">="
  | Gt -> ">" | Lt -> "<" | Neq -> "!="

let rec pprint ch = function
    Pequa (_,{ e_comp=comp; e_left=t1; e_right=t2 })  ->
      Printf.fprintf ch "%a %s %a" oprint t1 (print_comp comp) oprint t2
  | Ptrue -> Printf.fprintf ch "TT"
  | Pfalse -> Printf.fprintf ch "FF"
  | Pnot t -> Printf.fprintf ch "not(%a)" pprint t
  | Por (_,t1,t2) -> Printf.fprintf ch "(%a or %a)" pprint t1 pprint t2
  | Pand(_,t1,t2) -> Printf.fprintf ch "(%a and %a)" pprint t1 pprint t2
  | Pimp(_,t1,t2) -> Printf.fprintf ch "(%a => %a)" pprint t1 pprint t2
  | Pprop c -> Printf.fprintf ch "Prop"

(* \subsection{Omega vers Oformula} *)

let oformula_of_omega af =
  let rec loop = function
    | ({v=v; c=n}::r) -> Oplus(Omult(Oatom v,Oint n),loop r)
    | [] -> Oint af.constant
  in
  loop af.body

let app f v = EConstr.mkApp(Lazy.force f,v)

(* \subsection{Oformula vers COQ reel} *)

let coq_of_formula env t =
  let rec loop = function
  | Oplus (t1,t2) -> app Z.plus [| loop t1; loop t2 |]
  | Oopp t -> app Z.opp [| loop t |]
  | Omult(t1,t2) -> app Z.mult [| loop t1; loop t2 |]
  | Oint v ->   Z.mk v
  | Oatom var ->
      (* attention ne traite pas les nouvelles variables si on ne les
       * met pas dans env.term *)
      get_reified_atom env var
  | Ominus(t1,t2) -> app Z.minus [| loop t1; loop t2 |] in
  loop t

(* \subsection{Oformula vers COQ reifié} *)

let reified_of_atom env i =
  try IntHtbl.find env.real_indices i
  with Not_found ->
    Printf.printf "Atome %d non trouvé\n" i;
    IntHtbl.iter (fun k v -> Printf.printf "%d -> %d\n" k v) env.real_indices;
    raise Not_found

let reified_binop = function
  | Oplus _ -> app coq_t_plus
  | Ominus _ -> app coq_t_minus
  | Omult _ -> app coq_t_mult
  | _ -> assert false

let rec reified_of_formula env t = match t with
  | Oplus (t1,t2) | Omult (t1,t2) | Ominus (t1,t2) ->
     reified_binop t [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Oopp t -> app coq_t_opp [| reified_of_formula env t |]
  | Oint v -> app coq_t_int [| Z.mk v |]
  | Oatom i -> app coq_t_var [| mk_N (reified_of_atom env i) |]

let reified_of_formula env f =
  try reified_of_formula env f
  with reraise -> oprint stderr f; raise reraise

let reified_cmp = function
  | Eq -> app coq_p_eq
  | Leq -> app coq_p_leq
  | Geq -> app coq_p_geq
  | Gt -> app coq_p_gt
  | Lt -> app coq_p_lt
  | Neq -> app coq_p_neq

let reified_conn = function
  | Por _ -> app coq_p_or
  | Pand _ -> app coq_p_and
  | Pimp _ -> app coq_p_imp
  | _ -> assert false

let rec reified_of_oprop sigma env t = match t with
  | Pequa (_,{ e_comp=cmp; e_left=t1; e_right=t2 }) ->
     reified_cmp cmp [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Ptrue -> Lazy.force coq_p_true
  | Pfalse -> Lazy.force coq_p_false
  | Pnot t -> app coq_p_not [| reified_of_oprop sigma env t |]
  | Por (_,t1,t2) | Pand (_,t1,t2) | Pimp (_,t1,t2) ->
     reified_conn t
      [| reified_of_oprop sigma env t1; reified_of_oprop sigma env t2 |]
  | Pprop t -> app coq_p_prop [| mk_nat (add_prop sigma env t) |]

let reified_of_proposition sigma env f =
  try reified_of_oprop sigma env f
  with reraise -> pprint stderr f; raise reraise

let reified_of_eq env (l,r) =
  app coq_p_eq [| reified_of_formula env l; reified_of_formula env r |]

(* \section{Opérations sur les équations}
Ces fonctions préparent les traces utilisées par la tactique réfléchie
pour faire des opérations de normalisation sur les équations.  *)

(* \subsection{Extractions des variables d'une équation} *)
(* Extraction des variables d'une équation. *)
(* Chaque fonction retourne une liste triée sans redondance *)

let (@@) = IntSet.union

let rec vars_of_formula = function
  | Oint _ -> IntSet.empty
  | Oplus (e1,e2) -> (vars_of_formula e1) @@ (vars_of_formula e2)
  | Omult (e1,e2) -> (vars_of_formula e1) @@ (vars_of_formula e2)
  | Ominus (e1,e2) -> (vars_of_formula e1) @@ (vars_of_formula e2)
  | Oopp e -> vars_of_formula e
  | Oatom i -> IntSet.singleton i

let rec vars_of_equations = function
  | [] -> IntSet.empty
  | e::l ->
      (vars_of_formula e.e_left) @@
      (vars_of_formula e.e_right) @@
      (vars_of_equations l)

let rec vars_of_prop = function
  | Pequa(_,e) -> vars_of_equations [e]
  | Pnot p -> vars_of_prop p
  | Por(_,p1,p2) -> (vars_of_prop p1) @@ (vars_of_prop p2)
  | Pand(_,p1,p2) -> (vars_of_prop p1) @@ (vars_of_prop p2)
  | Pimp(_,p1,p2) -> (vars_of_prop p1) @@ (vars_of_prop p2)
  | Pprop _ | Ptrue | Pfalse -> IntSet.empty

(* Normalized formulas :

   - sorted list of monomials, largest index first,
     with non-null coefficients
   - a constant coefficient

   /!\ Keep in sync with the corresponding functions in ReflOmegaCore !
*)

type nformula =
  { coefs : (atom_index * Bigint.bigint) list;
    cst : Bigint.bigint }

let scale n { coefs; cst } =
  { coefs = List.map (fun (v,k) -> (v,k*n)) coefs;
    cst = cst*n }

let shuffle nf1 nf2 =
  let rec merge l1 l2 = match l1,l2 with
    | [],_ -> l2
    | _,[] -> l1
    | (v1,k1)::r1,(v2,k2)::r2 ->
       if Int.equal v1 v2 then
         let k = k1+k2 in
         if Bigint.equal k Bigint.zero then merge r1 r2
         else (v1,k) :: merge r1 r2
       else if v1 > v2 then (v1,k1) :: merge r1 l2
       else (v2,k2) :: merge l1 r2
  in
  { coefs = merge nf1.coefs nf2.coefs;
    cst = nf1.cst + nf2.cst }

let rec normalize = function
  | Oplus(t1,t2) -> shuffle (normalize t1) (normalize t2)
  | Ominus(t1,t2) -> normalize (Oplus (t1, Oopp(t2)))
  | Oopp(t) -> scale negone (normalize t)
  | Omult(t,Oint n) | Omult (Oint n, t) ->
     if Bigint.equal n Bigint.zero then { coefs = []; cst = zero }
     else scale n (normalize t)
  | Omult _ -> assert false (* invariant on Omult *)
  | Oint n -> { coefs = []; cst = n }
  | Oatom v -> { coefs = [v,Bigint.one]; cst=Bigint.zero}

(* From normalized formulas to omega representations *)

let omega_of_nformula env kind nf =
  { id = new_omega_eq ();
    kind;
    constant=nf.cst;
    body = List.map (fun (v,c) -> { v; c }) nf.coefs }


let negate_oper = function
    Eq -> Neq | Neq -> Eq | Leq -> Gt | Geq -> Lt | Lt -> Geq | Gt -> Leq

let normalize_equation env (negated,depends,origin,path) oper t1 t2 =
  let mk_step t kind =
    let equa = omega_of_nformula env kind (normalize t) in
    { e_comp = oper; e_left = t1; e_right = t2;
      e_negated = negated; e_depends = depends;
      e_origin = { o_hyp = origin; o_path = List.rev path };
      e_omega = equa }
  in
  try match (if negated then (negate_oper oper) else oper) with
    | Eq  -> mk_step (Oplus (t1,Oopp t2)) EQUA
    | Neq -> mk_step (Oplus (t1,Oopp t2)) DISE
    | Leq -> mk_step (Oplus (t2,Oopp t1)) INEQ
    | Geq -> mk_step (Oplus (t1,Oopp t2)) INEQ
    | Lt  -> mk_step (Oplus (Oplus(t2,Oint negone),Oopp t1)) INEQ
    | Gt -> mk_step (Oplus (Oplus(t1,Oint negone),Oopp t2)) INEQ
  with e when Logic.catchable_exception e -> raise e

(* \section{Compilation des hypothèses} *)

let mkPor i x y = Por (i,x,y)
let mkPand i x y = Pand (i,x,y)
let mkPimp i x y = Pimp (i,x,y)

let rec oformula_of_constr sigma env t =
  match Z.parse_term sigma t with
    | Tplus (t1,t2) -> binop sigma env (fun x y -> Oplus(x,y)) t1 t2
    | Tminus (t1,t2) -> binop sigma env (fun x y -> Ominus(x,y)) t1 t2
    | Tmult (t1,t2) ->
       (match Z.get_scalar sigma t1 with
        | Some n -> Omult (Oint n,oformula_of_constr sigma env t2)
        | None ->
           match Z.get_scalar sigma t2 with
           | Some n -> Omult (oformula_of_constr sigma env t1, Oint n)
           | None -> Oatom (add_reified_atom sigma t env))
    | Topp t -> Oopp(oformula_of_constr sigma env t)
    | Tsucc t -> Oplus(oformula_of_constr sigma env t, Oint one)
    | Tnum n -> Oint n
    | Tother -> Oatom (add_reified_atom sigma t env)

and binop sigma env c t1 t2 =
  let t1' = oformula_of_constr sigma env t1 in
  let t2' = oformula_of_constr sigma env t2 in
  c t1' t2'

and binprop sigma env (neg2,depends,origin,path)
             add_to_depends neg1 gl c t1 t2 =
  let i = new_connector_id env in
  let depends1 = if add_to_depends then Left i::depends else depends in
  let depends2 = if add_to_depends then Right i::depends else depends in
  if add_to_depends then
    IntHtbl.add env.constructors i {o_hyp = origin; o_path = List.rev path};
  let t1' =
    oproposition_of_constr sigma env (neg1,depends1,origin,O_left::path) gl t1 in
  let t2' =
    oproposition_of_constr sigma env (neg2,depends2,origin,O_right::path) gl t2 in
  (* On numérote le connecteur dans l'environnement. *)
  c i t1' t2'

and mk_equation sigma env ctxt c connector t1 t2 =
  let t1' = oformula_of_constr sigma env t1 in
  let t2' = oformula_of_constr sigma env t2 in
  (* On ajoute l'equation dans l'environnement. *)
  let omega = normalize_equation env ctxt connector t1' t2' in
  add_equation env omega;
  Pequa (c,omega)

and oproposition_of_constr sigma env ((negated,depends,origin,path) as ctxt) gl c =
  match Z.parse_rel gl c with
    | Req (t1,t2) -> mk_equation sigma env ctxt c Eq t1 t2
    | Rne (t1,t2) -> mk_equation sigma env ctxt c Neq t1 t2
    | Rle (t1,t2) -> mk_equation sigma env ctxt c Leq t1 t2
    | Rlt (t1,t2) -> mk_equation sigma env ctxt c Lt t1 t2
    | Rge (t1,t2) -> mk_equation sigma env ctxt c Geq t1 t2
    | Rgt (t1,t2) -> mk_equation sigma env ctxt c Gt t1 t2
    | Rtrue -> Ptrue
    | Rfalse -> Pfalse
    | Rnot t ->
       let ctxt' = (not negated, depends, origin,(O_mono::path)) in
       Pnot (oproposition_of_constr sigma env ctxt' gl t)
    | Ror (t1,t2) -> binprop sigma env ctxt (not negated) negated gl mkPor t1 t2
    | Rand (t1,t2) -> binprop sigma env ctxt negated negated gl mkPand t1 t2
    | Rimp (t1,t2) ->
       binprop sigma env ctxt (not negated) (not negated) gl mkPimp t1 t2
    | Riff (t1,t2) ->
       (* No lifting here, since Omega only works on closed propositions. *)
       binprop sigma env ctxt negated negated gl mkPand
         (EConstr.mkArrow t1 t2) (EConstr.mkArrow t2 t1)
    | _ -> Pprop c

(* Destructuration des hypothèses et de la conclusion *)

let display_gl env t_concl t_lhyps =
  Printf.printf "REIFED PROBLEM\n\n";
  Printf.printf "  CONCL: %a\n" pprint t_concl;
  List.iter
    (fun (i,_,t) -> Printf.printf "  %s: %a\n" (Id.to_string i) pprint t)
    t_lhyps;
  print_env_reification env

type defined = Defined | Assumed

let reify_hyp sigma env gl i =
  let open Context.Named.Declaration in
  let ctxt = (false,[],i,[]) in
  match Tacmach.New.pf_get_hyp i gl with
  | LocalDef (_,d,t) when Z.is_int_typ gl t ->
     let dummy = Lazy.force coq_True in
     let p = mk_equation sigma env ctxt dummy Eq (EConstr.mkVar i) d in
     i,Defined,p
  | LocalDef (_,_,t) | LocalAssum (_,t) ->
     let p = oproposition_of_constr sigma env ctxt gl t in
     i,Assumed,p

let reify_gl env gl =
  let sigma = Proofview.Goal.sigma gl in
  let concl = Tacmach.New.pf_concl gl in
  let hyps = Tacmach.New.pf_ids_of_hyps gl in
  let ctxt_concl = (true,[],id_concl,[O_mono]) in
  let t_concl = oproposition_of_constr sigma env ctxt_concl gl concl in
  let t_lhyps = List.map (reify_hyp sigma env gl) hyps in
  let () = if !debug then display_gl env t_concl t_lhyps in
  t_concl, t_lhyps

let rec destruct_pos_hyp eqns = function
  | Pequa (_,e) -> [e :: eqns]
  | Ptrue | Pfalse | Pprop _ -> [eqns]
  | Pnot t -> destruct_neg_hyp eqns t
  | Por (_,t1,t2) ->
      let s1 = destruct_pos_hyp eqns t1 in
      let s2 = destruct_pos_hyp eqns t2 in
      s1 @ s2
  | Pand(_,t1,t2) ->
      List.map_append
        (fun le1 -> destruct_pos_hyp le1 t2)
        (destruct_pos_hyp eqns t1)
  | Pimp(_,t1,t2) ->
      let s1 = destruct_neg_hyp eqns t1 in
      let s2 = destruct_pos_hyp eqns t2 in
      s1 @ s2

and destruct_neg_hyp eqns = function
  | Pequa (_,e) -> [e :: eqns]
  | Ptrue | Pfalse | Pprop _ -> [eqns]
  | Pnot t -> destruct_pos_hyp eqns t
  | Pand (_,t1,t2) ->
      let s1 = destruct_neg_hyp eqns t1 in
      let s2 = destruct_neg_hyp eqns t2 in
      s1 @ s2
  | Por(_,t1,t2) ->
      List.map_append
        (fun le1 -> destruct_neg_hyp le1 t2)
        (destruct_neg_hyp eqns t1)
  | Pimp(_,t1,t2) ->
      List.map_append
        (fun le1 -> destruct_neg_hyp le1 t2)
        (destruct_pos_hyp eqns t1)

let rec destructurate_hyps = function
  | [] -> [[]]
  | (i,_,t) :: l ->
     let l_syst1 = destruct_pos_hyp [] t in
     let l_syst2 = destructurate_hyps l in
     List.cartesian (@) l_syst1 l_syst2

(* \subsection{Affichage d'un système d'équation} *)

(* Affichage des dépendances de système *)
let display_depend = function
    Left i -> Printf.printf " L%d" i
  | Right i -> Printf.printf " R%d" i

let display_systems syst_list =
  let display_omega om_e =
    Printf.printf "  E%d : %a %s 0\n"
      om_e.id
      (fun _ -> display_eq display_omega_var)
      (om_e.body, om_e.constant)
      (operator_of_eq om_e.kind) in

  let display_equation oformula_eq =
    pprint stdout (Pequa (Lazy.force coq_I,oformula_eq)); print_newline ();
    display_omega oformula_eq.e_omega;
    Printf.printf "  Depends on:";
    List.iter display_depend oformula_eq.e_depends;
    Printf.printf "\n  Path: %s"
      (String.concat ""
	 (List.map (function O_left -> "L" | O_right -> "R" | O_mono -> "M")
	    oformula_eq.e_origin.o_path));
    Printf.printf "\n  Origin: %s (negated : %s)\n\n"
      (Id.to_string oformula_eq.e_origin.o_hyp)
      (if oformula_eq.e_negated then "yes" else "no") in

  let display_system syst =
    Printf.printf "=SYSTEM===================================\n";
    List.iter display_equation syst in
  List.iter display_system syst_list

(* Extraction des prédicats utilisées dans une trace. Permet ensuite le
   calcul des hypothèses *)

let rec hyps_used_in_trace = function
  | [] -> IntSet.empty
  | act :: l ->
     match act with
     | HYP e -> IntSet.add e.id (hyps_used_in_trace l)
     | SPLIT_INEQ (_,(_,act1),(_,act2)) ->
        hyps_used_in_trace act1 @@ hyps_used_in_trace act2
     | _ -> hyps_used_in_trace l

(** Retreive variables declared as extra equations during resolution
    and declare them into the environment.
    We should consider these variables in their introduction order,
    otherwise really bad things will happen. *)

let state_cmp x y = Int.compare x.st_var y.st_var

module StateSet =
  Set.Make (struct type t = state_action let compare = state_cmp end)

let rec stated_in_trace = function
  | [] -> StateSet.empty
  | [SPLIT_INEQ (_,(_,t1),(_,t2))] ->
     StateSet.union (stated_in_trace t1) (stated_in_trace t2)
  | STATE action :: l -> StateSet.add action (stated_in_trace l)
  | _ :: l -> stated_in_trace l

let rec stated_in_tree = function
  | Tree(_,t1,t2) -> StateSet.union (stated_in_tree t1) (stated_in_tree t2)
  | Leaf s -> stated_in_trace s.s_trace

let mk_refl t = app coq_refl_equal [|Lazy.force Z.typ; t|]

let digest_stated_equations env tree =
  let do_equation st (vars,gens,eqns,ids) =
    (** We turn the definition of [v]
        - into a reified formula : *)
    let v_def = oformula_of_omega st.st_def in
    (** - into a concrete Coq formula
          (this uses only older vars already in env) : *)
    let coq_v = coq_of_formula env v_def in
    (** We then update the environment *)
    set_reified_atom st.st_var coq_v env;
    (** The term we'll introduce *)
    let term_to_generalize = mk_refl coq_v in
    (** Its representation as equation (but not reified yet,
        we lack the proper env to do that). *)
    let term_to_reify = (v_def,Oatom st.st_var) in
    (st.st_var::vars,
     term_to_generalize::gens,
     term_to_reify::eqns,
     CCEqua st.st_def.id :: ids)
  in
  let (vars,gens,eqns,ids) =
    StateSet.fold do_equation (stated_in_tree tree) ([],[],[],[])
  in
  (List.rev vars, List.rev gens, List.rev eqns, List.rev ids)

(* Calcule la liste des éclatements à réaliser sur les hypothèses
   nécessaires pour extraire une liste d'équations donnée *)

(* PL: experimentally, the result order of the following function seems
   _very_ crucial for efficiency. No idea why. Do not remove the List.rev
   or modify the current semantics of Util.List.union (some elements of first
   arg, then second arg), unless you know what you're doing. *)

let rec get_eclatement env = function
  | [] -> []
  | i :: r ->
     let l = try (get_equation env i).e_depends with Not_found -> [] in
     List.union dir_eq (List.rev l) (get_eclatement env r)

let select_smaller l =
  let comp (_,x) (_,y) = Int.compare (List.length x) (List.length y) in
  try List.hd (List.sort comp l) with Failure _ -> failwith "select_smaller"

let filter_compatible_systems required systems =
  let rec select = function
    | [] -> []
    | (x::l) ->
       if List.mem_f dir_eq x required then select l
       else if List.mem_f dir_eq (barre x) required then raise Exit
       else x :: select l
  in
  List.map_filter
    (function (sol, splits) ->
      try Some (sol, select splits) with Exit -> None)
    systems

let rec equas_of_solution_tree = function
  | Tree(_,t1,t2) ->
     (equas_of_solution_tree t1)@@(equas_of_solution_tree t2)
  | Leaf s -> s.s_equa_deps

(** [maximize_prop] pushes useless props in a new Pprop atom.
  The reified formulas get shorter, but be careful with decidabilities.
  For instance, anything that contains a Pprop is considered to be
  undecidable in [ReflOmegaCore], whereas a Pfalse for instance at
  the same spot will lead to a decidable formula.
  In particular, do not use this function on the conclusion.
  Even in hypotheses, we could probably build pathological examples
  that romega won't handle correctly, but they should be pretty rare.
*)

let maximize_prop equas c =
  let rec loop c = match c with
    | Pequa(t,e) -> if IntSet.mem e.e_omega.id equas then c else Pprop t
    | Pnot t ->
       (match loop t with
        | Pprop p -> Pprop (app coq_not [|p|])
        | t' -> Pnot t')
    | Por(i,t1,t2) ->
       (match loop t1, loop t2 with
        | Pprop p1, Pprop p2 -> Pprop (app coq_or [|p1;p2|])
        | t1', t2' -> Por(i,t1',t2'))
    | Pand(i,t1,t2) ->
       (match loop t1, loop t2 with
        | Pprop p1, Pprop p2 -> Pprop (app coq_and [|p1;p2|])
        | t1', t2' -> Pand(i,t1',t2'))
    | Pimp(i,t1,t2) ->
       (match loop t1, loop t2 with
        | Pprop p1, Pprop p2 -> Pprop (EConstr.mkArrow p1 p2) (* no lift (closed) *)
        | t1', t2' -> Pimp(i,t1',t2'))
    | Ptrue -> Pprop (app coq_True [||])
    | Pfalse -> Pprop (app coq_False [||])
    | Pprop _ -> c
  in loop c

let rec display_solution_tree ch = function
    Leaf t ->
      output_string ch
       (Printf.sprintf "%d[%s]"
         t.s_index
         (String.concat " " (List.map string_of_int
                                      (IntSet.elements t.s_equa_deps))))
  | Tree(i,t1,t2) ->
      Printf.fprintf ch "S%d(%a,%a)" i
	display_solution_tree t1 display_solution_tree t2

let rec solve_with_constraints all_solutions path =
  let rec build_tree sol buf = function
      [] -> Leaf sol
    | (Left i :: remainder) ->
	Tree(i,
	     build_tree sol (Left i :: buf) remainder,
	     solve_with_constraints all_solutions (List.rev(Right i :: buf)))
    | (Right i :: remainder) ->
	 Tree(i,
	      solve_with_constraints all_solutions (List.rev (Left i ::  buf)),
	      build_tree sol (Right i :: buf) remainder) in
  let weighted = filter_compatible_systems path all_solutions in
  let (winner_sol,winner_deps) =
    try select_smaller weighted
    with reraise ->
      Printf.printf "%d - %d\n"
	(List.length weighted) (List.length all_solutions);
      List.iter display_depend path; raise reraise
  in
  build_tree winner_sol (List.rev path) winner_deps

let find_path {o_hyp=id;o_path=p} env =
  let rec loop_path = function
      ([],l) -> Some l
    | (x1::l1,x2::l2) when occ_step_eq x1 x2 -> loop_path (l1,l2)
    | _ -> None in
  let rec loop_id i = function
      CCHyp{o_hyp=id';o_path=p'} :: l when Id.equal id id' ->
	begin match loop_path (p',p) with
	  Some r -> i,r
	| None -> loop_id (succ i) l
	end
    | _ :: l -> loop_id (succ i) l
    | [] -> failwith "find_path" in
  loop_id 0 env

let mk_direction_list l =
  let trans = function
    | O_left -> Some (Lazy.force coq_d_left)
    | O_right -> Some (Lazy.force coq_d_right)
    | O_mono -> None (* No more [D_mono] constructor now *)
  in
  mk_list (Lazy.force coq_direction) (List.map_filter trans l)


(* \section{Rejouer l'historique} *)

let hyp_idx env_hyp i =
  let rec loop count = function
    | [] -> failwith (Printf.sprintf "get_hyp %d" i)
    | CCEqua i' :: _ when Int.equal i i' -> mk_nat count
    | _ :: l -> loop (succ count) l
  in loop 0 env_hyp


(* We now expand NEGATE_CONTRADICT and CONTRADICTION into
   a O_SUM followed by a O_BAD_CONSTANT *)

let sum_bad inv i1 i2 =
  let open EConstr in
  mkApp (Lazy.force coq_s_sum,
         [| Z.mk Bigint.one; i1;
            Z.mk (if inv then negone else Bigint.one); i2;
            mkApp (Lazy.force coq_s_bad_constant, [| mk_nat 0 |])|])

let rec reify_trace env env_hyp =
  let open EConstr in
  function
  | CONSTANT_NOT_NUL(e,_) :: []
  | CONSTANT_NEG(e,_) :: []
  | CONSTANT_NUL e :: [] ->
     mkApp (Lazy.force coq_s_bad_constant,[| hyp_idx env_hyp e |])
  | NEGATE_CONTRADICT(e1,e2,direct) :: [] ->
     sum_bad direct (hyp_idx env_hyp e1.id) (hyp_idx env_hyp e2.id)
  | CONTRADICTION (e1,e2) :: [] ->
     sum_bad false (hyp_idx env_hyp e1.id) (hyp_idx env_hyp e2.id)
  | NOT_EXACT_DIVIDE (e1,k) :: [] ->
     mkApp (Lazy.force coq_s_not_exact_divide,
            [| hyp_idx env_hyp e1.id; Z.mk k |])
  | DIVIDE_AND_APPROX (e1,_,k,_) :: l
  | EXACT_DIVIDE (e1,k) :: l ->
     mkApp (Lazy.force coq_s_divide,
            [| hyp_idx env_hyp e1.id; Z.mk k;
               reify_trace env env_hyp l |])
  | MERGE_EQ(e3,e1,e2) :: l ->
     mkApp (Lazy.force coq_s_merge_eq,
            [| hyp_idx env_hyp e1.id; hyp_idx env_hyp e2;
               reify_trace env (CCEqua e3:: env_hyp) l |])
  | SUM(e3,(k1,e1),(k2,e2)) :: l ->
     mkApp (Lazy.force coq_s_sum,
            [| Z.mk k1; hyp_idx env_hyp e1.id;
               Z.mk k2; hyp_idx env_hyp e2.id;
               reify_trace env (CCEqua e3 :: env_hyp) l |])
  | STATE {st_new_eq; st_def; st_orig; st_coef } :: l ->
     (* we now produce a [O_SUM] here *)
     mkApp (Lazy.force coq_s_sum,
            [| Z.mk Bigint.one; hyp_idx env_hyp st_orig.id;
               Z.mk st_coef; hyp_idx env_hyp st_def.id;
               reify_trace env (CCEqua st_new_eq.id :: env_hyp) l |])
  | HYP _ :: l -> reify_trace env env_hyp l
  | SPLIT_INEQ(e,(e1,l1),(e2,l2)) :: _ ->
     let r1 = reify_trace env (CCEqua e1 :: env_hyp) l1 in
     let r2 = reify_trace env (CCEqua e2 :: env_hyp) l2 in
     mkApp (Lazy.force coq_s_split_ineq,
            [| hyp_idx env_hyp e.id; r1 ; r2 |])
  | (FORGET_C _ | FORGET _ | FORGET_I _) :: l -> reify_trace env env_hyp l
  | WEAKEN  _ :: l -> failwith "not_treated"
  | _ -> failwith "bad history"

let rec decompose_tree env ctxt = function
   Tree(i,left,right) ->
     let org =
       try IntHtbl.find env.constructors i
       with Not_found ->
	 failwith (Printf.sprintf "Cannot find constructor %d" i) in
     let (index,path) = find_path org ctxt in
     let left_hyp = CCHyp{o_hyp=org.o_hyp;o_path=org.o_path @ [O_left]} in
     let right_hyp = CCHyp{o_hyp=org.o_hyp;o_path=org.o_path @ [O_right]} in
     app coq_e_split
       [| mk_nat index;
	  mk_direction_list path;
	  decompose_tree env (left_hyp::ctxt) left;
	  decompose_tree env (right_hyp::ctxt) right |]
  | Leaf s ->
      decompose_tree_hyps s.s_trace env ctxt (IntSet.elements s.s_equa_deps)
and decompose_tree_hyps trace env ctxt = function
    [] -> app coq_e_solve [| reify_trace env ctxt trace |]
  | (i::l) ->
      let equation =
        try IntHtbl.find env.equations i
        with Not_found ->
	  failwith (Printf.sprintf "Cannot find equation %d" i) in
      let (index,path) = find_path equation.e_origin ctxt in
      let cont =
	decompose_tree_hyps trace env
	   (CCEqua equation.e_omega.id :: ctxt) l in
      app coq_e_extract [|mk_nat index; mk_direction_list path; cont |]

let solve_system env index list_eq =
  let system = List.map (fun eq -> eq.e_omega) list_eq in
  let trace =
    OmegaSolver.simplify_strong
      (new_omega_eq,new_omega_var,display_omega_var)
      system
  in
  (* Hypotheses used for this solution *)
  let vars = hyps_used_in_trace trace in
  let splits = get_eclatement env (IntSet.elements vars) in
  if !debug then
    begin
      Printf.printf "SYSTEME %d\n" index;
      display_action display_omega_var trace;
      print_string "\n  Depend :";
      IntSet.iter (fun i -> Printf.printf " %d" i) vars;
      print_string "\n  Split points :";
      List.iter display_depend splits;
      Printf.printf "\n------------------------------------\n"
    end;
  {s_index = index; s_trace = trace; s_equa_deps = vars}, splits

(* \section{La fonction principale} *)
 (* Cette fonction construit la
trace pour la procédure de décision réflexive.  A partir des résultats
de l'extraction des systèmes, elle lance la résolution par Omega, puis
l'extraction d'un ensemble minimal de solutions permettant la
résolution globale du système et enfin construit la trace qui permet
de faire rejouer cette solution par la tactique réflexive. *)

let resolution unsafe sigma env (reified_concl,reified_hyps) systems_list =
  if !debug then Printf.printf "\n====================================\n";
  let all_solutions = List.mapi (solve_system env) systems_list in
  let solution_tree = solve_with_constraints all_solutions [] in
  if !debug then  begin
    display_solution_tree stdout solution_tree;
    print_newline()
  end;
  (** Collect all hypotheses and variables used in the solution tree *)
  let useful_equa_ids = equas_of_solution_tree solution_tree in
  let useful_hypnames, useful_vars =
    IntSet.fold
      (fun i (hyps,vars) ->
        let e = get_equation env i in
        Id.Set.add e.e_origin.o_hyp hyps,
        vars_of_equations [e] @@ vars)
      useful_equa_ids
      (Id.Set.empty, vars_of_prop reified_concl)
  in
  let useful_hypnames =
    Id.Set.elements (Id.Set.remove id_concl useful_hypnames)
  in

  (** Parts coming from equations introduced by omega: *)
  let stated_vars, l_generalize_arg, to_reify_stated, hyp_stated_vars =
    digest_stated_equations env solution_tree
  in
  (** The final variables are either coming from:
     - useful hypotheses (and conclusion)
     - equations introduced during resolution *)
  let all_vars_env = (IntSet.elements useful_vars) @ stated_vars
  in
  (** We prepare the renumbering from all variables to useful ones.
      Since [all_var_env] is sorted, this renumbering will preserve
      order: this way, the equations in ReflOmegaCore will have
      the same normal forms as here. *)
  let reduced_term_env =
    let rec loop i = function
      | [] -> []
      | var :: l ->
         let t = get_reified_atom env var in
         IntHtbl.add env.real_indices var i; t :: loop (succ i) l
    in
    mk_list (Lazy.force Z.typ) (loop 0 all_vars_env)
  in
  (** The environment [env] (and especially [env.real_indices]) is now
      ready for the coming reifications: *)
  let l_reified_stated = List.map (reified_of_eq env) to_reify_stated in
  let reified_concl = reified_of_proposition sigma env reified_concl in
  let l_reified_terms =
    List.map
      (fun id ->
        match Id.Map.find id reified_hyps with
        | Defined,p ->
           reified_of_proposition sigma env p, mk_refl (EConstr.mkVar id)
        | Assumed,p ->
           reified_of_proposition sigma env (maximize_prop useful_equa_ids p),
           EConstr.mkVar id
        | exception Not_found -> assert false)
      useful_hypnames
  in
  let l_reified_terms, l_reified_hypnames = List.split l_reified_terms in
  let env_props_reified = mk_plist env.props in
  let reified_goal =
    mk_list (Lazy.force coq_proposition)
            (l_reified_stated @ l_reified_terms) in
  let reified =
    app coq_interp_sequent
       [| reified_concl;env_props_reified;reduced_term_env;reified_goal|]
  in
  let mk_occ id = {o_hyp=id;o_path=[]} in
  let initial_context =
    List.map (fun id -> CCHyp (mk_occ id)) useful_hypnames in
  let context =
    CCHyp (mk_occ id_concl) :: hyp_stated_vars @ initial_context in
  let decompose_tactic = decompose_tree env context solution_tree in

  Tactics.generalize (l_generalize_arg @ l_reified_hypnames) >>
  Tactics.convert_concl_no_check reified DEFAULTcast >>
  Tactics.apply (app coq_do_omega [|decompose_tactic|]) >>
  show_goal >>
  (if unsafe then
     (* Trust the produced term. Faster, but might fail later at Qed.
        Also handy when debugging, e.g. via a Show Proof after romega. *)
     Tactics.convert_concl_no_check (Lazy.force coq_True) VMcast
   else
     Tactics.normalise_vm_in_concl) >>
  Tactics.apply (Lazy.force coq_I)

let total_reflexive_omega_tactic unsafe =
  Proofview.Goal.nf_enter begin fun gl ->
  Coqlib.check_required_library ["Coq";"romega";"ROmega"];
  rst_omega_eq ();
  rst_omega_var ();
  try
  let env = new_environment () in
  let (concl,hyps) = reify_gl env gl in
  (* Register all atom indexes created during reification as omega vars *)
  set_omega_maxvar (pred (List.length env.terms));
  let full_reified_goal = (id_concl,Assumed,Pnot concl) :: hyps in
  let systems_list = destructurate_hyps full_reified_goal in
  let hyps =
    List.fold_left (fun s (id,d,p) -> Id.Map.add id (d,p) s) Id.Map.empty hyps
  in
  if !debug then display_systems systems_list;
  let sigma = Proofview.Goal.sigma gl in
  resolution unsafe sigma env (concl,hyps) systems_list
  with NO_CONTRADICTION -> CErrors.user_err Pp.(str "ROmega can't solve this system")
  end

