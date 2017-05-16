(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

open Pp
open Util
open Proofview.Notations
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

let mkApp = Term.mkApp

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
    Pequa of Term.constr * oequation (* constr = copy of the Coq formula *)
  | Ptrue
  | Pfalse
  | Pnot of oproposition
  | Por of int * oproposition * oproposition
  | Pand of int * oproposition * oproposition
  | Pimp of int * oproposition * oproposition
  | Pprop of Term.constr

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
    e_omega: afine		(* la fonction normalisée *)
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
  mutable terms : Term.constr list;
  (* La meme chose pour les propositions *)
  mutable props : Term.constr list;
  (* Les variables introduites par omega *)
  mutable om_vars : (int * oformula) list;
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
  s_trace : action list }

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
  terms = []; props = []; om_vars = []; cnt_connectors = 0;
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
      let s = Printf.sprintf "(%c%02d)" c i in
      spc () ++ str s ++ str " := " ++ Printer.pr_lconstr t ++ fnl () ++
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

let new_omega_var, rst_omega_var =
  let cpt = ref (-1) in
  (function () -> incr cpt; !cpt),
  (function () -> cpt:=(-1))

(* Affichage des variables d'un système *)

let display_omega_var i = Printf.sprintf "OV%d" i

(* Register a new internal variable corresponding to some oformula
   (normally an [Oatom]). *)

let add_omega_var env t =
  let v = new_omega_var () in
  env.om_vars <- (v,t) :: env.om_vars

(* Ajout forcé d'un lien entre un terme et une variable  Cas où la
   variable est créée par Omega et où il faut la lier après coup à un atome
   réifié introduit de force *)
let force_omega_var env t v =
  env.om_vars <- (v,t) :: env.om_vars

(* Récupère le terme associé à une variable omega *)
let unintern_omega env v =
  try List.assoc_f Int.equal v env.om_vars
  with Not_found -> failwith "unintern_omega"

(* \subsection{Gestion des environnements de variable pour la réflexion}
   Gestion des environnements de traduction entre termes des constructions
   non réifiés et variables des termes reifies. Attention il s'agit de
   l'environnement initial contenant tout. Il faudra le réduire après
   calcul des variables utiles. *)

let add_reified_atom sync t env =
  try List.index0 Term.eq_constr t env.terms
  with Not_found ->
    let i = List.length env.terms in
    (* synchronize atom indexes and omega variables *)
    let () = if sync then add_omega_var env (Oatom i) in
    env.terms <- env.terms @ [t]; i

let get_reified_atom env =
  try List.nth env.terms with Invalid_argument _ -> failwith "get_reified_atom"

(* \subsection{Gestion de l'environnement de proposition pour Omega} *)
(* ajout d'une proposition *)
let add_prop env t =
  try List.index0 Term.eq_constr t env.props
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

let oformula_of_omega env af =
  let rec loop = function
    | ({v=v; c=n}::r) -> Oplus(Omult(unintern_omega env v,Oint n),loop r)
    | [] -> Oint af.constant
  in
  loop af.body

let app f v = mkApp(Lazy.force f,v)

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

let rec reified_of_oprop env t = match t with
  | Pequa (_,{ e_comp=cmp; e_left=t1; e_right=t2 }) ->
     reified_cmp cmp [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Ptrue -> Lazy.force coq_p_true
  | Pfalse -> Lazy.force coq_p_false
  | Pnot t -> app coq_p_not [| reified_of_oprop env t |]
  | Por (_,t1,t2) | Pand (_,t1,t2) | Pimp (_,t1,t2) ->
     reified_conn t [| reified_of_oprop env t1; reified_of_oprop env t2 |]
  | Pprop t -> app coq_p_prop [| mk_nat (add_prop env t) |]

let reified_of_proposition env f =
  try reified_of_oprop env f
  with reraise -> pprint stderr f; raise reraise

(* \subsection{Omega vers COQ réifié} *)

let reified_of_omega env body constant =
  let coeff_constant =
    app coq_t_int [| Z.mk constant |] in
  let mk_coeff {c=c; v=v} t =
    let coef =
      app coq_t_mult
	[| reified_of_formula env (unintern_omega env v);
	   app coq_t_int [| Z.mk c |] |] in
    app coq_t_plus [|coef; t |] in
  List.fold_right mk_coeff body coeff_constant

let reified_of_omega env body c  =
  try reified_of_omega env body c
  with reraise -> display_eq display_omega_var (body,c); raise reraise

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
  { coefs : (atom_index * bigint) list;
    cst : bigint }

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

let rec oformula_of_constr env t =
  match Z.parse_term t with
    | Tplus (t1,t2) -> binop env (fun x y -> Oplus(x,y)) t1 t2
    | Tminus (t1,t2) -> binop env (fun x y -> Ominus(x,y)) t1 t2
    | Tmult (t1,t2) ->
       (match Z.get_scalar t1 with
        | Some n -> Omult (Oint n,oformula_of_constr env t2)
        | None ->
           match Z.get_scalar t2 with
           | Some n -> Omult (oformula_of_constr env t1, Oint n)
           | None -> Oatom (add_reified_atom true t env))
    | Topp t -> Oopp(oformula_of_constr env t)
    | Tsucc t -> Oplus(oformula_of_constr env t, Oint one)
    | Tnum n -> Oint n
    | Tother -> Oatom (add_reified_atom true t env)

and binop env c t1 t2 =
  let t1' = oformula_of_constr env t1 in
  let t2' = oformula_of_constr env t2 in
  c t1' t2'

and binprop env (neg2,depends,origin,path)
             add_to_depends neg1 gl c t1 t2 =
  let i = new_connector_id env in
  let depends1 = if add_to_depends then Left i::depends else depends in
  let depends2 = if add_to_depends then Right i::depends else depends in
  if add_to_depends then
    IntHtbl.add env.constructors i {o_hyp = origin; o_path = List.rev path};
  let t1' =
    oproposition_of_constr env (neg1,depends1,origin,O_left::path) gl t1 in
  let t2' =
    oproposition_of_constr env (neg2,depends2,origin,O_right::path) gl t2 in
  (* On numérote le connecteur dans l'environnement. *)
  c i t1' t2'

and mk_equation env ctxt c connector t1 t2 =
  let t1' = oformula_of_constr env t1 in
  let t2' = oformula_of_constr env t2 in
  (* On ajoute l'equation dans l'environnement. *)
  let omega = normalize_equation env ctxt connector t1' t2' in
  add_equation env omega;
  Pequa (c,omega)

and oproposition_of_constr env ((negated,depends,origin,path) as ctxt) gl c =
  match Z.parse_rel gl c with
    | Req (t1,t2) -> mk_equation env ctxt c Eq t1 t2
    | Rne (t1,t2) -> mk_equation env ctxt c Neq t1 t2
    | Rle (t1,t2) -> mk_equation env ctxt c Leq t1 t2
    | Rlt (t1,t2) -> mk_equation env ctxt c Lt t1 t2
    | Rge (t1,t2) -> mk_equation env ctxt c Geq t1 t2
    | Rgt (t1,t2) -> mk_equation env ctxt c Gt t1 t2
    | Rtrue -> Ptrue
    | Rfalse -> Pfalse
    | Rnot t ->
       let ctxt' = (not negated, depends, origin,(O_mono::path)) in
       Pnot (oproposition_of_constr env ctxt' gl t)
    | Ror (t1,t2) -> binprop env ctxt (not negated) negated gl mkPor t1 t2
    | Rand (t1,t2) -> binprop env ctxt negated negated gl mkPand t1 t2
    | Rimp (t1,t2) ->
       binprop env ctxt (not negated) (not negated) gl mkPimp t1 t2
    | Riff (t1,t2) ->
       (* No lifting here, since Omega only works on closed propositions. *)
       binprop env ctxt negated negated gl mkPand
         (Term.mkArrow t1 t2) (Term.mkArrow t2 t1)
    | _ -> Pprop c

(* Destructuration des hypothèses et de la conclusion *)

let display_gl env t_concl t_lhyps =
  Printf.printf "REIFED PROBLEM\n\n";
  Printf.printf "  CONCL: %a\n" pprint t_concl;
  List.iter
    (fun (i,t) -> Printf.printf "  %s: %a\n" (Id.to_string i) pprint t)
    t_lhyps;
  print_env_reification env

let reify_gl env gl =
  let concl = Tacmach.New.pf_concl gl in
  let concl = EConstr.Unsafe.to_constr concl in
  let hyps = Tacmach.New.pf_hyps_types gl in
  let hyps = List.map (fun (i,t) -> (i,EConstr.Unsafe.to_constr t)) hyps in
  let t_concl =
    oproposition_of_constr env (true,[],id_concl,[O_mono]) gl concl in
  let t_lhyps =
    List.map
      (fun (i,t) -> i,oproposition_of_constr env (false,[],i,[]) gl t)
      hyps
  in
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
  | (i,t) :: l ->
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

(* Extraction des variables déclarées dans une équation. Permet ensuite
   de les déclarer dans l'environnement de la procédure réflexive et
   éviter les créations de variable au vol *)

let rec variable_stated_in_trace = function
  | [] -> []
  | act :: l ->
     match act with
     | STATE action ->
        (*i nlle_equa: afine, def: afine, eq_orig: afine, i*)
        (*i coef: int, var:int                            i*)
        action :: variable_stated_in_trace l
     | SPLIT_INEQ (_,(_,act1),(_,act2)) ->
        variable_stated_in_trace act1 @ variable_stated_in_trace act2
     | _ -> variable_stated_in_trace l

let add_stated_equations env tree =
  (* Il faut trier les variables par ordre d'introduction pour ne pas risquer
     de définir dans le mauvais ordre *)
  let stated_equations =
    let cmpvar x y = Int.compare x.st_var y.st_var in
    let rec loop = function
      | Tree(_,t1,t2) -> List.merge cmpvar (loop t1) (loop t2)
      | Leaf s -> List.sort cmpvar (variable_stated_in_trace s.s_trace)
    in loop tree
  in
  let add_env st =
    (* On retransforme la définition de v en formule reifiée *)
    let v_def = oformula_of_omega env st.st_def in
    (* Notez que si l'ordre de création des variables n'est pas respecté,
     * ca va planter *)
    let coq_v = coq_of_formula env v_def in
    let v = add_reified_atom false coq_v env in
    (* Le terme qu'il va falloir introduire *)
    let term_to_generalize = app coq_refl_equal [|Lazy.force Z.typ; coq_v|] in
    (* sa représentation sous forme d'équation mais non réifié car on n'a pas
     * l'environnement pour le faire correctement *)
    let term_to_reify = (v_def,Oatom v) in
    (* enregistre le lien entre la variable omega et la variable Coq *)
    force_omega_var env (Oatom v) st.st_var;
    (v, term_to_generalize,term_to_reify,st.st_def.id) in
 List.map add_env stated_equations

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
    Tree(_,t1,t2) -> (equas_of_solution_tree t1)@@(equas_of_solution_tree t2)
  | Leaf s -> s.s_equa_deps

(* [really_useful_prop] pushes useless props in a new Pprop variable *)
(* Things get shorter, but may also get wrong, since a Prop is considered
   to be undecidable in ReflOmegaCore.concl_to_hyp, whereas for instance
   Pfalse is decidable. So should not be used on conclusion (??) *)

let rec coq_of_oprop = function
  | Pequa(t,_) -> t
  | Ptrue -> app coq_True [||]
  | Pfalse -> app coq_False [||]
  | Pnot t1 -> app coq_not [|coq_of_oprop t1|]
  | Por(_,t1,t2) -> app coq_or [|coq_of_oprop t1; coq_of_oprop t2|]
  | Pand(_,t1,t2) -> app coq_and [|coq_of_oprop t1; coq_of_oprop t2|]
  | Pimp(_,t1,t2) ->
     (* No lifting here, since Omega only works on closed propositions. *)
     Term.mkArrow (coq_of_oprop t1) (coq_of_oprop t2)
  | Pprop t -> t

let really_useful_prop equas c =
  let rec loop c = match c with
    | Pequa(_,e) -> if IntSet.mem e.e_omega.id equas then Some c else None
    | Pnot t1 ->
       begin match loop t1 with None -> None | Some t1' -> Some (Pnot t1') end
    | Por(i,t1,t2) -> binop (fun (t1,t2) -> Por(i,t1,t2)) t1 t2
    | Pand(i,t1,t2) -> binop (fun (t1,t2) -> Pand(i,t1,t2)) t1 t2
    | Pimp(i,t1,t2) -> binop (fun (t1,t2) -> Pimp(i,t1,t2)) t1 t2
    | Ptrue | Pfalse | Pprop _ -> None
  and binop f t1 t2 =
    begin match loop t1, loop t2 with
      None, None -> None
    | Some t1',Some t2' -> Some (f(t1',t2'))
    | Some t1',None -> Some (f(t1',Pprop (coq_of_oprop t2)))
    | None,Some t2' -> Some (f(Pprop (coq_of_oprop t1),t2'))
    end
  in
  match loop c with
  | None -> Pprop (coq_of_oprop c)
  | Some t -> t

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

let get_hyp env_hyp i =
  let rec loop count = function
    | [] -> failwith (Printf.sprintf "get_hyp %d" i)
    | CCEqua i' :: _ when Int.equal i i' -> count
    | _ :: l -> loop (succ count) l
  in loop 0 env_hyp

let replay_history env env_hyp =
  let rec loop env_hyp t =
    match t with
      | CONTRADICTION (e1,e2) :: l ->
         mkApp (Lazy.force coq_s_contradiction,
                [| mk_nat (get_hyp env_hyp e1.id);
                   mk_nat (get_hyp env_hyp e2.id) |])
      | DIVIDE_AND_APPROX (e1,e2,k,d) :: l ->
         mkApp (Lazy.force coq_s_div_approx,
                [| mk_nat (get_hyp env_hyp e1.id); Z.mk k; Z.mk d;
                   reified_of_omega env e2.body e2.constant;
                   loop env_hyp l |])
      | NOT_EXACT_DIVIDE (e1,k) :: l ->
         let e2_constant = floor_div e1.constant k in
         let d = e1.constant - e2_constant * k in
         let e2_body = map_eq_linear (fun c -> c / k) e1.body in
         mkApp (Lazy.force coq_s_not_exact_divide,
                [| mk_nat (get_hyp env_hyp e1.id); Z.mk k; Z.mk d;
                   reified_of_omega env e2_body e2_constant |])
      | EXACT_DIVIDE (e1,k) :: l ->
         let e2_body = map_eq_linear (fun c -> c / k) e1.body in
         let e2_constant = floor_div e1.constant k in
         mkApp (Lazy.force coq_s_exact_divide,
                [| mk_nat (get_hyp env_hyp e1.id); Z.mk k;
                   reified_of_omega env e2_body e2_constant;
                   loop env_hyp l |])
      | (MERGE_EQ(e3,e1,e2)) :: l ->
	  let n1 = get_hyp env_hyp e1.id and n2 = get_hyp env_hyp e2 in
          mkApp (Lazy.force coq_s_merge_eq,
		 [| mk_nat n1; mk_nat n2;
		    loop (CCEqua e3:: env_hyp) l |])
      | SUM(e3,(k1,e1),(k2,e2)) :: l ->
         let n1 = get_hyp env_hyp e1.id
         and n2 = get_hyp env_hyp e2.id in
         mkApp (Lazy.force coq_s_sum,
                [| Z.mk k1; mk_nat n1; Z.mk k2;
                   mk_nat n2; (loop (CCEqua e3 :: env_hyp) l) |])
      | CONSTANT_NOT_NUL(e,k) :: l ->
          mkApp (Lazy.force coq_s_constant_not_nul,
		 [|  mk_nat (get_hyp env_hyp e) |])
      | CONSTANT_NEG(e,k) :: l ->
          mkApp (Lazy.force coq_s_constant_neg,
		 [|  mk_nat (get_hyp env_hyp e) |])
      | STATE {st_new_eq=new_eq; st_def =def;
               st_orig=orig; st_coef=m;
               st_var=sigma } :: l ->
         let n1 = get_hyp env_hyp orig.id
         and n2 = get_hyp env_hyp def.id in
         mkApp (Lazy.force coq_s_state,
                [| Z.mk m; mk_nat n1; mk_nat n2;
                   loop (CCEqua new_eq.id :: env_hyp) l |])
      |	HYP _ :: l -> loop env_hyp l
      |	CONSTANT_NUL e :: l ->
	  mkApp (Lazy.force coq_s_constant_nul,
		 [|  mk_nat (get_hyp env_hyp e) |])
      |	NEGATE_CONTRADICT(e1,e2,true) :: l ->
	  mkApp (Lazy.force coq_s_negate_contradict,
		 [|  mk_nat (get_hyp env_hyp e1.id);
		     mk_nat (get_hyp env_hyp e2.id) |])
      |	NEGATE_CONTRADICT(e1,e2,false) :: l ->
	  mkApp (Lazy.force coq_s_negate_contradict_inv,
		 [|  mk_nat (get_hyp env_hyp e1.id);
		     mk_nat (get_hyp env_hyp e2.id) |])
      | SPLIT_INEQ(e,(e1,l1),(e2,l2)) :: l ->
	  let i =  get_hyp env_hyp e.id in
	  let r1 = loop (CCEqua e1 :: env_hyp) l1 in
	  let r2 = loop (CCEqua e2 :: env_hyp) l2 in
	  mkApp (Lazy.force coq_s_split_ineq,
                  [| mk_nat i; r1 ; r2 |])
      |	(FORGET_C _ | FORGET _ | FORGET_I _) :: l ->
	  loop env_hyp l
      | (WEAKEN  _ ) :: l -> failwith "not_treated"
      |	[] -> failwith "no contradiction"
  in loop env_hyp

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
    [] -> app coq_e_solve [| replay_history env ctxt trace |]
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

(* \section{La fonction principale} *)
 (* Cette fonction construit la
trace pour la procédure de décision réflexive.  A partir des résultats
de l'extraction des systèmes, elle lance la résolution par Omega, puis
l'extraction d'un ensemble minimal de solutions permettant la
résolution globale du système et enfin construit la trace qui permet
de faire rejouer cette solution par la tactique réflexive. *)

let resolution env (reified_concl,reified_hyps) systems_list =
  let num = ref 0 in
  let solve_system list_eq =
    let index = !num in
    let system = List.map (fun eq -> eq.e_omega) list_eq in
    let trace =
      simplify_strong
	(new_omega_eq,new_omega_var,display_omega_var)
	system in
    (* Hypotheses used for this solution *)
    let vars = hyps_used_in_trace trace in
    let splits = get_eclatement env (IntSet.elements vars) in
    if !debug then begin
      Printf.printf "SYSTEME %d\n" index;
      display_action display_omega_var trace;
      print_string "\n  Depend :";
      IntSet.iter (fun i -> Printf.printf " %d" i) vars;
      print_string "\n  Split points :";
      List.iter display_depend splits;
      Printf.printf "\n------------------------------------\n"
    end;
    incr num;
    {s_index = index; s_trace = trace; s_equa_deps = vars}, splits  in
  if !debug then Printf.printf "\n====================================\n";
  let all_solutions = List.map solve_system systems_list in
  let solution_tree = solve_with_constraints all_solutions [] in
  if !debug then  begin
    display_solution_tree stdout solution_tree;
    print_newline()
  end;
  (* Collect all hypotheses used in the solution tree *)
  let useful_equa_ids = equas_of_solution_tree solution_tree in
  let equations = List.map (get_equation env) (IntSet.elements useful_equa_ids)
  in
  let hyps_of_eqns =
    List.fold_left (fun s e -> Id.Set.add e.e_origin.o_hyp s) Id.Set.empty in
  let hyps = hyps_of_eqns equations in
  let useful_hypnames = Id.Set.elements (Id.Set.remove id_concl hyps) in
  let useful_hyptypes =
    List.map (fun id -> List.assoc_f Id.equal id reified_hyps) useful_hypnames
  in
  let useful_vars = vars_of_equations equations @@ vars_of_prop reified_concl
  in

  (* variables a introduire *)
  let to_introduce = add_stated_equations env solution_tree in
  let stated_vars =  List.map (fun (v,_,_,_) -> v) to_introduce in
  let l_generalize_arg = List.map (fun (_,t,_,_) -> EConstr.of_constr t) to_introduce in
  let hyp_stated_vars = List.map (fun (_,_,_,id) -> CCEqua id) to_introduce in
  (* L'environnement de base se construit en deux morceaux :
     - les variables des équations utiles (et de la conclusion)
     - les nouvelles variables declarées durant les preuves *)
  let all_vars_env = (IntSet.elements useful_vars) @ stated_vars in
  let basic_env =
    let rec loop i = function
      | [] -> []
      | var :: l ->
         let t = get_reified_atom env var in
         IntHtbl.add env.real_indices var i; t :: loop (succ i) l
    in
    loop 0 all_vars_env in
  (* Since [all_vars_env] is sorted, this renumbering of variables
     should have preserved order *)
  let env_terms_reified = mk_list (Lazy.force Z.typ) basic_env in
  (* On peut maintenant généraliser le but : env est a jour *)
  let l_reified_stated =
     List.map (fun (_,_,(l,r),_) ->
                 app coq_p_eq [| reified_of_formula env l;
                                 reified_of_formula env r |])
              to_introduce in
  let reified_concl = reified_of_proposition env reified_concl in
  let l_reified_terms =
    List.map
      (fun p ->
        reified_of_proposition env (really_useful_prop useful_equa_ids p))
      useful_hyptypes
  in
  let env_props_reified = mk_plist env.props in
  let reified_goal =
    mk_list (Lazy.force coq_proposition)
            (l_reified_stated @ l_reified_terms) in
  let reified =
    app coq_interp_sequent
       [| reified_concl;env_props_reified;env_terms_reified;reified_goal|]
  in
  let initial_context =
    List.map (fun id -> CCHyp{o_hyp=id;o_path=[]}) useful_hypnames in
  let context =
    CCHyp{o_hyp=id_concl;o_path=[]} :: hyp_stated_vars @ initial_context in
  let decompose_tactic = decompose_tree env context solution_tree in

  Tactics.generalize
    (l_generalize_arg @ List.map EConstr.mkVar useful_hypnames) >>
  Tactics.change_concl (EConstr.of_constr reified) >>
  Tactics.apply (EConstr.of_constr (app coq_do_omega [|decompose_tactic|])) >>
  show_goal >>
  Tactics.normalise_vm_in_concl >>
  (*i Alternatives to the previous line:
   - Normalisation without VM:
      Tactics.normalise_in_concl
   - Skip the conversion check and rely directly on the QED:
      Tactics.convert_concl_no_check (Lazy.force coq_True) Term.VMcast >>
  i*)
  Tactics.apply (EConstr.of_constr (Lazy.force coq_I))

let total_reflexive_omega_tactic =
  Proofview.Goal.nf_enter { enter = begin fun gl ->
  Coqlib.check_required_library ["Coq";"romega";"ROmega"];
  rst_omega_eq ();
  rst_omega_var ();
  try
  let env = new_environment () in
  let (concl,hyps) as reified_goal = reify_gl env gl in
  let full_reified_goal = (id_concl,Pnot concl) :: hyps in
  let systems_list = destructurate_hyps full_reified_goal in
  if !debug then display_systems systems_list;
  resolution env reified_goal systems_list
  with NO_CONTRADICTION -> CErrors.error "ROmega can't solve this system"
  end }

(*i let tester = Tacmach.hide_atomic_tactic "TestOmega" test_tactic i*)


