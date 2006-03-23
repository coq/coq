(*************************************************************************

   PROJET RNRT Calife - 2001
   Author: Pierre Crégut - France Télécom R&D
   Licence : LGPL version 2.1

 *************************************************************************)

open Const_omega
module OmegaSolver = Omega.MakeOmegaSolver (Bigint)
open OmegaSolver

(* \section{Useful functions and flags} *)
(* Especially useful debugging functions *)
let debug = ref false

let show_goal gl =
  if !debug then Pp.ppnl (Tacmach.pr_gls gl); Tacticals.tclIDTAC gl

let pp i = print_int i; print_newline (); flush stdout

(* More readable than the prefix notation *)
let (>>) = Tacticals.tclTHEN

(* [list_index t l = i] \eqv $nth l i = t \wedge \forall j < i nth l j != t$ *)

let list_index t = 
  let rec loop i = function
    | (u::l) -> if u = t then i else loop (succ i) l
    | [] -> raise Not_found in
  loop 0

(* [list_uniq l = filter_i (x i -> nth l (i-1) != x) l] *)
let list_uniq l  = 
  let rec uniq = function
      x :: ((y :: _) as l) when x = y -> uniq l
    | x :: l -> x :: uniq l
    | [] -> [] in
  uniq (List.sort compare l)

(* $\forall x. mem x  (list\_union l1 l2) \eqv x \in \{l1\} \cup \{l2\}$ *)
let list_union l1 l2 =
  let rec loop buf = function
      x :: r -> if List.mem x l2 then loop buf r else loop (x :: buf) r
    | [] -> buf in
  loop l2 l1

(* $\forall x. 
      mem \;\; x \;\; (list\_intersect\;\; l1\;\;l2) \eqv x \in \{l1\} 
       \cap \{l2\}$ *)
let list_intersect l1 l2 =
  let rec loop buf = function
      x :: r -> if List.mem x l2 then loop (x::buf) r else loop buf r
    | [] -> buf in
  loop [] l1

(* cartesian product. Elements are lists and are concatenated.
   $cartesian [x_1 ... x_n] [y_1 ... y_p] = [x_1 @ y_1, x_2 @ y_1 ... x_n @ y_1 , x_1 @ y_2 ... x_n @ y_p]$ *)

let rec cartesien l1 l2 =
  let rec loop = function
      (x2 :: r2) -> List.map (fun x1 -> x1 @ x2) l1 @ loop r2
    | [] -> [] in
  loop l2

(* remove element e from list l *)
let list_remove e l =
  let rec loop = function
      x :: l -> if x = e then loop l else x :: loop l
    | [] -> [] in
  loop l

(* equivalent of the map function but no element is added when the function
   raises an exception (and the computation silently continues) *)
let map_exc f = 
  let rec loop = function 
    (x::l) -> 
      begin match try Some (f x) with exc -> None with
        Some v -> v :: loop l | None -> loop l
      end
    | [] -> [] in
  loop 

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
type occurence = {o_hyp : Names.identifier; o_path : occ_path}

(* \subsection{refiable formulas} *)
type oformula =
    (* integer *)
  | Oint of Bigint.bigint
    (* recognized binary and unary operations *)
  | Oplus of oformula * oformula
  | Omult of oformula * oformula
  | Ominus of oformula * oformula
  | Oopp of  oformula
    (* an atome in the environment *)
  | Oatom of int
    (* weird expression that cannot be translated *)
  | Oufo of oformula

(* Operators for comparison recognized by Omega *)
type comparaison = Eq | Leq | Geq | Gt | Lt | Neq

(* Type des prédicats réifiés (fragment de calcul propositionnel. Les 
 * quantifications sont externes au langage) *)
type oproposition = 
    Pequa of Term.constr * oequation
  | Ptrue 
  | Pfalse
  | Pnot of oproposition
  | Por of int * oproposition * oproposition
  | Pand of int * oproposition * oproposition
  | Pimp of int * oproposition * oproposition
  | Pprop of Term.constr

(* Les équations ou proposiitions atomiques utiles du calcul *)
and oequation = {
    e_comp: comparaison;		(* comparaison *)
    e_left: oformula;			(* formule brute gauche *)
    e_right: oformula;			(* formule brute droite *)
    e_trace: Term.constr;		(* tactique de normalisation *)
    e_origin: occurence;		(* l'hypothèse dont vient le terme *)
    e_negated: bool;			(* vrai si apparait en position nié 
					   après normalisation *)
    e_depends: direction  list;		(* liste des points de disjonction dont 
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
  mutable om_vars : (oformula * int) list;
  (* Traduction des indices utilisés ici en les indices finaux utilisés par 
   * la tactique Omega après dénombrement des variables utiles *)
  real_indices : (int,int) Hashtbl.t;
  mutable cnt_connectors : int;
  equations : (int,oequation) Hashtbl.t;
  constructors : (int, occurence) Hashtbl.t
}

(* \subsection{Solution tree}
   Définition d'une solution trouvée par Omega sous la forme d'un identifiant,
   d'un ensemble d'équation dont dépend la solution et d'une trace *)
type solution = {
  s_index : int;
  s_equa_deps : int list;
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
    CCHyp of occurence
  | CCEqua of int

(* \section{Specific utility functions to handle base types} *)
(* Nom arbitraire de l'hypothèse codant la négation du but final *)  
let id_concl = Names.id_of_string "__goal__"

(* Initialisation de l'environnement de réification de la tactique *)
let new_environment () = {
  terms = []; props = []; om_vars = []; cnt_connectors = 0; 
  real_indices = Hashtbl.create 7;
  equations = Hashtbl.create 7;
  constructors = Hashtbl.create 7;
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
      [] -> Printf.printf "  ===============================\n\n"
    | t :: l -> 
	Printf.printf "  (%c%02d) := " c i;
	Pp.ppnl (Printer.pr_lconstr t);
	Pp.flush_all ();
	loop c (succ i) l in
  print_newline ();
  Printf.printf "  ENVIRONMENT OF PROPOSITIONS :\n\n"; loop 'P' 0 env.props;
  Printf.printf "  ENVIRONMENT OF TERMS :\n\n"; loop 'V' 0 env.terms


(* \subsection{Gestion des environnements de variable pour Omega} *)
(* generation d'identifiant d'equation pour Omega *)

let new_omega_eq, rst_omega_eq = 
  let cpt = ref 0 in 
  (function () -> incr cpt; !cpt), 
  (function () -> cpt:=0)

(* generation d'identifiant de variable pour Omega *)

let new_omega_var, rst_omega_var = 
  let cpt = ref 0 in 
  (function () -> incr cpt; !cpt), 
  (function () -> cpt:=0)

(* Affichage des variables d'un système *)

let display_omega_var i = Printf.sprintf "OV%d" i

(* Recherche la variable codant un terme pour Omega et crée la variable dans
   l'environnement si il n'existe pas. Cas ou la variable dans Omega représente
   le terme d'un monome (le plus souvent un atome) *)

let intern_omega env t =
  begin try List.assoc t env.om_vars
  with Not_found -> 
    let v = new_omega_var () in 
    env.om_vars <- (t,v) :: env.om_vars; v
  end

(* Ajout forcé d'un lien entre un terme et une variable  Cas où la
   variable est créée par Omega et où il faut la lier après coup à un atome
   réifié introduit de force *)
let intern_omega_force env t v = env.om_vars <- (t,v) :: env.om_vars

(* Récupère le terme associé à une variable *)
let unintern_omega env id =
  let rec loop = function 
	[] -> failwith "unintern" 
      | ((t,j)::l) -> if id = j then t else loop l in
  loop env.om_vars

(* \subsection{Gestion des environnements de variable pour la réflexion} 
   Gestion des environnements de traduction entre termes des constructions
   non réifiés et variables des termes reifies. Attention il s'agit de 
   l'environnement initial contenant tout. Il faudra le réduire après
   calcul des variables utiles. *)

let add_reified_atom t env =
  try list_index t env.terms
  with Not_found ->
    let i = List.length env.terms in
    env.terms <- env.terms @ [t]; i

let get_reified_atom env = 
  try List.nth env.terms with _ -> failwith "get_reified_atom"

(* \subsection{Gestion de l'environnement de proposition pour Omega} *)
(* ajout d'une proposition *)
let add_prop env t =
  try list_index t env.props
  with Not_found ->
    let i = List.length env.props in  env.props <- env.props @ [t]; i

(* accès a une proposition *)
let get_prop v env = try List.nth v env with _ -> failwith "get_prop"

(* \subsection{Gestion du nommage des équations} *)
(* Ajout d'une equation dans l'environnement de reification *)
let add_equation env e =
  let id = e.e_omega.id in
  try let _ = Hashtbl.find env.equations id in ()
  with Not_found -> Hashtbl.add env.equations id e

(* accès a une equation *)
let get_equation env id = 
  try Hashtbl.find env.equations id
  with e -> Printf.printf "Omega Equation %d non trouvée\n" id; raise e

(* Affichage des termes réifiés *)
let rec oprint ch = function 
  | Oint n -> Printf.fprintf ch "%s" (Bigint.to_string n)
  | Oplus (t1,t2) -> Printf.fprintf ch "(%a + %a)" oprint t1 oprint t2  
  | Omult (t1,t2) -> Printf.fprintf ch "(%a * %a)" oprint t1 oprint t2 
  | Ominus(t1,t2) -> Printf.fprintf ch "(%a - %a)" oprint t1 oprint t2 
  | Oopp t1 ->Printf.fprintf ch "~ %a" oprint t1
  | Oatom n -> Printf.fprintf ch "V%02d" n
  | Oufo x ->  Printf.fprintf ch "?"

let rec pprint ch = function
    Pequa (_,{ e_comp=comp; e_left=t1; e_right=t2 })  ->
      let connector = 
	match comp with 
	  Eq -> "=" | Leq -> "<=" | Geq -> ">="
	| Gt -> ">" | Lt -> "<" | Neq -> "!=" in
      Printf.fprintf ch "%a %s %a" oprint t1 connector oprint t2  
  | Ptrue -> Printf.fprintf ch "TT"
  | Pfalse -> Printf.fprintf ch "FF"
  | Pnot t -> Printf.fprintf ch "not(%a)" pprint t
  | Por (_,t1,t2) -> Printf.fprintf ch "(%a or %a)" pprint t1 pprint t2  
  | Pand(_,t1,t2) -> Printf.fprintf ch "(%a and %a)" pprint t1 pprint t2  
  | Pimp(_,t1,t2) -> Printf.fprintf ch "(%a => %a)" pprint t1 pprint t2  
  | Pprop c -> Printf.fprintf ch "Prop"

let rec weight env = function
  | Oint _ -> -1
  | Oopp c -> weight env c
  | Omult(c,_) -> weight env c
  | Oplus _ -> failwith "weight"
  | Ominus _ -> failwith "weight minus"
  | Oufo _ -> -1
  | Oatom _ as c -> (intern_omega env c)

(* \section{Passage entre oformules et représentation interne de Omega} *)

(* \subsection{Oformula vers Omega} *)

let omega_of_oformula env kind = 
  let rec loop accu = function
    | Oplus(Omult(v,Oint n),r) -> 
	loop ({v=intern_omega env v; c=n} :: accu) r
    | Oint n ->
	let id = new_omega_eq () in
	(*i tag_equation name id; i*)
	{kind = kind; body = List.rev accu; 
	 constant = n; id = id}
    | t -> print_string "CO"; oprint stdout t; failwith "compile_equation" in
  loop []

(* \subsection{Omega vers Oformula} *)

let reified_of_atom env i =
  try Hashtbl.find env.real_indices i
  with Not_found -> 
    Printf.printf "Atome %d non trouvé\n" i; 
    Hashtbl.iter (fun k v -> Printf.printf "%d -> %d\n" k v) env.real_indices;
    raise Not_found

let rec oformula_of_omega env af = 
  let rec loop = function
    | ({v=v; c=n}::r) ->
	Oplus(Omult(unintern_omega env v,Oint n),loop r)
    | [] -> Oint af.constant in
  loop af.body

let app f v = mkApp(Lazy.force f,v)

(* \subsection{Oformula vers COQ reel} *)

let rec coq_of_formula env t =
  let rec loop = function
  | Oplus (t1,t2) -> app coq_Zplus [| loop t1; loop t2 |]
  | Oopp t -> app coq_Zopp [| loop t |]
  | Omult(t1,t2) -> app coq_Zmult [| loop t1; loop t2 |]
  | Oint v ->   mk_Z v
  | Oufo t -> loop t
  | Oatom var ->
      (* attention ne traite pas les nouvelles variables si on ne les
       * met pas dans env.term *)
      get_reified_atom env var
  | Ominus(t1,t2) -> app coq_Zminus [| loop t1; loop t2 |] in
  loop t

(* \subsection{Oformula vers COQ reifié} *)

let rec reified_of_formula env = function
  | Oplus (t1,t2) ->
      app coq_t_plus [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Oopp t ->
      app coq_t_opp [| reified_of_formula env t |]
  | Omult(t1,t2) ->
      app coq_t_mult [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Oint v ->  app coq_t_int [| mk_Z v |]
  | Oufo t -> reified_of_formula env t
  | Oatom i -> app coq_t_var [| mk_nat (reified_of_atom env i) |]
  | Ominus(t1,t2) ->
      app coq_t_minus [| reified_of_formula env t1; reified_of_formula env t2 |]

let reified_of_formula env f =
  begin try reified_of_formula env f with e -> oprint stderr f; raise e end

let rec reified_of_proposition env = function
    Pequa (_,{ e_comp=Eq; e_left=t1; e_right=t2 }) -> 
      app coq_p_eq [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Pequa (_,{ e_comp=Leq; e_left=t1; e_right=t2 }) -> 
      app coq_p_leq [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Pequa(_,{ e_comp=Geq; e_left=t1; e_right=t2 }) -> 
      app coq_p_geq [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Pequa(_,{ e_comp=Gt; e_left=t1; e_right=t2 }) -> 
      app coq_p_gt [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Pequa(_,{ e_comp=Lt; e_left=t1; e_right=t2 }) ->  
      app coq_p_lt [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Pequa(_,{ e_comp=Neq; e_left=t1; e_right=t2 }) -> 
      app coq_p_neq [| reified_of_formula env t1; reified_of_formula env t2 |]
  | Ptrue -> Lazy.force coq_p_true
  | Pfalse -> Lazy.force coq_p_false
  | Pnot t -> 
      app coq_p_not [| reified_of_proposition env t |]
  | Por (_,t1,t2) -> 
      app coq_p_or
	[| reified_of_proposition env t1; reified_of_proposition env t2 |]
  | Pand(_,t1,t2) -> 
      app coq_p_and
	[| reified_of_proposition env t1; reified_of_proposition env t2 |]
  | Pimp(_,t1,t2) -> 
      app coq_p_imp
	[| reified_of_proposition env t1; reified_of_proposition env t2 |]
  | Pprop t -> app coq_p_prop [| mk_nat (add_prop env t) |]

let reified_of_proposition env f =
  begin try reified_of_proposition env f 
  with e -> pprint stderr f; raise e end

(* \subsection{Omega vers COQ réifié} *)

let reified_of_omega env body constant = 
  let coeff_constant = 
    app coq_t_int [| mk_Z constant |] in
  let mk_coeff {c=c; v=v} t =
    let coef = 
      app coq_t_mult 
	[| reified_of_formula env (unintern_omega env v); 
	   app coq_t_int [| mk_Z c |] |] in
    app coq_t_plus [|coef; t |] in
  List.fold_right mk_coeff body coeff_constant

let reified_of_omega env body c  = 
  begin try 
    reified_of_omega env body c 
  with e -> 
    display_eq display_omega_var (body,c); raise e 
  end

(* \section{Opérations sur les équations}
Ces fonctions préparent les traces utilisées par la tactique réfléchie
pour faire des opérations de normalisation sur les équations.  *)

(* \subsection{Extractions des variables d'une équation} *)
(* Extraction des variables d'une équation *)

let rec vars_of_formula = function
  | Oint _ -> []
  | Oplus (e1,e2)  -> (vars_of_formula e1) @ (vars_of_formula e2)
  | Omult (e1,e2)  -> (vars_of_formula e1) @ (vars_of_formula e2)
  | Ominus (e1,e2) -> (vars_of_formula e1) @ (vars_of_formula e2)
  | Oopp e -> (vars_of_formula e)
  | Oatom i -> [i]
  | Oufo _ -> []

let vars_of_equations l =
  let rec loop = function
      e :: l -> vars_of_formula e.e_left @ vars_of_formula e.e_right @ loop l
    | [] -> [] in
  list_uniq (List.sort compare (loop l))

(* \subsection{Multiplication par un scalaire} *)

let rec scalar n = function
   Oplus(t1,t2) -> 
     let tac1,t1' = scalar  n t1 and 
         tac2,t2' = scalar  n t2 in
     do_list [Lazy.force coq_c_mult_plus_distr; do_both tac1 tac2], 
     Oplus(t1',t2')
 | Oopp t ->
     do_list [Lazy.force coq_c_mult_opp_left], Omult(t,Oint(Bigint.neg n))
 | Omult(t1,Oint x) -> 
     do_list [Lazy.force coq_c_mult_assoc_reduced], Omult(t1,Oint (n*x))
 | Omult(t1,t2) -> 
     Util.error "Omega: Can't solve a goal with non-linear products"
 | (Oatom _ as t) -> do_list [], Omult(t,Oint n)
 | Oint i -> do_list [Lazy.force coq_c_reduce],Oint(n*i)
 | (Oufo _ as t)-> do_list [], Oufo (Omult(t,Oint n))
 | Ominus _ -> failwith "scalar minus"

(* \subsection{Propagation de l'inversion} *)

let rec negate = function
   Oplus(t1,t2) -> 
     let tac1,t1' = negate t1 and 
         tac2,t2' = negate t2 in
     do_list [Lazy.force coq_c_opp_plus ; (do_both tac1 tac2)],
     Oplus(t1',t2')
 | Oopp t ->
     do_list [Lazy.force coq_c_opp_opp], t
 | Omult(t1,Oint x) -> 
     do_list [Lazy.force coq_c_opp_mult_r], Omult(t1,Oint (Bigint.neg x))
 | Omult(t1,t2) -> 
     Util.error "Omega: Can't solve a goal with non-linear products"
 | (Oatom _ as t) ->
     do_list [Lazy.force coq_c_opp_one], Omult(t,Oint(negone))
 | Oint i -> do_list [Lazy.force coq_c_reduce] ,Oint(Bigint.neg i)
 | Oufo c -> do_list [], Oufo (Oopp c)
 | Ominus _ -> failwith "negate minus"

let rec norm l = (List.length l)

(* \subsection{Mélange (fusion) de deux équations} *)
(* \subsubsection{Version avec coefficients} *)
let rec shuffle_path k1 e1 k2 e2 =
  let rec loop = function
      (({c=c1;v=v1}::l1) as l1'),
      (({c=c2;v=v2}::l2) as l2') ->
	if v1 = v2 then
          if k1*c1 + k2 * c2 = zero then (
            Lazy.force coq_f_cancel :: loop (l1,l2))
          else (
            Lazy.force coq_f_equal :: loop (l1,l2) )
	else if v1 > v2 then (
	  Lazy.force coq_f_left :: loop(l1,l2'))
	else (
	  Lazy.force coq_f_right :: loop(l1',l2))
    | ({c=c1;v=v1}::l1), [] -> 
	  Lazy.force coq_f_left :: loop(l1,[])
    | [],({c=c2;v=v2}::l2) -> 
	  Lazy.force coq_f_right :: loop([],l2)
    | [],[] -> flush stdout; [] in
  mk_shuffle_list (loop (e1,e2))

(* \subsubsection{Version sans coefficients} *)
let rec shuffle env (t1,t2) = 
  match t1,t2 with
    Oplus(l1,r1), Oplus(l2,r2) ->
      if weight env l1 > weight env l2 then 
	let l_action,t' = shuffle env (r1,t2) in
	do_list [Lazy.force coq_c_plus_assoc_r;do_right l_action], Oplus(l1,t')
      else 
	let l_action,t' = shuffle env (t1,r2) in
	do_list [Lazy.force coq_c_plus_permute;do_right l_action], Oplus(l2,t')
  | Oplus(l1,r1), t2 -> 
      if weight env l1 > weight env t2 then
        let (l_action,t') = shuffle env (r1,t2) in
	do_list [Lazy.force coq_c_plus_assoc_r;do_right l_action],Oplus(l1, t')
      else do_list [Lazy.force coq_c_plus_comm], Oplus(t2,t1)
  | t1,Oplus(l2,r2) -> 
      if weight env l2 > weight env t1 then
        let (l_action,t') = shuffle env (t1,r2) in
	do_list [Lazy.force coq_c_plus_permute;do_right l_action], Oplus(l2,t')
      else do_list [],Oplus(t1,t2)
  | Oint t1,Oint t2 ->
      do_list [Lazy.force coq_c_reduce], Oint(t1+t2)
  | t1,t2 ->
      if weight env t1 < weight env t2 then
	do_list [Lazy.force coq_c_plus_comm], Oplus(t2,t1)
      else do_list [],Oplus(t1,t2)

(* \subsection{Fusion avec réduction} *)

let shrink_pair f1 f2 =
  begin match f1,f2 with
     Oatom v,Oatom _ -> 
       Lazy.force coq_c_red1, Omult(Oatom v,Oint two)
   | Oatom v, Omult(_,c2) -> 
       Lazy.force coq_c_red2, Omult(Oatom v,Oplus(c2,Oint one))
   | Omult (v1,c1),Oatom v -> 
       Lazy.force coq_c_red3, Omult(Oatom v,Oplus(c1,Oint one))
   | Omult (Oatom v,c1),Omult (v2,c2) ->
       Lazy.force coq_c_red4, Omult(Oatom v,Oplus(c1,c2))
   | t1,t2 -> 
       oprint stdout t1; print_newline (); oprint stdout t2; print_newline (); 
       flush Pervasives.stdout; Util.error "shrink.1"
  end

(* \subsection{Calcul d'une sous formule constante} *)

let reduce_factor = function
   Oatom v ->
     let r = Omult(Oatom v,Oint one) in
       [Lazy.force coq_c_red0],r
  | Omult(Oatom v,Oint n) as f -> [],f
  | Omult(Oatom v,c) ->
      let rec compute = function
          Oint n -> n
	| Oplus(t1,t2) -> compute t1 + compute t2 
	| _ -> Util.error "condense.1" in
	[Lazy.force coq_c_reduce], Omult(Oatom v,Oint(compute c))
  | t -> Util.error "reduce_factor.1"

(* \subsection{Réordonnancement} *)

let rec condense env = function
    Oplus(f1,(Oplus(f2,r) as t)) ->
      if weight env f1 = weight env f2 then begin
	let shrink_tac,t = shrink_pair f1 f2 in
	let assoc_tac = Lazy.force coq_c_plus_assoc_l in
	let tac_list,t' = condense env (Oplus(t,r)) in
	assoc_tac :: do_left (do_list [shrink_tac]) :: tac_list, t'
      end else begin
	let tac,f = reduce_factor f1 in
	let tac',t' = condense env t in 
	[do_both (do_list tac) (do_list tac')], Oplus(f,t') 
      end
  | Oplus(f1,Oint n) -> 
      let tac,f1' = reduce_factor f1 in 
      [do_left (do_list tac)],Oplus(f1',Oint n)
  | Oplus(f1,f2) -> 
      if weight env f1 = weight env f2 then begin
	let tac_shrink,t = shrink_pair f1 f2 in
	let tac,t' = condense env t in
	tac_shrink :: tac,t'
      end else begin
	let tac,f = reduce_factor f1 in
	let tac',t' = condense env f2 in 
	[do_both (do_list tac) (do_list tac')],Oplus(f,t') 
      end
  | (Oint _ as t)-> [],t
  | t -> 
      let tac,t' = reduce_factor t in
      let final = Oplus(t',Oint zero) in
      tac @ [Lazy.force coq_c_red6], final

(* \subsection{Elimination des zéros} *)

let rec clear_zero = function
   Oplus(Omult(Oatom v,Oint n),r) when n=zero ->
     let tac',t = clear_zero r in
     Lazy.force coq_c_red5 :: tac',t
  | Oplus(f,r) -> 
      let tac,t = clear_zero r in 
      (if tac = [] then [] else [do_right (do_list tac)]),Oplus(f,t)
  | t -> [],t;;

(* \subsection{Transformation des hypothèses} *)

let rec reduce env = function
    Oplus(t1,t2) ->
      let t1', trace1 = reduce env t1 in
      let t2', trace2 = reduce env t2 in
      let trace3,t' = shuffle env (t1',t2') in
      t', do_list [do_both trace1 trace2; trace3]
  | Ominus(t1,t2) ->
      let t,trace = reduce env (Oplus(t1, Oopp t2)) in
      t, do_list [Lazy.force coq_c_minus; trace]
  | Omult(t1,t2) as t ->
      let t1', trace1 = reduce env t1 in
      let t2', trace2 = reduce env t2 in
      begin match t1',t2' with
      | (_, Oint n) ->
	  let tac,t' = scalar n t1' in
	  t', do_list [do_both trace1 trace2; tac]
      | (Oint n,_) ->
	  let tac,t' = scalar n t2' in
	  t', do_list [do_both trace1 trace2; Lazy.force coq_c_mult_comm; tac]
      | _ -> Oufo t, Lazy.force coq_c_nop
      end
  | Oopp t ->
      let t',trace = reduce env  t in
      let trace',t'' = negate t' in
      t'', do_list [do_left trace; trace']
  | (Oint _ | Oatom _ | Oufo _) as t -> t, Lazy.force coq_c_nop

let normalize_linear_term env t =
  let t1,trace1 = reduce env t in
  let trace2,t2 = condense env t1 in
  let trace3,t3 = clear_zero t2 in
  do_list [trace1; do_list trace2; do_list trace3], t3

(* Cette fonction reproduit très exactement le comportement de [p_invert] *)
let negate_oper = function
    Eq -> Neq | Neq -> Eq | Leq -> Gt | Geq -> Lt | Lt -> Geq | Gt -> Leq
 
let normalize_equation env (negated,depends,origin,path) (oper,t1,t2) = 
  let mk_step t1 t2 f kind =
    let t = f t1 t2 in
    let trace, oterm = normalize_linear_term env t in
    let equa = omega_of_oformula env kind oterm in 
    { e_comp = oper; e_left = t1; e_right = t2; 
      e_negated = negated; e_depends = depends; 
      e_origin = { o_hyp = origin; o_path = List.rev path };
      e_trace = trace; e_omega = equa } in
  try match (if negated then (negate_oper oper) else oper) with
    | Eq  -> mk_step t1 t2 (fun o1 o2 -> Oplus (o1,Oopp o2)) EQUA
    | Neq -> mk_step t1 t2 (fun o1 o2 -> Oplus (o1,Oopp o2)) DISE
    | Leq -> mk_step t1 t2 (fun o1 o2 -> Oplus (o2,Oopp o1)) INEQ
    | Geq -> mk_step t1 t2 (fun o1 o2 -> Oplus (o1,Oopp o2)) INEQ
    | Lt  ->
        mk_step t1 t2 (fun o1 o2 -> Oplus (Oplus(o2,Oint negone),Oopp o1))
	  INEQ
    | Gt ->
        mk_step t1 t2 (fun o1 o2 -> Oplus (Oplus(o1,Oint negone),Oopp o2)) 
	  INEQ
  with e when Logic.catchable_exception e -> raise e

(* \section{Compilation des hypothèses} *)

let is_scalar t =
  let rec aux t = match destructurate t with
    | Kapp(("Zplus"|"Zminus"|"Zmult"),[t1;t2]) -> aux t1 & aux t2
    | Kapp(("Zopp"|"Zsucc"),[t]) -> aux t
    | Kapp(("Zpos"|"Zneg"|"Z0"),_) -> let _ = recognize_number t in true
    | _ -> false in
  try aux t with _ -> false

let rec oformula_of_constr env t =
  try match destructurate t with
  | Kapp("Zplus",[t1;t2]) -> binop env (fun x y -> Oplus(x,y)) t1 t2
  | Kapp("Zminus",[t1;t2]) -> binop env (fun x y -> Ominus(x,y)) t1 t2
  | Kapp("Zmult",[t1;t2]) when is_scalar t1 or is_scalar t2 ->
      binop env (fun x y -> Omult(x,y)) t1 t2
  | Kapp("Zopp",[t]) -> Oopp(oformula_of_constr env t)
  | Kapp("Zsucc",[t]) -> Oplus(oformula_of_constr env t, Oint one)
  | Kapp(("Zpos"|"Zneg"|"Z0"),_) -> 
      begin try Oint(recognize_number t)
      with _ -> Oatom (add_reified_atom t env) end
  | _ -> 
      Oatom (add_reified_atom t env)
  with e when Logic.catchable_exception e ->
    Oatom (add_reified_atom t env)

and  binop env c t1 t2 = 
    let t1' = oformula_of_constr env t1 in
    let t2' = oformula_of_constr env t2 in
    c t1' t2'

and  binprop env (neg2,depends,origin,path) 
             add_to_depends neg1 gl c t1 t2 =
  let i = new_connector_id env in
  let depends1 = if add_to_depends then Left i::depends else depends in
  let depends2 = if add_to_depends then Right i::depends else depends in
  if add_to_depends then
    Hashtbl.add env.constructors i {o_hyp = origin; o_path = List.rev path};
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
  let omega = normalize_equation env ctxt (connector,t1',t2') in
  add_equation env omega;
  Pequa (c,omega)

and oproposition_of_constr env ((negated,depends,origin,path) as ctxt) gl c = 
  try match destructurate c with
    | Kapp("eq",[typ;t1;t2]) 
      when destructurate (Tacmach.pf_nf gl typ) = Kapp("Z",[]) ->
         mk_equation env ctxt c Eq t1 t2
    | Kapp("Zne",[t1;t2]) -> 
	mk_equation env ctxt c Neq t1 t2
    | Kapp("Zle",[t1;t2]) -> 
	mk_equation env ctxt c Leq t1 t2
    | Kapp("Zlt",[t1;t2]) -> 
	mk_equation env ctxt c Lt t1 t2
    | Kapp("Zge",[t1;t2]) -> 
	mk_equation env ctxt c Geq t1 t2
    | Kapp("Zgt",[t1;t2]) -> 
	mk_equation env ctxt c Gt t1 t2
    | Kapp("True",[]) -> Ptrue
    | Kapp("False",[]) -> Pfalse
    | Kapp("not",[t]) ->
       let t' = 
	 oproposition_of_constr 
	   env (not negated, depends, origin,(O_mono::path)) gl t in 
       Pnot t'
    | Kapp("or",[t1;t2]) ->  
	binprop env ctxt (not negated) negated gl (fun i x y -> Por(i,x,y)) t1 t2
    | Kapp("and",[t1;t2]) ->
	binprop env ctxt negated negated gl
	  (fun i x y -> Pand(i,x,y)) t1 t2
    | Kimp(t1,t2) ->
	binprop env ctxt (not negated) (not negated) gl 
	  (fun i x y -> Pimp(i,x,y)) t1 t2
    | _ -> Pprop c
  with e when Logic.catchable_exception e -> Pprop c

(* Destructuration des hypothèses et de la conclusion *)

let reify_gl env gl =
  let concl = Tacmach.pf_concl gl in
  let t_concl =
    Pnot (oproposition_of_constr env (true,[],id_concl,[O_mono]) gl concl) in
  if !debug then begin
    Printf.printf "REIFED PROBLEM\n\n";
    Printf.printf "  CONCL: "; pprint stdout t_concl; Printf.printf "\n"
  end;
  let rec loop = function
      (i,t) :: lhyps ->
	let t' = oproposition_of_constr env (false,[],i,[]) gl t in
	if !debug then begin
	  Printf.printf "  %s: " (Names.string_of_id i);
	  pprint stdout t';
	  Printf.printf "\n"
	end;
	(i,t') :: loop lhyps
    | [] -> 
	if !debug then print_env_reification env; 
	[] in
  let t_lhyps = loop (Tacmach.pf_hyps_types gl) in
  (id_concl,t_concl) :: t_lhyps 

let rec destructurate_pos_hyp orig list_equations list_depends = function
  | Pequa (_,e) -> [e :: list_equations]
  | Ptrue | Pfalse | Pprop _ -> [list_equations]
  | Pnot t -> destructurate_neg_hyp orig list_equations list_depends t
  | Por (i,t1,t2) -> 
      let s1 = 
	destructurate_pos_hyp orig list_equations (i::list_depends) t1 in
      let s2 = 
	destructurate_pos_hyp orig list_equations (i::list_depends) t2 in
      s1 @ s2
  | Pand(i,t1,t2) -> 
      let list_s1 =
	destructurate_pos_hyp orig list_equations (list_depends) t1 in
      let rec loop = function 
	  le1 :: ll -> destructurate_pos_hyp orig le1 list_depends t2 @ loop ll
	| [] -> [] in
      loop list_s1
  | Pimp(i,t1,t2) -> 
      let s1 =
	destructurate_neg_hyp orig list_equations (i::list_depends) t1 in
      let s2 =
	destructurate_pos_hyp orig list_equations (i::list_depends) t2 in
      s1 @ s2

and destructurate_neg_hyp orig list_equations list_depends = function
  | Pequa (_,e) -> [e :: list_equations]
  | Ptrue | Pfalse | Pprop _ -> [list_equations]
  | Pnot t -> destructurate_pos_hyp orig list_equations list_depends t
  | Pand (i,t1,t2) -> 
      let s1 =
	destructurate_neg_hyp orig list_equations (i::list_depends) t1 in
      let s2 =
	destructurate_neg_hyp orig list_equations (i::list_depends) t2 in
      s1 @ s2
  | Por(_,t1,t2) -> 
      let list_s1 =
	destructurate_neg_hyp orig list_equations list_depends t1 in
      let rec loop = function 
	  le1 :: ll -> destructurate_neg_hyp orig le1 list_depends t2 @ loop ll
	| [] -> [] in
      loop list_s1
  | Pimp(_,t1,t2) -> 
      let list_s1 =
	destructurate_pos_hyp orig list_equations list_depends t1 in
      let rec loop = function 
	  le1 :: ll -> destructurate_neg_hyp orig le1 list_depends t2 @ loop ll
	| [] -> [] in
      loop list_s1

let destructurate_hyps syst =
  let rec loop = function
      (i,t) :: l -> 
	let l_syst1 = destructurate_pos_hyp i []  [] t in
	let l_syst2 = loop l in
	cartesien l_syst1 l_syst2
    | [] -> [[]] in
  loop syst

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
    pprint stdout (Pequa (Lazy.force coq_c_nop,oformula_eq)); print_newline ();
    display_omega oformula_eq.e_omega;
    Printf.printf "  Depends on:"; 
    List.iter display_depend oformula_eq.e_depends;
    Printf.printf "\n  Path: %s" 
      (String.concat ""
	 (List.map (function O_left -> "L" | O_right -> "R" | O_mono -> "M")
	    oformula_eq.e_origin.o_path));
    Printf.printf "\n  Origin: %s (negated : %s)\n\n"
      (Names.string_of_id oformula_eq.e_origin.o_hyp)
      (if oformula_eq.e_negated then "yes" else "no") in

  let display_system syst =
    Printf.printf "=SYSTEM===================================\n";
    List.iter display_equation syst in
  List.iter display_system syst_list

(* Extraction des prédicats utilisées dans une trace. Permet ensuite le
   calcul des hypothèses *)

let rec hyps_used_in_trace = function
  | act :: l -> 
      begin match act with
	| HYP e -> e.id :: hyps_used_in_trace l
	| SPLIT_INEQ (_,(_,act1),(_,act2)) -> 
	    hyps_used_in_trace act1 @ hyps_used_in_trace act2
	| _ -> hyps_used_in_trace l
      end
  | [] -> []

(* Extraction des variables déclarées dans une équation. Permet ensuite
   de les déclarer dans l'environnement de la procédure réflexive et
   éviter les créations de variable au vol *)

let rec variable_stated_in_trace = function
  | act :: l -> 
      begin match act with
	| STATE action ->
	    (*i nlle_equa: afine, def: afine, eq_orig: afine, i*)
            (*i coef: int, var:int                            i*)
	    action :: variable_stated_in_trace l
	| SPLIT_INEQ (_,(_,act1),(_,act2)) -> 
	    variable_stated_in_trace act1 @ variable_stated_in_trace act2
	| _ -> variable_stated_in_trace l
      end
  | [] -> []
;;

let add_stated_equations env tree = 
  let rec loop = function
      Tree(_,t1,t2) -> 
	list_union (loop t1) (loop t2)
    | Leaf s -> variable_stated_in_trace s.s_trace in
  (* Il faut trier les variables par ordre d'introduction pour ne pas risquer
     de définir dans le mauvais ordre *)
  let stated_equations = 
    List.sort (fun x y -> Pervasives.(-) x.st_var y.st_var) (loop tree) in
  let add_env st = 
    (* On retransforme la définition de v en formule reifiée *)
    let v_def = oformula_of_omega env st.st_def in
    (* Notez que si l'ordre de création des variables n'est pas respecté, 
     * ca va planter *)
    let coq_v = coq_of_formula env v_def in
    let v = add_reified_atom coq_v env in
    (* Le terme qu'il va falloir introduire *)
    let term_to_generalize = app coq_refl_equal [|Lazy.force coq_Z; coq_v|] in
    (* sa représentation sous forme d'équation mais non réifié car on n'a pas
     * l'environnement pour le faire correctement *)
    let term_to_reify = (v_def,Oatom v) in
    (* enregistre le lien entre la variable omega et la variable Coq *)
    intern_omega_force env (Oatom v) st.st_var; 
    (v, term_to_generalize,term_to_reify,st.st_def.id) in
 List.map add_env stated_equations

(* Calcule la liste des éclatements à réaliser sur les hypothèses 
   nécessaires pour extraire une liste d'équations donnée *)

let rec get_eclatement env = function
    i :: r -> 
      let l = try (get_equation env i).e_depends with Not_found -> [] in
      list_union l (get_eclatement env r)
  | [] -> []

let select_smaller l = 
  let comp (_,x) (_,y) = Pervasives.(-) (List.length x) (List.length y) in
  try List.hd (List.sort comp l) with Failure _ -> failwith "select_smaller"

let filter_compatible_systems required systems =
  let rec select = function
      (x::l) -> 
	if List.mem x required then select l
	else if List.mem (barre x) required then raise Exit 
	else x :: select l
    | [] -> [] in
  map_exc (function (sol,splits) -> (sol,select splits)) systems

let rec equas_of_solution_tree = function
    Tree(_,t1,t2) -> 
      list_union (equas_of_solution_tree t1) (equas_of_solution_tree t2)
  | Leaf s -> s.s_equa_deps


(* Because of really_useful_prop, decidable formulas such as Pfalse
   and Ptrue are moved to Pprop, thus breaking the decidability check
   in ReflOmegaCore.concl_to_hyp... *)

let really_useful_prop l_equa c =
  let rec real_of = function
      Pequa(t,_) -> t
    | Ptrue ->  app  coq_True [||]
    | Pfalse -> app  coq_False [||]
    | Pnot t1 -> app coq_not [|real_of t1|]
    | Por(_,t1,t2) -> app coq_or [|real_of t1; real_of t2|]
    | Pand(_,t1,t2) -> app coq_and [|real_of t1; real_of t2|]
    (* Attention : implications sur le lifting des variables à comprendre ! *)
    | Pimp(_,t1,t2) -> Term.mkArrow (real_of t1) (real_of t2)
    | Pprop t -> t in
  let rec loop c = 
    match c with 
      Pequa(_,e) ->
	if List.mem e.e_omega.id l_equa then Some c else None
    | Ptrue -> None
    | Pfalse -> None
    | Pnot t1 -> 
	begin match loop t1 with None -> None | Some t1' -> Some (Pnot t1') end
    | Por(i,t1,t2) -> binop (fun (t1,t2) -> Por(i,t1,t2)) t1 t2
    | Pand(i,t1,t2) -> binop (fun (t1,t2) -> Pand(i,t1,t2)) t1 t2
    | Pimp(i,t1,t2) -> binop (fun (t1,t2) -> Pimp(i,t1,t2)) t1 t2
    | Pprop t -> None
  and binop f t1 t2 = 
    begin match loop t1, loop t2 with
      None, None -> None 
    | Some t1',Some t2' -> Some (f(t1',t2'))
    | Some t1',None -> Some (f(t1',Pprop (real_of t2)))
    | None,Some t2' -> Some (f(Pprop (real_of t1),t2'))
    end in
  match loop c with
    None -> Pprop (real_of c)
  | Some t -> t

let rec display_solution_tree ch = function
    Leaf t -> 
      output_string ch 
       (Printf.sprintf "%d[%s]" 
	 t.s_index
         (String.concat " " (List.map string_of_int t.s_equa_deps)))
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
    with e ->  
      Printf.printf "%d - %d\n" 
	(List.length weighted) (List.length all_solutions);
      List.iter display_depend path; raise e in
  build_tree winner_sol (List.rev path) winner_deps 

let find_path {o_hyp=id;o_path=p} env = 
  let rec loop_path = function
      ([],l) -> Some l
    | (x1::l1,x2::l2) when x1 = x2 -> loop_path (l1,l2)
    | _ -> None in
  let rec loop_id i = function
      CCHyp{o_hyp=id';o_path=p'} :: l when id = id' ->
	begin match loop_path (p',p) with
	  Some r -> i,r
	| None -> loop_id (succ i) l
	end
    | _ :: l -> loop_id (succ i) l
    | [] -> failwith "find_path" in
  loop_id 0 env

let mk_direction_list l = 
  let trans = function 
      O_left -> coq_d_left | O_right -> coq_d_right | O_mono -> coq_d_mono in
  mk_list (Lazy.force coq_direction) (List.map (fun d-> Lazy.force(trans d)) l)


(* \section{Rejouer l'historique} *)

let get_hyp env_hyp i =
  try list_index (CCEqua i) env_hyp
  with Not_found -> failwith (Printf.sprintf "get_hyp %d" i)

let replay_history env env_hyp =
  let rec loop env_hyp t =
    match t with
      | CONTRADICTION (e1,e2) :: l -> 
	  let trace = mk_nat (List.length e1.body) in
	  mkApp (Lazy.force coq_s_contradiction,
		 [| trace ; mk_nat (get_hyp env_hyp e1.id); 
		    mk_nat (get_hyp env_hyp e2.id) |])
      | DIVIDE_AND_APPROX (e1,e2,k,d) :: l ->
	  mkApp (Lazy.force coq_s_div_approx,
		 [| mk_Z k; mk_Z d; 
		    reified_of_omega env e2.body e2.constant;
		    mk_nat (List.length e2.body); 
		    loop env_hyp l; mk_nat (get_hyp env_hyp e1.id) |])
      | NOT_EXACT_DIVIDE (e1,k) :: l ->
	  let e2_constant = floor_div e1.constant k in
	  let d = e1.constant - e2_constant * k in
	  let e2_body = map_eq_linear (fun c -> c / k) e1.body in
          mkApp (Lazy.force coq_s_not_exact_divide,
		 [|mk_Z k; mk_Z d; 
		   reified_of_omega env e2_body e2_constant; 
		   mk_nat (List.length e2_body); 
		   mk_nat (get_hyp env_hyp e1.id)|])
      | EXACT_DIVIDE (e1,k) :: l ->
	  let e2_body =  
	    map_eq_linear (fun c -> c / k) e1.body in
	  let e2_constant = floor_div e1.constant k in
          mkApp (Lazy.force coq_s_exact_divide,
		 [|mk_Z k; 
		   reified_of_omega env e2_body e2_constant; 
		   mk_nat (List.length e2_body);
		   loop env_hyp l; mk_nat (get_hyp env_hyp e1.id)|])
      | (MERGE_EQ(e3,e1,e2)) :: l ->
	  let n1 = get_hyp env_hyp e1.id and n2 = get_hyp env_hyp e2 in
          mkApp (Lazy.force coq_s_merge_eq,
		 [| mk_nat (List.length e1.body);
		    mk_nat n1; mk_nat n2;
		    loop (CCEqua e3:: env_hyp) l |])
      | SUM(e3,(k1,e1),(k2,e2)) :: l ->
	  let n1 = get_hyp env_hyp e1.id 
	  and n2 = get_hyp env_hyp e2.id in
	  let trace = shuffle_path k1 e1.body k2 e2.body in
          mkApp (Lazy.force coq_s_sum,
		 [| mk_Z k1; mk_nat n1; mk_Z k2;
		    mk_nat n2; trace; (loop (CCEqua e3 :: env_hyp) l) |])
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
	  let v = unintern_omega env sigma in
	  let o_def = oformula_of_omega env def in
	  let o_orig = oformula_of_omega env orig in
	  let body =
	     Oplus (o_orig,Omult (Oplus (Oopp v,o_def), Oint m)) in
          let trace,_ = normalize_linear_term env body in
	  mkApp (Lazy.force coq_s_state,
		 [| mk_Z m; trace; mk_nat n1; mk_nat n2; 
		    loop (CCEqua new_eq.id :: env_hyp) l |])
      |	HYP _ :: l -> loop env_hyp l
      |	CONSTANT_NUL e :: l ->
	  mkApp (Lazy.force coq_s_constant_nul, 
		 [|  mk_nat (get_hyp env_hyp e) |])
      |	NEGATE_CONTRADICT(e1,e2,b) :: l ->
	  mkApp (Lazy.force coq_s_negate_contradict, 
		 [|  mk_nat (get_hyp env_hyp e1.id);
		     mk_nat (get_hyp env_hyp e2.id) |])
      | SPLIT_INEQ(e,(e1,l1),(e2,l2)) :: l ->
	  let i =  get_hyp env_hyp e.id in
	  let r1 = loop (CCEqua e1 :: env_hyp) l1 in
	  let r2 = loop (CCEqua e2 :: env_hyp) l2 in
	  mkApp (Lazy.force coq_s_split_ineq, 
                  [| mk_nat (List.length e.body); mk_nat i; r1 ; r2 |])
      |	(FORGET_C _ | FORGET _ | FORGET_I _) :: l ->
	  loop env_hyp l
      | (WEAKEN  _ ) :: l -> failwith "not_treated"
      |	[] -> failwith "no contradiction"
  in loop env_hyp

let rec decompose_tree env ctxt = function
   Tree(i,left,right) ->
     let org = 
       try Hashtbl.find env.constructors i 
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
      decompose_tree_hyps s.s_trace env ctxt  s.s_equa_deps
and decompose_tree_hyps trace env ctxt = function
    [] -> app coq_e_solve [| replay_history env ctxt trace |]
  | (i::l) -> 
      let equation =
        try Hashtbl.find env.equations i 
        with Not_found ->
	  failwith (Printf.sprintf "Cannot find equation %d" i) in
      let (index,path) = find_path equation.e_origin ctxt in
      let full_path = if equation.e_negated then path @ [O_mono] else path in
      let cont = 
	decompose_tree_hyps trace env 
	   (CCEqua equation.e_omega.id :: ctxt) l in
      app coq_e_extract [|mk_nat index;
			  mk_direction_list full_path;
			  cont |]

(* \section{La fonction principale} *)
 (* Cette fonction construit la
trace pour la procédure de décision réflexive.  A partir des résultats
de l'extraction des systèmes, elle lance la résolution par Omega, puis
l'extraction d'un ensemble minimal de solutions permettant la
résolution globale du système et enfin construit la trace qui permet
de faire rejouer cette solution par la tactique réflexive. *)

let resolution env full_reified_goal systems_list =
  let num = ref 0 in
  let solve_system list_eq = 
    let index = !num in
    let system = List.map (fun eq -> eq.e_omega) list_eq in
    let trace = 
      simplify_strong 
	(new_omega_eq,new_omega_var,display_omega_var) 
	system in 
    (* calcule les hypotheses utilisées pour la solution *)
    let vars = hyps_used_in_trace trace in
    let splits = get_eclatement env vars in
    if !debug then begin
      Printf.printf "SYSTEME %d\n" index;
      display_action display_omega_var trace;
      print_string "\n  Depend :";
      List.iter (fun i -> Printf.printf " %d" i) vars;
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
  (* calcule la liste de toutes les hypothèses utilisées dans l'arbre de solution *)
  let useful_equa_id = list_uniq (equas_of_solution_tree solution_tree) in
  (* recupere explicitement ces equations *)
  let equations = List.map (get_equation env) useful_equa_id in
  let l_hyps' = list_uniq (List.map (fun e -> e.e_origin.o_hyp) equations) in
  let l_hyps = id_concl :: list_remove id_concl l_hyps' in
  let useful_hyps =
    List.map (fun id -> List.assoc id full_reified_goal) l_hyps in
  let useful_vars = vars_of_equations equations in
  (* variables a introduire *)
  let to_introduce = add_stated_equations env solution_tree in
  let stated_vars =  List.map (fun (v,_,_,_) -> v) to_introduce in
  let l_generalize_arg = List.map (fun (_,t,_,_) -> t) to_introduce in
  let hyp_stated_vars = List.map (fun (_,_,_,id) -> CCEqua id) to_introduce in
  (* L'environnement de base se construit en deux morceaux :
     - les variables des équations utiles
     - les nouvelles variables declarées durant les preuves *)
  let all_vars_env = useful_vars @ stated_vars in
  let basic_env =
    let rec loop i = function
	var :: l -> 
	  let t = get_reified_atom env var in 
	  Hashtbl.add env.real_indices var i; t :: loop (succ i) l
      |	[] -> [] in
    loop 0 all_vars_env in
  let env_terms_reified = mk_list (Lazy.force coq_Z) basic_env in
  (* On peut maintenant généraliser le but : env est a jour *)
  let l_reified_stated =
     List.map (fun (_,_,(l,r),_) -> 
                 app coq_p_eq [| reified_of_formula env l; 
                                 reified_of_formula env r |])
              to_introduce in
  let reified_concl = 
    match useful_hyps with
      (Pnot p) :: _ ->
	reified_of_proposition env (really_useful_prop useful_equa_id p)
    | _ ->  reified_of_proposition env Pfalse in
  let l_reified_terms =
    (List.map
      (fun p ->
         reified_of_proposition env (really_useful_prop useful_equa_id p))
      (List.tl useful_hyps)) in
  let env_props_reified = mk_plist env.props in
  let reified_goal = 
    mk_list (Lazy.force coq_proposition)
            (l_reified_stated @ l_reified_terms) in
  let reified = 
    app coq_interp_sequent 
       [| reified_concl;env_props_reified;env_terms_reified;reified_goal|] in
  let normalize_equation e = 
    let rec loop = function
	[] -> app (if e.e_negated then coq_p_invert else coq_p_step)
	          [| e.e_trace |]
      |	((O_left | O_mono) :: l) -> app coq_p_left [| loop l |]
      |	(O_right :: l) -> app coq_p_right [| loop l |] in
    app coq_pair_step 
        [| mk_nat (list_index e.e_origin.o_hyp l_hyps) ;
	   loop e.e_origin.o_path |] in
  let normalization_trace =
    mk_list (Lazy.force coq_h_step) (List.map normalize_equation equations) in

  let initial_context =
    List.map (fun id -> CCHyp{o_hyp=id;o_path=[]}) (List.tl l_hyps) in
  let context = 
    CCHyp{o_hyp=id_concl;o_path=[]} :: hyp_stated_vars @ initial_context in
  let decompose_tactic = decompose_tree env context solution_tree in

  Tactics.generalize 
    (l_generalize_arg @ List.map Term.mkVar (List.tl l_hyps)) >>
  Tactics.change_in_concl None reified >> 
  Tactics.apply (app coq_do_omega [|decompose_tactic; normalization_trace|]) >>
  show_goal >>
  Tactics.normalise_in_concl >>
  Tactics.apply (Lazy.force coq_I)

let total_reflexive_omega_tactic gl = 
  Coqlib.check_required_library ["Coq";"romega";"ROmega"];
  rst_omega_eq (); 
  rst_omega_var ();
  try
  let env = new_environment () in
  let full_reified_goal = reify_gl env gl in
  let systems_list = destructurate_hyps full_reified_goal in
  if !debug then display_systems systems_list;
  resolution env full_reified_goal systems_list gl
  with NO_CONTRADICTION -> Util.error "ROmega can't solve this system"


(*i let tester = Tacmach.hide_atomic_tactic "TestOmega" test_tactic i*)


