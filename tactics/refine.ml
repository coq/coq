(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* JCF -- 6 janvier 1998  EXPERIMENTAL *)

(*
 *  L'idée est, en quelque sorte, d'avoir de "vraies" métavariables
 *  dans Coq, c'est-à-dire de donner des preuves incomplètes -- mais
 *  où les trous sont typés -- et que les sous-buts correspondants
 *  soient engendrés pour finir la preuve.
 *
 *  Exemple : 
 *    J'ai le but
 *        (x:nat) { y:nat | (minus y x) = x }
 *    et je donne la preuve incomplète
 *        [x:nat](exist nat [y:nat]((minus y x)=x) (plus x x) ?)
 *    ce qui engendre le but
 *        (minus (plus x x) x)=x
 *)

(*  Pour cela, on procède de la manière suivante :
 *
 *  1. Un terme de preuve incomplet est un terme contenant des variables
 *     existentielles Evar i.e. "?" en syntaxe concrète.
 *     La résolution de ces variables n'est plus nécessairement totale
 *     (ise_resolve called with fail_evar=false) et les variables
 *     existentielles restantes sont remplacées par des méta-variables
 *     castées par leur types (celui est connu : soit donné, soit trouvé
 *     pendant la phase de résolution).
 *
 *  2. On met ensuite le terme "à plat" i.e. on n'autorise des MV qu'au
 *     permier niveau et pour chacune d'elles, si nécessaire, on donne
 *     à son tour un terme de preuve incomplet pour la résoudre.
 *     Exemple: le terme (f a ? [x:nat](e ?)) donne
 *         (f a ?1 ?2) avec ?2 => [x:nat]?3 et ?3 => (e ?4)
 *         ?1 et ?4 donneront des buts
 *
 *  3. On écrit ensuite une tactique tcc qui engendre les sous-buts
 *     à partir d'une preuve incomplète.
 *)

open Pp
open Util
open Names
open Term
open Termops
open Tacmach
open Sign
open Environ
open Reduction
open Typing
open Tactics
open Tacticals
open Printer

type term_with_holes = TH of constr * metamap * sg_proofs
and  sg_proofs       = (term_with_holes option) list

(* pour debugger *)

let rec pp_th (TH(c,mm,sg)) =
  (str"TH=[ " ++ hov 0 (prterm c ++ fnl () ++
			      (* pp_mm mm ++ fnl () ++ *)
			   pp_sg sg) ++ str "]")
and pp_mm l =
  hov 0 (prlist_with_sep (fun _ -> (fnl ())) 
	   (fun (n,c) -> (int n ++ str" --> " ++ prterm c)) l)
and pp_sg sg =
  hov 0 (prlist_with_sep (fun _ -> (fnl ()))
	   (function None -> (str"None") | Some th -> (pp_th th)) sg)
     
(*  compute_metamap : constr -> 'a evar_map -> term_with_holes
 *  réalise le 2. ci-dessus
 *
 *  Pour cela, on renvoie une meta_map qui indique pour chaque meta-variable
 *  si elle correspond à un but (None) ou si elle réduite à son tour
 *  par un terme de preuve incomplet (Some c).
 *
 *  On a donc l'INVARIANT suivant : le terme c rendu est "de niveau 1"
 *  -- i.e. à plat -- et la meta_map contient autant d'éléments qu'il y 
 *  a de meta-variables dans c. On suppose de plus que l'ordre dans la
 *  meta_map correspond à celui des buts qui seront engendrés par le refine.
 *)

let replace_by_meta env gmm = function
  | TH (m, mm, sgp) when isMeta (strip_outer_cast m) -> m,mm,sgp
  | (TH (c,mm,_)) as th ->
      let n = Clenv.new_meta() in
      let m = mkMeta n in
      (* quand on introduit une mv on calcule son type *)
      let ty = match kind_of_term c with
	| Lambda (Name id,c1,c2) when isCast c2 ->
	    mkNamedProd id c1 (snd (destCast c2))
	| Lambda (Anonymous,c1,c2) when isCast c2 ->
	    mkArrow c1 (snd (destCast c2))
	| _ -> (* (App _ | Case _) -> *)
	    Retyping.get_type_of_with_meta env Evd.empty (gmm@mm) c
	(*
	| Fix ((_,j),(v,_,_)) ->
	    v.(j) (* en pleine confiance ! *)
	| _ -> invalid_arg "Tcc.replace_by_meta (TO DO)" 
        *)
      in
      mkCast (m,ty),[n,ty],[Some th]

exception NoMeta

let replace_in_array env gmm a =
  if array_for_all (function (TH (_,_,[])) -> true | _ -> false) a then
    raise NoMeta;
  let a' = Array.map (function
			| (TH (c,mm,[])) -> c,mm,[]
			| th -> replace_by_meta env gmm th) a 
  in
  let v' = Array.map (fun (x,_,_) -> x) a' in
  let mm = Array.fold_left (@) [] (Array.map (fun (_,x,_) -> x) a') in
  let sgp = Array.fold_left (@) [] (Array.map (fun (_,_,x) -> x) a') in
  v',mm,sgp
    
let fresh env n =
  let id = match n with Name x -> x | _ -> id_of_string "_" in
  next_global_ident_away true id (ids_of_named_context (named_context env))

let rec compute_metamap env gmm c = match kind_of_term c with
  (* le terme est directement une preuve *)
  | (Const _ | Evar _ | Ind _ | Construct _ |
    Sort _ | Var _ | Rel _) -> 
      TH (c,[],[])
  (* le terme est une mv => un but *)
  | Meta n ->
      (* 
      Pp.warning (Printf.sprintf ("compute_metamap: MV(%d) sans type !\n") n);
      let ty = Retyping.get_type_of_with_meta env Evd.empty lmeta c in 
      *)
      TH (c,[],[None])
  | Cast (m,ty) when isMeta m -> 
      TH (c,[destMeta m,ty],[None])

  (* abstraction => il faut décomposer si le terme dessous n'est pas pur
   *    attention : dans ce cas il faut remplacer (Rel 1) par (Var x)
   *    où x est une variable FRAICHE *)
  | Lambda (name,c1,c2) ->
      let v = fresh env name in
      let env' = push_named (v,None,c1) env in
      begin match compute_metamap env' gmm (subst1 (mkVar v) c2) with
	(* terme de preuve complet *)
	| TH (_,_,[]) -> TH (c,[],[])
	(* terme de preuve incomplet *)    
	| th ->
	    let m,mm,sgp = replace_by_meta env' gmm th in
	    TH (mkLambda (Name v,c1,m), mm, sgp)
      end

  | LetIn (name, c1, t1, c2) ->
      if occur_meta c1 then 
	error "Refine: body of let-in cannot contain existentials";
      let v = fresh env name in
      let env' = push_named (v,Some c1,t1) env in
      begin match compute_metamap env' gmm (subst1 (mkVar v) c2) with
	(* terme de preuve complet *)
	| TH (_,_,[]) -> TH (c,[],[])
	(* terme de preuve incomplet *)    
	| th ->
	    let m,mm,sgp = replace_by_meta env' gmm th in
	    TH (mkLetIn (Name v,c1,t1,m), mm, sgp)
      end

  (* 4. Application *)
  | App (f,v) ->
      let a = Array.map (compute_metamap env gmm) (Array.append [|f|] v) in
      begin
	try
	  let v',mm,sgp = replace_in_array env gmm a in
          let v'' = Array.sub v' 1 (Array.length v) in
          TH (mkApp(v'.(0), v''),mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end

  | Case (ci,p,cc,v) ->
      (* bof... *)
      let nbr = Array.length v in
      let v = Array.append [|p;cc|] v in
      let a = Array.map (compute_metamap env gmm) v in
      begin
	try
	  let v',mm,sgp = replace_in_array env gmm a in
	  let v'' = Array.sub v' 2 nbr in
	  TH (mkCase (ci,v'.(0),v'.(1),v''),mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end

  (* 5. Fix. *)
  | Fix ((ni,i),(fi,ai,v)) ->
      (* TODO: use a fold *)
      let vi = Array.map (fresh env) fi in
      let fi' = Array.map (fun id -> Name id) vi in
      let env' = push_named_rec_types (fi',ai,v) env in
      let a = Array.map
		(compute_metamap env' gmm)
		(Array.map (substl (List.map mkVar (Array.to_list vi))) v) 
      in
      begin
	try
	  let v',mm,sgp = replace_in_array env' gmm a in
	  let fix = mkFix ((ni,i),(fi',ai,v')) in
	  TH (fix,mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end
	      
  (* Cast. Est-ce bien exact ? *)
  | Cast (c,t) -> compute_metamap env gmm c
      (*let TH (c',mm,sgp) = compute_metamap sign c in
	TH (mkCast (c',t),mm,sgp) *)
      
  (* Produit. Est-ce bien exact ? *)
  | Prod (_,_,_) ->
      if occur_meta c then
	error "Refine: proof term contains metas in a product"
      else
      	TH (c,[],[])

  (* Cofix. *)
  | CoFix (i,(fi,ai,v)) ->
      let vi = Array.map (fresh env) fi in
      let fi' = Array.map (fun id -> Name id) vi in
      let env' = push_named_rec_types (fi',ai,v) env in
      let a = Array.map
		(compute_metamap env' gmm)
		(Array.map (substl (List.map mkVar (Array.to_list vi))) v) 
      in
      begin
	try
	  let v',mm,sgp = replace_in_array env' gmm a in
	  let cofix = mkCoFix (i,(fi',ai,v')) in
	  TH (cofix,mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end


(*  tcc_aux : term_with_holes -> tactic
 * 
 *  Réalise le 3. ci-dessus
 *)

let rec tcc_aux subst (TH (c,mm,sgp) as th) gl =
  let c = substl subst c in
  match (kind_of_term c,sgp) with
    (* mv => sous-but : on ne fait rien *)
    | Meta _ , _ ->
	tclIDTAC gl

    | Cast (c,_), _ when isMeta c ->
	tclIDTAC gl
	  
    (* terme pur => refine *)
    | _,[] ->
	refine c gl
	
    (* abstraction => intro *)
    | Lambda (Name id,_,m), _ when isMeta (strip_outer_cast m) ->
	begin match sgp with
	  | [None] -> introduction id gl
	  | [Some th] ->
              tclTHEN (introduction id)
                (onLastHyp (fun id -> tcc_aux (mkVar id::subst) th)) gl
	  | _ -> assert false
	end
	
    | Lambda _, _ ->
	anomaly "invalid lambda passed to function tcc_aux"

    (* let in *)
    | LetIn (Name id,c1,t1,c2), _ when isMeta (strip_outer_cast c2) ->
	let c = pf_concl gl in
	let newc = mkNamedLetIn id c1 t1 c in
	tclTHEN 
	  (change_in_concl None newc) 
	  (match sgp with 
	     | [None] -> introduction id
	     | [Some th] ->
                 tclTHEN (introduction id)
                   (onLastHyp (fun id -> tcc_aux (mkVar id::subst) th))
	     | _ -> assert false) 
	  gl

    | LetIn _, _ ->
	anomaly "invalid let-in passed to function tcc_aux"

    (* fix => tactique Fix *)
    | Fix ((ni,_),(fi,ai,_)) , _ ->
	let out_name = function
	  | Name id -> id
          | _ -> error "recursive functions must have names !"
	in
	let fixes = array_map3 (fun f n c -> (out_name f,succ n,c)) fi ni ai in
	tclTHENS
	  (mutual_fix (out_name fi.(0)) (succ ni.(0))
	    (List.tl (Array.to_list fixes)))
	  (List.map (function
		       | None -> tclIDTAC 
		       | Some th -> tcc_aux subst th) sgp)
	  gl

    (* cofix => tactique CoFix *)
    | CoFix (_,(fi,ai,_)) , _ ->
	let out_name = function
	  | Name id -> id
          | _ -> error "recursive functions must have names !"
	in
	let cofixes = array_map2 (fun f c -> (out_name f,c)) fi ai in
	tclTHENS
	  (mutual_cofix (out_name fi.(0)) (List.tl (Array.to_list cofixes)))
	  (List.map (function
		       | None -> tclIDTAC 
		       | Some th -> tcc_aux subst th) sgp)
	  gl

    (* sinon on fait refine du terme puis appels rec. sur les sous-buts.
     * c'est le cas pour App et MutCase. *)
    | _ ->
	tclTHENS
	  (refine c)
	  (List.map
            (function None -> tclIDTAC | Some th -> tcc_aux subst th) sgp)
	  gl

(* Et finalement la tactique refine elle-même : *)

let refine oc gl =
  let sigma = project gl in
  let env = pf_env gl in
  let (gmm,c) = Clenv.exist_to_meta sigma oc in
  let th = compute_metamap env gmm c in
  tcc_aux [] th gl

