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
open Identifier
open Names
open Term
open Tacmach
open Sign
open Environ
open Reduction
open Typing
open Tactics
open Tacticals
open Printer

type metamap = (int * constr) list

type term_with_holes = TH of constr * metamap * sg_proofs
and  sg_proofs       = (term_with_holes option) list

(* pour debugger *)

let rec pp_th (TH(c,mm,sg)) =
  str"TH=[ " ++ hov 0 (  prterm c ++ fnl () ++
			      (* pp_mm mm ++ fnl () ++ *)
			   pp_sg sg  ) ++ str "]"
and pp_mm l =
  hov 0 (prlist_with_sep (fun _ -> (**)(  fnl ()  )(**)) 
	   (fun (n,c) -> (**)(  int n ++ str" --> " ++ prterm c  )(**)) l)
and pp_sg sg =
  hov 0 (prlist_with_sep (fun _ -> (**)(  fnl ()  )(**))
	   (function None -> (**)(  str"None"  )(**) | Some th -> (**)(  pp_th th  )(**)) sg)
     
(*  compute_metamap : constr -> 'a evar_map -> term_with_holes
 *  réalise le 2. ci-dessus
 *
 *  Pour cela, on renvoie une metamap qui indique pour chaque meta-variable
 *  si elle correspond à un but (None) ou si elle réduite à son tour
 *  par un terme de preuve incomplet (Some c).
 *
 *  On a donc l'INVARIANT suivant : le terme c rendu est "de niveau 1"
 *  -- i.e. à plat -- et la metamap contient autant d'éléments qu'il y 
 *  a de meta-variables dans c. On suppose de plus que l'ordre dans la
 *  metamap correspond à celui des buts qui seront engendrés par le refine.
 *)

let replace_by_meta env = function
  | TH (m, mm, sgp) when isMeta (strip_outer_cast m) -> m,mm,sgp
  | (TH (c,mm,_)) as th ->
      let n = Clenv.new_meta() in
      let m = mkMeta n in
      (* quand on introduit une mv on calcule son type *)
      let ty = match kind_of_term c with
	| IsLambda (Name id,c1,c2) when isCast c2 ->
	    mkNamedProd id c1 (snd (destCast c2))
	| IsLambda (Anonymous,c1,c2) when isCast c2 ->
	    mkArrow c1 (snd (destCast c2))
	| _ -> (* (IsApp _ | IsMutCase _) -> *)
	    Retyping.get_type_of_with_meta env Evd.empty mm c
	(*
	| IsFix ((_,j),(v,_,_)) ->
	    v.(j) (* en pleine confiance ! *)
	| _ -> invalid_arg "Tcc.replace_by_meta (TO DO)" 
        *)
      in
      mkCast (m,ty),[n,ty],[Some th]

exception NoMeta

let replace_in_array env a =
  if array_for_all (function (TH (_,_,[])) -> true | _ -> false) a then
    raise NoMeta;
  let a' = Array.map (function
			| (TH (c,mm,[])) -> c,mm,[]
			| th -> replace_by_meta env th) a 
  in
  let v' = Array.map (fun (x,_,_) -> x) a' in
  let mm = Array.fold_left (@) [] (Array.map (fun (_,x,_) -> x) a') in
  let sgp = Array.fold_left (@) [] (Array.map (fun (_,_,x) -> x) a') in
  v',mm,sgp
    
let fresh env n =
  let id = match n with Name x -> x | _ -> id_of_string "_" in
  next_global_ident_away id (ids_of_named_context (named_context env))

let rec compute_metamap env c = match kind_of_term c with
  (* le terme est directement une preuve *)
  | (IsConst _ | IsEvar _ | IsMutInd _ | IsMutConstruct _ |
    IsSort _ | IsVar _ | IsRel _) -> 
      TH (c,[],[])
  (* le terme est une mv => un but *)
  | IsMeta n ->
      (* 
      Pp.warning (Printf.sprintf ("compute_metamap: MV(%d) sans type !\n") n);
      let ty = Retyping.get_type_of_with_meta env Evd.empty lmeta c in 
      *)
      TH (c,[],[None])
  | IsCast (m,ty) when isMeta m -> 
      TH (c,[destMeta m,ty],[None])

  (* abstraction => il faut décomposer si le terme dessous n'est pas pur
   *    attention : dans ce cas il faut remplacer (Rel 1) par (Var x)
   *    où x est une variable FRAICHE *)
  | IsLambda (name,c1,c2) ->
      let v = fresh env name in
      let env' = push_named_assum (v,c1) env in
      begin match compute_metamap env' (subst1 (mkVar v) c2) with
	(* terme de preuve complet *)
	| TH (_,_,[]) -> TH (c,[],[])
	(* terme de preuve incomplet *)    
	| th ->
	    let m,mm,sgp = replace_by_meta env' th in
	    TH (mkLambda (Name v,c1,m), mm, sgp)
      end

  | IsLetIn (name, c1, t1, c2) -> (* Adaptation to confirm *)
      compute_metamap env (subst1 c1 c2)

  (* 4. Application *)
  | IsApp (f,v) ->
      let a = Array.map (compute_metamap env) (Array.append [|f|] v) in
      begin
	try
	  let v',mm,sgp = replace_in_array env a in TH (mkAppA v',mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end

  | IsMutCase (ci,p,c,v) ->
      (* bof... *)
      let nbr = Array.length v in
      let v = Array.append [|p;c|] v in
      let a = Array.map (compute_metamap env) v in
      begin
	try
	  let v',mm,sgp = replace_in_array env a in
	  let v'' = Array.sub v' 2 nbr in
	  TH (mkMutCase (ci,v'.(0),v'.(1),v''),mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end

  (* 5. Fix. *)
  | IsFix ((ni,i),(fi,ai,v)) ->
      (* TODO: use a fold *)
      let vi = Array.map (fresh env) fi in
      let fi' = Array.map (fun id -> Name id) vi in
      let env' = push_named_rec_types (fi',ai,v) env in
      let a = Array.map
		(compute_metamap env')
		(Array.map (substl (List.map mkVar (Array.to_list vi))) v) 
      in
      begin
	try
	  let v',mm,sgp = replace_in_array env' a in
	  let fix = mkFix ((ni,i),(fi',ai,v')) in
	  TH (fix,mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end
	      
  (* Cast. Est-ce bien exact ? *)
  | IsCast (c,t) -> compute_metamap env c
      (*let TH (c',mm,sgp) = compute_metamap sign c in
	TH (mkCast (c',t),mm,sgp) *)
      
  (* Produit. Est-ce bien exact ? *)
  | IsProd (_,_,_) ->
      if occur_meta c then
	error "Refine: proof term contains metas in a product"
      else
      	TH (c,[],[])

  (* Cofix. *)
  | IsCoFix (i,(fi,ai,v)) ->
      let vi = Array.map (fresh env) fi in
      let fi' = Array.map (fun id -> Name id) vi in
      let env' = push_named_rec_types (fi',ai,v) env in
      let a = Array.map
		(compute_metamap env')
		(Array.map (substl (List.map mkVar (Array.to_list vi))) v) 
      in
      begin
	try
	  let v',mm,sgp = replace_in_array env' a in
	  let cofix = mkCoFix (i,(fi',ai,v')) in
	  TH (cofix,mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end


(*  tcc_aux : term_with_holes -> tactic
 * 
 *  Réalise le 3. ci-dessus
 *)

let rec tcc_aux (TH (c,mm,sgp) as th) gl =
  match (kind_of_term c,sgp) with
    (* mv => sous-but : on ne fait rien *)
    | IsMeta _ , _ ->
	tclIDTAC gl

    | IsCast (c,_), _ when isMeta c ->
	tclIDTAC gl
	  
    (* terme pur => refine *)
    | _,[] ->
	refine c gl
	
    (* abstraction => intro *)
    | IsLambda (Name id,_,m) , _ when isMeta (strip_outer_cast m) ->
	begin match sgp with
	  | [None] -> introduction id gl
	  | [Some th] ->
	      tclTHEN (introduction id) (tcc_aux th) gl
	  | _ -> invalid_arg "Tcc.tcc_aux (bad length)"
	end
	
    | IsLambda (_,_,_) , _ ->
	error "invalid abstraction passed to function tcc_aux !"
      
    (* fix => tactique Fix *)
    | IsFix ((ni,_),(fi,ai,_)) , _ ->
	let ids =
	  Array.to_list
            (Array.map
              (function Name id -> id
                | _ -> error "recursive functions must have names !")
              fi) 
	in
	tclTHENS
	  (mutual_fix ids (List.map succ (Array.to_list ni))
             (List.tl (Array.to_list ai)))
	  (List.map (function
		       | None -> tclIDTAC 
		       | Some th -> tcc_aux th) sgp)
	  gl

    (* cofix => tactique CoFix *)
    | IsCoFix (_,(fi,ai,_)) , _ ->
	let ids =
	  Array.to_list
            (Array.map
              (function Name id -> id
                | _ -> error "recursive functions must have names !")
              fi) 
	in
	tclTHENS
	  (mutual_cofix ids (List.tl (Array.to_list ai)))
	  (List.map (function
		       | None -> tclIDTAC 
		       | Some th -> tcc_aux th) sgp)
	  gl

    (* sinon on fait refine du terme puis appels rec. sur les sous-buts.
     * c'est le cas pour App et MutCase. *)
    | _ ->
	tclTHENS
	  (refine c)
	  (List.map (function None -> tclIDTAC | Some th -> tcc_aux th) sgp)
	  gl

(* Et finalement la tactique refine elle-même : *)

let refine oc gl =
  let env = pf_env gl in
  let (_,c) = Clenv.exist_to_meta oc in
  let th = compute_metamap env c in
  tcc_aux th gl

let refine_tac = Tacmach.hide_openconstr_tactic "Refine" refine

open Proof_type

let dyn_tcc args gl = match args with 
  | [Command com]  ->
      let env = pf_env gl in
      refine
	(Astterm.interp_casted_openconstr (project gl) env com (pf_concl gl))
	gl
  | [OpenConstr c] -> 
      refine c gl
  | _ -> assert false

let tcc_tac = hide_tactic "Tcc" dyn_tcc


