(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* JCF -- 6 janvier 1998  EXPERIMENTAL *)

(*
 *  L'id�e est, en quelque sorte, d'avoir de "vraies" m�tavariables
 *  dans Coq, c'est-�-dire de donner des preuves incompl�tes -- mais
 *  o� les trous sont typ�s -- et que les sous-buts correspondants
 *  soient engendr�s pour finir la preuve.
 *
 *  Exemple : 
 *    J'ai le but
 *        (x:nat) { y:nat | (minus y x) = x }
 *    et je donne la preuve incompl�te
 *        [x:nat](exist nat [y:nat]((minus y x)=x) (plus x x) ?)
 *    ce qui engendre le but
 *        (minus (plus x x) x)=x
 *)

(*  Pour cela, on proc�de de la mani�re suivante :
 *
 *  1. Un terme de preuve incomplet est un terme contenant des variables
 *     existentielles Evar i.e. "?" en syntaxe concr�te.
 *     La r�solution de ces variables n'est plus n�cessairement totale
 *     (ise_resolve called with fail_evar=false) et les variables
 *     existentielles restantes sont remplac�es par des m�ta-variables
 *     cast�es par leur types (celui est connu : soit donn�, soit trouv�
 *     pendant la phase de r�solution).
 *
 *  2. On met ensuite le terme "� plat" i.e. on n'autorise des MV qu'au
 *     permier niveau et pour chacune d'elles, si n�cessaire, on donne
 *     � son tour un terme de preuve incomplet pour la r�soudre.
 *     Exemple: le terme (f a ? [x:nat](e ?)) donne
 *         (f a ?1 ?2) avec ?2 => [x:nat]?3 et ?3 => (e ?4)
 *         ?1 et ?4 donneront des buts
 *
 *  3. On �crit ensuite une tactique tcc qui engendre les sous-buts
 *     � partir d'une preuve incompl�te.
 *)

(* arnaud: � virer, sans doute
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
  (str"TH=[ " ++ hov 0 (pr_lconstr c ++ fnl () ++
			      (* pp_mm mm ++ fnl () ++ *)
			   pp_sg sg) ++ str "]")
and pp_mm l =
  hov 0 (prlist_with_sep (fun _ -> (fnl ())) 
	   (fun (n,c) -> (int n ++ str" --> " ++ pr_lconstr c)) l)
and pp_sg sg =
  hov 0 (prlist_with_sep (fun _ -> (fnl ()))
	   (function None -> (str"None") | Some th -> (pp_th th)) sg)
     
(*  compute_metamap : constr -> 'a evar_map -> term_with_holes
 *  r�alise le 2. ci-dessus
 *
 *  Pour cela, on renvoie une meta_map qui indique pour chaque meta-variable
 *  si elle correspond � un but (None) ou si elle r�duite � son tour
 *  par un terme de preuve incomplet (Some c).
 *
 *  On a donc l'INVARIANT suivant : le terme c rendu est "de niveau 1"
 *  -- i.e. � plat -- et la meta_map contient autant d'�l�ments qu'il y 
 *  a de meta-variables dans c. On suppose de plus que l'ordre dans la
 *  meta_map correspond � celui des buts qui seront engendr�s par le refine.
 *)

let replace_by_meta env sigma = function
  | TH (m, mm, sgp) when isMeta (strip_outer_cast m) -> m,mm,sgp
  | (TH (c,mm,_)) as th ->
      let n = Evarutil.new_meta() in
      let m = mkMeta n in
      (* quand on introduit une mv on calcule son type *)
      let ty = match kind_of_term c with
	| Lambda (Name id,c1,c2) when isCast c2 ->
	    let _,_,t = destCast c2 in mkNamedProd id c1 t
	| Lambda (Anonymous,c1,c2) when isCast c2 ->
	    let _,_,t = destCast c2 in mkArrow c1 t
	| _ -> (* (App _ | Case _) -> *)
	    Retyping.get_type_of_with_meta env sigma mm c
	(*
	| Fix ((_,j),(v,_,_)) ->
	    v.(j) (* en pleine confiance ! *)
	| _ -> invalid_arg "Tcc.replace_by_meta (TO DO)" 
        *)
      in
      mkCast (m,DEFAULTcast, ty),[n,ty],[Some th]

exception NoMeta

let replace_in_array keep_length env sigma a =
  if array_for_all (function (TH (_,_,[])) -> true | _ -> false) a then
    raise NoMeta;
  let a' = Array.map (function
			| (TH (c,mm,[])) when not keep_length -> c,mm,[]
			| th -> replace_by_meta env sigma th) a 
  in
  let v' = Array.map pi1 a' in
  let mm = Array.fold_left (@) [] (Array.map pi2 a') in
  let sgp = Array.fold_left (@) [] (Array.map pi3 a') in
  v',mm,sgp
    
let fresh env n =
  let id = match n with Name x -> x | _ -> id_of_string "_H" in
  next_global_ident_away true id (ids_of_named_context (named_context env))

let rec compute_metamap env sigma c = match kind_of_term c with
  (* le terme est directement une preuve *)
  | (Const _ | Evar _ | Ind _ | Construct _ |
    Sort _ | Var _ | Rel _) -> 
      TH (c,[],[])

  (* le terme est une mv => un but *)
  | Meta n ->
      TH (c,[],[None])

  | Cast (m,_, ty) when isMeta m -> 
      TH (c,[destMeta m,ty],[None])


  (* abstraction => il faut d�composer si le terme dessous n'est pas pur
   *    attention : dans ce cas il faut remplacer (Rel 1) par (Var x)
   *    o� x est une variable FRAICHE *)
  | Lambda (name,c1,c2) ->
      let v = fresh env name in
      let env' = push_named (v,None,c1) env in
      begin match compute_metamap env' sigma (subst1 (mkVar v) c2) with
	(* terme de preuve complet *)
	| TH (_,_,[]) -> TH (c,[],[])
	(* terme de preuve incomplet *)    
	| th ->
	    let m,mm,sgp = replace_by_meta env' sigma th in
	    TH (mkLambda (Name v,c1,m), mm, sgp)
      end

  | LetIn (name, c1, t1, c2) ->
      let v = fresh env name in
      let th1 = compute_metamap env sigma c1 in
      let env' = push_named (v,Some c1,t1) env in
      let th2 = compute_metamap env' sigma (subst1 (mkVar v) c2) in
      begin match th1,th2 with
	(* terme de preuve complet *)
	| TH (_,_,[]), TH (_,_,[]) -> TH (c,[],[])
	(* terme de preuve incomplet *)    
	| TH (c1,mm1,sgp1), TH (c2,mm2,sgp2) ->
	    let m1,mm1,sgp1 =
              if sgp1=[] then (c1,mm1,[]) 
              else replace_by_meta env sigma th1 in
	    let m2,mm2,sgp2 =
              if sgp2=[] then (c2,mm2,[]) 
              else replace_by_meta env' sigma th2 in
	    TH (mkNamedLetIn v m1 t1 m2, mm1@mm2, sgp1@sgp2)
      end

  (* 4. Application *)
  | App (f,v) ->
      let a = Array.map (compute_metamap env sigma) (Array.append [|f|] v) in
      begin
	try
	  let v',mm,sgp = replace_in_array false env sigma a in
          let v'' = Array.sub v' 1 (Array.length v) in
          TH (mkApp(v'.(0), v''),mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end

  | Case (ci,p,cc,v) ->
      (* bof... *)
      let nbr = Array.length v in
      let v = Array.append [|p;cc|] v in
      let a = Array.map (compute_metamap env sigma) v in
      begin
	try
	  let v',mm,sgp = replace_in_array false env sigma a in
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
		(compute_metamap env' sigma)
		(Array.map (substl (List.map mkVar (Array.to_list vi))) v) 
      in
      begin
	try
	  let v',mm,sgp = replace_in_array true env' sigma a in
	  let fix = mkFix ((ni,i),(fi',ai,v')) in
	  TH (fix,mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end
	      
  (* Cast. Est-ce bien exact ? *)
  | Cast (c,_,t) -> compute_metamap env sigma c
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
		(compute_metamap env' sigma)
		(Array.map (substl (List.map mkVar (Array.to_list vi))) v) 
      in
      begin
	try
	  let v',mm,sgp = replace_in_array true env' sigma a in
	  let cofix = mkCoFix (i,(fi',ai,v')) in
	  TH (cofix,mm,sgp)
	with NoMeta ->
	  TH (c,[],[])
      end


(*  tcc_aux : term_with_holes -> tactic
 * 
 *  R�alise le 3. ci-dessus
 *)

let rec tcc_aux subst (TH (c,mm,sgp) as _th) gl =
  let c = substl subst c in
  match (kind_of_term c,sgp) with
    (* mv => sous-but : on ne fait rien *)
    | Meta _ , _ ->
	tclIDTAC gl

    | Cast (c,_,_), _ when isMeta c ->
	tclIDTAC gl
	  
    (* terme pur => refine *)
    | _,[] ->
	refine c gl
	
    (* abstraction => intro *)
    | Lambda (Name id,_,m), _ ->
	assert (isMeta (strip_outer_cast m));
	begin match sgp with
	  | [None] -> introduction id gl
	  | [Some th] ->
              tclTHEN (introduction id)
                (onLastHyp (fun id -> tcc_aux (mkVar id::subst) th)) gl
	  | _ -> assert false
	end

    | Lambda (Anonymous,_,m), _ -> (* if anon vars are allowed in evars *)
        assert (isMeta (strip_outer_cast m));
	begin match sgp with
	  | [None] -> tclTHEN intro (onLastHyp (fun id -> clear [id])) gl
	  | [Some th] ->
              tclTHEN
                intro
                (onLastHyp (fun id -> 
                  tclTHEN
                    (clear [id])
                    (tcc_aux (mkVar (*dummy*) id::subst) th))) gl
	  | _ -> assert false
	end

    (* let in without holes in the body => possibly dependent intro *)
    | LetIn (Name id,c1,t1,c2), _ when not (isMeta (strip_outer_cast c1)) ->
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

    (* let in with holes in the body => unable to handle dependency
       because of evars limitation, use non dependent assert instead *)
    | LetIn (Name id,c1,t1,c2), _ ->
	tclTHENS
          (assert_tac true (Name id) t1) 
	  [(match List.hd sgp with 
	     | None -> tclIDTAC
	     | Some th -> onLastHyp (fun id -> tcc_aux (mkVar id::subst) th));
           (match List.tl sgp with 
	     | [] -> refine (subst1 (mkVar id) c2)  (* a complete proof *)
	     | [None] -> tclIDTAC                   (* a meta *)
	     | [Some th] ->                         (* a partial proof *)
                 onLastHyp (fun id -> tcc_aux (mkVar id::subst) th)
             | _ -> assert false)]
          gl

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

(* Et finalement la tactique refine elle-m�me : *)

let refine oc gl =
  let sigma = project gl in
  let (sigma,c) = Evarutil.evars_to_metas sigma oc in
  (* Relies on Cast's put on Meta's by evars_to_metas, because it is otherwise 
     complicated to update meta types when passing through a binder *)
  let th = compute_metamap (pf_env gl) sigma c in
  tclTHEN (Refiner.tclEVARS sigma) (tcc_aux [] th) gl
*)
