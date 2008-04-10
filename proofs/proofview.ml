(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* The subproof datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a subproof which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof, together
   with a comb: a datastructure that gives order to some of these nodes, 
   namely the open goals. 
   The natural candidate for the solution is an {!Evd.evar_defs}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the subproof
   to be able to return information about the subproof. *)

type subproof = {
     initial : Term.constr list;
     solution : Evd.evar_defs;
     comb : Goal.goal list
     }

let rec init = function
  | [] ->  { initial = [] ; 
	     solution = Evd.create_evar_defs Evd.empty ;
	     comb = []
	   }
      (* arnaud, garder les names ? *)
  | (env,typ,name)::l -> let { initial = ret ; solution = sol ; comb = comb } =
                           init l
                         in
                         let ( new_defs , econstr ) = 
			   Evarutil.new_evar sol env typ
			 in
			 let e = match Term.kind_of_term econstr with
			         | Term.Evar (e,_) -> e
				 | _ -> Util.anomaly 
				     "Proofview.init: new_evar failure"
				       (* arnaud:faire un nouveau new_evar 
					  ad hoc. Ou utiliser destEvar.
				          Chercher le pattern dans 
				          goal.ml aussi.*)
				       (* the above error would mean
					  that [Evarutil.new_evar]
					  outputed a non-evar constr,
					  which it should not. *)
			 in
			 let gl = Goal.build e in
			 { initial = econstr::ret;
			   solution = new_defs ;
			   comb = gl::comb }

(* arnaud: plutôt dans proofutils		    
let rec start env l =
  init (List.map (fun x -> (env,x,None)) l)
*)

(* Returns whether this subproof is finished or not. *)
let finished = function
  | {comb = []} -> true
  | _  -> false


(* Function which returns the current state of refinement of the required
   evars. *)
let return { initial=init; solution=defs } =
  List.map (Evarutil.nf_evar (Evd.evars_of defs)) init

(* arnaud: reporter certaines fonctions dans lib/ *)
(* [IndexOutOfRange] occurs in case of malformed indices
   with respect to list lengths. *)
exception IndexOutOfRange

(*arnaud: commenter*)
let list_goto i = 
  let rec aux acc index = function
    | l when index = 0-> (acc,l)
    | [] -> raise IndexOutOfRange
    | a::q -> aux (a::acc) (index-1) q
  in
  fun l -> (* arnaud: descendre i ici probablement*)
    if i < 0 then
      raise IndexOutOfRange
    else
      aux [] i l

type focus_context = Goal.goal list * Goal.goal list

(* arnaud: is de NegativeIndex *)
(* arnaud: préciser "between two indices". Et tout le reste qui est
   probablement pas correct. *)
(* arnaud : [list_goto i] et [list_chop i] renvoient tous les deux une 
   paire (l,r) avec [List.length l = i].
   On va dire que [focus_sublist] focus sur les buts [i] à [j] inclus.
   Donc on doit rajouter plein de +1, sachant que les buts sont numérotés
   à partir de 1. *)
(* This (internal) function extracts a sublist between two indices, and
   returns this sublist together with its context :
   if it returns [(a,(b,c))] then [a] is the sublist and (rev b)@a@c is the
   original list.
   [focus_sublist i j l] raises [IndexOutOfRange] if
   [i > length l], or if [j > length l]. 
   It can also raise [NegativeIndex] if either [i] or [j-i] are negative. *)
let focus_sublist i j l =
  let (left,sub_right) = list_goto (i-1) l in
  let (sub, right) = Util.list_chop (j-i+1) sub_right in
  (sub, (left,right))

(* Inverse operation to the previous one. *)
let unfocus_sublist (left,right) s =
  List.rev_append left (s@right)


(* [focus i j] focuses a subproof on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned subproof).
   It returns the focus proof, and a context for the focus trace. *)
let focus i j sp =
  let (new_comb, context) = focus_sublist i j sp.comb in
  ( { sp with comb = new_comb } , context )

(* Unfocuses a subproof with respect to a context. *)
let unfocus c sp =
  { sp with comb = unfocus_sublist c sp.comb }


(* arnaud : à virer ? utile pour "choose_one" mais "choose_one"
   devrait probablement dégager, si je ne dis pas de bêtise.
   Ou pas... Choose one est un brilliant tactical *)
let focus_proof_step i j ps =
  let (new_subgoals, context) = focus_sublist i j ps.Goal.subgoals in
  ( { ps with Goal.subgoals = new_subgoals } , context )

(* arnaud: à virer pareil ?
   Ou pas pareil. *)
let unfocus_proof_step c ps =
  { ps with Goal.subgoals = unfocus_sublist c ps.Goal.subgoals }
  

(* Returns the open goals of the subproof *)
let goals { comb = comb } = comb









(******************************************************************)
(***                                                            ***)
(***                Definition related to tactics               ***)
(***                                                            ***)
(******************************************************************)



(* type of tactics *)
type +'a result = { proof_step : Goal.proof_step;
		    content : 'a }

type +'a tactic = Environ.env -> Goal.proof_step -> 'a result

(* exception which represent a failure in a command *)
exception TacticFailure of Pp.std_ppcmds

(* [fail s] raises [TacticFailure s].  *)
let fail msg = raise (TacticFailure msg)


(* Applies a tactic to the current subproof. *)
let apply env t sp  = 
  let start = { Goal.subgoals = sp.comb ; Goal.new_defs = sp.solution } in
  let next = (t env start).proof_step in
  {sp with
     solution = next.Goal.new_defs ;
     comb = next.Goal.subgoals
  }


(* arnaud: à recommenter *)
(* Transforms a function of type 
   [Evd.evar_defs -> Goal.goal -> Goal.proof_step] (i.e.
   a tactic that operates on a single goal) into an actual tactic.
   It operates by iterating the single-tactic from the last goal to 
   the first one. *)
(* arnaud: avancer dans les termes modifiés par effet de bord peut se faire
   en mutuel-recursant wrap et [tactic_of...]*)
let tactic_of_goal_tactic f env ps =
  let wrap g ((defs, partial_list) as partial_res) = 
    if Goal.is_defined (Evd.evars_of defs) g then 
      partial_res
    else
      let { Goal.new_defs = d' ; Goal.subgoals = sg } = Goal.run f env defs g in
      (d',sg::partial_list)
  in
  let ( new_defs , combed_subgoals ) = 
    List.fold_right wrap ps.Goal.subgoals (ps.Goal.new_defs,[])
  in
  { proof_step = 
      { Goal.new_defs = new_defs;
	Goal.subgoals = List.flatten combed_subgoals };
    content = ()
  }

(* arnaud: kill sans doute en faveur d'un [tactic sensitive -> tactic] *)
let goal_tactic_of_tactic t =
  let (>>=) = Goal.bind in (* arnaud: peut-être à déplacer, peut-être pas*)
  Goal.env >>= fun env ->
  Goal.null >>= fun ps ->
  Goal.return (t env ps).proof_step


(*** tactics ***)

(* Prototype to the [idtac] tactic, also plays the role of 
   "return" in the tactic monad *)
let id a _ ps =
  { proof_step = ps; content = a }

(* Internal function to freeze. *)
let rec sensitive_assoc = function
  | ((_,t),v)::l -> Goal.cond (Goal.has_itag t) ~thn:
                      (Goal.return v)
	            ~els:
	               (sensitive_assoc l)
  | [] -> fail (Pp.str"") (* arnaud: améliorer le message d'erreur *)

(* Freezes a goal sensitive value to its "current value".
   Its value will be the same inside a goal than inside its 
   ancestor among current goal.
   If there is no such parent then it raises an error to evaluate
   it, better be careful not to use it after unfocusing. *)
(* arnaud: I believe it raises a simple tactic failure when
   incorrectly evaluated. *)
(* spiwack: there are probably optimisation to be done *)
let freeze s env ps =
  let assoc_list = 
    List.map (fun g -> Goal.freeze g, Goal.run s env ps.Goal.new_defs g) 
              ps.Goal.subgoals
  in
  { proof_step =
      { ps with Goal.subgoals = List.map (fun ((g,_),_) -> g) assoc_list };
    content =
      sensitive_assoc assoc_list
  }

(* Reoders the goals on the comb according to a permutation *)
let reorder p _ ps =
  { proof_step =
    { ps with Goal.subgoals = Array.to_list 
                                (Permutation.permute p 
				(Array.of_list ps.Goal.subgoals)) 
    };
    content = ()
  }


(*** tacticals ***)

(* Interpretes the ";" (semicolon) of Ltac. *)
let tclTHEN t1 t2 env ps = t2 env (t1 env ps).proof_step  

(* Bind operation of the tactic monad.*)
(* For now it is used only for the OCaml tactic toolkit, no 
   equivalent in Ltac. *)
let tclBIND t1 t2 env ps = 
  let result1 = t1 env ps in
  t2 result1.content env result1.proof_step

(* Focuses a tactic at a single subgoal, found by it's index. *)
(* There could easily be such a tactical for a range of goals. *)
(* arnaud: bug if 0 goals ! *)
let tclFOCUS i t env sp =
  let (single,context) = focus_proof_step i i sp in
  { proof_step = unfocus_proof_step context (t env single).proof_step ;
    content = ()
  }

(* Makes a list of tactic into a tactic (interpretes the [ | ] construct).
   It applies the tactics from the last one to the first one.
   Fails on the proofs with a number of subgoals not matching the length
   of the list.*)
let rec tclLIST tac_list env ps =
  match tac_list, ps.Goal.subgoals with
  | tac::list,goal::sgoals -> let rec_ps = { ps with Goal.subgoals = sgoals } in
                            let intermediate = (tclLIST list env rec_ps).proof_step in
		            let this_ps = { intermediate with Goal.subgoals = [goal] } in
			    let almost = (tac env this_ps).proof_step in
			    { proof_step =
			      { almost
				with Goal.subgoals = almost.Goal.subgoals@intermediate.Goal.subgoals };
			      content = ()
			    }
  | [],[] -> { proof_step = ps ; content = () }
  | _,_ -> fail (Pp.str "Not the right number of subgoals.")

(* arnaud: syntax de la construction ? *)
(* arnaud: catcher l'erreur en Failure, à faire après avoir retouché Util... *)
(* Interpretes the [ t1 | t2 | ... | t3 | t4 ] construct.
   That is it applies [t1] to the first goal, [t3] and [t4] to the 
   last two, and [t2] to the rest (this generalizes to two lists
   of tactics and a tactic to be repeated).
   As in the other constructions, the tactics are applied from the last
   goal to the first. *)
let tclEXTEND begin_tac_list repeat_tac end_tac_list env ps =
  let subgoals = ps.Goal.subgoals in
  let (b,m_e) = Util.list_chop (List.length begin_tac_list) subgoals in
  let (m,e) = Util.list_chop (List.length m_e - List.length end_tac_list) m_e in
  let end_ps = { ps with Goal.subgoals = e } in
  let intermediate_end_ps = (tclLIST end_tac_list env end_ps).proof_step in
  let middle_ps = { intermediate_end_ps with Goal.subgoals = m } in
  let intermediate_middle_ps = (repeat_tac env middle_ps).proof_step in
  let begin_ps = { intermediate_middle_ps with Goal.subgoals = b } in
  let almost = (tclLIST begin_tac_list env begin_ps).proof_step in
  { proof_step =
    { almost with Goal.subgoals  = almost.Goal.subgoals
                                   @(intermediate_middle_ps.Goal.subgoals
				   @ intermediate_end_ps.Goal.subgoals)
    };
    content = ()
  }

(* This internal tactical specialises the argument tactic on every single 
   goal. Making, for instance, global backtracking local. *)
let rec traverse tac env ps = 
  match ps.Goal.subgoals with
  | goal::sgoals -> let intermediate = 
                      (traverse tac env { ps with Goal.subgoals = sgoals }).proof_step 
                    in
                    let almost = 
		      (tac env { ps with Goal.subgoals = sgoals }).proof_step
		    in
		    { proof_step = 
			{ almost with Goal.subgoals = almost.Goal.subgoals
			                              @intermediate.Goal.subgoals
			};
		      content = ()
		    }
  | [] -> { proof_step = ps ; content = () }

(* Interpretes the "solve" tactical. *)
let tclSOLVE t env ps =
  let new_result = t env ps in
  match new_result.proof_step.Goal.subgoals with
  | [] -> new_result
  | _ -> fail (Pp.str "") (* arnaud: améliorer le message d'erreur sans doute :D*)

(* G stands for global, it backtracks on all current goals instead
   of just one.
   It is also used to implement tclORELSE *)
(* spiwack: not exporter at the moment but might be needed *)
(* arnaud: mettre le commentaire suivant au bon endroit. *)
(* Interpretes the or-else tactical. (denoted "||") *)
(* arnaud: penser à transmettre les info comme le message de l'idtac *)
let tclGORELSE t1 t2 env ps =
  try
    t1 env ps
  with TacticFailure _ ->
    t2 env ps

let tclORELSE t1 t2 =
  traverse (tclGORELSE t1 t2)

(* Interpretes the repeat tactical *)
(* Despite what it may look like, tclREPEAT cannot be defined
   out of Proofview. This is left as an exercise to the reader ;) .*)
let rec tclREPEAT tac env ps =
  tclORELSE (tclTHEN tac (tclREPEAT tac)) (id ()) env ps

let tclIGNORE tac env ps = 
  { (tac env ps) with content = () }


(*** **)
(* arnaud: hack pour debugging *)
let pr_subgoals sp pr_fun =
  pr_fun None (Evd.evars_of sp.solution) sp.comb

let defs_of sp = sp.solution
