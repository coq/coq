(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* The proofview datastructure is a pure datastructure underlying the notion
   of proof (namely, a proof is a proofview which can evolve and has safety
   mechanisms attached).
   The general idea of the structure is that it is composed of a chemical
   solution: an unstructured bag of stuff which has some relations with 
   one another, which represents the various subnodes of the proof, together
   with a comb: a datastructure that gives order to some of these nodes, 
   namely the open goals. 
   The natural candidate for the solution is an {!Evd.evar_defs}, that is
   a calculus of evars. The comb is then a list of goals (evars wrapped 
   with some extra information, like possible name anotations).
   There is also need of a list of the evars which initialised the proofview
   to be able to return information about the proofview. *)

(* Type of proofviews. *)
type proofview = {
     initial : Term.constr list;
     solution : Evd.evar_defs;
     comb : Goal.goal list
     }

(* Initialises a proofview, the argument is a list of environement, 
   conclusion types, and optional names, creating that many initial goals. *)
(* arnaud: doit-elle être définitivement comme ça ? *)
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
			 let (e,_) = Term.destEvar econstr in
			 let gl = Goal.build e in
			 { initial = econstr::ret;
			   solution = new_defs ;
			   comb = gl::comb }

(* Returns whether this proofview is finished or not. That is,
   if it has empty subgoals in the comb. There could still be unsolved
   subgoaled, but they would then be out of the view, focused out. *)
let finished = function
  | {comb = []} -> true
  | _  -> false


(* Function which returns the current state of refinement of the required
   (= initial) evars. *)
let return { initial=init; solution=defs } =
  List.map (Evarutil.nf_evar (Evd.evars_of defs)) init

(* arnaud: reporter certaines fonctions dans lib/ *)
(* [IndexOutOfRange] occurs in case of malformed indices
   with respect to list lengths. *)
exception IndexOutOfRange

(* [list_goto i l] returns a pair of lists [c,t] where
   [c] has length [i] and is the reversed of the [i] first
   elements of [l], and [t] is the rest of the list.
   The idea is to navigate through the list, [c] is then
   seen as the context of the current position. 
   Raises [IndexOutOfRange] if [i > length l]*)
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

(* Type of the object which allow to unfocus a view.*)
(* First component is a reverse list of what comes before
   and second component is what goes after (in the expected
   order) *)
type focus_context = Goal.goal list * Goal.goal list

(* This (internal) function extracts a sublist between two indices, and
   returns this sublist together with its context:
   if it returns [(a,(b,c))] then [a] is the sublist and (rev b)@a@c is the
   original list.
   The focused list has lenght [j-i-1] and contains the goals from
   number [i] to number [j] (both included) the first goal of the list
   being numbered [1].
   [focus_sublist i j l] raises [IndexOutOfRange] if
   [i > length l], or [j > length l] or [ j < i ].  *)
(* arnaud: il faudrait corriger l'erreur de list_chop de façon 
   à rendre le commentaire correct. *)
let focus_sublist i j l =
  let (left,sub_right) = list_goto (i-1) l in
  let (sub, right) = Util.list_chop (j-i+1) sub_right in
  (sub, (left,right))

(* Inverse operation to the previous one. *)
let unfocus_sublist (left,right) s =
  List.rev_append left (s@right)


(* [focus i j] focuses a proofview on the goals from index [i] to index [j] 
   (inclusive). (i.e. goals number [i] to [j] become the only goals of the
   returned proofview).
   It returns the focus proof, and a context for the focus trace. *)
let focus i j sp =
  let (new_comb, context) = focus_sublist i j sp.comb in
  ( { sp with comb = new_comb } , context )

(* Unfocuses a proofview with respect to a context. *)
let unfocus c sp =
  { sp with comb = unfocus_sublist c sp.comb }


(* arnaud: on devrait peut-être rendre les proofviews plus ou moins
   identiques aux proof_steps, ça simplifierait peut-être. *)
(* Focusing operation on proof_steps. *)
let focus_proof_step i j ps =
  let (new_subgoals, context) = focus_sublist i j ps.Goal.subgoals in
  ( { ps with Goal.subgoals = new_subgoals } , context )

(* Unfocusing operation of proof_steps. *)
let unfocus_proof_step c ps =
  { ps with Goal.subgoals = unfocus_sublist c ps.Goal.subgoals }
  

(* Returns the open goals of the proofview *)
let goals { comb = comb } = comb









(******************************************************************)
(***                                                            ***)
(***                Definition related to tactics               ***)
(***                                                            ***)
(******************************************************************)


(* The tactic monad:
   - Tactics are objects which apply a transformation to all
     the subgoals of the current view at the same time. By opposed
     to the old vision of applying it to a single goal. It mostly 
     allows to consider tactic like [reorder] to reorder the goals
     in the current view (which might be useful for the tactic designer)
     (* spiwack: the ordering of goals, though, is actually very
        brittle. It would be much more interesting to find a more
        robust way to adress goals, I have no idea at this time 
        though*) 
     or global automation tactic for dependent subgoals (instantiating
     an evar has influences on the other goals of the proof in progress,
     not being able to take that into account causes the current eauto
     tactic to fail on some instances where it could succeed).
   - Tactics are a monad ['a tactic], in a sense a tactic can be 
     seens as a function (without argument) which returns a value
     of type 'a and modifies the environement (in our case: the view).
     Tactics of course have arguments, but these are given at the 
     meta-level as OCaml functions.
     Most tactics in the sense we are used to return [ () ], that is
     no really interesting values. But some might, to pass information 
     around; for instance [Proofview.freeze] allows to store a certain
     goal sensitive value "at the present time" (which means, considering the
     structure of the dynamics of proofs, [Proofview.freeze s] will have,
     for every current goal [gl], and for any of its descendent [g'] in 
     the future the same value in [g'] that in [gl]). 
     (* spiwack: I don't know how much all this relates to F. Kirchner and 
        C. Muñoz. I wasn't able to understand how they used the monad
        structure in there developpement.
     *)
     The tactics seen in Coq's Ltac are (for now at least) only 
     [unit tactic], the return values are kept for the OCaml toolkit.
     The operation or the monad are [Proofview.tclIDTAC] (which is the 
     "return" of the tactic monad) [Proofview.tclBIND] (which is
     the "bind") and [Proofview.tclTHEN] (which is a specialized
     bind on unit-returning tactics).
*)


(* type of tactics *)
type +'a result = { proof_step : Goal.proof_step;
		    content : 'a }

type +'a tactic = Environ.env -> Goal.proof_step -> 'a result

(* arnaud: abandon, cf le .mli
(* exception which represent a failure in a command *)
exception TacticFailure of Pp.std_ppcmds
*)

(* [fail s] raises [TacticFailure s].  *)
let fail msg = 
  Pp.pp_with Format.str_formatter msg;
  Util.error (Format.flush_str_formatter ())


(* Applies a tactic to the current proofview. *)
let apply env t sp  = 
  let start = { Goal.subgoals = sp.comb ; Goal.new_defs = sp.solution } in
  let next = (t env start).proof_step in
  {sp with
     solution = next.Goal.new_defs ;
     comb = next.Goal.subgoals
  }


(* A [proof_step Goal.sensitive] can be seen as a tactic by
   contatenating its value inside each individual goal of the
   current view. *)
(* arnaud: avancer dans les termes modifiés par effet de bord peut se faire
   en mutuel-recursant wrap et [tactic_of...]*)
let tactic_of_sensitive_proof_step f env ps =
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

(* arnaud: abandonné en faveur de [sensitive_tactic]
(* arnaud: kill sans doute en faveur d'un [tactic sensitive -> tactic] *)
let goal_tactic_of_tactic t =
  let (>>=) = Goal.bind in (* arnaud: peut-être à déplacer, peut-être pas*)
  Goal.env >>= fun env ->
  Goal.null >>= fun ps ->
  Goal.return (t env ps).proof_step
*)


(* This tactical is included for compatibitility with the previous
   way of building tactic. It corresponds to a very natural way of building
   tactic according to it, far less now, though it may be unavoidable (
   if we want to really get rid of it, it might be necessary to have
   some clever ways or "focusing" or such).
   It takes a [unit tactic Goal.sensitive] that is a value that becomes
   a tactic inside a goal and make it a tactic by applying it individually
   to a view containing a single goal (it peeks inside the goal to figure
   which tactic it should apply, then applies it). *)
let sensitive_tactic st =
  let sps =
    let (>>=) = Goal.bind in (* arnaud: peut-être à déplacer, peut-être pas*)
    Goal.env  >>= fun env ->
    Goal.null >>= fun ps ->
    st        >>= fun st ->
    let  result = st env ps in
    Goal.return result.proof_step
  in
  tactic_of_sensitive_proof_step sps
  

(*** tactics ***)

let tclFAIL msg env ps =
  if ps.Goal.subgoals = [] then
    { proof_step = ps; content = () }
  else begin
    Pp.pp_with Format.str_formatter msg;
    Util.error (Format.flush_str_formatter ())
  end

(* Prototype to the [idtac] tactic, also plays the role of 
   "return" in the tactic monad *)
let tclIDTAC a _ ps =
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

(* Interpretes the ";" (semicolon) of Ltac.
   As a monadic operation, it's a specialized "bind"
   on unit-returning tactic (meaning "there is no value to bind") *)
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
		      (tac env { ps with Goal.subgoals = [goal] }).proof_step
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
  with Util.UserError _ | Failure _ (*arnaud: faudra rattraper les erreurs mieux que ça :). *)->
    t2 env ps

let tclORELSE t1 t2 =
  traverse (tclGORELSE t1 t2)

(* Interpretes the repeat tactical *)
(* Despite what it might look like, tclREPEAT cannot be defined
   out of Proofview. This is left as an exercise to the reader ;) .*)
(* arnaud: c'est plus vrai maintenant que tclBIND est dans la place, 
   à regarder mais ya des chances que ça ne coûte rien de sortir
   tclREPEAT d'ici donc. *)
let rec tclREPEAT tac env ps =
  tclORELSE (tclTHEN tac (tclREPEAT tac)) (tclIDTAC ()) env ps

let tclIGNORE tac env ps = 
  { (tac env ps) with content = () }


(*** **)
(* arnaud: hack pour debugging *)
let pr_subgoals sp pr_fun =
  pr_fun None (Evd.evars_of sp.solution) sp.comb

let defs_of sp = sp.solution
