(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(*arnaud: commenter le module en général aussi *)

(* arnaud: peut-être faut-il considérer l'idée d'avoir un type des refine-step
   soit un constr et un environement d'evar, qui pourrait se passer en argument de tactique, plutôt que bêtement raw-constr... 
   A ce stade de la réflexion, rawconstr paraît mieux*)

open Tacexpr (*arnaud: probablement enlever les références à tacexpr qui restent*)
open Genarg

(* arnaud: à commenter un peu plus dans le sens de ce que c'est vraiment. A savoir les valeurs qui peuvent être dans des variables de tactique *)
(* Values for interpretation *)
type value =
  | VTactic of Util.loc * Subproof.tactic  (* For mixed ML/Ltac tactics (e.g. Tauto) *)
  | VFun of (Names.identifier * value) list * Names.identifier option list * Tacexpr.glob_tactic_expr
  | VVoid
  | VInteger of int
  | VIntroPattern of Genarg.intro_pattern_expr
  | VConstr of Term.constr (* arnaud: constr ou rawconstr ? *)
  | VConstr_context of Term.constr (* arnaud: contr ou rawconstr ? *)
  | VList of value list
  | VRec of value ref



(*** ***)
(* arnaud: partie pas certaine, probablement souvent temporaire *)

(* arnaud: très temporaire *)
(* Gives the state of debug *)
let get_debug () = Tactic_debug.DebugOff

(* arnaud: plutôt "contexte de généralisation je suppose" *)
(* Interpretation of extra generic arguments *)
type glob_sign = { 
  ltacvars : Names.identifier list * Names.identifier list;
     (* ltac variables and the subset of vars introduced by Intro/Let/... *)
  ltacrecvars : (Names.identifier * Nametab.ltac_constant) list;
     (* ltac recursive names *)
  gsigma : Evd.evar_map;
     (* arnaud: environnement pour typer les evars, pourquoi pas un defs ? *)
  genv : Environ.env }
     (* environement pour typer le reste, normal *)


(*****************)
(* Globalization *)
(*****************)
(* arnaud: globalization = jouer au binder ? *)

(* arnaud: Que veut dire ce truc ? *)
(* We have identifier <| global_reference <| constr *)

(* arnaud: commenter il y a deux lignes il faut les piger *)
let find_ident id sign = 
    (* Has the name been introduced by a tactic function, or and intro
       (or similar) tactic. *)
  List.mem id (fst sign.ltacvars) or 
    (* or has it been introduced earlier, like as an hypothesis of the
       current goal (if the tactic is a single_tactic) *)
    (* arnaud: single_tactic changera sûrement de nom *)
  List.mem id (Termops.ids_of_named_context (Environ.named_context sign.genv))

(* arnaud: commenter plus clairement. C'est probablement le seul endroit
   où lf est utilisé, ist aussi peut-être ? Probablement pas pour ist*)
(* Globalize a name introduced by Intro/LetTac/... ; it is allowed to *)
(* be fresh in which case it is binding later on *)
let intern_ident lf ist id =
  (* We use identifier both for variables and new names; thus nothing to do *)
  if not (find_ident id ist) then lf:=(id::fst !lf,id::snd !lf);
  id

(* arnaud: à commenter *)
let rec intern_intro_pattern lf ist = function
  | IntroOrAndPattern l ->
      IntroOrAndPattern (intern_case_intro_pattern lf ist l)
  | IntroIdentifier id ->
      IntroIdentifier (intern_ident lf ist id)
  | IntroWildcard | IntroAnonymous | IntroFresh _ as x -> x

(*arnaud: à commenter *)
and intern_case_intro_pattern lf ist =
  List.map (List.map (intern_intro_pattern lf ist))

(* Globalizes tactics : raw_tactic_expr -> glob_tactic_expr *)
let rec intern_atomic lf ist x =
  match (x:raw_atomic_tactic_expr) with 
  | TacIntroPattern l ->
      TacIntroPattern (List.map (intern_intro_pattern lf ist) l)
  | _ -> Util.anomaly "Ltacinterp.intern_atomic: todo"

(* arnaud: à déplacer et restaurer, pas encore compris ce que c'était ce
   truc strict_check. *)
let adjust_loc loc = loc (*was: if !strict_check then dloc else loc*)

(* arnaud: à commenter *)
let intern_tactic_seq ist = function
  | TacAtom (loc,t) ->
      let lf = ref ist.ltacvars in
      let t = intern_atomic lf ist t in
      !lf, TacAtom (adjust_loc loc, t)
  | _ -> Util.anomaly "Ltacinterp.intern_tactic_seq: todo"

let intern_tactic ist tac = (snd (intern_tactic_seq ist tac) : glob_tactic_expr)



(******************)
(* Interpretation *)
(******************)

(* arnaud: recommenter peut-être ? *)
(* Signature for interpretation: val_interp and interpretation functions *)
type interp_sign =
    { lfun : (Names.identifier * value) list;
      avoid_ids : Names.identifier list; (* ids inherited from the call context
				      (needed to get fresh ids) *)
      debug : Tactic_debug.debug_info;
      last_loc : Util.loc }

open Pp (*arnaud: déplacer au début sans doute ? *)

(* arnaud: déplacer ? *)
(* Displays a value *)
let rec pr_value env = function
  | VVoid -> str "()"
  | VInteger n -> int n
  | VIntroPattern ipat -> pr_intro_pattern ipat
  | VConstr c | VConstr_context c ->
      (match env with Some env -> Printer.pr_lconstr_env env c | _ -> str "a term")
  | (VTactic _ | VFun _ | VRec _) -> str "a tactic"
  | VList [] -> str "an empty list"
  | VList (a::_) ->
      str "a list (first element is " ++ pr_value env a ++ str")"
let error_ltac_variable loc id env v s =
   Util.user_err_loc (loc, "", str "Ltac variable " ++ Ppconstr.pr_id id ++ 
   str " is bound to" ++ spc () ++ pr_value env v ++ spc () ++ 
   str "which cannot be coerced to " ++ str s)

exception CannotCoerceTo of string

(* Raise Not_found if not in interpretation sign *)
let try_interp_ltac_var coerce ist env (loc,id) =
  let v = List.assoc id ist.lfun in
  try coerce v with CannotCoerceTo s -> error_ltac_variable loc id env v s

(* arnaud: commenter ? *)
let coerce_to_intro_pattern env = function
  | VIntroPattern ipat -> ipat
  | VConstr c when Term.isVar c ->
      (* This happens e.g. in definitions like "Tac H = clear H; intro H" *)
      (* but also in "destruct H as (H,H')" *)
      IntroIdentifier (Term.destVar c)
  | v -> raise (CannotCoerceTo "an introduction pattern")

(* arnaud: je comprends pas ce que fait cette fonction... *)
let interp_intro_pattern_var ist env id =
  try try_interp_ltac_var (coerce_to_intro_pattern env) ist (Some env)(Util.dummy_loc,id)
  with Not_found -> IntroIdentifier id

(* arnaud: commenter ces deux fonctions *)
let rec interp_intro_pattern ist = function
  | IntroOrAndPattern l -> IntroOrAndPattern (interp_case_intro_pattern ist l)
  | IntroIdentifier id -> interp_intro_pattern_var ist (Environ.empty_env (* arnaud: corriger ça au plus vite !!!!!!!!!*) ) id
  | IntroWildcard | IntroAnonymous | IntroFresh _ as x -> x

and interp_case_intro_pattern ist =
  List.map (List.map (interp_intro_pattern ist))

(*arnaud: très temporary function *)
let unintro_pattern = function
  | IntroIdentifier id -> id
  | _ -> Util.anomaly "Ltacinterp.TacIntroPattern: pour l'instant on ne sait faire que des intro simples"

(* arnaud: très temporary function *)
let do_intro = function
  [x] -> Logic.interprete_simple_tactic_as_single_tactic (Global.env ()) (* arnaud: changer ça probablement *)
                                                          (Logic.Intro x)
  | _ -> Util.anomaly "Ltacinterp.TacIntroPattern: pour l'instant on ne sait faire que des intro simples (bis)"

let interp_atomic ist = function
  (* Basic tactics *)
  | TacIntroPattern l ->
         Subproof.single_tactic (do_intro (List.map unintro_pattern (List.map (interp_intro_pattern ist) l)))
  | _ -> Util.anomaly "Ltacinterp.interp_atomic: todo"

(* arnaud: à déplacer ?*)
(* For tactic_of_value *)
exception NotTactic

(* Gives the tactic corresponding to the tactic value *)
let tactic_of_value vle =
  match vle with
  | VTactic (loc,tac) -> tac (* arnaud:remettre les infos de location ?*)
  | VFun _ -> Util.error "A fully applied tactic is expected"
  | _ -> raise NotTactic

(* arnaud: commenter et renommer *)
let other_eval_tactic ist = function
  | TacAtom (loc,t) -> interp_atomic ist t
  | _ -> Util.anomaly "Ltacinterp.other_eval_tactic: todo"

let rec val_interp ist (tac:glob_tactic_expr) =

  let value_interp ist = match tac with
  (* Immediate evaluation *)
  | TacFun (it,body) -> VFun (ist.lfun,it,body)
  (* arnaud: todo? : TacArg, TacLet(Rec)In*)
  (* Delayed_evaluation *)
  | t -> VTactic (ist.last_loc,other_eval_tactic ist t)
  in
  Util.check_for_interrupt ();
    match ist.debug with
    | Tactic_debug.DebugOn lev -> Util.anomaly "Ltacinterp.tactic_of_value: todo"
	(* arnaud:was: debug_prompt lev gl tac (fun v -> value_interp {ist with debug=v})*)
    | _ -> value_interp ist 

(* arnaud: commenter ? *)
let interp_tactic ist tac  =
  try tactic_of_value (val_interp ist tac) 
  with NotTactic ->
    Util.errorlabstrm "" (str "Must be a command or must give a tactic value")

(* arnaud: commenter/renommer *)
let eval_tactic t =
  interp_tactic { lfun=[]; avoid_ids=[]; debug=get_debug(); last_loc=Util.dummy_loc } t



(* arnaud: fonction très temporaire *)
let hide_interp p t ot =
  let ist = { ltacvars = ([],[]); 
	      ltacrecvars = []; 
              gsigma = Evd.evars_of (Subproof.defs_of (Proof.subproof_of p));
              genv = Global.env () } in
  let te = intern_tactic ist t in
  let t = eval_tactic te in
  match ot with 
  | None -> t
      (* arnaud: was: abstract_tactic_expr (TacArg (Tacexp te)) t*)
  | Some t' -> Util.anomaly "Logic.hide_interp: todo: end tactic"
      (* arnaud: original: abstract_tactic_expr ~dflt:true (TacArg (Tacexp te)) (tclTHEN t t') gl*)
