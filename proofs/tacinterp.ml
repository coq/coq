
(* $Id$ *)

open Astterm
open Closure
open Declarations
open Dyn
open Libobject
open Pattern
open Pp
open Rawterm
open Sign
open Tacred
open Util
open Names
open Pfedit
open Proof_type
open Tacmach
open Tactic_debug
open Coqast
open Ast
open Term

let err_msg_tactic_not_found macro_loc macro =
  user_err_loc
    (macro_loc,"macro_expand",
     [<'sTR "Tactic macro "; 'sTR macro; 'sPC; 'sTR "not found">])

(* Values for interpretation *)
type value =
  | VTactic of tactic
  | VFTactic of tactic_arg list * (tactic_arg list->tactic)
  | VRTactic of (goal list sigma * validation)
  | VContext of (interp_sign -> goal sigma -> value)
  | VArg of tactic_arg
  | VFun of (string * value) list * string option list * Coqast.t
  | VVoid
  | VRec of value ref

(* Signature for interpretation: val_interp and interpretation functions *)
and interp_sign =
  enamed_declarations * Environ.env * (string * value) list *
    (int * constr) list * goal sigma option * debug_info

(* For tactic_of_value *)
exception NotTactic

(* Gives the tactic corresponding to the tactic value *)
let tactic_of_value vle g =
  match vle with
  | VTactic tac -> (tac g)
  | VFTactic (largs,f) -> (f largs g) 
  | VRTactic res -> res
  | _ -> raise NotTactic

(* Gives the identifier corresponding to an Identifier tactic_arg *)
let id_of_Identifier = function
  | Identifier id -> id
  | _ ->
    anomalylabstrm "id_of_Identifier" [<'sTR "Not an IDENTIFIER tactic_arg">]

(* Gives the constr corresponding to a Constr tactic_arg *)
let constr_of_Constr = function
  | Constr c -> c
  | _ -> anomalylabstrm "constr_of_Constr" [<'sTR "Not a Constr tactic_arg">]

(* Gives the constr corresponding to a Constr_context tactic_arg *)
let constr_of_Constr_context = function
  | Constr_context c -> c
  | _ ->
    anomalylabstrm "constr_of_Constr_context" [<'sTR
      "Not a Constr_context tactic_arg">]

(* Transforms a named_context into a (string * constr) list *)
let make_hyps = List.map (fun (id,_,typ) -> (string_of_id id,body_of_type typ))

(* Transforms an id into a constr if possible *)
let constr_of_id id = function
  | None -> raise Not_found
  | Some goal ->
    let hyps = pf_hyps goal in
    if mem_named_context id hyps then
      mkVar id
    else
      let csr = Declare.global_reference CCI id in
      (match kind_of_term csr with
      | IsVar _ -> raise Not_found
      | _ -> csr)

(* Extracted the constr list from lfun *)
let rec constr_list goalopt = function
  | (str,VArg(Constr c))::tl -> (id_of_string str,c)::(constr_list goalopt tl)
  | (str,VArg(Identifier id))::tl ->
    (try (id_of_string str,(constr_of_id id goalopt))::(constr_list goalopt tl)
     with | Not_found -> (constr_list goalopt tl))

(*    (match goalopt with
    | None -> constr_list goalopt tl
    | Some goal ->
      let hyps = pf_hyps goal in
      if mem_named_context id hyps then
        (id_of_string str,mkVar id)::(constr_list goalopt tl)
      else
        (try
           let csr = Declare.global_reference CCI id in
           (match kind_of_term csr with
           | IsVar _ -> constr_list goalopt tl
  	   | _ -> (id_of_string str,csr)::(constr_list goalopt tl))
         with
	 | Not_found -> (constr_list goalopt tl)))*)

(*      (try
         let csr = Declare.global_reference CCI id in
         (match kind_of_term csr with
         | IsVar idc ->
           if mem_named_context idc hyps then
             (id_of_string str,csr)::(constr_list goalopt tl)
           else
             constr_list goalopt tl
	 | _ ->
           (id_of_string str,Declare.global_reference CCI id)::
             (constr_list goalopt tl))
       with
      |	Not_found ->
        if mem_named_context id (pf_hyps goal) then
          (id_of_string str,mkVar id)::(constr_list goalopt tl)
        else
          constr_list goalopt tl))*)
  | _::tl -> constr_list goalopt tl
  | [] -> []

(* For user tactics *)
let ((ocamlIn : (unit -> Coqast.t) -> Dyn.t),
     (ocamlOut : Dyn.t -> (unit -> Coqast.t))) = create "ocaml"

(* To provide the tactic expressions *)
let loc = (0,0)
let tacticIn t = Dynamic (loc,ocamlIn t)

(* References for dynamic interpretation of user tactics. They are all
   initialized with dummy values *)
let r_evc     = ref Evd.empty
let r_env     = ref Environ.empty_env
let r_lfun    = ref []
let r_lmatch  = ref []
let r_goalopt = ref None
let r_debug   = ref DebugOn

(* Updates the references with the current environment *)
let env_update (evc,env,lfun,lmatch,goalopt,debug) =
  r_evc     := evc;
  r_env     := env;
  r_lfun    := lfun;
  r_lmatch  := lmatch;
  r_goalopt := goalopt;
  r_debug   := debug

(* Table of interpretation functions *)
let interp_tab =
  (Hashtbl.create 17 : (string , interp_sign -> Coqast.t -> value) Hashtbl.t)

(* Adds an interpretation function *)
let interp_add (ast_typ,interp_fun) =
  try
    Hashtbl.add interp_tab ast_typ interp_fun
  with
      Failure _ ->
        errorlabstrm "interp_add"
          [<'sTR "Cannot add the interpretation function for "; 'sTR ast_typ;
            'sTR " twice">]

(* Adds a possible existing interpretation function *)
let overwriting_interp_add (ast_typ,interp_fun) =
  if Hashtbl.mem interp_tab ast_typ then
  begin
    Hashtbl.remove interp_tab ast_typ;
    warning ("Overwriting definition of tactic interpreter command " ^ ast_typ)
  end;
  Hashtbl.add interp_tab ast_typ interp_fun

(* Finds the interpretation function corresponding to a given ast type *)
let look_for_interp = Hashtbl.find interp_tab

(* Globalizes the identifier *)
let glob_const_nvar loc env qid =
  try
    (* We first look for a variable of the current proof *)
    match repr_qualid qid with
      | [],s ->
	  let id = id_of_string s in
	  (* lookup_value may raise Not_found *)
	  (match Environ.lookup_named_value id env with
	     | Some _ -> EvalVarRef id
	     | None -> error (s^" does not denote an evaluable constant"))
      | _ -> raise Not_found
  with Not_found ->
  try
    match Nametab.locate qid with
      | ConstRef sp when Environ.evaluable_constant (Global.env ()) sp ->
	  EvalConstRef sp
      | VarRef sp when
	  Environ.evaluable_named_decl (Global.env ()) (basename sp) ->
	  EvalVarRef (basename sp)
      | _ -> error ((string_of_qualid qid) ^
		    " does not denote an evaluable constant")
  with Not_found ->
    Pretype_errors.error_global_not_found_loc loc qid

let qid_interp = function
  | Node (loc, "QUALIDARG", p) -> interp_qualid p
  | ast -> 
      anomaly_loc (Ast.loc ast, "Tacinterp.qid_interp",[<'sTR
        "Unrecognizable qualid ast: "; print_ast ast>])

(* Summary and Object declaration *)
let mactab = ref Gmap.empty

let lookup id = Gmap.find id !mactab

let _ = 
  let init () = mactab := Gmap.empty in
  let freeze () = !mactab in
  let unfreeze fs = mactab := fs in
  Summary.declare_summary "tactic-definition"
    { Summary.freeze_function   = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function     = init;
      Summary.survive_section   = false }

(* Unboxes the tactic_arg *)
let unvarg = function
  | VArg a -> a
  | _ -> errorlabstrm "unvarg" [<'sTR "Not a tactic argument">]

(* Unboxes VRec *)
let unrec = function
  | VRec v -> !v
  | a -> a

(* Unboxes REDEXP *)
let unredexp = function
  | Redexp c -> c
  | _ ->  errorlabstrm "unredexp" [<'sTR "Not a REDEXP tactic_arg">]

(* Reads the head of Fun *)
let read_fun ast =
  let rec read_fun_rec = function
    | Node(_,"VOID",[])::tl -> None::(read_fun_rec tl)
    | Nvar(_,s)::tl -> (Some s)::(read_fun_rec tl)
    | [] -> []
    | _ ->
      anomalylabstrm "Tacinterp.read_fun_rec" [<'sTR "Fun not well formed">]
  in
    match ast with
      | Node(_,"FUNVAR",l) -> read_fun_rec l
      | _ ->
        anomalylabstrm "Tacinterp.read_fun" [<'sTR "Fun not well formed">]

(* Reads the clauses of a Rec *)
let rec read_rec_clauses = function
  | [] -> []
  | Node(_,"RECCLAUSE",[Nvar(_,name);it;body])::tl ->
    (name,it,body)::(read_rec_clauses tl)
  |_ ->
    anomalylabstrm "Tacinterp.read_rec_clauses"
      [<'sTR "Rec not well formed">]

(* Associates variables with values and gives the remaining variables and
   values *)
let head_with_value (lvar,lval) =
  let rec head_with_value_rec lacc = function
    | ([],[]) -> (lacc,[],[])
    | (vr::tvr,ve::tve) ->
      (match vr with
      |	None -> head_with_value_rec lacc (tvr,tve)
      | Some v -> head_with_value_rec ((v,ve)::lacc) (tvr,tve))
    | (vr,[]) -> (lacc,vr,[])
    | ([],ve) -> (lacc,[],ve)
  in
    head_with_value_rec [] (lvar,lval)

(* Type of patterns *)
type match_pattern =
  | Term of constr_pattern
  | Subterm of string option * constr_pattern

(* Type of hypotheses for a Match Context rule *)
type match_context_hyps =
  | NoHypId of match_pattern
  | Hyp of string * match_pattern

(* Type of a Match rule for Match Context and Match *)
type match_rule=
  | Pat of match_context_hyps list * match_pattern * Coqast.t
  | All of Coqast.t

(* Gives a context couple if there is a context identifier *)
let give_context ctxt = function
  | None -> []
  | Some id -> [id,VArg (Constr_context ctxt)]

(* Gives the ast of a COMMAND ast node *)
let ast_of_command = function
  | Node(_,"COMMAND",[c]) -> c
  | ast ->
    anomaly_loc (Ast.loc ast, "Tacinterp.ast_of_command",[<'sTR
      "Not a COMMAND ast node: "; print_ast ast>])

(* Reads a pattern *)
let read_pattern evc env lfun = function
  | Node(_,"SUBTERM",[Nvar(_,s);pc]) ->
    Subterm (Some s,snd (interp_constrpattern_gen evc env lfun (ast_of_command
      pc)))
  | Node(_,"SUBTERM",[pc]) ->
    Subterm (None,snd (interp_constrpattern_gen evc env lfun (ast_of_command
      pc)))
  | Node(_,"TERM",[pc]) ->
    Term (snd (interp_constrpattern_gen evc env lfun (ast_of_command pc)))
  | ast ->
    anomaly_loc (Ast.loc ast, "Tacinterp.read_pattern",[<'sTR
      "Not a pattern ast node: "; print_ast ast>])

(* Reads the hypotheses of a Match Context rule *)
let rec read_match_context_hyps evc env lfun = function
  | Node(_,"MATCHCONTEXTHYPS",[mp])::tl ->
    (NoHypId (read_pattern evc env lfun mp))::(read_match_context_hyps evc env
      lfun tl)
  | Node(_,"MATCHCONTEXTHYPS",[Nvar(_,s);mp])::tl ->
    (Hyp (s,read_pattern evc env lfun mp))::(read_match_context_hyps evc env
      lfun tl)
  | ast::tl ->
    anomaly_loc (Ast.loc ast, "Tacinterp.read_match_context_hyp",[<'sTR
      "Not a MATCHCONTEXTHYP ast node: "; print_ast ast>])
  | [] -> []

(* Reads the rules of a Match Context *)
let rec read_match_context_rule evc env lfun = function
  | Node(_,"MATCHCONTEXTRULE",[tc])::tl ->
    (All tc)::(read_match_context_rule evc env lfun tl)
  | Node(_,"MATCHCONTEXTRULE",l)::tl ->
    let rl=List.rev l in
      (Pat (read_match_context_hyps evc env lfun (List.rev (List.tl (List.tl
        rl))),read_pattern evc env lfun (List.nth rl 1),List.hd
        rl))::(read_match_context_rule evc env lfun tl)
  | ast::tl ->
    anomaly_loc (Ast.loc ast, "Tacinterp.read_match_context_rule",[<'sTR
      "Not a MATCHCONTEXTRULE ast node: "; print_ast ast>])
  | [] -> []

(* Reads the rules of a Match *)
let rec read_match_rule evc env lfun = function
  | Node(_,"MATCHRULE",[te])::tl ->
    (All te)::(read_match_rule evc env lfun tl)
  | Node(_,"MATCHRULE",[mp;te])::tl ->
    (Pat ([],read_pattern evc env lfun mp,te))::(read_match_rule evc env lfun
      tl)
  | ast::tl ->
    anomaly_loc (Ast.loc ast, "Tacinterp.read_match_context_rule",[<'sTR
      "Not a MATCHRULE ast node: "; print_ast ast>])
  | [] -> []

(* For Match Context and Match *)
exception No_match
exception Not_coherent_metas

(* Evaluation with FailError catching *)
let eval_with_fail interp ast goal =
  try 
    (match interp ast with
    | VTactic tac -> VRTactic (tac goal)
    | VFTactic (largs,f) -> VRTactic (f largs goal)
    | a -> a)
  with | FailError lvl ->
    if lvl = 0 then
      raise No_match
    else
      raise (FailError (lvl - 1))

(* Verifies if the matched list is coherent with respect to lcm *)
let rec verify_metas_coherence lcm = function
  | (num,csr)::tl ->
    if (List.for_all
         (fun (a,b) ->
            if a=num then
              eq_constr b csr
            else
              true) lcm) then
      (num,csr)::(verify_metas_coherence lcm tl)
    else
      raise Not_coherent_metas
  | [] -> []

(* Tries to match a pattern and a constr *)
let apply_matching pat csr =
  try
    (Pattern.matches pat csr)
  with
     PatternMatchingFailure -> raise No_match

(* Tries to match one hypothesis pattern with a list of hypotheses *)
let apply_one_mhyp_context lmatch mhyp lhyps noccopt =
  let get_pattern = function
    | Hyp (_,pat) -> pat
    | NoHypId pat -> pat
  and get_id_couple id = function
    | Hyp(idpat,_) -> [idpat,VArg (Identifier (id_of_string id))]
    | NoHypId _ -> [] in
  let rec apply_one_mhyp_context_rec mhyp lhyps_acc nocc = function
    | (id,hyp)::tl ->
      (match (get_pattern mhyp) with
      | Term t ->
        (try
          let lmeta = verify_metas_coherence lmatch (Pattern.matches t hyp) in
          (get_id_couple id mhyp,[],lmeta,tl,(id,hyp),None)
         with | PatternMatchingFailure | Not_coherent_metas ->
          apply_one_mhyp_context_rec mhyp (lhyps_acc@[id,hyp]) 0 tl)
      | Subterm (ic,t) ->
        (try
          let (lm,ctxt) = sub_match nocc t hyp in
          let lmeta = verify_metas_coherence lmatch lm in
          (get_id_couple id mhyp,give_context ctxt
            ic,lmeta,tl,(id,hyp),Some nocc)
         with
        | NextOccurrence _ ->
          apply_one_mhyp_context_rec mhyp (lhyps_acc@[id,hyp]) 0 tl
        | Not_coherent_metas ->
          apply_one_mhyp_context_rec mhyp lhyps_acc (nocc + 1) ((id,hyp)::tl)))
    | [] -> raise No_match in
  let nocc =
    match noccopt with
    | None -> 0
    | Some n -> n in
  apply_one_mhyp_context_rec mhyp [] nocc lhyps

(* Prepares the lfun list for constr substitutions *)
let rec make_subs_list = function
  | (id,VArg (Identifier i))::tl ->
    (id_of_string id,mkVar i)::(make_subs_list tl)
  | (id,VArg (Constr c))::tl ->
    (id_of_string id,c)::(make_subs_list tl)
  | e::tl -> make_subs_list tl
  | [] -> []

(* Debug reference *)
let debug =ref DebugOff

(* Sets the debugger mode *)
let set_debug pos = debug := pos

(* Gives the state of debug *)
let get_debug () = !debug

(* Interprets any expression *)
let rec val_interp (evc,env,lfun,lmatch,goalopt,debug) ast =

(* mSGNL [<print_ast ast>]; *)
(* mSGNL [<print_ast (Termast.ast_of_constr false (Pretty.assumptions_for_print []) c)>] *)

  let value_interp debug =
  match ast with
    | Node(_,"APP",l) ->
      let fv = val_interp (evc,env,lfun,lmatch,goalopt,debug) (List.hd l)
      and largs = List.map (val_interp (evc,env,lfun,lmatch,goalopt,debug))
        (List.tl l) in
      app_interp (evc,env,lfun,lmatch,goalopt,debug) fv largs ast
    | Node(_,"FUN",l) -> VFun (lfun,read_fun (List.hd l),List.nth l 1)
    | Node(_,"REC",l) ->
      rec_interp (evc,env,lfun,lmatch,goalopt,debug) ast l
    | Node(_,"LET",[Node(_,"LETDECL",l);u]) ->
      let addlfun=letin_interp (evc,env,lfun,lmatch,goalopt,debug) ast l in
        val_interp (evc,env,(lfun@addlfun),lmatch,goalopt,debug) u
    | Node(_,"LETCUT",[Node(_,"LETDECL",l)]) ->
      VTactic (letcut_interp (evc,env,lfun,lmatch,goalopt,debug) ast l)
    | Node(_,"MATCHCONTEXT",lmr) ->
      match_context_interp (evc,env,lfun,lmatch,goalopt,debug) ast lmr
    | Node(_,"MATCH",lmr) ->
      match_interp (evc,env,lfun,lmatch,goalopt,debug) ast lmr
    | Node(_,"IDTAC",[]) -> VTactic tclIDTAC
    | Node(_,"FAIL",[]) -> VTactic (tclFAIL 0)
    | Node(_,"FAIL",[n]) -> VTactic (tclFAIL (num_of_ast n))
    | Node(_,"TACTICLIST",l) ->
      VTactic (interp_semi_list tclIDTAC lfun lmatch debug l)
    | Node(_,"DO",[n;tac]) ->
      VTactic (tclDO (num_of_ast n) (tac_interp lfun lmatch debug tac))
    | Node(_,"TRY",[tac]) ->
      VTactic (tclTRY (tac_interp lfun lmatch debug tac))
    | Node(_,"INFO",[tac]) ->
      VTactic (tclINFO (tac_interp lfun lmatch debug tac))
    | Node(_,"REPEAT",[tac]) ->
      VTactic (tclREPEAT (tac_interp lfun lmatch debug tac))
    | Node(_,"ORELSE",[tac1;tac2]) ->
      VTactic (tclORELSE (tac_interp lfun lmatch debug tac1)
        (tac_interp lfun lmatch debug tac2))
    | Node(_,"FIRST",l) ->
      VTactic (tclFIRST (List.map (tac_interp lfun lmatch debug) l))
    | Node(_,"TCLSOLVE",l) ->
      VTactic (tclSOLVE (List.map (tac_interp lfun lmatch debug) l))
    | Node(loc0,"APPTACTIC",[Node(loc1,s,l)]) ->
      val_interp (evc,env,lfun,lmatch,goalopt,debug)
        (Node(loc0,"APP",[Node(loc1,"PRIM-TACTIC",[Node(loc1,s,[])])]@l))
    | Node(_,"PRIM-TACTIC",[Node(loc,opn,[])]) ->
      VFTactic ([],(interp_atomic opn))
    | Node(_,"VOID",[]) -> VVoid
    | Nvar(_,s) ->
      (try (unrec (List.assoc s lfun))
       with | Not_found ->
         (try (vcontext_interp (evc,env,lfun,lmatch,goalopt,debug) (lookup s))
          with | Not_found -> VArg (Identifier (id_of_string s))))
    | Node(_,"QUALID",[Nvar(_,s)]) ->
      (try (unrec (List.assoc s lfun))
       with | Not_found ->
         (try (vcontext_interp (evc,env,lfun,lmatch,goalopt,debug) (lookup s))
          with | Not_found -> VArg (Identifier (id_of_string s))))
    | Str(_,s) -> VArg (Quoted_string s)
    | Num(_,n) -> VArg (Integer n)
    | Node(_,"COMMAND",[c]) ->
      com_interp (evc,env,lfun,lmatch,goalopt,debug) c
    | Node(_,"CASTEDCOMMAND",[c]) ->
      cast_com_interp (evc,env,lfun,lmatch,goalopt,debug) c
    | Node(_,"CASTEDOPENCOMMAND",[c]) ->
      cast_opencom_interp (evc,env,lfun,lmatch,goalopt,debug) c
    | Node(_,"BINDINGS",astl) ->
      VArg (Cbindings (List.map (bind_interp
        (evc,env,lfun,lmatch,goalopt,debug)) astl))
    | Node(_,"REDEXP",[Node(_,redname,args)]) ->
      VArg (Redexp (redexp_of_ast (evc,env,lfun,lmatch,goalopt,debug)
        (redname,args)))
    | Node(_,"CLAUSE",cl) ->
      VArg (Clause (List.map (fun ast -> id_of_Identifier (unvarg (val_interp
        (evc,env,lfun,lmatch,goalopt,debug) ast))) cl))
    | Node(_,"TACTIC",[ast]) ->
      VArg (Tac ((tac_interp lfun lmatch debug ast),ast))
(*Remains to treat*)
    | Node(_,"FIXEXP", [Nvar(_,s); Num(_,n);Node(_,"COMMAND",[c])]) ->
      VArg ((Fixexp (id_of_string s,n,c)))
    | Node(_,"COFIXEXP", [Nvar(_,s); Node(_,"COMMAND",[c])]) ->
      VArg ((Cofixexp (id_of_string s,c)))
(*End of Remains to treat*)
    | Node(_,"INTROPATTERN", [ast]) ->
      VArg ((Intropattern (cvt_intro_pattern
        (evc,env,lfun,lmatch,goalopt,debug) ast)))
    | Node(_,"LETPATTERNS",astl) ->
      VArg (Letpatterns (List.fold_left (cvt_letpattern
        (evc,env,lfun,lmatch,goalopt,debug)) (None,[]) astl))
    | Node(loc,s,l) ->
      (try
         ((look_for_interp s) (evc,env,lfun,lmatch,goalopt,debug) ast)
       with
           Not_found ->
             val_interp (evc,env,lfun,lmatch,goalopt,debug)
               (Node(dummy_loc,"APPTACTIC",[ast])))
    | Dynamic(_,t) -> 
      env_update (evc,env,lfun,lmatch,goalopt,debug);
      let f = (ocamlOut t) in
      Obj.magic (val_interp (evc,env,lfun,lmatch,goalopt,debug) (f ()))
    | _ ->
      anomaly_loc (Ast.loc ast, "Tacinterp.val_interp",[<'sTR
        "Unrecognizable ast: "; print_ast ast>]) in
  if debug = DebugOn then
    match debug_prompt goalopt ast with
    | Exit -> VTactic tclIDTAC
    | v -> value_interp v
  else
    value_interp debug

(* Interprets an application node *)
and app_interp (evc,env,lfun,lmatch,goalopt,debug) fv largs ast =
  match fv with
    | VFTactic(l,f) -> VFTactic(l@(List.map unvarg largs),f)
    | VFun(olfun,var,body) ->
      let (newlfun,lvar,lval)=head_with_value (var,largs) in
      if lvar=[] then
        if lval=[] then
          val_interp (evc,env,(olfun@newlfun),lmatch,goalopt,debug) body
        else
          app_interp (evc,env,lfun,lmatch,goalopt,debug) (val_interp (evc,env,
            (olfun@newlfun),lmatch,goalopt,debug) body) lval ast
      else
        VFun(olfun@newlfun,lvar,body)
    | _ ->
      anomaly_loc (Ast.loc ast, "Tacinterp.app_interp",[<'sTR
        "Illegal application: "; print_ast ast>])

(* Interprets recursive expressions *)
and rec_interp (evc,env,lfun,lmatch,goalopt,debug) ast = function
  | [Node(_,"RECCLAUSE",_)] as l ->
     let (name,var,body) = List.hd (read_rec_clauses l)
     and ve = ref VVoid in
       let newve = VFun(lfun@[(name,VRec ve)],read_fun var,body) in
       begin
         ve:=newve;
         !ve
       end
  | [Node(_,"RECDECL",l);u] ->
    let lrc = read_rec_clauses l in
    let lref = Array.to_list (Array.make (List.length lrc) (ref VVoid)) in
    let lenv = List.fold_right2 (fun (name,_,_) vref l -> (name,VRec vref)::l)
      lrc lref [] in
    let lve = List.map (fun (name,var,body) -> (name,VFun(lfun@lenv,read_fun
      var,body))) lrc in
    begin
      List.iter2 (fun vref (_,ve) -> vref:=ve) lref lve;
      val_interp (evc,env,(lfun@lve),lmatch,goalopt,debug) u
    end
  | _ ->
    anomaly_loc (Ast.loc ast, "Tacinterp.rec_interp",[<'sTR
      "Rec not well formed: "; print_ast ast>])

(* Interprets the clauses of a Let *)
and let_interp (evc,env,lfun,lmatch,goalopt,debug) ast = function
  | [] -> []
  | Node(_,"LETCLAUSE",[Nvar(_,id);t])::tl ->
    (id,val_interp (evc,env,lfun,lmatch,goalopt,debug) t)::
      (let_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl)
  | _ ->
    anomaly_loc (Ast.loc ast, "Tacinterp.let_interp",[<'sTR
      "Let not well formed: "; print_ast ast>])

(* Interprets the clauses of a LetCutIn *)
and letin_interp (evc,env,lfun,lmatch,goalopt,debug) ast = function
  | [] -> []
  | Node(_,"LETCLAUSE",[Nvar(_,id);t])::tl ->
    (id,val_interp (evc,env,lfun,lmatch,goalopt,debug) t)::
      (letin_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl)
  | Node(_,"LETCUTCLAUSE",[Nvar(_,s);com;tce])::tl ->
    let id = id_of_string s
    and typ =
      constr_of_Constr (unvarg
      (val_interp (evc,env,lfun,lmatch,goalopt,debug) com))
    and tac = val_interp (evc,env,lfun,lmatch,goalopt,debug) tce in
    (match tac with
    | VArg (Constr csr) ->
      (s,VArg (Constr (mkCast (csr,typ))))::
      (letin_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl)
    | VArg (Identifier id) ->
      (try
         (s,VArg (Constr (mkCast (constr_of_id id goalopt,typ))))::
         (letin_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl)
       with | Not_found ->
         errorlabstrm "Tacinterp.letin_interp"
         [< 'sTR "Term or tactic expected" >])
    | _ ->
      (try
         let t = tactic_of_value tac in
         let ndc =
           (match goalopt with
           | None -> Global.named_context ()
           | Some g -> pf_hyps g) in
         start_proof id Declare.NeverDischarge ndc typ;
         by t;
         let (_,({const_entry_body = pft; const_entry_type = _},_)) =
           cook_proof () in
         delete_proof id;
         (s,VArg (Constr (mkCast (pft,typ))))::
         (letin_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl)
       with | NotTactic ->
         delete_proof id;
         errorlabstrm "Tacinterp.letin_interp"
         [< 'sTR "Term or tactic expected" >]))
  | _ ->
    anomaly_loc (Ast.loc ast, "Tacinterp.letin_interp",
    [<'sTR "LetIn not well formed: "; print_ast ast>])

(* Interprets the clauses of a LetCut *)
and letcut_interp (evc,env,lfun,lmatch,goalopt,debug) ast = function
  | [] -> tclIDTAC
  | Node(_,"LETCUTCLAUSE",[Nvar(_,s);com;tce])::tl ->
    let id = id_of_string s
    and typ =
      constr_of_Constr (unvarg
      (val_interp (evc,env,lfun,lmatch,goalopt,debug) com))
    and tac = val_interp (evc,env,lfun,lmatch,goalopt,debug) tce
    and (ndc,ccl) =
      match goalopt with
      |	None -> 
        errorlabstrm "Tacinterp.letcut_interp" [< 'sTR
        "Do not use Let for toplevel definitions, use Lemma, ... instead" >]
      |	Some g -> (pf_hyps g,pf_concl g) in
    (match tac with
    | VArg (Constr csr) ->
      let cutt = interp_atomic "Cut" [Constr typ]
      and exat = interp_atomic "Exact" [Constr csr] in
      tclTHENS cutt [tclTHEN (introduction id)
      (letcut_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl);exat]

(*      let lic = mkLetIn (Name id,csr,typ,ccl) in
      let ntac = refine (mkCast (mkMeta (Environ.new_meta ()),lic)) in
      tclTHEN ntac (tclTHEN (introduction id)
      (letcut_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl))*)

    | VArg (Identifier ir) ->
      (try
         let cutt = interp_atomic "Cut" [Constr typ]
         and exat = interp_atomic "Exact" [Constr (constr_of_id ir goalopt)] in
         tclTHENS cutt [tclTHEN (introduction id)
         (letcut_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl);exat]
       with | Not_found ->
         errorlabstrm "Tacinterp.letin_interp"
         [< 'sTR "Term or tactic expected" >])
    | _ ->
      (try
         let t = tactic_of_value tac in
         start_proof id Declare.NeverDischarge ndc typ;
         by t;
         let (_,({const_entry_body = pft; const_entry_type = _},_)) =
           cook_proof () in
         delete_proof id;
         let cutt = interp_atomic "Cut" [Constr typ]
         and exat = interp_atomic "Exact" [Constr pft] in
         tclTHENS cutt [tclTHEN (introduction id)
         (letcut_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl);exat]

(*         let lic = mkLetIn (Name id,pft,typ,ccl) in
         let ntac = refine (mkCast (mkMeta (Environ.new_meta ()),lic)) in
         tclTHEN ntac (tclTHEN (introduction id)
         (letcut_interp (evc,env,lfun,lmatch,goalopt,debug) ast tl))*)
       with | NotTactic ->
         delete_proof id;
         errorlabstrm "Tacinterp.letcut_interp"
         [< 'sTR "Term or tactic expected" >]))
  | _ ->
    anomaly_loc (Ast.loc ast, "Tacinterp.letcut_interp",[<'sTR
      "LetCut not well formed: "; print_ast ast>])

(* Interprets the Match Context expressions *)
and match_context_interp (evc,env,lfun,lmatch,goalopt,debug) ast lmr =
(*  let goal =
    (match goalopt with
    | None ->
      errorlabstrm "Tacinterp.apply_match_context" [< 'sTR
        "No goal available" >]
    | Some g -> g) in*)
  let rec apply_goal_sub (evc,env,lfun,lmatch,goalopt,debug) goal nocc (id,c)
    csr mt mhyps hyps =
    try
      let (lgoal,ctxt) = sub_match nocc c csr in
      let lctxt = give_context ctxt id in
      if mhyps = [] then
        eval_with_fail (val_interp
          (evc,env,lctxt@lfun,lgoal@lmatch,Some goal,debug)) mt goal
      else
        apply_hyps_context evc env (lctxt@lfun) lmatch goal debug mt lgoal
          mhyps hyps
    with
    | (FailError _) as e -> raise e
    | NextOccurrence _ -> raise No_match
    | No_match | _ ->
      apply_goal_sub (evc,env,lfun,lmatch,goalopt,debug) goal (nocc + 1) (id,c)
      csr mt mhyps hyps in
  let rec apply_match_context (evc,env,lfun,lmatch,goalopt,debug) goal =
    function
    | (All t)::tl ->
      (try
         eval_with_fail (val_interp (evc,env,lfun,lmatch,Some goal,debug)) t
           goal
       with No_match | _ ->
         apply_match_context (evc,env,lfun,lmatch,goalopt,debug) goal tl)
    | (Pat (mhyps,mgoal,mt))::tl ->
      let hyps = make_hyps (List.rev (pf_hyps goal))
      and concl = pf_concl goal in
      (match mgoal with
      |	Term mg ->
        (try
           (let lgoal = apply_matching mg concl in
            begin
            db_matched_concl debug env concl;
            if mhyps = [] then
              eval_with_fail (val_interp
                (evc,env,lfun,lgoal@lmatch,Some goal,debug)) mt goal
            else
              apply_hyps_context evc env lfun lmatch goal debug mt lgoal mhyps
                hyps
            end)
         with | No_match | _ ->
           apply_match_context (evc,env,lfun,lmatch,goalopt,debug) goal tl)
      |	Subterm (id,mg) ->
        (try
          apply_goal_sub (evc,env,lfun,lmatch,goalopt,debug) goal 0 (id,mg)
          concl mt mhyps hyps
         with
        | No_match | _ ->
          apply_match_context (evc,env,lfun,lmatch,goalopt,debug) goal tl))
    | _ ->
      errorlabstrm "Tacinterp.apply_match_context" [<'sTR
        "No matching clauses for Match Context">] in
  let app_wo_goal = 
    (fun (evc,env,lfun,lmatch,goalopt,debug) goal ->
     apply_match_context (evc,env,lfun,lmatch,goalopt,debug) goal
     (read_match_context_rule evc env (constr_list goalopt lfun) lmr)) in
 (match goalopt with
    | None -> VContext app_wo_goal
    | Some g -> app_wo_goal (evc,env,lfun,lmatch,goalopt,debug) g)

(*  apply_match_context evc env lfun lmatch goal (read_match_context_rule evc env
    (constr_list goalopt lfun) lmr)*)

(* Tries to match the hypotheses in a Match Context *)
and apply_hyps_context evc env lfun_glob lmatch_glob goal debug mt lgmatch
  mhyps hyps =
  let rec apply_hyps_context_rec evc env lfun_glob lmatch_glob goal mt lfun
    lmatch mhyps lhyps_mhyp lhyps_rest noccopt =
    match mhyps with
      | hd::tl ->
        let (lid,lc,lm,newlhyps,hyp_match,noccopt) =
          apply_one_mhyp_context lmatch hd lhyps_mhyp noccopt in
        begin
        db_matched_hyp debug env hyp_match;
        (try
        if tl = [] then
            eval_with_fail (val_interp (evc,env,(lfun@lid@lc@lfun_glob),
              (lmatch@lm@lmatch_glob),Some goal,debug)) mt goal
        else
          let nextlhyps =
            List.fold_left (fun l e -> if e = hyp_match then l else l@[e]) []
              lhyps_rest in
          apply_hyps_context_rec evc env lfun_glob lmatch_glob goal mt
            (lfun@lid@lc) (lmatch@lm) tl nextlhyps nextlhyps None
         with
        | (FailError _) as e -> raise e
        | _ ->
          (match noccopt with
          | None ->
            apply_hyps_context_rec evc env lfun_glob lmatch_glob goal mt lfun
              lmatch mhyps newlhyps lhyps_rest None
          | Some nocc ->
            apply_hyps_context_rec evc env lfun_glob lmatch_glob goal mt lfun
              lmatch mhyps (hyp_match::newlhyps) lhyps_rest (Some (nocc +
              1))))
        end
      |	[] ->
        anomalylabstrm "apply_hyps_context_rec" [<'sTR
          "Empty list should not occur" >] in
  apply_hyps_context_rec evc env lfun_glob lmatch_glob goal mt [] lgmatch mhyps
    hyps hyps None

(* Interprets a VContext value *)
and vcontext_interp (evc,env,lfun,lmatch,goalopt,debug) = function
  | (VContext f) as v ->
    (match goalopt with
    | None -> v
    | Some g -> f (evc,env,lfun,lmatch,goalopt,debug) g)
  | v -> v

(* Interprets the Match expressions *)
and match_interp (evc,env,lfun,lmatch,goalopt,debug) ast lmr =
  let rec apply_sub_match (evc,env,lfun,lmatch,goalopt,debug) nocc (id,c) csr
    mt =
    match goalopt with
    | None ->
      (try 
        let (lm,ctxt) = sub_match nocc c csr in
        let lctxt = give_context ctxt id in
        val_interp (evc,env,lctxt@lfun,lm@lmatch,goalopt,debug) mt
       with | NextOccurrence _ -> raise No_match)
    | Some g ->
      (try
        let (lm,ctxt) = sub_match nocc c csr in
        let lctxt = give_context ctxt id in
        eval_with_fail (val_interp
          (evc,env,lctxt@lfun,lm@lmatch,goalopt,debug)) mt g
       with
       | NextOccurrence n -> raise No_match
       | (FailError _) as e -> raise e
       | _ ->
         apply_sub_match (evc,env,lfun,lmatch,goalopt,debug) (nocc + 1) (id,c)
           csr mt)
  in
  let rec apply_match (evc,env,lfun,lmatch,goalopt,debug) csr = function
    | (All t)::tl -> val_interp (evc,env,lfun,lmatch,goalopt,debug) t
    | (Pat ([],mp,mt))::tl ->
      (match mp with
      |	Term c ->
        (try
           val_interp
             (evc,env,lfun,(apply_matching c csr)@lmatch,goalopt,debug) mt
         with | No_match ->
           apply_match (evc,env,lfun,lmatch,goalopt,debug) csr tl)
      |	Subterm (id,c) ->
        (try
           apply_sub_match (evc,env,lfun,lmatch,goalopt,debug) 0 (id,c) csr mt
         with | No_match ->
           apply_match (evc,env,lfun,lmatch,goalopt,debug) csr tl))
    | _ ->
      errorlabstrm "Tacinterp.apply_match" [<'sTR
        "No matching clauses for Match">] in
  let csr =
    constr_of_Constr (unvarg (val_interp (evc,env,lfun,lmatch,goalopt,debug)
      (List.hd lmr)))
  and ilr = read_match_rule evc env (constr_list goalopt lfun) (List.tl lmr) in
  apply_match (evc,env,lfun,lmatch,goalopt,debug) csr ilr

(* Interprets tactic expressions *)
and tac_interp lfun lmatch debug ast g =
  let evc = project g
  and env = pf_env g in
  try tactic_of_value (val_interp (evc,env,lfun,lmatch,(Some g),debug) ast) g
  with | NotTactic ->
    errorlabstrm "Tacinterp.tac_interp" [<'sTR
    "Interpretation gives a non-tactic value">]

(*    match (val_interp (evc,env,lfun,lmatch,(Some g),debug) ast) with
      | VTactic tac -> (tac g)
      | VFTactic (largs,f) -> (f largs g) 
      | VRTactic res -> res
      | _ ->
        errorlabstrm "Tacinterp.tac_interp" [<'sTR
          "Interpretation gives a non-tactic value">]*)

(* Interprets a primitive tactic *)
and interp_atomic opn args = vernac_tactic(opn,args)

(* Interprets sequences of tactics *)
and interp_semi_list acc lfun lmatch debug = function
  | (Node(_,"TACLIST",seq))::l ->
    interp_semi_list (tclTHENS acc (List.map (tac_interp lfun lmatch debug)
      seq)) lfun lmatch debug l
  | t::l ->
    interp_semi_list (tclTHEN acc (tac_interp lfun lmatch debug t)) lfun lmatch
      debug l
  | [] -> acc

(* Interprets bindings for tactics *)
and bind_interp (evc,env,lfun,lmatch,goalopt,debug) = function
  | Node(_,"BINDING", [Num(_,n);Node(loc,"COMMAND",[c])]) ->
    (NoDep n,constr_of_Constr (unvarg (val_interp
      (evc,env,lfun,lmatch,goalopt,debug) (Node(loc,"COMMAND",[c])))))
  | Node(_,"BINDING", [Nvar(loc0,s); Node(loc1,"COMMAND",[c])]) -> 
    (Dep (id_of_Identifier (unvarg (val_interp
      (evc,env,lfun,lmatch,goalopt,debug)
      (Nvar(loc0,s))))),constr_of_Constr (unvarg (val_interp
      (evc,env,lfun,lmatch,goalopt,debug) (Node(loc1,"COMMAND",[c])))))
  | Node(_,"BINDING", [Node(loc,"COMMAND",[c])]) ->
    (Com,constr_of_Constr (unvarg
      (val_interp (evc,env,lfun,lmatch,goalopt,debug)
      (Node(loc,"COMMAND",[c])))))
  | x ->
    errorlabstrm "bind_interp" [<'sTR "Not the expected form in binding";
      print_ast x>]

(* Interprets a COMMAND expression (in case of failure, returns Command) *)
and com_interp (evc,env,lfun,lmatch,goalopt,debug) = function
  | Node(_,"EVAL",[c;rtc]) ->
    let redexp = unredexp (unvarg (val_interp
      (evc,env,lfun,lmatch,goalopt,debug) rtc)) in
    VArg (Constr ((reduction_of_redexp redexp) env evc
		    (interp_constr_gen evc env (constr_list goalopt lfun)
		       lmatch c None)))
  | Node(_,"CONTEXT",[Nvar (_,s);c]) as ast ->
    (try
      let ic =
	interp_constr_gen evc env (constr_list goalopt lfun) lmatch c None
      and ctxt = constr_of_Constr_context (unvarg (List.assoc s lfun)) in
      VArg (Constr (subst_meta [-1,ic] ctxt))
     with
    | Not_found ->
      errorlabstrm "com_interp" [<'sTR "Unbound context identifier";
        print_ast ast>])
  | c ->
      VArg (Constr
	      (interp_constr_gen evc env (constr_list goalopt lfun) lmatch
		 c None))

(* Interprets a CASTEDCOMMAND expression *)
and cast_com_interp (evc,env,lfun,lmatch,goalopt,debug) com =
  match goalopt with
  | Some gl ->
    (match com with
    | Node(_,"EVAL",[c;rtc]) ->
      let redexp = unredexp (unvarg (val_interp
        (evc,env,lfun,lmatch,goalopt,debug) rtc)) in
      VArg (Constr ((reduction_of_redexp redexp) env evc (interp_constr_gen
        evc env (constr_list goalopt lfun) lmatch c (Some (pf_concl gl)))))
    | Node(_,"CONTEXT",[Nvar (_,s);c]) as ast ->
      (try
        let ic =
	  interp_constr_gen evc env (constr_list goalopt lfun) lmatch c None
        and ctxt = constr_of_Constr_context (unvarg (List.assoc s lfun)) in
        begin
          wARNING [<'sTR
            "Cannot pre-constrain the context expression with goal">];
          VArg (Constr (subst_meta [-1,ic] ctxt))
        end
       with
      |	Not_found ->
        errorlabstrm "cast_com_interp" [<'sTR "Unbound context identifier";
          print_ast ast>])
    | c ->
        VArg (Constr (interp_constr_gen evc env (constr_list goalopt lfun)
          lmatch c (Some (pf_concl gl)))))
  | None ->
    errorlabstrm "val_interp" [<'sTR "Cannot cast a constr without goal">]

(* Interprets a CASTEDOPENCOMMAND expression *)
and cast_opencom_interp (evc,env,lfun,lmatch,goalopt,debug) com =
  match goalopt with
  | Some gl ->
    (match com with
    | Node(_,"EVAL",[c;rtc]) ->
      let redexp = unredexp (unvarg (val_interp
        (evc,env,lfun,lmatch,goalopt,debug) rtc)) in
      VArg (Constr ((reduction_of_redexp redexp) env evc (interp_constr_gen
        evc env (constr_list goalopt lfun) lmatch c (Some (pf_concl gl)))))
    | Node(_,"CONTEXT",[Nvar (_,s);c]) as ast ->
      (try
        let ic =
	  interp_constr_gen evc env (constr_list goalopt lfun) lmatch c None
        and ctxt = constr_of_Constr_context (unvarg (List.assoc s lfun)) in
        begin
          wARNING [<'sTR
            "Cannot pre-constrain the context expression with goal">];
          VArg (Constr (subst_meta [-1,ic] ctxt))
        end
       with
      |	Not_found ->
        errorlabstrm "cast_opencom_interp" [<'sTR "Unbound context identifier";
          print_ast ast>])
    | c ->
        VArg
	  (OpenConstr (interp_openconstr_gen evc env (constr_list goalopt lfun)
			 lmatch c (Some (pf_concl gl)))))
  | None ->
    errorlabstrm "val_interp" [<'sTR "Cannot cast a constr without goal">]

and cvt_pattern (evc,env,lfun,lmatch,goalopt,debug) = function
  | Node(_,"PATTERN", Node(loc,"COMMAND",[com])::nums) ->
      let occs = List.map num_of_ast nums
      and csr = constr_of_Constr (unvarg (val_interp
        (evc,env,lfun,lmatch,goalopt,debug) (Node(loc,"COMMAND",[com])))) in
      let jdt = Typing.unsafe_machine env evc csr in
      (occs, jdt.Environ.uj_val, body_of_type jdt.Environ.uj_type)
  | arg -> invalid_arg_loc (Ast.loc arg,"cvt_pattern")

and cvt_unfold (evc,env,lfun,lmatch,goalopt,debug) = function
  | Node(_,"UNFOLD", com::nums) ->
(*
    (List.map num_of_ast nums,
     glob_const_nvar loc (id_of_Identifier (unvarg (val_interp
       (evc,env,lfun,lmatch,goalopt,debug) com))))
*)
      let qid = qid_interp com in
      (List.map num_of_ast nums, glob_const_nvar loc env qid)

  | arg -> invalid_arg_loc (Ast.loc arg,"cvt_unfold")

(* Interprets the arguments of Fold *)
and cvt_fold (evc,env,lfun,lmatch,goalopt,debug) = function
  | Node(_,"COMMAND",[c]) as ast ->
    constr_of_Constr (unvarg (val_interp (evc,env,lfun,lmatch,goalopt,debug)
      ast))
  | arg -> invalid_arg_loc (Ast.loc arg,"cvt_fold")

(* Interprets the reduction flags *)
and flag_of_ast (evc,env,lfun,lmatch,goalopt,debug) lf =
  let rec add_flag red = function
    | [] -> red
    | Node(_,"Beta",[])::lf -> add_flag (red_add red BETA) lf
    | Node(_,"Delta",[])::lf ->
	(match lf with
	   | Node(loc,"Unf",l)::lf ->
               let idl=
		 List.fold_right
		   (fun v red -> 
		      match glob_const_nvar loc env (qid_interp v) with
			| EvalVarRef id -> red_add red (VAR id)
			| EvalConstRef sp -> red_add red (CONST [sp])) l red
	       in add_flag idl lf
(*
(id_of_Identifier (unvarg
		   (val_interp (evc,env,lfun,lmatch,goalopt,debug) v)))) l
	       in add_flag (red_add red (CONST idl)) lf
*)
	   | Node(loc,"UnfBut",l)::lf ->
               let idl=
		 List.fold_right
		   (fun v red -> 
		      match glob_const_nvar loc env (qid_interp v) with
			| EvalVarRef id -> red_add red (VARBUT id)
			| EvalConstRef sp -> red_add red (CONSTBUT [sp])) l red
	       in add_flag idl lf

(*
		 List.map
		   (fun v -> glob_const_nvar loc (id_of_Identifier (unvarg
                   (val_interp (evc,env,lfun,lmatch,goalopt,debug) v)))) l
               in add_flag (red_add red (CONSTBUT idl)) lf
*)
	   | _ -> add_flag (red_add red DELTA) lf)
    | Node(_,"Iota",[])::lf -> add_flag (red_add red IOTA) lf
    | Node(loc,("Unf"|"UnfBut"),l)::_ ->
	user_err_loc(loc,"flag_of_ast",
                     [<'sTR "Delta must be specified just before">])

    | arg::_ -> invalid_arg_loc (Ast.loc arg,"flag_of_ast")
  in
  add_flag no_red lf;

(* Interprets a reduction expression *)
and redexp_of_ast (evc,env,lfun,lmatch,goalopt,debug) = function
  | ("Red", []) -> Red false
  | ("Hnf", []) -> Hnf
  | ("Simpl", []) -> Simpl
  | ("Unfold", ul) ->
    Unfold (List.map (cvt_unfold (evc,env,lfun,lmatch,goalopt,debug)) ul)
  | ("Fold", cl) ->
    Fold (List.map (cvt_fold (evc,env,lfun,lmatch,goalopt,debug)) cl)
  | ("Cbv",lf) ->
    Cbv(UNIFORM, flag_of_ast (evc,env,lfun,lmatch,goalopt,debug) lf)
  | ("Lazy",lf) ->
    Lazy(UNIFORM, flag_of_ast (evc,env,lfun,lmatch,goalopt,debug) lf)
  | ("Pattern",lp) ->
    Pattern (List.map (cvt_pattern (evc,env,lfun,lmatch,goalopt,debug)) lp)
  | (s,_) -> invalid_arg ("malformed reduction-expression: "^s)

(* Interprets the patterns of Intro *)
and cvt_intro_pattern (evc,env,lfun,lmatch,goalopt,debug) = function
  | Node(_,"IDENTIFIER", [Nvar(loc,s)]) ->
    IdPat (id_of_Identifier (unvarg (val_interp
      (evc,env,lfun,lmatch,goalopt,debug) (Nvar (loc,s)))))
  | Node(_,"DISJPATTERN", l) ->
    DisjPat (List.map (cvt_intro_pattern (evc,env,lfun,lmatch,goalopt,debug))
      l)
  | Node(_,"CONJPATTERN", l) ->
    ConjPat (List.map (cvt_intro_pattern (evc,env,lfun,lmatch,goalopt,debug))
      l)
  | Node(_,"LISTPATTERN", l) ->
    ListPat (List.map (cvt_intro_pattern (evc,env,lfun,lmatch,goalopt,debug))
      l)
  | x ->
    errorlabstrm "cvt_intro_pattern"
      [<'sTR "Not the expected form for an introduction pattern!"; print_ast
        x>]

(* Interprets a pattern of Let *)
and cvt_letpattern (evc,env,lfun,lmatch,goalopt,debug) (o,l) = function
  | Node(_,"HYPPATTERN", Nvar(loc,s)::nums) ->
    (o,(id_of_Identifier (unvarg (val_interp
      (evc,env,lfun,lmatch,goalopt,debug)
      (Nvar (loc,s)))),List.map num_of_ast nums)::l)
  | Node(_,"CCLPATTERN", nums) ->
    if o <> None then
      error "\"Goal\" occurs twice"
    else
      (Some (List.map num_of_ast nums), l)
  | arg -> invalid_arg_loc (Ast.loc arg,"cvt_hyppattern")

(* Interprets tactic arguments *)
let interp_tacarg sign ast = unvarg (val_interp sign ast)

(* Initial call for interpretation *)
let interp = fun ast -> tac_interp [] [] !debug ast

(* For bad tactic calls *)
let bad_tactic_args s =
  anomalylabstrm s
    [<'sTR "Tactic "; 'sTR s; 'sTR " called with bad arguments">]

(* Declaration of the TAC-DEFINITION object *)
let (inMD,outMD) =
  let add (na,td) = mactab := Gmap.add na td !mactab in
  let cache_md (_,(na,td)) =  
    let ve=val_interp (Evd.empty,Environ.empty_env,[],[],None,get_debug ()) td 
    in add (na,ve) in 
    declare_object ("TAC-DEFINITION",
       {cache_function  = cache_md;
        load_function   = (fun _ -> ());
        open_function   = cache_md;
        export_function = (fun x -> Some x)})

(* Adds a definition for tactics in the table *)
let add_tacdef na vbody =
  begin
    if Gmap.mem na !mactab then
      errorlabstrm "Tacinterp.add_tacdef" 
      [< 'sTR
         "There is already a Meta Definition or a Tactic Definition named ";
         'sTR na>];
    let _ = Lib.add_leaf (id_of_string na) OBJ (inMD (na,vbody)) in
    if Options.is_verbose() then mSGNL [< 'sTR (na ^ " is defined") >]
  end
