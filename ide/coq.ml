open Vernac
open Vernacexpr
open Pfedit
open Pp
open Util
open Names
open Term
open Printer
open Environ
open Evarutil
open Evd
open Hipattern
open Tacmach
open Reductionops
open Ideutils

let prerr_endline s = if !debug then prerr_endline s else ()

let output = ref (Format.formatter_of_out_channel stdout)

let msg x = 
  Format.fprintf !output "%s\n" x;
  Format.pp_print_flush !output ();;
 
let init () = 
  Options.make_silent true;
  Coqtop.init_ide ()

let i = ref 0

let version () =
  Printf.sprintf "The Coq Proof Assistant, version %s (%s)\nCompiled on %s\n"
    Coq_config.version Coq_config.date Coq_config.compile_date

let is_in_coq_lib dir = 
  prerr_endline ("Is it a coq theory ? : "^dir);
  try
    let stat = Unix.stat dir in
    List.exists 
      (fun s -> 
	 try
	   let fdir = Filename.concat 
			Coq_config.coqlib 
			(Filename.concat "theories" s) 
	   in
	   prerr_endline (" Comparing to : "^fdir);
	   let fstat = Unix.stat fdir in 
	   (fstat.Unix.st_dev = stat.Unix.st_dev) &&
	   (fstat.Unix.st_ino = stat.Unix.st_ino) && 
           (prerr_endline " YES";true)
	 with _ -> prerr_endline " No(because of a local exn)";false
      )
      Coq_config.theories_dirs
  with _ -> prerr_endline " No(because of a global exn)";false

let interp s = 
  prerr_endline s;
  flush stderr;
  let po = Pcoq.Gram.parsable (Stream.of_string s) in
  Vernac.raw_do_vernac po;
  let po = Pcoq.Gram.parsable (Stream.of_string s) in
  match Pcoq.Gram.Entry.parse Pcoq.main_entry po with
    (* | Some (_, VernacDefinition _) *)
    | Some last -> 
	prerr_endline ("Done with "^s);
	flush stderr;
	last
    | None -> assert false

let is_tactic = function
  | VernacSolve _ -> true
  | _ -> false

let msg m = 
  let b =  Buffer.create 103 in
  Pp.msg_with (Format.formatter_of_buffer b) m;
  Buffer.contents b

let msgnl m = 
  (msg m)^"\n"

let rec is_pervasive_exn = function
  | Out_of_memory | Stack_overflow | Sys.Break -> true
  | Error_in_file (_,_,e) -> is_pervasive_exn e
  | Stdpp.Exc_located (_,e) -> is_pervasive_exn e
  | DuringCommandInterp (_,e) -> is_pervasive_exn e
  | _ -> false

let print_toplevel_error exc =
  let (dloc,exc) =
    match exc with
      | DuringCommandInterp (loc,ie) ->
          if loc = dummy_loc then (None,ie) else (Some loc, ie)
      | _ -> (None, exc) 
  in
  let (loc,exc) =
    match exc with
      | Stdpp.Exc_located (loc, ie) -> (Some loc),ie
      | Error_in_file (s, (fname, loc), ie) -> None, ie
      | _ -> dloc,exc
  in
  match exc with
    | End_of_input  -> 	str "Please report: End of input",None
    | Vernacexpr.ProtectedLoop -> 
	str "ProtectedLoop  not allowed by coqide!",None
    | Vernacexpr.Drop ->  str "Drop is not allowed by coqide!",None
    | Vernacexpr.Quit -> str "Quit is not allowed by coqide! Use menus.",None
    | _ -> 
	(try Cerrors.explain_exn exc with e -> 
	   str "Failed to explain error. This is an internal Coq error. Please report.\n"
	   ++ str (Printexc.to_string  e)),
	(if is_pervasive_exn exc then None else loc)

let process_exn e = let s,loc=print_toplevel_error e in (msgnl s,loc)

let interp_last last = 
  prerr_string "*";
  try
    vernac_com (States.with_heavy_rollback Vernacentries.interp) last
  with e ->
    let s,_ = process_exn e in prerr_endline s; raise e

(* type hyp = (identifier * constr option * constr) * string*)
type hyp = env * evar_map *
           ((identifier * string) * constr option * constr) * 
           (string * string)
type concl = env * evar_map * constr * string
type goal = hyp list * concl

let prepare_hyp sigma env ((i,c,d) as a) =
  env, sigma,
  ((i,string_of_id i),c,d), 
  (msg (pr_var_decl env a), msg (prterm_env_at_top env d))

let prepare_hyps sigma env =
  assert (rel_context env = []);
  let hyps =
    fold_named_context
      (fun env d acc -> let hyp = prepare_hyp sigma env d in hyp :: acc)
      env ~init:[] 
  in
  List.rev hyps

let prepare_goal sigma g =
  let env = evar_env g in
  (prepare_hyps sigma env,
   (env, sigma, g.evar_concl, msg (prterm_env_at_top env g.evar_concl)))

let get_current_goals () = 
    let pfts = get_pftreestate () in
    let gls = fst (Refiner.frontier (Tacmach.proof_of_pftreestate pfts)) in 
    let sigma = Tacmach.evc_of_pftreestate pfts in
    List.map (prepare_goal sigma) gls

let print_no_goal () =
    let pfts = get_pftreestate () in
    let gls = fst (Refiner.frontier (Tacmach.proof_of_pftreestate pfts)) in 
    assert (gls = []);
    let sigma = Tacmach.project (Tacmach.top_goal_of_pftreestate pfts) in
    msg (Proof_trees.pr_subgoals_existential sigma gls)


type word_class = Normal | Kwd | Reserved


let kwd = [(* "Compile";"Inductive";"Qed";"Type";"end";"Axiom";
	      "Definition";"Load";"Quit";"Variable";"in";"Cases";"FixPoint";
	      "Parameter";"Set";"of";"CoFixpoint";"Grammar";"Proof";"Syntax";
	      "using";"CoInductive";"Hypothesis";"Prop";"Theorem";
	   *)
  "Add"; "AddPath"; "Axiom"; "Chapter"; "CoFixpoint";
  "CoInductive"; "Defined"; "Definition"; 
  "End"; "Export"; "Fact"; "Fix"; "Fixpoint"; "Global"; "Grammar"; "Hint";
  "Hints"; "Hypothesis"; "Immediate"; "Implicits"; "Import"; "Inductive"; 
  "Infix"; "Lemma"; "Load"; "Local"; 
  "Match"; "Module"; "Module Type";
  "Mutual"; "Parameter"; "Print"; "Proof"; "Qed";
  "Record"; "Recursive"; "Remark"; "Require"; "Save"; "Scheme";
  "Section"; "Show"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; 
  "Unset"; "Variable"; "Variables"; 
]
	    
let reserved = []

module SHashtbl = 
  Hashtbl.Make 
    (struct 
       type t = string
       let equal = ( = )
       let hash = Hashtbl.hash
     end)


let word_tbl = SHashtbl.create 37
let _ = 
  List.iter (fun w -> SHashtbl.add word_tbl w Kwd) kwd;
  List.iter (fun w -> SHashtbl.add word_tbl w Reserved) reserved

let word_class s = 
  try
    SHashtbl.find word_tbl s
  with Not_found -> Normal

type reset_info = NoReset | Reset of Names.identifier * bool ref

let compute_reset_info = function 
  | VernacDefinition (_, id, DefineBody _, _, _) 
  | VernacBeginSection id 
  | VernacDefineModule (id, _, _, _) 
  | VernacDeclareModule (id, _, _, _)
  | VernacDeclareModuleType (id, _, _)
  | VernacAssumption (_, (_,(id,_))::_) ->
      Reset (id, ref true)
  | VernacDefinition (_, id, ProveBody _, _, _)
  | VernacStartTheoremProof (_, id, _, _, _) ->
      Reset (id, ref false)
  | _ -> NoReset

let reset_initial () = 
  prerr_endline "Reset initial called"; flush stderr;
  Vernacentries.abort_refine Lib.reset_initial ()

let reset_to id = 
  prerr_endline ("Reset called with "^(string_of_id id)); flush stderr;
  Vernacentries.abort_refine Lib.reset_name (Util.dummy_loc,id)


let hyp_menu (env, sigma, ((coqident,ident),_,ast),(s,pr_ast)) =
  [("Clear "^ident),("Clear "^ident^".");

   ("Assumption"),
   ("Assumption.");
   
   ("Apply "^ident),
   ("Apply "^ident^".");
   
   ("Generalize "^ident),
   ("Generalize "^ident^".");
   
   ("Absurd <"^ident^">"),
   ("Absurd "^
    pr_ast
    ^".") ] @

   (if is_equation ast then
      [ "Discriminate "^ident, "Discriminate "^ident^".";
	"Injection "^ident, "Injection "^ident^"." ]
    else
      []) @
   
   (let _,t = splay_prod env sigma ast in
    if is_equation t then 
      [ "Rewrite "^ident, "Rewrite "^ident^".";
	"Rewrite <- "^ident, "Rewrite <- "^ident^"." ]
    else
      []) @
   
  [("Elim "^ident),
   ("Elim "^ident^".");
   
   ("Inversion "^ident),
   ("Inversion "^ident^".");
   
   ("Inversion_clear "^ident),
   ("Inversion_clear "^ident^".")] 

let concl_menu (_,_,concl,_) = 
  let is_eq = is_equation concl in
  ["Intro", "Intro.";
   "Intros", "Intros.";
   "Intuition","Intuition." ] @
   
   (if is_eq then 
      ["Reflexivity", "Reflexivity.";
       "Discriminate", "Discriminate.";
       "Symmetry", "Symmetry." ]
    else 
      []) @

  ["Omega", "Omega.";
   "Ring", "Ring.";
   "Auto with *", "Auto with *.";
   "EAuto with *", "EAuto with *.";
   "Tauto", "Tauto.";
   "Trivial", "Trivial.";
   "Decide Equality", "Decide Equality.";

   "Simpl", "Simpl.";
   "Red", "Red.";
   "Split", "Split.";
   "Left", "Left.";
   "Right", "Right.";

  ]
