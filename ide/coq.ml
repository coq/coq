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


let output = ref (Format.formatter_of_out_channel stdout)

let msg x = 
  Format.fprintf !output "%s\n" x;
  Format.pp_print_flush !output ();;
 
let init () = 
  Options.make_silent true;
  Coqtop.init ()

let i = ref 0

let interp s = 
  prerr_endline s;
  flush stderr;
  let po = Pcoq.Gram.parsable (Stream.of_string s) in
  Vernac.raw_do_vernac po;
  let po = Pcoq.Gram.parsable (Stream.of_string s) in
  match Pcoq.Gram.Entry.parse Pcoq.main_entry po with
    (* | Some (_, VernacDefinition _) *)
    | Some (_,ast) -> 
	prerr_endline ("Done with "^s);
	flush stderr;
	ast
    | None -> assert false

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
      | Error_in_file (s, (fname, loc), ie) -> assert false
      | _ -> dloc,exc
  in
  match exc with
    | End_of_input  -> 	str "Please report: End of input",None
    | Vernacexpr.ProtectedLoop -> 
	str "ProtectedLoop  not allowed by coqide!",None
    | Vernacexpr.Drop ->  str "Drop is not allowed by coqide!",None
    | Vernacexpr.Quit -> str "Quit is not allowed by coqide! Use menus.",None
    | _ -> 
	(Cerrors.explain_exn exc),
	(if is_pervasive_exn exc then None else loc)

let process_exn e = let s,loc=print_toplevel_error e in (msgnl s,loc)

(* type hyp = (identifier * constr option * constr) * string*)
type hyp = ((identifier * string) * constr option * constr) * (string * string)
type concl = constr * string
type goal = hyp list * concl

let prepare_hyp env ((i,c,d) as a) =
  ((i,string_of_id i),c,d), (msg (pr_var_decl env a), 
			     msg (prterm_env_at_top env d))

let prepare_hyps env =
  assert (rel_context env = []);
  let hyps =
    fold_named_context
      (fun env d acc -> let hyp =  prepare_hyp env d in hyp :: acc)
      env ~init:[] 
  in
  List.rev hyps

let prepare_goal g =
  let env = evar_env g in
  (prepare_hyps env,
   (g.evar_concl, msg (prterm_env_at_top env g.evar_concl)))

let get_curent_goals () = 
    let pfts = get_pftreestate () in
    let gls = fst (Refiner.frontier (Tacmach.proof_of_pftreestate pfts)) in 
    List.map prepare_goal gls

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

