(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "grammar/grammar.cma" i*)

DECLARE PLUGIN "decl_mode_plugin"

open Compat
open Pp
open Decl_expr
open Names
open Pcoq
open Vernacexpr
open Tok (* necessary for camlp4 *)

open Pcoq.Constr
open Pltac
open Ppdecl_proof

let pr_goal gs =
  let (g,sigma) = Goal.V82.nf_evar (Tacmach.project gs) (Evd.sig_it gs) in
  let env = Goal.V82.env sigma g in
  let concl = Goal.V82.concl sigma g in
  let goal =
    Printer.pr_context_of env sigma ++ cut () ++
      str "============================" ++ cut ()  ++
      str "thesis :=" ++ cut () ++
      Printer.pr_goal_concl_style_env env sigma concl in
  str "     *** Declarative Mode ***" ++ fnl () ++ fnl () ++
    str "  " ++ v 0 goal

let pr_subgoals ?(pr_first=true) _ sigma _ _ _ gll =
  match gll with
  | [goal] when pr_first ->
      pr_goal { Evd.it = goal ; sigma = sigma }
  | _ ->
      (* spiwack: it's not very nice to have to call proof global
         here, a more robust solution would be to add a hook for
         [Printer.pr_open_subgoals] in proof modes, in order to
         compute the end command. Yet a more robust solution would be
         to have focuses give explanations of their unfocusing
         behaviour. *)
      let p = Proof_global.give_me_the_proof () in
      let close_cmd = Decl_mode.get_end_command p in
      str "Subproof completed, now type " ++ str close_cmd ++ str "."

let interp_proof_instr _ { Evd.it = gl ; sigma = sigma }=
  Decl_interp.interp_proof_instr 
    (Decl_mode.get_info sigma gl)
    (Goal.V82.env sigma gl)
    (sigma)

let vernac_decl_proof () = 
  let pf = Proof_global.give_me_the_proof () in
  if Proof.is_done pf then 
    CErrors.error "Nothing left to prove here."
  else
    begin
      Decl_proof_instr.go_to_proof_mode () ;
      Proof_global.set_proof_mode "Declarative"
    end

(* spiwack: some bureaucracy is not performed here *)
let vernac_return () =
  begin
    Decl_proof_instr.return_from_tactic_mode () ;
    Proof_global.set_proof_mode "Declarative"
  end

let vernac_proof_instr instr =
  Decl_proof_instr.proof_instr instr

(* Before we can write an new toplevel command (see below) 
    which takes a [proof_instr] as argument, we need to declare
    how to parse it, print it, globalise it and interprete it.
    Normally we could do that easily through ARGUMENT EXTEND, 
    but as the parsing is fairly complicated we will do it manually to
    indirect through the [proof_instr] grammar entry. *)
(* spiwack: proposal: doing that directly from argextend.ml4, maybe ? *)

(* Only declared at raw level, because only used in vernac commands. *)
let wit_proof_instr : (raw_proof_instr, glob_proof_instr, proof_instr) Genarg.genarg_type =
  Genarg.make0 "proof_instr"

(* We create a new parser entry [proof_mode]. The Declarative proof mode
    will replace the normal parser entry for tactics with this one. *)
let proof_mode : vernac_expr Gram.entry =
  Gram.entry_create "vernac:proof_command"
(* Auxiliary grammar entry. *)
let proof_instr : raw_proof_instr Gram.entry =
  Pcoq.create_generic_entry Pcoq.utactic "proof_instr" (Genarg.rawwit wit_proof_instr)

let _ = Pptactic.declare_extra_genarg_pprule wit_proof_instr
  pr_raw_proof_instr pr_glob_proof_instr pr_proof_instr

let classify_proof_instr = function
  | { instr = Pescape |Pend B_proof } -> VtProofMode "Classic", VtNow
  | _ -> Vernac_classifier.classify_as_proofstep

(* We use the VERNAC EXTEND facility with a custom non-terminal
    to populate [proof_mode] with a new toplevel interpreter.
    The "-" indicates that the rule does not start with a distinguished
    string. *)
VERNAC proof_mode EXTEND ProofInstr
  [ - proof_instr(instr) ] => [classify_proof_instr instr] -> [ vernac_proof_instr instr ]
END

(* It is useful to use GEXTEND directly to call grammar entries that have been
    defined previously VERNAC EXTEND. In this case we allow, in proof mode,
    the use of commands like Check or Print. VERNAC EXTEND does quite a bit of
    bureaucracy for us, but it is not needed in this sort of case, and it would require
    to have an ARGUMENT EXTEND version of the "proof_mode" grammar entry. *)
GEXTEND Gram
  GLOBAL: proof_mode ;

  proof_mode: LAST
    [ [ c=G_vernac.subgoal_command -> c (Some (Vernacexpr.SelectNth 1)) ] ]
  ;
END  

(* We register a new proof mode here *)

let _ = 
  Proof_global.register_proof_mode { Proof_global.
				       name = "Declarative" ; (* name for identifying and printing *)
				       (* function [set] goes from No Proof Mode to 
					   Declarative Proof Mode performing side effects *)
				       set = begin fun () ->
					 (* We set the command non terminal to
					     [proof_mode] (which we just defined). *)
					 Pcoq.set_command_entry proof_mode ;
					 (* We substitute the goal printer, by the one we built
					     for the proof mode. *)
					 Printer.set_printer_pr { Printer.default_printer_pr with
								                Printer.pr_goal = pr_goal;
                                                                                pr_subgoals = pr_subgoals; }
				       end ;
                                       (* function [reset] goes back to No Proof Mode from
					   Declarative Proof Mode *)
				       reset = begin fun () ->
					 (* We restore the command non terminal to
					      [noedit_mode]. *)
					 Pcoq.set_command_entry Pcoq.Vernac_.noedit_mode ;
					 (* We restore the goal printer to default *)
					 Printer.set_printer_pr Printer.default_printer_pr
				       end
				   }

VERNAC COMMAND EXTEND DeclProof
[ "proof" ] => [ VtProofMode "Declarative", VtNow ] -> [ vernac_decl_proof () ]
END
VERNAC COMMAND EXTEND  DeclReturn
[ "return" ] => [ VtProofMode "Declarative", VtNow ] -> [ vernac_return () ]
END

let none_is_empty = function
    None -> []
  | Some l -> l

GEXTEND Gram
GLOBAL: proof_instr;
  thesis :
    [[ "thesis" -> Plain 
     | "thesis"; "for"; i=ident -> (For i)
     ]];
  statement :
    [[ i=ident ; ":" ; c=constr -> {st_label=Name i;st_it=c}
     | i=ident -> {st_label=Anonymous;
		   st_it=Constrexpr.CRef (Libnames.Ident (!@loc, i), None)}
     | c=constr -> {st_label=Anonymous;st_it=c}
     ]];
  constr_or_thesis :
     [[ t=thesis -> Thesis t ] |
      [ c=constr -> This c
      ]];
  statement_or_thesis : 
    [
      [ t=thesis -> {st_label=Anonymous;st_it=Thesis t} ] 
    |
      [ i=ident ; ":" ; cot=constr_or_thesis -> {st_label=Name i;st_it=cot}
      | i=ident -> {st_label=Anonymous;
		    st_it=This (Constrexpr.CRef (Libnames.Ident (!@loc, i), None))}
      | c=constr -> {st_label=Anonymous;st_it=This c}
      ]
    ];
  justification_items : 
    [[ -> Some [] 
     | "by"; l=LIST1 constr SEP "," -> Some l
     | "by"; "*"                    -> None ]]
  ;
  justification_method : 
    [[ -> None 
     | "using";  tac = tactic -> Some tac ]]
  ;
  simple_cut_or_thesis :
    [[ ls = statement_or_thesis;
       j = justification_items;
       taco = justification_method 	
	 -> {cut_stat=ls;cut_by=j;cut_using=taco} ]]
  ;
  simple_cut :
    [[ ls = statement;
       j = justification_items;
       taco = justification_method 	
	 -> {cut_stat=ls;cut_by=j;cut_using=taco} ]]
  ;
  elim_type:
    [[ IDENT "induction" -> ET_Induction
     | IDENT "cases" -> ET_Case_analysis ]]
  ;
  block_type :
    [[ IDENT "claim" -> B_claim
     | IDENT "focus" -> B_focus
     | IDENT "proof" -> B_proof
     | et=elim_type -> B_elim et ]]
  ;    
  elim_obj:
    [[ IDENT "on"; c=constr -> Real c
     | IDENT "of"; c=simple_cut -> Virtual c ]]
  ;  
  elim_step:
    [[ IDENT "consider" ; 
       h=consider_vars ; IDENT "from" ; c=constr -> Pconsider (c,h)
     | IDENT "per"; et=elim_type; obj=elim_obj -> Pper (et,obj)
     | IDENT "suffices"; ls=suff_clause;
       j = justification_items;
       taco = justification_method 	
	-> Psuffices {cut_stat=ls;cut_by=j;cut_using=taco} ]] 
  ;
  rew_step :
    [[ "~=" ;         c=simple_cut -> (Rhs,c)       
     | "=~" ;         c=simple_cut -> (Lhs,c)]]
  ;
  cut_step:
    [[ "then"; tt=elim_step -> Pthen tt
     | "then"; c=simple_cut_or_thesis -> Pthen (Pcut c)
     | IDENT "thus"; tt=rew_step -> Pthus (let s,c=tt in Prew (s,c)) 
     | IDENT "thus"; c=simple_cut_or_thesis -> Pthus (Pcut c)
     | IDENT "hence"; c=simple_cut_or_thesis -> Phence (Pcut c)
     | tt=elim_step -> tt
     | tt=rew_step -> let s,c=tt in Prew (s,c); 
     | IDENT "have"; c=simple_cut_or_thesis -> Pcut c;
     | IDENT "claim"; c=statement -> Pclaim c;
     | IDENT "focus"; IDENT "on"; c=statement -> Pfocus c;    
     | "end"; bt = block_type -> Pend bt;
     | IDENT "escape" -> Pescape ]]
  ;
  (* examiner s'il est possible de faire R _ et _ R pour R une relation qcq*)
  loc_id: 
    [[ id=ident -> fun x -> (!@loc,(id,x)) ]];
  hyp:
    [[ id=loc_id -> id None ;
     | id=loc_id ; ":" ; c=constr -> id (Some c)]]
  ;
  consider_vars:
    [[ name=hyp -> [Hvar name]
     | name=hyp; ","; v=consider_vars -> (Hvar name) :: v
     | name=hyp; 
       IDENT "such"; IDENT "that"; h=consider_hyps -> (Hvar name)::h
     ]]
  ;
  consider_hyps:  
    [[ st=statement; IDENT "and"; h=consider_hyps  -> Hprop st::h
     | st=statement; IDENT "and"; 
       IDENT "consider" ; v=consider_vars  -> Hprop st::v
     | st=statement -> [Hprop st]
     ]]
  ;  
  assume_vars:
    [[ name=hyp -> [Hvar name]
     | name=hyp; ","; v=assume_vars -> (Hvar name) :: v
     | name=hyp; 
       IDENT "such"; IDENT "that"; h=assume_hyps -> (Hvar name)::h
     ]]
  ;
  assume_hyps:  
    [[ st=statement; IDENT "and"; h=assume_hyps  -> Hprop st::h
     | st=statement; IDENT "and"; 
       IDENT "we"; IDENT "have" ; v=assume_vars  -> Hprop st::v
     | st=statement -> [Hprop st]
     ]]
  ;
  assume_clause:
    [[ IDENT "we" ; IDENT "have" ; v=assume_vars -> v
    |  h=assume_hyps -> h ]]
  ; 
  suff_vars:
    [[ name=hyp; IDENT "to"; IDENT "show" ; c = constr_or_thesis ->
      [Hvar name],c
     | name=hyp; ","; v=suff_vars -> 
	 let (q,c) = v in ((Hvar name) :: q),c
     | name=hyp; 
       IDENT "such"; IDENT "that"; h=suff_hyps -> 
	 let (q,c) = h in ((Hvar name) :: q),c
     ]];
  suff_hyps:  
    [[ st=statement; IDENT "and"; h=suff_hyps  ->	 
	 let (q,c) = h in (Hprop st::q),c
     | st=statement; IDENT "and"; 
       IDENT "to" ; IDENT "have" ; v=suff_vars -> 
	 let (q,c) = v in (Hprop st::q),c
     | st=statement; IDENT "to"; IDENT "show" ; c = constr_or_thesis -> 
	 [Hprop st],c
     ]]
  ;
  suff_clause:
    [[ IDENT "to" ; IDENT "have" ; v=suff_vars -> v
    |  h=suff_hyps -> h ]]
  ; 
  let_vars:
    [[ name=hyp -> [Hvar name]
     | name=hyp; ","; v=let_vars -> (Hvar name) :: v
     | name=hyp; IDENT "be"; 
       IDENT "such"; IDENT "that"; h=let_hyps -> (Hvar name)::h
     ]]
  ;
  let_hyps:  
    [[ st=statement; IDENT "and"; h=let_hyps  -> Hprop st::h
    |  st=statement; IDENT "and"; "let"; v=let_vars  -> Hprop st::v
    |  st=statement -> [Hprop st]
    ]];
  given_vars:
    [[ name=hyp -> [Hvar name]
     | name=hyp; ","; v=given_vars -> (Hvar name) :: v
     | name=hyp; IDENT "such"; IDENT "that"; h=given_hyps -> (Hvar name)::h
     ]]
  ;
  given_hyps:  
    [[ st=statement; IDENT "and"; h=given_hyps  -> Hprop st::h
    |  st=statement; IDENT "and"; IDENT "given"; v=given_vars  -> Hprop st::v
    |  st=statement -> [Hprop st]
    ]];
  suppose_vars:
    [[name=hyp -> [Hvar name] 
     |name=hyp; ","; v=suppose_vars -> (Hvar name) :: v
     |name=hyp; OPT[IDENT "be"]; 
      IDENT "such"; IDENT "that"; h=suppose_hyps -> (Hvar name)::h
     ]]
  ;
  suppose_hyps:  
    [[ st=statement_or_thesis; IDENT "and"; h=suppose_hyps -> Hprop st::h
     | st=statement_or_thesis; IDENT "and"; IDENT "we"; IDENT "have";
          v=suppose_vars -> Hprop st::v
     | st=statement_or_thesis -> [Hprop st]
     ]]
  ;
  suppose_clause:
    [[ IDENT "we"; IDENT "have"; v=suppose_vars -> v;
     |  h=suppose_hyps -> h ]]
  ;
  intro_step:
    [[ IDENT "suppose" ; h=assume_clause -> Psuppose h
     | IDENT "suppose" ; IDENT "it"; IDENT "is" ; c=pattern LEVEL "0" ;
       po=OPT[ "with"; p=LIST1 hyp SEP ","-> p  ] ; 
       ho=OPT[ IDENT "and" ; h=suppose_clause -> h ] -> 
	 Pcase (none_is_empty po,c,none_is_empty ho)
     | "let" ; v=let_vars -> Plet v	 
     | IDENT "take"; witnesses = LIST1 constr SEP ","  -> Ptake witnesses
     | IDENT "assume"; h=assume_clause -> Passume h
     | IDENT "given"; h=given_vars -> Pgiven h
     | IDENT "define"; id=ident; args=LIST0 hyp; 
       "as"; body=constr -> Pdefine(id,args,body)
     | IDENT "reconsider"; id=ident; "as" ; typ=constr -> Pcast (This id,typ)
     | IDENT "reconsider"; t=thesis; "as" ; typ=constr -> Pcast (Thesis t ,typ)
     ]]
  ;
  emphasis : 
    [[ -> 0
     | "*" -> 1
     | "**" -> 2
     | "***" -> 3
     ]]
  ;
  bare_proof_instr:
    [[ c = cut_step -> c ;
     | i = intro_step -> i ]]
  ;
  proof_instr :
    [[ e=emphasis;i=bare_proof_instr;"." -> {emph=e;instr=i}]]
  ;
END;;
