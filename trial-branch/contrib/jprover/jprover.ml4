(*i camlp4deps: "parsing/grammar.cma" i*)

open Jlogic

module JA = Jall
module JT = Jterm
module T = Tactics
module TCL = Tacticals
module TM = Tacmach
module N = Names
module PT = Proof_type
module HT = Hiddentac
module PA = Pattern
module HP = Hipattern
module TR = Term
module PR = Printer
module RO = Reductionops
module UT = Util
module RA = Rawterm

module J=JA.JProver(JLogic)         (* the JProver *)

(*i
module NO = Nameops
module TO = Termops
module RE = Reduction
module CL = Coqlib
module ID = Inductiveops
module CV = Clenv
module RF = Refiner
i*)

(* Interface to JProver: *)
(* type JLogic.inf_step = rule * (string * Jterm.term) * (string * Jterm.term) *)
type jp_inf_step = JLogic.inf_step
type jp_inference = JLogic.inference    (* simply a list of [inf_step] *)

(* Definitions for rebuilding proof tree from JProver: *)
(* leaf, one-branch, two-branch, two-branch, true, false *)
type jpbranch = JP0 | JP1 | JP2 | JP2' | JPT | JPF
type jptree = | JPempty                                 (* empty tree *)
              | JPAx of jp_inf_step                     (* Axiom node *)
              | JPA of jp_inf_step * jptree
              | JPB of jp_inf_step * jptree * jptree

(* Private debugging tools: *)
(*i*)
let mbreak s = Format.print_flush (); print_string ("-break at: "^s);
               Format.print_flush (); let _ = input_char stdin in ()
(*i*)
let jp_error re = raise (JT.RefineError ("jprover", JT.StringError re))

(* print Coq constructor *)
let print_constr ct = Pp.ppnl (PR.pr_lconstr ct); Format.print_flush ()

let rec print_constr_list = function
  |  [] -> ()
  |  ct::r -> print_constr ct; print_constr_list r

let print_constr_pair op c1 c2 =
    print_string (op^"(");
    print_constr c1;
    print_string ",";
    print_constr c2;
    print_string ")\n"


(* Parsing modules for Coq:         *)
(* [is_coq_???] : testing functions *)
(* [dest_coq_???] : destructors     *)

let is_coq_true ct = (HP.is_unit_type ct) && not (HP.is_equation ct)

let is_coq_false = HP.is_empty_type

(* return two subterms *)
let dest_coq_and ct =
    match (HP.match_with_conjunction ct) with
      | Some (hdapp,args) ->
(*i            print_constr hdapp; print_constr_list args; i*)
            begin
               match args with
                   | s1::s2::[] ->
(*i                       print_constr_pair "and" s1 s2; i*)
                       (s1,s2)
                   | _ -> jp_error "dest_coq_and"
            end
      | None -> jp_error "dest_coq_and"

let is_coq_or = HP.is_disjunction

(* return two subterms *)
let dest_coq_or ct =
    match (HP.match_with_disjunction ct) with
      | Some (hdapp,args) ->
(*i            print_constr hdapp; print_constr_list args; i*)
            begin
               match args with
                   | s1::s2::[] ->
(*i                       print_constr_pair "or" s1 s2; i*)
                       (s1,s2)
                   | _ -> jp_error "dest_coq_or"
            end
      | None -> jp_error "dest_coq_or"

let is_coq_not = HP.is_nottype

let dest_coq_not ct =
    match (HP.match_with_nottype ct) with
      | Some (hdapp,arg) ->
(*i            print_constr hdapp; print_constr args; i*)
(*i            print_string "not ";
            print_constr arg; i*)
            arg
      | None -> jp_error "dest_coq_not"


let is_coq_impl ct =
  match TR.kind_of_term ct with
    | TR.Prod (_,_,b) -> (not (Termops.dependent (TR.mkRel 1) b))
    | _  -> false


let dest_coq_impl c =
  match TR.kind_of_term c with
    | TR.Prod (_,b,c) ->
(*i            print_constr_pair "impl" b c; i*)
            (b, c)
    | _ -> jp_error "dest_coq_impl"

(* provide new variables for renaming of universal variables *)
let new_counter =
  let ctr = ref 0 in
    fun () -> incr ctr;!ctr

(* provide new symbol name for unknown Coq constructors *)
let new_ecounter =
  let ectr = ref 0 in
    fun () -> incr ectr;!ectr

(* provide new variables for address naming *)
let new_acounter =
  let actr = ref 0 in
    fun () -> incr actr;!actr

let is_coq_forall ct =
  match TR.kind_of_term (RO.whd_betaiota ct) with
    | TR.Prod (_,_,b) -> Termops.dependent (TR.mkRel 1) b
    | _  -> false

(* return the bounded variable (as a string) and the bounded term *)
let dest_coq_forall ct =
  match TR.kind_of_term (RO.whd_betaiota ct) with
    | TR.Prod (_,_,b) ->
        let x ="jp_"^(string_of_int (new_counter())) in
        let v = TR.mkVar (N.id_of_string x) in
        let c = TR.subst1 v b in    (* substitute de Bruijn variable by [v] *)
(*i        print_constr_pair "forall" v c; i*)
        (x, c)
    | _  -> jp_error "dest_coq_forall"


(* Apply [ct] to [t]: *)
let sAPP ct t =
  match TR.kind_of_term (RO.whd_betaiota ct) with
    | TR.Prod (_,_,b) ->
        let c = TR.subst1 t b in
            c
    | _  -> jp_error "sAPP"


let is_coq_exists ct =
  if not (HP.is_conjunction ct) then false
  else let (hdapp,args) = TR.decompose_app ct in
     match args with
      | _::la::[] ->
           begin
            try
              match TR.destLambda la with
                | (N.Name _,_,_) -> true
                | _ -> false
            with _ -> false
           end
      | _ -> false

(* return the bounded variable (as a string) and the bounded term *)
let dest_coq_exists ct =
  let (hdapp,args) = TR.decompose_app ct in
     match args with
      | _::la::[] ->
           begin
            try
             match TR.destLambda la with
                    | (N.Name x,t1,t2) ->
                         let v = TR.mkVar x in
                         let t3 = TR.subst1 v t2 in
(*i                            print_constr_pair "exists" v t3; i*)
                            (N.string_of_id x, t3)
                    | _ -> jp_error "dest_coq_exists"
            with _ -> jp_error "dest_coq_exists"
           end
      | _ -> jp_error "dest_coq_exists"


let is_coq_and ct =
  if (HP.is_conjunction ct) && not (is_coq_exists ct)
  && not (is_coq_true ct) then true
  else false


(* Parsing modules: *)

let jtbl = Hashtbl.create 53        (* associate for unknown Coq constr. *)
let rtbl = Hashtbl.create 53        (* reverse table of [jtbl] *)

let dest_coq_symb ct =
    N.string_of_id (TR.destVar ct)

(* provide new names for unknown Coq constr. *)
(* [ct] is the unknown constr., string [s] is appended to the name encoding *)
let create_coq_name ct s =
    try
       Hashtbl.find jtbl ct
    with Not_found ->
       let t = ("jp_"^s^(string_of_int (new_ecounter()))) in
          Hashtbl.add jtbl ct t;
          Hashtbl.add rtbl t ct;
          t

let dest_coq_app ct s =
    let (hd, args) = TR.decompose_app ct in
(*i        print_constr hd;
        print_constr_list args; i*)
       if TR.isVar hd then
          (dest_coq_symb hd, args)
       else                         (* unknown constr *)
          (create_coq_name hd s, args)

let rec parsing2 c =        (* for function symbols, variables, constants *)
    if (TR.isApp c) then    (* function symbol? *)
        let (f,args) = dest_coq_app c "fun_" in
            JT.fun_ f (List.map parsing2 args)
    else if TR.isVar c then (* identifiable variable or constant *)
            JT.var_ (dest_coq_symb c)
    else                    (* unknown constr *)
            JT.var_ (create_coq_name c "var_")

(* the main parsing function *)
let rec parsing c =
    let ct = Reduction.whd_betadeltaiota (Global.env ()) c in
(*    let ct = Reduction.whd_betaiotazeta (Global.env ()) c in *)
    if is_coq_true ct then
       JT.true_
    else if is_coq_false ct then
       JT.false_
    else if is_coq_not ct then
        JT.not_ (parsing (dest_coq_not ct))
    else if is_coq_impl ct then
        let (t1,t2) = dest_coq_impl ct in
            JT.imp_ (parsing t1) (parsing t2)
    else if is_coq_or ct then
        let (t1,t2) = dest_coq_or ct in
            JT.or_ (parsing t1) (parsing t2)
    else if is_coq_and ct then
        let (t1,t2) = dest_coq_and ct in
            JT.and_ (parsing t1) (parsing t2)
    else if is_coq_forall ct then
        let (v,t) = dest_coq_forall ct in
            JT.forall v (parsing t)
    else if is_coq_exists ct then
        let (v,t) = dest_coq_exists ct in
            JT.exists v (parsing t)
    else if TR.isApp ct then            (* predicate symbol with arguments *)
        let (p,args) = dest_coq_app ct "P_" in
            JT.pred_ p (List.map parsing2 args)
    else if TR.isVar ct then            (* predicate symbol without arguments *)
        let p = dest_coq_symb ct in
            JT.pred_ p []
    else                                (* unknown predicate *)
        JT.pred_ (create_coq_name ct "Q_") []

(*i
        print_string "??";print_constr ct;
        JT.const_ ("err_"^(string_of_int (new_ecounter())))
i*)


(* Translate JProver terms into Coq constructors: *)
(* The idea is to retrieve it from [rtbl] if it exists indeed, otherwise
   create one. *)
let rec constr_of_jterm t =
  if (JT.is_var_term t) then            (* a variable *)
     let v = JT.dest_var t in
     try
        Hashtbl.find rtbl v
     with Not_found -> TR.mkVar (N.id_of_string v)
  else if (JT.is_fun_term t) then       (* a function symbol *)
     let (f,ts) = JT.dest_fun t in
     let f' = try Hashtbl.find rtbl f with Not_found -> TR.mkVar (N.id_of_string f) in
        TR.mkApp (f', Array.of_list (List.map constr_of_jterm ts))
  else jp_error "constr_of_jterm"


(* Coq tactics for Sequent Calculus LJ: *)
(* Note that for left-rule a name indicating the being applied rule
   in Coq's Hints is required; for right-rule a name is also needed
   if it will pass some subterm to the left-hand side.
   However, all of these can be computed by the path [id] of the being
   applied rule.
*)

let assoc_addr = Hashtbl.create 97

let short_addr s =
  let ad =
    try
       Hashtbl.find assoc_addr s
    with Not_found ->
       let t = ("jp_H"^(string_of_int (new_acounter()))) in
          Hashtbl.add assoc_addr s t;
          t
  in
    N.id_of_string ad

(* and-right *)
let dyn_andr =
  T.split RA.NoBindings

(* For example, the following implements the [and-left] rule: *)
let dyn_andl id =   (* [id1]: left child; [id2]: right child *)
  let id1 = (short_addr (id^"_1")) and id2 = (short_addr (id^"_2")) in
    (TCL.tclTHEN (T.simplest_elim (TR.mkVar (short_addr id))) (T.intros_using [id1;id2]))

let dyn_orr1 =
  T.left RA.NoBindings

let dyn_orr2 =
  T.right RA.NoBindings

let dyn_orl id =
  let id1 = (short_addr (id^"_1")) and id2 = (short_addr (id^"_2")) in
    (TCL.tclTHENS (T.simplest_elim (TR.mkVar (short_addr id)))
                  [T.intro_using id1; T.intro_using id2])

let dyn_negr id =
  let id1 = id^"_1_1" in
     HT.h_intro (short_addr id1)

let dyn_negl id =
  T.simplest_elim (TR.mkVar (short_addr id))

let dyn_impr id =
  let id1 = id^"_1_1" in
     HT.h_intro (short_addr id1)

let dyn_impl id gl =
  let t = TM.pf_get_hyp_typ gl (short_addr id) in
    let ct = Reduction.whd_betadeltaiota (Global.env ()) t in   (* unfolding *)
    let (_,b) = dest_coq_impl ct in
      let id2 = (short_addr (id^"_1_2")) in
         (TCL.tclTHENLAST
            (TCL.tclTHENS (T.cut b) [T.intro_using id2;TCL.tclIDTAC])
         (T.apply_term (TR.mkVar (short_addr id))
                       [TR.mkMeta (Evarutil.new_meta())])) gl

let dyn_allr c =       (* [c] must be an eigenvariable which replaces [v] *)
  HT.h_intro (N.id_of_string c)

(* [id2] is the path of the instantiated term for [id]*)
let dyn_alll id id2 t gl =
  let id' = short_addr id in
  let id2' = short_addr id2 in
  let ct = TM.pf_get_hyp_typ gl id' in
    let ct' = Reduction.whd_betadeltaiota (Global.env ()) ct in   (* unfolding *)
    let ta = sAPP ct' t in
       TCL.tclTHENS (T.cut ta) [T.intro_using id2'; T.apply (TR.mkVar id')] gl

let dyn_exl id id2 c = (* [c] must be an eigenvariable *)
  (TCL.tclTHEN (T.simplest_elim (TR.mkVar (short_addr id)))
               (T.intros_using [(N.id_of_string c);(short_addr id2)]))

let dyn_exr t =
  T.one_constructor 1 (RA.ImplicitBindings [t])

let dyn_falsel = dyn_negl

let dyn_truer =
  T.one_constructor 1 RA.NoBindings

(* Do the proof by the guidance of JProver. *)

let do_one_step inf =
  let (rule, (s1, t1), (s2, t2)) = inf in
   begin
(*i   if not (Jterm.is_xnil_term t2) then
   begin
      print_string "1: "; JT.print_term stdout t2; print_string "\n";
      print_string "2: "; print_constr (constr_of_jterm t2); print_string "\n";
   end;
i*)
   match rule with
     | Andl -> dyn_andl s1
     | Andr -> dyn_andr
     | Orl  -> dyn_orl s1
     | Orr1 -> dyn_orr1
     | Orr2 -> dyn_orr2
     | Impr -> dyn_impr s1
     | Impl -> dyn_impl s1
     | Negr -> dyn_negr s1
     | Negl -> dyn_negl s1
     | Allr -> dyn_allr (JT.dest_var t2)
     | Alll -> dyn_alll s1 s2 (constr_of_jterm t2)
     | Exr  -> dyn_exr (Tactics.inj_open (constr_of_jterm t2))
     | Exl  -> dyn_exl s1 s2 (JT.dest_var t2)
     | Ax -> T.assumption (*i TCL.tclIDTAC i*)
     | Truer -> dyn_truer
     | Falsel -> dyn_falsel s1
     | _ -> jp_error "do_one_step"
            (* this is impossible *)
    end
;;

(* Parameter [tr] is the reconstucted proof tree from output of JProver. *)
let do_coq_proof tr =
 let rec rec_do trs =
    match trs with
     | JPempty -> TCL.tclIDTAC
     | JPAx h -> do_one_step h
     | JPA (h, t) -> TCL.tclTHEN (do_one_step h) (rec_do t)
     | JPB (h, left, right) -> TCL.tclTHENS (do_one_step h) [rec_do left; rec_do right]
 in
    rec_do tr


(* Rebuild the proof tree from the output of JProver: *)

(* Since some universal variables are not necessarily first-order,
   lazy substitution may happen. They are recorded in [rtbl]. *)
let reg_unif_subst t1 t2 =
  let (v,_,_) = JT.dest_all t1 in
    Hashtbl.add rtbl v (TR.mkVar (N.id_of_string (JT.dest_var t2)))

let count_jpbranch one_inf =
    let (rule, (_, t1), (_, t2)) = one_inf in
      begin
      match rule with
        | Ax -> JP0
        | Orr1 | Orr2 | Negl | Impr | Alll | Exr | Exl -> JP1
        | Andr | Orl -> JP2
        | Negr -> if (JT.is_true_term t1) then JPT else JP1
        | Andl -> if (JT.is_false_term t1) then JPF else JP1
        | Impl -> JP2'  (* reverse the sons of [Impl] since [dyn_impl] reverses them *)
        | Allr -> reg_unif_subst t1 t2; JP1
        | _ -> jp_error "count_jpbranch"
      end

let replace_by r = function
  (rule, a, b) -> (r, a, b)

let rec build_jptree inf =
    match inf with
     |  [] -> ([], JPempty)
     |  h::r ->
        begin
          match count_jpbranch h with
           | JP0 -> (r,JPAx h)
           | JP1 -> let (r1,left) = build_jptree r in
                    (r1, JPA(h, left))
           | JP2 -> let (r1,left) = build_jptree r in
                    let (r2,right) = build_jptree r1 in
                    (r2, JPB(h, left, right))
           | JP2' -> let (r1,left) = build_jptree r in      (* for [Impl] *)
                    let (r2,right) = build_jptree r1 in
                    (r2, JPB(h, right, left))
           | JPT -> let (r1,left) = build_jptree r in       (* right True *)
                    (r1, JPAx (replace_by Truer h))
           | JPF -> let (r1,left) = build_jptree r in       (* left False *)
                    (r1, JPAx (replace_by Falsel h))
        end


(* The main function: *)
(* [limits] is the multiplicity limit. *)
let jp limits gls =
   let concl = TM.pf_concl gls in
   let ct = concl in
(*i     print_constr ct; i*)
     Hashtbl.clear jtbl;    (* empty the hash tables *)
     Hashtbl.clear rtbl;
     Hashtbl.clear assoc_addr;
     let t = parsing ct in
(*i     JT.print_term stdout t; i*)
        try
        let p = (J.prover limits [] t) in
(*i            print_string "\n";
            JLogic.print_inf p; i*)
            let (il,tr) = build_jptree p in
               if (il = []) then
               begin
                  Pp.msgnl (Pp.str "Proof is built.");
                  do_coq_proof tr gls
               end
               else UT.error "Cannot reconstruct proof tree from JProver."
        with e -> Pp.msgnl (Pp.str "JProver fails to prove this:");
                  JT.print_error_msg e;
                  UT.error "JProver terminated."

(* an unfailed generalization procedure *)
let non_dep_gen b gls =
  let concl = TM.pf_concl gls in
      if (not (Termops.dependent b concl)) then
         T.generalize [b] gls
      else
         TCL.tclIDTAC gls

let rec unfail_gen = function
  | [] -> TCL.tclIDTAC
  | h::r ->
     TCL.tclTHEN
        (TCL.tclORELSE (non_dep_gen h) (TCL.tclIDTAC))
        (unfail_gen r)

(*
(* no argument, which stands for no multiplicity limit *)
let jp gls =
  let ls = List.map (fst) (TM.pf_hyps_types gls) in
(*i     T.generalize (List.map TR.mkVar ls) gls i*)
    (* generalize the context *)
    TCL.tclTHEN (TCL.tclTRY T.red_in_concl)
                (TCL.tclTHEN (unfail_gen (List.map TR.mkVar ls))
                             (jp None)) gls
*)
(*
let dyn_jp l gls =
  assert (l = []);
  jp
*)

(* one optional integer argument for the multiplicity *)
let jpn n gls =
  let ls = List.map (fst) (TM.pf_hyps_types gls) in
  TCL.tclTHEN (TCL.tclTRY T.red_in_concl)
              (TCL.tclTHEN (unfail_gen (List.map TR.mkVar ls))
                         (jp n)) gls

TACTIC EXTEND jprover
  [ "jp" natural_opt(n) ] -> [ jpn n ]
END

(*
TACTIC EXTEND Andl
  [ "Andl" ident(id)] -> [ ... (Andl id) ... ].
END
*)
