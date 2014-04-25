(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* This file is about the automatic generation of schemes about
   decidable equality, created by Vincent Siles, Oct 2007 *)

open Tacmach
open Errors
open Util
open Pp
open Term
open Vars
open Termops
open Declarations
open Names
open Globnames
open Inductiveops
open Tactics
open Ind_tables
open Misctypes
open Proofview.Notations

(**********************************************************************)
(* Generic synthesis of boolean equality *)

let quick_chop n l =
  let rec kick_last = function
    | t::[] -> []
    | t::q -> t::(kick_last q)
    | [] -> failwith "kick_last"
and aux = function
    | (0,l') -> l'
    | (n,h::t) -> aux (n-1,t)
    | _ -> failwith "quick_chop"
  in
  if n > (List.length l) then failwith "quick_chop args"
  else kick_last (aux (n,l) )

let deconstruct_type t =
  let l,r = decompose_prod t in
  (List.rev_map snd l)@[r]

exception EqNotFound of inductive * inductive
exception EqUnknown of string
exception UndefinedCst of string
exception InductiveWithProduct
exception InductiveWithSort
exception ParameterWithoutEquality of constant
exception NonSingletonProp of inductive

let dl = Loc.ghost

(* Some pre declaration of constant we are going to use *)
let bb = constr_of_global Coqlib.glob_bool

let andb_prop = fun _ -> (Coqlib.build_bool_type()).Coqlib.andb_prop

let andb_true_intro = fun _ ->
    (Coqlib.build_bool_type()).Coqlib.andb_true_intro

let tt = constr_of_global Coqlib.glob_true

let ff = constr_of_global Coqlib.glob_false

let eq = constr_of_global Coqlib.glob_eq

let sumbool = Coqlib.build_coq_sumbool

let andb = fun _ -> (Coqlib.build_bool_type()).Coqlib.andb

let induct_on c =
  new_induct false
    [Tacexpr.ElimOnConstr (Evd.empty,(c,NoBindings))]
    None (None,None) None

let destruct_on_using c id =
  new_destruct false
    [Tacexpr.ElimOnConstr (Evd.empty,(c,NoBindings))]
    None
    (None,Some (dl,IntroOrAndPattern [
                                    [dl,IntroAnonymous];
                                    [dl,IntroIdentifier id]]))
    None

let destruct_on c =
  new_destruct false
    [Tacexpr.ElimOnConstr (Evd.empty,(c,NoBindings))]
    None (None,None) None

(* reconstruct the inductive with the correct deBruijn indexes *)
let mkFullInd ind n =
  let mib = Global.lookup_mind (fst ind) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  (* params context divided *)
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  if nparrec > 0
    then mkApp (mkInd ind,
      Array.of_list(extended_rel_list (nparrec+n) lnamesparrec))
    else mkInd ind

let check_bool_is_defined () =
  try let _ = Global.type_of_global Coqlib.glob_bool in ()
  with e when Errors.noncritical e -> raise (UndefinedCst "bool")

let beq_scheme_kind_aux = ref (fun _ -> failwith "Undefined")

let build_beq_scheme kn =
  check_bool_is_defined ();
  (* fetching global env *)
  let env = Global.env() in
  (* fetching the mutual inductive body *)
  let mib = Global.lookup_mind kn in
  (* number of inductives in the mutual *)
  let nb_ind = Array.length mib.mind_packets in
  (* number of params in the type *)
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  (* params context divided *)
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  (* predef coq's boolean type *)
  (* rec name *)
  let rec_name i =(Id.to_string (Array.get mib.mind_packets i).mind_typename)^
                    "_eqrec"
  in
  (* construct the "fun A B ... N, eqA eqB eqC ... N => fixpoint" part *)
  let create_input c =
    let myArrow u v = mkArrow u (lift 1 v)
    and eqName = function
        | Name s -> Id.of_string ("eq_"^(Id.to_string s))
        | Anonymous -> Id.of_string "eq_A"
    in
    let ext_rel_list = extended_rel_list 0 lnamesparrec in
      let lift_cnt = ref 0 in
      let eqs_typ = List.map (fun aa ->
                                let a = lift !lift_cnt aa in
                                  incr lift_cnt;
                                  myArrow a (myArrow a bb)
                             ) ext_rel_list in

        let eq_input = List.fold_left2
          ( fun a b (n,_,_) -> (* mkLambda(n,b,a) ) *)
                (* here I leave the Naming thingy so that the type of
                  the function is more readable for the user *)
                mkNamedLambda (eqName n) b a )
                c (List.rev eqs_typ) lnamesparrec
       in
        List.fold_left (fun a (n,_,t) ->(* mkLambda(n,t,a)) eq_input rel_list *)
          (* Same here , hoping the auto renaming will do something good ;)  *)
          mkNamedLambda
                (match n with Name s -> s | Anonymous ->  Id.of_string "A")
                t  a) eq_input lnamesparrec
 in
 let make_one_eq cur =
  let ind = kn,cur in
  (* current inductive we are working on *)
  let cur_packet = mib.mind_packets.(snd ind) in
  (* Inductive toto : [rettyp] := *)
  let rettyp = Inductive.type_of_inductive env (mib,cur_packet) in
  (* split rettyp in a list without the non rec params and the last ->
  e.g. Inductive vec (A:Set) : nat -> Set := ... will do [nat] *)
  let rettyp_l = quick_chop nparrec (deconstruct_type rettyp) in
    (* give a type A, this function tries to find the equality on A declared
       previously *)
    (*  nlist = the number of args (A , B , ... )
        eqA   = the deBruijn index of the first eq param
        ndx   = how much to translate due to the 2nd Case
    *)
    let compute_A_equality rel_list nlist eqA ndx t =
      let lifti = ndx in
      let rec aux c =
	let (c,a) = Reductionops.whd_betaiota_stack Evd.empty c in
	match kind_of_term c with
        | Rel x -> mkRel (x-nlist+ndx), Declareops.no_seff
        | Var x -> mkVar (id_of_string ("eq_"^(string_of_id x))), Declareops.no_seff
        | Cast (x,_,_) -> aux (applist (x,a))
        | App _ -> assert false
        | Ind (kn',i as ind') -> 
            if eq_mind kn kn' then mkRel(eqA-nlist-i+nb_ind-1), Declareops.no_seff
            else begin
              try
                let eq, eff =
                  let c, eff = find_scheme (!beq_scheme_kind_aux()) (kn',i) in
                  mkConst c, eff in
                let eqa, eff =
                  let eqa, effs = List.split (List.map aux a) in
                  Array.of_list eqa,
                  Declareops.union_side_effects
                    (Declareops.flatten_side_effects (List.rev effs))
                    eff in
                let args =
                  Array.append 
                    (Array.of_list (List.map (fun x -> lift lifti x) a)) eqa in
                if Int.equal (Array.length args) 0 then eq, eff
                else mkApp (eq, args), eff
              with Not_found -> raise(EqNotFound (ind',ind))
            end
        | Sort _  -> raise InductiveWithSort
        | Prod _ -> raise InductiveWithProduct
        | Lambda _-> raise (EqUnknown "Lambda")
        | LetIn _ -> raise (EqUnknown "LetIn")
        | Const kn ->
	    (match Environ.constant_opt_value env kn with
	      | None -> raise (ParameterWithoutEquality kn)
	      | Some c -> aux (applist (c,a)))
        | Construct _ -> raise (EqUnknown "Construct")
        | Case _ -> raise (EqUnknown "Case")
        | CoFix _ -> raise (EqUnknown "CoFix")
        | Fix _   -> raise (EqUnknown "Fix")
        | Meta _  -> raise (EqUnknown "Meta")
        | Evar _  -> raise (EqUnknown "Evar")
    in
      aux t
  in
  (* construct the predicate for the Case part*)
  let do_predicate rel_list n =
     List.fold_left (fun a b -> mkLambda(Anonymous,b,a))
      (mkLambda (Anonymous,
                 mkFullInd ind (n+3+(List.length rettyp_l)+nb_ind-1),
                 bb))
      (List.rev rettyp_l) in
  (* make_one_eq *)
  (* do the [| C1 ... =>  match Y with ... end
               ...
               Cn => match Y with ... end |]  part *)
    let ci = make_case_info env ind MatchStyle in
    let constrs n = get_constructors env (make_ind_family (ind,
      extended_rel_list (n+nb_ind-1) mib.mind_params_ctxt)) in
    let constrsi = constrs (3+nparrec) in
    let n = Array.length constrsi in
    let ar = Array.make n ff in
        let eff = ref Declareops.no_seff in
	for i=0 to n-1 do
	  let nb_cstr_args = List.length constrsi.(i).cs_args in
	  let ar2 = Array.make n ff in
          let constrsj = constrs (3+nparrec+nb_cstr_args) in
	    for j=0 to n-1 do
	      if Int.equal i j then
		ar2.(j) <- let cc = (match nb_cstr_args with
                    | 0 -> tt
                    | _ -> let eqs = Array.make nb_cstr_args tt in
                      for ndx = 0 to nb_cstr_args-1 do
                        let _,_,cc = List.nth constrsi.(i).cs_args ndx in
                          let eqA, eff' = compute_A_equality rel_list
                                          nparrec
                                          (nparrec+3+2*nb_cstr_args)
                                          (nb_cstr_args+ndx+1)
                                          cc
                          in
                          eff := Declareops.union_side_effects eff' !eff;
                          Array.set eqs ndx
                              (mkApp (eqA,
                                [|mkRel (ndx+1+nb_cstr_args);mkRel (ndx+1)|]
                              ))
                      done;
                      Array.fold_left
                          (fun a b -> mkApp (andb(),[|b;a|]))
                          (eqs.(0))
                          (Array.sub eqs 1 (nb_cstr_args - 1))
                  )
   		  in
		    (List.fold_left (fun a (p,q,r) -> mkLambda (p,r,a)) cc
                    (constrsj.(j).cs_args)
		)
	      else ar2.(j) <- (List.fold_left (fun a (p,q,r) ->
			mkLambda (p,r,a)) ff (constrsj.(j).cs_args) )
	    done;

	  ar.(i) <- (List.fold_left (fun a (p,q,r) -> mkLambda (p,r,a))
			(mkCase (ci,do_predicate rel_list nb_cstr_args,
				  mkVar (Id.of_string "Y") ,ar2))
			 (constrsi.(i).cs_args))
	done;
        mkNamedLambda (Id.of_string "X") (mkFullInd ind (nb_ind-1+1))  (
          mkNamedLambda (Id.of_string "Y") (mkFullInd ind (nb_ind-1+2))  (
 	    mkCase (ci, do_predicate rel_list 0,mkVar (Id.of_string "X"),ar))),
        !eff
    in (* build_beq_scheme *)
    let names = Array.make nb_ind Anonymous and
        types = Array.make nb_ind mkSet and
        cores = Array.make nb_ind mkSet in
    let eff = ref Declareops.no_seff in
    for i=0 to (nb_ind-1) do
        names.(i) <- Name (Id.of_string (rec_name i));
	types.(i) <- mkArrow (mkFullInd (kn,i) 0)
                     (mkArrow (mkFullInd (kn,i) 1) bb);
        let c, eff' = make_one_eq i in
        cores.(i) <- c;
        eff := Declareops.union_side_effects eff' !eff
    done;
    Array.init nb_ind (fun i ->
      let kelim = Inductive.elim_sorts (mib,mib.mind_packets.(i)) in
      if not (Sorts.List.mem InSet kelim) then
	raise (NonSingletonProp (kn,i));
      let fix = mkFix (((Array.make nb_ind 0),i),(names,types,cores)) in
      create_input fix),
    !eff

let beq_scheme_kind = declare_mutual_scheme_object "_beq" build_beq_scheme

let _ = beq_scheme_kind_aux := fun () -> beq_scheme_kind

(* This function tryies to get the [inductive] between a constr
  the constr should be Ind i or App(Ind i,[|args|])
*)
let destruct_ind c =
    try let u,v =  destApp c in
          let indc = destInd u in
            indc,v
    with DestKO -> let indc = destInd c in
            indc,[||]

(*
  In the following, avoid is the list of names to avoid.
  If the args of the Inductive type are A1 ... An
  then avoid should be
 [| lb_An ... lb _A1  (resp. bl_An ... bl_A1)
    eq_An .... eq_A1 An ... A1 |]
so from Ai we can find the the correct eq_Ai bl_ai or lb_ai
*)
(* used in the leib -> bool side*)
let do_replace_lb lb_scheme_key aavoid narg p q =
  let avoid = Array.of_list aavoid in
  let do_arg v offset =
  try
    let x = narg*offset in
    let s = destVar v in
    let n = Array.length avoid in
    let rec find i =
      if Id.equal avoid.(n-i) s then avoid.(n-i-x)
      else (if i<n then find (i+1)
            else error ("Var "^(Id.to_string s)^" seems unknown.")
      )
    in mkVar (find 1)
  with e when Errors.noncritical e ->
      (* if this happen then the args have to be already declared as a
              Parameter*)
      (
        let mp,dir,lbl = repr_con (destConst v) in
          mkConst (make_con mp dir (Label.make (
          if Int.equal offset 1 then ("eq_"^(Label.to_string lbl))
                       else ((Label.to_string lbl)^"_lb")
        )))
      )
  in
  Proofview.Goal.enter begin fun gl ->
    let type_of_pq = Tacmach.New.of_old (fun gl -> pf_type_of gl p) gl in
    let u,v = destruct_ind type_of_pq
    in let lb_type_of_p =
        try
          let c, eff = find_scheme lb_scheme_key u in
          Proofview.tclUNIT (mkConst c, eff)
        with Not_found ->
          (* spiwack: the format of this error message should probably
	              be improved. *)
          let err_msg =
	    (str "Leibniz->boolean:" ++
             str "You have to declare the" ++
	     str "decidability over " ++
	     Printer.pr_constr type_of_pq ++
	     str " first.")
          in
          Proofview.tclZERO (Errors.UserError("",err_msg))
       in
       lb_type_of_p >>= fun (lb_type_of_p,eff) ->
       let lb_args = Array.append (Array.append
                          (Array.map (fun x -> x) v)
                          (Array.map (fun x -> do_arg x 1) v))
                          (Array.map (fun x -> do_arg x 2) v)
        in let app =  if Array.equal eq_constr lb_args [||]
                       then lb_type_of_p else mkApp (lb_type_of_p,lb_args)
           in
           Tacticals.New.tclTHENLIST [
             Proofview.tclEFFECTS eff;
             Equality.replace p q ; Proofview.V82.tactic (apply app) ; Auto.default_auto]
  end

(* used in the bool -> leib side *)
let do_replace_bl bl_scheme_key ind aavoid narg lft rgt =
  let avoid = Array.of_list aavoid in
  let do_arg v offset =
  try
    let x = narg*offset in
    let s = destVar v in
    let n = Array.length avoid in
    let rec find i =
      if Id.equal avoid.(n-i) s then avoid.(n-i-x)
      else (if i<n then find (i+1)
            else error ("Var "^(Id.to_string s)^" seems unknown.")
      )
    in mkVar (find 1)
  with e when Errors.noncritical e ->
      (* if this happen then the args have to be already declared as a
         Parameter*)
      (
        let mp,dir,lbl = repr_con (destConst v) in
          mkConst (make_con mp dir (Label.make (
          if Int.equal offset 1 then ("eq_"^(Label.to_string lbl))
                       else ((Label.to_string lbl)^"_bl")
        )))
      )
  in

  let rec aux l1 l2 =
    match (l1,l2) with
    | (t1::q1,t2::q2) ->
        Proofview.Goal.raw_enter begin fun gl ->
        let tt1 = Tacmach.New.pf_type_of gl t1 in
        if eq_constr t1 t2 then aux q1 q2
        else (
          let u,v = try  destruct_ind tt1
          (* trick so that the good sequence is returned*)
                with e when Errors.noncritical e -> ind,[||]
          in if eq_ind u ind
             then Tacticals.New.tclTHENLIST [Equality.replace t1 t2; Auto.default_auto ; aux q1 q2 ]
             else (
               let bl_t1, eff =
               try 
                 let c, eff = find_scheme bl_scheme_key u in
                 mkConst c, eff
               with Not_found ->
		 (* spiwack: the format of this error message should probably
	                     be improved. *)
		 let err_msg = string_of_ppcmds
	                                (str "boolean->Leibniz:" ++
                                         str "You have to declare the" ++
			   	         str "decidability over " ++
				         Printer.pr_constr tt1 ++
				         str " first.")
		 in
		 error err_msg
               in let bl_args =
                        Array.append (Array.append
                          (Array.map (fun x -> x) v)
                          (Array.map (fun x -> do_arg x 1) v))
                          (Array.map (fun x -> do_arg x 2) v )
                in
                let app =  if Array.equal eq_constr bl_args [||]
                           then bl_t1 else mkApp (bl_t1,bl_args)
                in
                Tacticals.New.tclTHENLIST [
                  Proofview.tclEFFECTS eff;
                  Equality.replace_by t1 t2
                    (Tacticals.New.tclTHEN (Proofview.V82.tactic (apply app)) (Auto.default_auto)) ;
                  aux q1 q2 ]
              )
        )
        end
    | ([],[]) -> Proofview.tclUNIT ()
    | _ -> Proofview.tclZERO (UserError ("" , str"Both side of the equality must have the same arity."))
  in
  begin try Proofview.tclUNIT (destApp lft)
    with DestKO ->  Proofview.tclZERO (UserError ("" , str"replace failed."))
  end >>= fun (ind1,ca1) ->
  begin try Proofview.tclUNIT (destApp rgt)
    with DestKO -> Proofview.tclZERO (UserError ("" , str"replace failed."))
  end >>= fun (ind2,ca2) ->
  begin try Proofview.tclUNIT (destInd ind1)
    with DestKO ->
      begin try Proofview.tclUNIT (fst (destConstruct ind1))
        with DestKO -> Proofview.tclZERO (UserError ("" , str"The expected type is an inductive one."))
      end
  end >>= fun (sp1,i1) ->
  begin try Proofview.tclUNIT (destInd ind2)
    with DestKO ->
      begin try Proofview.tclUNIT (fst (destConstruct ind2))
        with DestKO -> Proofview.tclZERO (UserError ("" , str"The expected type is an inductive one."))
      end
  end >>= fun (sp2,i2) ->
  if not (eq_mind sp1 sp2) || not (Int.equal i1 i2)
  then Proofview.tclZERO (UserError ("" , str"Eq should be on the same type"))
  else aux (Array.to_list ca1) (Array.to_list ca2)

(*
  create, from a list of ids [i1,i2,...,in] the list
  [(in,eq_in,in_bl,in_al),,...,(i1,eq_i1,i1_bl_i1_al  )]
*)
let list_id l = List.fold_left ( fun a (n,_,t) -> let s' =
      match n with
        Name s -> Id.to_string s
      | Anonymous -> "A" in
          (Id.of_string s',Id.of_string ("eq_"^s'),
              Id.of_string (s'^"_bl"),
              Id.of_string (s'^"_lb"))
            ::a
    ) [] l
(*
  build the right eq_I A B.. N eq_A .. eq_N
*)
let eqI ind l =
  let list_id = list_id l in
  let eA = Array.of_list((List.map (fun (s,_,_,_) -> mkVar s) list_id)@
                           (List.map (fun (_,seq,_,_)-> mkVar seq) list_id ))
  and e, eff = 
    try let c, eff = find_scheme beq_scheme_kind ind in mkConst c, eff 
    with Not_found -> error
        ("The boolean equality on "^(string_of_mind (fst ind))^" is needed.");
  in (if Array.equal eq_constr eA [||] then e else mkApp(e,eA)), eff

(**********************************************************************)
(* Boolean->Leibniz *)

let compute_bl_goal ind lnamesparrec nparrec =
  let eqI, eff = eqI ind lnamesparrec in
  let list_id = list_id lnamesparrec in
  let create_input c =
    let x = Id.of_string "x" and
        y = Id.of_string "y" in
      let bl_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd x (mkVar s) (
            mkNamedProd y (mkVar s) (
              mkArrow
               ( mkApp(eq,[|bb;mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt|]))
               ( mkApp(eq,[|mkVar s;mkVar x;mkVar y|]))
          ))
        ) list_id in
      let bl_input = List.fold_left2 ( fun a (s,_,sbl,_) b ->
        mkNamedProd sbl b a
      ) c (List.rev list_id) (List.rev bl_typ) in
      let eqs_typ = List.map (fun (s,_,_,_) ->
          mkProd(Anonymous,mkVar s,mkProd(Anonymous,mkVar s,bb))
          ) list_id in
      let eq_input = List.fold_left2 ( fun a (s,seq,_,_) b ->
        mkNamedProd seq b a
      ) bl_input (List.rev list_id) (List.rev eqs_typ) in
      List.fold_left (fun a (n,_,t) -> mkNamedProd
                (match n with Name s -> s | Anonymous ->  Id.of_string "A")
                t  a) eq_input lnamesparrec
    in
      let n = Id.of_string "x" and
          m = Id.of_string "y" in
     create_input (
        mkNamedProd n (mkFullInd ind nparrec) (
          mkNamedProd m (mkFullInd ind (nparrec+1)) (
            mkArrow
              (mkApp(eq,[|bb;mkApp(eqI,[|mkVar n;mkVar m|]);tt|]))
              (mkApp(eq,[|mkFullInd ind (nparrec+3);mkVar n;mkVar m|]))
        ))), eff

let compute_bl_tact bl_scheme_key ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let avoid = ref [] in
      let first_intros =
        ( List.map (fun (s,_,_,_) -> s ) list_id ) @
        ( List.map (fun (_,seq,_,_ ) -> seq) list_id ) @
        ( List.map (fun (_,_,sbl,_ ) -> sbl) list_id )
      in
      let fresh_id s gl =
        Tacmach.New.of_old begin fun gsig ->
          let fresh = fresh_id (!avoid) s gsig in
          avoid := fresh::(!avoid); fresh
        end gl
      in
      Proofview.Goal.enter begin fun gl ->
      let fresh_first_intros = List.map (fun id -> fresh_id id gl) first_intros in
      let freshn = fresh_id (Id.of_string "x") gl in
      let freshm = fresh_id (Id.of_string "y") gl in
      let freshz = fresh_id (Id.of_string "Z") gl in
  (* try with *)
      Tacticals.New.tclTHENLIST [ intros_using fresh_first_intros;
                     intro_using freshn ;
                     induct_on (mkVar freshn);
                     intro_using freshm;
                     destruct_on (mkVar freshm);
                     intro_using freshz;
                     intros;
                     Tacticals.New.tclTRY (
                      Tacticals.New.tclORELSE reflexivity (Equality.discr_tac false None)
                     );
                     Proofview.V82.tactic (simpl_in_hyp (freshz,Locus.InHyp));
(*
repeat ( apply andb_prop in z;let z1:= fresh "Z" in destruct z as [z1 z]).
*)
                    Tacticals.New.tclREPEAT (
                      Tacticals.New.tclTHENLIST [
                         apply_in false false freshz [Loc.ghost, (andb_prop(), NoBindings)] None;
                         Proofview.Goal.enter begin fun gl ->
                           let fresht = fresh_id (Id.of_string "Z") gl in
                            (new_destruct false [Tacexpr.ElimOnConstr
                                      (Evd.empty,((mkVar freshz,NoBindings)))]
                                  None
                                  (None, Some (dl,IntroOrAndPattern [[
                                    dl,IntroIdentifier fresht;
                                    dl,IntroIdentifier freshz]])) None)
                         end
                        ]);
(*
  Ci a1 ... an = Ci b1 ... bn
 replace bi with ai; auto || replace bi with ai by  apply typeofbi_prod ; auto
*)
                      Proofview.Goal.enter begin fun gls ->
                        let gl = Proofview.Goal.concl gls in
                        match (kind_of_term gl) with
                        | App (c,ca) -> (
                          match (kind_of_term c) with
                          | Ind indeq ->
                              if eq_gr (IndRef indeq) Coqlib.glob_eq
                              then
                                Tacticals.New.tclTHEN
                                  (do_replace_bl bl_scheme_key ind
				     (!avoid)
                                     nparrec (ca.(2))
                                     (ca.(1)))
                                  Auto.default_auto
                              else
                                Proofview.tclZERO (UserError ("",str"Failure while solving Boolean->Leibniz."))
                          | _ -> Proofview.tclZERO (UserError ("", str"Failure while solving Boolean->Leibniz."))
                        )
                        | _ -> Proofview.tclZERO (UserError ("", str"Failure while solving Boolean->Leibniz."))
                      end

                    ]
      end

let bl_scheme_kind_aux = ref (fun _ -> failwith "Undefined")

let make_bl_scheme mind =
  let mib = Global.lookup_mind mind in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    errorlabstrm ""
      (str "Automatic building of boolean->Leibniz lemmas not supported");
  let ind = (mind,0) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  let bl_goal, eff = compute_bl_goal ind lnamesparrec nparrec in
  [|fst (Pfedit.build_by_tactic (Global.env()) bl_goal
    (compute_bl_tact (!bl_scheme_kind_aux()) ind lnamesparrec nparrec))|],
  eff

let bl_scheme_kind = declare_mutual_scheme_object "_dec_bl" make_bl_scheme

let _ = bl_scheme_kind_aux := fun () -> bl_scheme_kind

(**********************************************************************)
(* Leibniz->Boolean *)

let compute_lb_goal ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let eqI, eff = eqI ind lnamesparrec in
    let create_input c =
      let x = Id.of_string "x" and
          y = Id.of_string "y" in
      let lb_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd x (mkVar s) (
            mkNamedProd y (mkVar s) (
              mkArrow
               ( mkApp(eq,[|mkVar s;mkVar x;mkVar y|]))
               ( mkApp(eq,[|bb;mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt|]))
          ))
        ) list_id in
      let lb_input = List.fold_left2 ( fun a (s,_,_,slb) b ->
        mkNamedProd slb b a
      ) c (List.rev list_id) (List.rev lb_typ) in
      let eqs_typ = List.map (fun (s,_,_,_) ->
          mkProd(Anonymous,mkVar s,mkProd(Anonymous,mkVar s,bb))
          ) list_id in
      let eq_input = List.fold_left2 ( fun a (s,seq,_,_) b ->
        mkNamedProd seq b a
      ) lb_input (List.rev list_id) (List.rev eqs_typ) in
      List.fold_left (fun a (n,_,t) -> mkNamedProd
                (match n with Name s -> s | Anonymous ->  Id.of_string "A")
                t  a) eq_input lnamesparrec
    in
      let n = Id.of_string "x" and
          m = Id.of_string "y" in
      create_input (
        mkNamedProd n (mkFullInd ind nparrec) (
          mkNamedProd m (mkFullInd ind (nparrec+1)) (
            mkArrow
              (mkApp(eq,[|mkFullInd ind (nparrec+2);mkVar n;mkVar m|]))
              (mkApp(eq,[|bb;mkApp(eqI,[|mkVar n;mkVar m|]);tt|]))
        ))), eff

let compute_lb_tact lb_scheme_key ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
    let avoid = ref [] in
      let first_intros =
        ( List.map (fun (s,_,_,_) -> s ) list_id ) @
        ( List.map (fun (_,seq,_,_) -> seq) list_id ) @
        ( List.map (fun (_,_,_,slb) -> slb) list_id )
      in
      let fresh_id s gl =
        Tacmach.New.of_old begin fun gsig ->
          let fresh = fresh_id (!avoid) s gsig in
          avoid := fresh::(!avoid); fresh
        end gl
      in
      Proofview.Goal.enter begin fun gl ->
      let fresh_first_intros = List.map (fun id -> fresh_id id gl) first_intros in
      let freshn = fresh_id (Id.of_string "x") gl in
      let freshm = fresh_id (Id.of_string "y") gl in
      let freshz = fresh_id (Id.of_string "Z") gl in
  (* try with *)
      Tacticals.New.tclTHENLIST [ intros_using fresh_first_intros;
                     intro_using freshn ;
                     induct_on (mkVar freshn);
                     intro_using freshm;
                     destruct_on (mkVar freshm);
                     intro_using freshz;
                     intros;
                     Tacticals.New.tclTRY (
                      Tacticals.New.tclORELSE reflexivity (Equality.discr_tac false None)
                     );
                     Equality.inj None false (mkVar freshz,NoBindings);
		     intros; (Proofview.V82.tactic simpl_in_concl);
                     Auto.default_auto;
                     Tacticals.New.tclREPEAT (
                      Tacticals.New.tclTHENLIST [Proofview.V82.tactic (apply (andb_true_intro()));
                                  simplest_split ;Auto.default_auto ]
                      );
                      Proofview.Goal.enter begin fun gls ->
                        let gl = Proofview.Goal.concl gls in
                        (* assume the goal to be eq (eq_type ...) = true *)
                        match (kind_of_term gl) with
                        | App(c,ca) -> (match (kind_of_term ca.(1)) with
                          | App(c',ca') ->
                              let n = Array.length ca' in
                              do_replace_lb lb_scheme_key
				(!avoid)
                                nparrec
                                ca'.(n-2) ca'.(n-1)
                          | _ ->
                              Proofview.tclZERO (UserError ("",str"Failure while solving Leibniz->Boolean."))
                        )
                        | _ ->
                            Proofview.tclZERO (UserError ("",str"Failure while solving Leibniz->Boolean."))
                      end
                    ]
      end

let lb_scheme_kind_aux = ref (fun () -> failwith "Undefined")

let make_lb_scheme mind =
  let mib = Global.lookup_mind mind in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    errorlabstrm ""
      (str "Automatic building of Leibniz->boolean lemmas not supported");
  let ind = (mind,0) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  let lb_goal, eff = compute_lb_goal ind lnamesparrec nparrec in
  [|fst (Pfedit.build_by_tactic (Global.env()) lb_goal
    (compute_lb_tact (!lb_scheme_kind_aux()) ind lnamesparrec nparrec))|],
  eff

let lb_scheme_kind = declare_mutual_scheme_object "_dec_lb" make_lb_scheme

let _ = lb_scheme_kind_aux := fun () -> lb_scheme_kind

(**********************************************************************)
(* Decidable equality *)

let check_not_is_defined () =
  try ignore (Coqlib.build_coq_not ())
  with e when Errors.noncritical e -> raise (UndefinedCst "not")

(* {n=m}+{n<>m}  part  *)
let compute_dec_goal ind lnamesparrec nparrec =
  check_not_is_defined ();
  let list_id = list_id lnamesparrec in
    let create_input c =
      let x = Id.of_string "x" and
          y = Id.of_string "y" in
      let lb_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd x (mkVar s) (
            mkNamedProd y (mkVar s) (
              mkArrow
               ( mkApp(eq,[|mkVar s;mkVar x;mkVar y|]))
               ( mkApp(eq,[|bb;mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt|]))
          ))
        ) list_id in
      let bl_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd x (mkVar s) (
            mkNamedProd y (mkVar s) (
              mkArrow
               ( mkApp(eq,[|bb;mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt|]))
               ( mkApp(eq,[|mkVar s;mkVar x;mkVar y|]))
          ))
        ) list_id in

      let lb_input = List.fold_left2 ( fun a (s,_,_,slb) b ->
        mkNamedProd slb b a
      ) c (List.rev list_id) (List.rev lb_typ) in
      let bl_input = List.fold_left2 ( fun a (s,_,sbl,_) b ->
        mkNamedProd sbl b a
      ) lb_input (List.rev list_id) (List.rev bl_typ) in

      let eqs_typ = List.map (fun (s,_,_,_) ->
          mkProd(Anonymous,mkVar s,mkProd(Anonymous,mkVar s,bb))
          ) list_id in
      let eq_input = List.fold_left2 ( fun a (s,seq,_,_) b ->
        mkNamedProd seq b a
      ) bl_input (List.rev list_id) (List.rev eqs_typ) in
      List.fold_left (fun a (n,_,t) -> mkNamedProd
                (match n with Name s -> s | Anonymous ->  Id.of_string "A")
                t  a) eq_input lnamesparrec
    in
      let n = Id.of_string "x" and
          m = Id.of_string "y" in
        let eqnm = mkApp(eq,[|mkFullInd ind (2*nparrec+2);mkVar n;mkVar m|]) in
        create_input (
          mkNamedProd n (mkFullInd ind (2*nparrec)) (
            mkNamedProd m (mkFullInd ind (2*nparrec+1)) (
              mkApp(sumbool(),[|eqnm;mkApp (Coqlib.build_coq_not(),[|eqnm|])|])
          )
        )
      )

let compute_dec_tact ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let eqI, eff = eqI ind lnamesparrec in
  let avoid = ref [] in
  let eqtrue x = mkApp(eq,[|bb;x;tt|]) in
  let eqfalse x = mkApp(eq,[|bb;x;ff|]) in
  let first_intros =
      ( List.map (fun (s,_,_,_) -> s ) list_id ) @
      ( List.map (fun (_,seq,_,_) -> seq) list_id ) @
      ( List.map (fun (_,_,sbl,_) -> sbl) list_id ) @
      ( List.map (fun (_,_,_,slb) -> slb) list_id )
  in
  let fresh_id s gl =
    Tacmach.New.of_old begin fun gsig ->
      let fresh = fresh_id (!avoid) s gsig in
      avoid := fresh::(!avoid); fresh
    end gl
  in
  Proofview.Goal.enter begin fun gl ->
  let fresh_first_intros = List.map (fun id -> fresh_id id gl) first_intros in
  let freshn = fresh_id (Id.of_string "x") gl in
  let freshm = fresh_id (Id.of_string "y") gl in
  let freshH = fresh_id (Id.of_string "H") gl in
  let eqbnm = mkApp(eqI,[|mkVar freshn;mkVar freshm|]) in
  let arfresh = Array.of_list fresh_first_intros in
  let xargs = Array.sub arfresh 0 (2*nparrec) in
  begin try
          let c, eff = find_scheme bl_scheme_kind ind in
          Proofview.tclUNIT (mkConst c,eff) with
    Not_found ->
      Proofview.tclZERO (UserError ("",str"Error during the decidability part, boolean to leibniz"++
        str" equality is required."))
  end >>= fun (blI,eff') ->
  begin try
          let c, eff = find_scheme lb_scheme_kind ind in
          Proofview.tclUNIT (mkConst c,eff) with
    Not_found ->
      Proofview.tclZERO (UserError ("",str"Error during the decidability part, leibniz to boolean"++
        str" equality is required."))
  end >>= fun (lbI,eff'') ->
  let eff = (Declareops.union_side_effects eff'' (Declareops.union_side_effects eff' eff)) in
  Tacticals.New.tclTHENLIST [
        Proofview.tclEFFECTS eff;
        intros_using fresh_first_intros;
        intros_using [freshn;freshm];
	(*we do this so we don't have to prove the same goal twice *)
        assert_by (Name freshH) (
          mkApp(sumbool(),[|eqtrue eqbnm; eqfalse eqbnm|])
	)
	  (Tacticals.New.tclTHEN (destruct_on eqbnm) Auto.default_auto);

        Proofview.Goal.enter begin fun gl ->
          let freshH2 = fresh_id (Id.of_string "H") gl in
	  Tacticals.New.tclTHENS (destruct_on_using (mkVar freshH) freshH2) [
	    (* left *)
	    Tacticals.New.tclTHENLIST [
	      simplest_left;
              Proofview.V82.tactic (apply (mkApp(blI,Array.map(fun x->mkVar x) xargs)));
              Auto.default_auto
            ]
            ;

	    (*right *)
            Proofview.Goal.enter begin fun gl ->
            let freshH3 = fresh_id (Id.of_string "H") gl in
            Tacticals.New.tclTHENLIST [
	      simplest_right ;
              Proofview.V82.tactic (unfold_constr (Lazy.force Coqlib.coq_not_ref));
              intro;
              Equality.subst_all ();
              assert_by (Name freshH3)
		(mkApp(eq,[|bb;mkApp(eqI,[|mkVar freshm;mkVar freshm|]);tt|]))
		(Tacticals.New.tclTHENLIST [
		  Proofview.V82.tactic (apply (mkApp(lbI,Array.map (fun x->mkVar x) xargs)));
                  Auto.default_auto
		]);
	      Equality.general_rewrite_bindings_in true
	                      Locus.AllOccurrences true false
                              (List.hd !avoid)
                              ((mkVar (List.hd (List.tl !avoid))),
                                NoBindings
                              )
                              true;
              Equality.discr_tac false None
	    ]
            end
	  ]
        end
  ]
  end

let make_eq_decidability mind =
  let mib = Global.lookup_mind mind in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    anomaly (Pp.str "Decidability lemma for mutual inductive types not supported");
  let ind = (mind,0) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  [|fst (Pfedit.build_by_tactic (Global.env())
    (compute_dec_goal ind lnamesparrec nparrec)
    (compute_dec_tact ind lnamesparrec nparrec))|], Declareops.no_seff

let eq_dec_scheme_kind =
  declare_mutual_scheme_object "_eq_dec" make_eq_decidability

(* The eq_dec_scheme proofs depend on the equality and discr tactics
   but the inj tactics, that comes with discr, depends on the
   eq_dec_scheme... *)

let _ = Equality.set_eq_dec_scheme_kind eq_dec_scheme_kind
