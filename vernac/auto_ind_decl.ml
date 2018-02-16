(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This file is about the automatic generation of schemes about
   decidable equality, created by Vincent Siles, Oct 2007 *)

open CErrors
open Util
open Pp
open Term
open Constr
open Vars
open Termops
open Declarations
open Names
open Globnames
open Inductiveops
open Tactics
open Ind_tables
open Namegen
open Tactypes
open Proofview.Notations

module RelDecl = Context.Rel.Declaration

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
exception ParameterWithoutEquality of GlobRef.t
exception NonSingletonProp of inductive
exception DecidabilityMutualNotSupported
exception NoDecidabilityCoInductive
exception ConstructorWithNonParametricInductiveType of inductive
exception DecidabilityIndicesNotSupported

(* Some pre declaration of constant we are going to use *)
let andb_prop = fun _ -> UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.bool.andb_prop")

let andb_true_intro = fun _ ->
  UnivGen.constr_of_monomorphic_global
    (Coqlib.lib_ref "core.bool.andb_true_intro")

(* We avoid to use lazy as the binding of constants can change *)
let bb () = UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.bool.type")
let tt () = UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.bool.true")
let ff () = UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.bool.false")
let eq () = UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.eq.type")

let sumbool () = UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.sumbool.type")
let andb = fun _ -> UnivGen.constr_of_monomorphic_global (Coqlib.lib_ref "core.bool.andb")

let induct_on  c = induction false None c None None
let destruct_on c = destruct false None c None None

let destruct_on_using c id =
  destruct false None c
    (Some (CAst.make @@ IntroOrPattern [[CAst.make @@ IntroNaming IntroAnonymous];
               [CAst.make @@ IntroNaming (IntroIdentifier id)]]))
    None

let destruct_on_as c l =
  destruct false None c (Some (CAst.make l)) None

let inj_flags = Some {
    Equality.keep_proof_equalities = true; (* necessary *)
    injection_in_context = true; (* does not matter here *)
    Equality.injection_pattern_l2r_order = true; (* does not matter here *)
  }

let my_discr_tac = Equality.discr_tac false None
let my_inj_tac x = Equality.inj inj_flags None false None (EConstr.mkVar x,NoBindings)

(* reconstruct the inductive with the correct de Bruijn indexes *)
let mkFullInd (ind,u) n =
  let mib = Global.lookup_mind (fst ind) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  (* params context divided *)
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  if nparrec > 0
    then mkApp (mkIndU (ind,u),
      Array.of_list(Context.Rel.to_extended_list mkRel (nparrec+n) lnamesparrec))
    else mkIndU (ind,u)

let check_bool_is_defined () =
  try let _ = Typeops.type_of_global_in_context (Global.env ()) Coqlib.(lib_ref "core.bool.type") in ()
  with e when CErrors.noncritical e -> raise (UndefinedCst "bool")

let check_no_indices mib =
  if Array.exists (fun mip -> mip.mind_nrealargs <> 0) mib.mind_packets then
    raise DecidabilityIndicesNotSupported

let beq_scheme_kind_aux = ref (fun _ -> failwith "Undefined")

let build_beq_scheme mode kn =
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
  check_no_indices mib;
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
    let ext_rel_list = Context.Rel.to_extended_list mkRel 0 lnamesparrec in
      let lift_cnt = ref 0 in
      let eqs_typ = List.map (fun aa ->
                                let a = lift !lift_cnt aa in
                                  incr lift_cnt;
                                  myArrow a (myArrow a (bb ()))
                             ) ext_rel_list in

        let eq_input = List.fold_left2
          ( fun a b decl -> (* mkLambda(n,b,a) ) *)
                (* here I leave the Naming thingy so that the type of
                  the function is more readable for the user *)
                mkNamedLambda (eqName (RelDecl.get_name decl)) b a )
                c (List.rev eqs_typ) lnamesparrec
       in
        List.fold_left (fun a decl ->(* mkLambda(n,t,a)) eq_input rel_list *)
          (* Same here , hoping the auto renaming will do something good ;)  *)
          mkNamedLambda
                (match RelDecl.get_name decl with Name s -> s | Anonymous ->  Id.of_string "A")
                (RelDecl.get_type decl)  a) eq_input lnamesparrec
 in
 let make_one_eq cur =
  let u = Univ.Instance.empty in
  let ind = (kn,cur),u (* FIXME *) in
  (* current inductive we are working on *)
  let cur_packet = mib.mind_packets.(snd (fst ind)) in
  (* Inductive toto : [rettyp] := *)
  let rettyp = Inductive.type_of_inductive env ((mib,cur_packet),u) in
  (* split rettyp in a list without the non rec params and the last ->
  e.g. Inductive vec (A:Set) : nat -> Set := ... will do [nat] *)
  let rettyp_l = quick_chop nparrec (deconstruct_type rettyp) in
    (* give a type A, this function tries to find the equality on A declared
       previously *)
    (*  nlist = the number of args (A , B , ... )
        eqA   = the de Bruijn index of the first eq param
        ndx   = how much to translate due to the 2nd Case
    *)
    let compute_A_equality rel_list nlist eqA ndx t =
      let lifti = ndx in
      let rec aux c =
        let (c,a) = Reductionops.whd_betaiota_stack Evd.empty EConstr.(of_constr c) in
        let (c,a) = EConstr.Unsafe.(to_constr c, List.map to_constr a) in
        match Constr.kind c with
        | Rel x -> mkRel (x-nlist+ndx), Safe_typing.empty_private_constants
        | Var x ->
          (* Support for working in a context with "eq_x : x -> x -> bool" *)
          let eid = Id.of_string ("eq_"^(Id.to_string x)) in
          let () =
            try ignore (Environ.lookup_named eid env)
            with Not_found -> raise (ParameterWithoutEquality (VarRef x))
          in
          mkVar eid, Safe_typing.empty_private_constants
        | Cast (x,_,_) -> aux (Term.applist (x,a))
        | App _ -> assert false
        | Ind ((kn',i as ind'),u) (*FIXME: universes *) -> 
            if MutInd.equal kn kn' then mkRel(eqA-nlist-i+nb_ind-1), Safe_typing.empty_private_constants
            else begin
              try
                let eq, eff =
                  let c, eff = find_scheme ~mode (!beq_scheme_kind_aux()) (kn',i) in
                  mkConst c, eff in
                let eqa, eff =
                  let eqa, effs = List.split (List.map aux a) in
                  Array.of_list eqa,
                  List.fold_left Safe_typing.concat_private eff (List.rev effs)
                  in
                let args =
                  Array.append
                    (Array.of_list (List.map (fun x -> lift lifti x) a)) eqa in
                if Int.equal (Array.length args) 0 then eq, eff
                else mkApp (eq, args), eff
              with Not_found -> raise(EqNotFound (ind', fst ind))
            end
        | Sort _  -> raise InductiveWithSort
        | Prod _ -> raise InductiveWithProduct
        | Lambda _-> raise (EqUnknown "abstraction")
        | LetIn _ -> raise (EqUnknown "let-in")
        | Const (kn, u) ->
             (match Environ.constant_opt_value_in env (kn, u) with
              | Some c -> aux (Term.applist (c,a))
              | None ->
                 (* Support for working in a context with "eq_x : x -> x -> bool" *)
                 (* Needs Hints, see test suite *)
                 let eq_lbl = Label.make ("eq_" ^ Label.to_string (Constant.label kn)) in
                 let kneq = Constant.change_label kn eq_lbl in
                 try let _ = Environ.constant_opt_value_in env (kneq, u) in
                   Term.applist (mkConst kneq,a),
                   Safe_typing.empty_private_constants
                 with Not_found -> raise (ParameterWithoutEquality (ConstRef kn)))
        | Proj _ -> raise (EqUnknown "projection")
        | Construct _ -> raise (EqUnknown "constructor")
        | Case _ -> raise (EqUnknown "match")
        | CoFix _ -> raise (EqUnknown "cofix")
        | Fix _   -> raise (EqUnknown "fix")
        | Meta _  -> raise (EqUnknown "meta-variable")
        | Evar _  -> raise (EqUnknown "existential variable")
        | Int _ -> raise (EqUnknown "int")
    in
      aux t
  in
  (* construct the predicate for the Case part*)
  let do_predicate rel_list n =
     List.fold_left (fun a b -> mkLambda(Anonymous,b,a))
      (mkLambda (Anonymous,
                 mkFullInd ind (n+3+(List.length rettyp_l)+nb_ind-1),
                 (bb ())))
      (List.rev rettyp_l) in
  (* make_one_eq *)
  (* do the [| C1 ... =>  match Y with ... end
               ...
               Cn => match Y with ... end |]  part *)
    let ci = make_case_info env (fst ind) MatchStyle in
    let constrs n = get_constructors env (make_ind_family (ind,
      Context.Rel.to_extended_list mkRel (n+nb_ind-1) mib.mind_params_ctxt)) in
    let constrsi = constrs (3+nparrec) in
    let n = Array.length constrsi in
    let ar = Array.make n (ff ()) in
    let eff = ref Safe_typing.empty_private_constants in
	for i=0 to n-1 do
	  let nb_cstr_args = List.length constrsi.(i).cs_args in
          let ar2 = Array.make n (ff ()) in
          let constrsj = constrs (3+nparrec+nb_cstr_args) in
	    for j=0 to n-1 do
	      if Int.equal i j then
		ar2.(j) <- let cc = (match nb_cstr_args with
                    | 0 -> tt ()
                    | _ -> let eqs = Array.make nb_cstr_args (tt ()) in
                      for ndx = 0 to nb_cstr_args-1 do
                        let cc = RelDecl.get_type (List.nth constrsi.(i).cs_args ndx) in
                          let eqA, eff' = compute_A_equality rel_list
                                          nparrec
                                          (nparrec+3+2*nb_cstr_args)
                                          (nb_cstr_args+ndx+1)
                                          cc
                          in
                          eff := Safe_typing.concat_private eff' !eff;
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
		    (List.fold_left (fun a decl -> mkLambda (RelDecl.get_name decl, RelDecl.get_type decl, a)) cc
                    (constrsj.(j).cs_args)
		)
	      else ar2.(j) <- (List.fold_left (fun a decl ->
                        mkLambda (RelDecl.get_name decl, RelDecl.get_type decl, a)) (ff ())  (constrsj.(j).cs_args) )
	    done;

	  ar.(i) <- (List.fold_left (fun a decl -> mkLambda (RelDecl.get_name decl, RelDecl.get_type decl, a))
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
    let eff = ref Safe_typing.empty_private_constants in
    let u = Univ.Instance.empty in
    for i=0 to (nb_ind-1) do
        names.(i) <- Name (Id.of_string (rec_name i));
	types.(i) <- mkArrow (mkFullInd ((kn,i),u) 0)
                     (mkArrow (mkFullInd ((kn,i),u) 1) (bb ()));
        let c, eff' = make_one_eq i in
        cores.(i) <- c;
        eff := Safe_typing.concat_private eff' !eff
    done;
      (Array.init nb_ind (fun i ->
      let kelim = Inductive.elim_sorts (mib,mib.mind_packets.(i)) in
	if not (Sorts.List.mem InSet kelim) then
	  raise (NonSingletonProp (kn,i));
        let fix = match mib.mind_finite with
        | CoFinite ->
	  raise NoDecidabilityCoInductive;
        | Finite ->
          mkFix (((Array.make nb_ind 0),i),(names,types,cores))
        | BiFinite ->
          (* If the inductive type is not recursive, the fixpoint is
             not used, so let's replace it with garbage *)
          let subst = List.init nb_ind (fun _ -> mkProp) in
          Vars.substl subst cores.(i)
        in
        create_input fix),
       UState.make (Global.universes ())),
      !eff

let beq_scheme_kind = declare_mutual_scheme_object "_beq" build_beq_scheme

let _ = beq_scheme_kind_aux := fun () -> beq_scheme_kind

(* This function tryies to get the [inductive] between a constr
  the constr should be Ind i or App(Ind i,[|args|])
*)
let destruct_ind env sigma c =
  let open EConstr in
  let (c,v) = Reductionops.whd_all_stack env sigma c in
  destInd sigma c, Array.of_list v

(*
  In the following, avoid is the list of names to avoid.
  If the args of the Inductive type are A1 ... An
  then avoid should be
 [| lb_An ... lb _A1  (resp. bl_An ... bl_A1)
    eq_An .... eq_A1 An ... A1 |]
so from Ai we can find the correct eq_Ai bl_ai or lb_ai
*)
(* used in the leib -> bool side*)
let do_replace_lb mode lb_scheme_key aavoid narg p q =
  let open EConstr in
  let avoid = Array.of_list aavoid in
  let do_arg sigma hd v offset =
    match kind sigma v with
    | Var s ->
    let x = narg*offset in
    let n = Array.length avoid in
    let rec find i =
      if Id.equal avoid.(n-i) s then avoid.(n-i-x)
      else (if i<n then find (i+1)
            else user_err ~hdr:"AutoIndDecl.do_replace_lb"
                   (str "Var " ++ Id.print s ++ str " seems unknown.")
      )
    in mkVar (find 1)
    | Const (cst,_) ->
      (* Works in specific situations where the args have to be already declared as a
         Parameter (see example "J" in test file SchemeEquality.v) *)
        let lbl = Label.to_string (Constant.label cst) in
        let newlbl = if Int.equal offset 1 then ("eq_" ^ lbl) else (lbl ^ "_lb") in
        mkConst (Constant.change_label cst (Label.make newlbl))
    | _ -> raise (ConstructorWithNonParametricInductiveType (fst hd))

  in
  Proofview.Goal.enter begin fun gl ->
    let type_of_pq = Tacmach.New.pf_unsafe_type_of gl p in
    let sigma = Tacmach.New.project gl in
    let env = Tacmach.New.pf_env gl in
    let u,v = destruct_ind env sigma type_of_pq
    in let lb_type_of_p =
        try
          let c, eff = find_scheme ~mode lb_scheme_key (fst u) (*FIXME*) in
          Proofview.tclUNIT (mkConst c, eff)
        with Not_found ->
          (* spiwack: the format of this error message should probably
	              be improved. *)
          let err_msg =
	    (str "Leibniz->boolean:" ++
             str "You have to declare the" ++
	     str "decidability over " ++
             Printer.pr_econstr_env env sigma type_of_pq ++
	     str " first.")
          in
          Tacticals.New.tclZEROMSG err_msg
       in
       lb_type_of_p >>= fun (lb_type_of_p,eff) ->
       Proofview.tclEVARMAP >>= fun sigma ->
       let lb_args = Array.append (Array.append
                          v
                          (Array.Smart.map (fun x -> do_arg sigma u x 1) v))
                          (Array.Smart.map (fun x -> do_arg sigma u x 2) v)
        in let app =  if Array.is_empty lb_args
                       then lb_type_of_p else mkApp (lb_type_of_p,lb_args)
           in
           Tacticals.New.tclTHENLIST [
             Proofview.tclEFFECTS eff;
             Equality.replace p q ; apply app ; Auto.default_auto]
  end

(* used in the bool -> leb side *)
let do_replace_bl mode bl_scheme_key (ind,u as indu) aavoid narg lft rgt =
  let open EConstr in
  let avoid = Array.of_list aavoid in
  let do_arg sigma hd v offset =
    match kind sigma v with
    | Var s ->
    let x = narg*offset in
    let n = Array.length avoid in
    let rec find i =
      if Id.equal avoid.(n-i) s then avoid.(n-i-x)
      else (if i<n then find (i+1)
            else user_err ~hdr:"AutoIndDecl.do_replace_bl"
                   (str "Var " ++ Id.print s ++ str " seems unknown.")
      )
    in mkVar (find 1)
    | Const (cst,_) ->
      (* Works in specific situations where the args have to be already declared as a
         Parameter (see example "J" in test file SchemeEquality.v) *)
        let lbl = Label.to_string (Constant.label cst) in
        let newlbl = if Int.equal offset 1 then ("eq_" ^ lbl) else (lbl ^ "_bl") in
        mkConst (Constant.change_label cst (Label.make newlbl))
    | _ -> raise (ConstructorWithNonParametricInductiveType (fst hd))
  in

  let rec aux l1 l2 =
    match (l1,l2) with
    | (t1::q1,t2::q2) ->
        Proofview.Goal.enter begin fun gl ->
        let tt1 = Tacmach.New.pf_unsafe_type_of gl t1 in
        let sigma = Tacmach.New.project gl in
        let env = Tacmach.New.pf_env gl in
        if EConstr.eq_constr sigma t1 t2 then aux q1 q2
        else (
          let u,v = try destruct_ind env sigma tt1
          (* trick so that the good sequence is returned*)
                with e when CErrors.noncritical e -> indu,[||]
          in if eq_ind (fst u) ind
             then Tacticals.New.tclTHENLIST [Equality.replace t1 t2; Auto.default_auto ; aux q1 q2 ]
             else (
               let bl_t1, eff =
               try 
                 let c, eff = find_scheme bl_scheme_key (fst u) (*FIXME*) in
                 mkConst c, eff
               with Not_found ->
		 (* spiwack: the format of this error message should probably
	                     be improved. *)
		 let err_msg =
	                                (str "boolean->Leibniz:" ++
                                         str "You have to declare the" ++
			   	         str "decidability over " ++
                                         Printer.pr_econstr_env env sigma tt1 ++
				         str " first.")
		 in
		 user_err err_msg
               in let bl_args =
                        Array.append (Array.append
                          v
                          (Array.Smart.map (fun x -> do_arg sigma u x 1) v))
                          (Array.Smart.map (fun x -> do_arg sigma u x 2) v )
                in
                let app =  if Array.is_empty bl_args
                           then bl_t1 else mkApp (bl_t1,bl_args)
                in
                Tacticals.New.tclTHENLIST [
                  Proofview.tclEFFECTS eff;
                  Equality.replace_by t1 t2
                    (Tacticals.New.tclTHEN (apply app) (Auto.default_auto)) ;
                  aux q1 q2 ]
              )
        )
        end
    | ([],[]) -> Proofview.tclUNIT ()
    | _ -> Tacticals.New.tclZEROMSG (str "Both side of the equality must have the same arity.")
  in
  Proofview.tclEVARMAP >>= fun sigma ->
  begin try Proofview.tclUNIT (destApp sigma lft)
    with DestKO -> Tacticals.New.tclZEROMSG (str "replace failed.")
  end >>= fun (ind1,ca1) ->
  begin try Proofview.tclUNIT (destApp sigma rgt)
    with DestKO -> Tacticals.New.tclZEROMSG (str "replace failed.")
  end >>= fun (ind2,ca2) ->
  begin try Proofview.tclUNIT (fst (destInd sigma ind1))
    with DestKO ->
      begin try Proofview.tclUNIT (fst (fst (destConstruct sigma ind1)))
        with DestKO -> Tacticals.New.tclZEROMSG (str "The expected type is an inductive one.")
      end
  end >>= fun (sp1,i1) ->
  begin try Proofview.tclUNIT (fst (destInd sigma ind2))
    with DestKO ->
      begin try Proofview.tclUNIT (fst (fst (destConstruct sigma ind2)))
        with DestKO -> Tacticals.New.tclZEROMSG (str "The expected type is an inductive one.")
      end
  end >>= fun (sp2,i2) ->
  if not (MutInd.equal sp1 sp2) || not (Int.equal i1 i2)
  then Tacticals.New.tclZEROMSG (str "Eq should be on the same type")
  else aux (Array.to_list ca1) (Array.to_list ca2)

(*
  create, from a list of ids [i1,i2,...,in] the list
  [(in,eq_in,in_bl,in_al),,...,(i1,eq_i1,i1_bl_i1_al  )]
*)
let list_id l = List.fold_left ( fun a decl -> let s' =
      match RelDecl.get_name decl with
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
    with Not_found -> user_err ~hdr:"AutoIndDecl.eqI"
      (str "The boolean equality on " ++ Printer.pr_inductive (Global.env ()) ind ++ str " is needed.");
  in (if Array.equal Constr.equal eA [||] then e else mkApp(e,eA)), eff

(**********************************************************************)
(* Boolean->Leibniz *)

open Namegen

let compute_bl_goal ind lnamesparrec nparrec =
  let eqI, eff = eqI ind lnamesparrec in
  let list_id = list_id lnamesparrec in
  let avoid = List.fold_right (Nameops.Name.fold_right (fun id l -> Id.Set.add id l)) (List.map RelDecl.get_name lnamesparrec) Id.Set.empty in
  let create_input c =
    let x = next_ident_away (Id.of_string "x") avoid and
        y = next_ident_away (Id.of_string "y") avoid in
      let bl_typ = List.map (fun (s,seq,_,_) ->
        mkNamedProd x (mkVar s) (
            mkNamedProd y (mkVar s) (
              mkArrow
               ( mkApp(eq (),[|bb (); mkApp(mkVar seq,[|mkVar x;mkVar y|]);tt () |]))
               ( mkApp(eq (),[|mkVar s;mkVar x;mkVar y|]))
          ))
        ) list_id in
      let bl_input = List.fold_left2 ( fun a (s,_,sbl,_) b ->
        mkNamedProd sbl b a
      ) c (List.rev list_id) (List.rev bl_typ) in
      let eqs_typ = List.map (fun (s,_,_,_) ->
          mkProd(Anonymous,mkVar s,mkProd(Anonymous,mkVar s,(bb ())))
          ) list_id in
      let eq_input = List.fold_left2 ( fun a (s,seq,_,_) b ->
        mkNamedProd seq b a
      ) bl_input (List.rev list_id) (List.rev eqs_typ) in
      List.fold_left (fun a decl -> mkNamedProd
                (match RelDecl.get_name decl with Name s -> s | Anonymous -> next_ident_away (Id.of_string "A") avoid)
                (RelDecl.get_type decl) a) eq_input lnamesparrec
    in
      let n = next_ident_away (Id.of_string "x") avoid and
          m = next_ident_away (Id.of_string "y") avoid in
      let u = Univ.Instance.empty in
     create_input (
        mkNamedProd n (mkFullInd (ind,u) nparrec) (
          mkNamedProd m (mkFullInd (ind,u) (nparrec+1)) (
            mkArrow
              (mkApp(eq (),[|bb ();mkApp(eqI,[|mkVar n;mkVar m|]);tt ()|]))
              (mkApp(eq (),[|mkFullInd (ind,u) (nparrec+3);mkVar n;mkVar m|]))
        ))), eff

let compute_bl_tact mode bl_scheme_key ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let avoid = ref [] in
      let first_intros =
        ( List.map (fun (s,_,_,_) -> s ) list_id ) @
        ( List.map (fun (_,seq,_,_ ) -> seq) list_id ) @
        ( List.map (fun (_,_,sbl,_ ) -> sbl) list_id )
      in
      let fresh_id s gl =
          let fresh = fresh_id_in_env (Id.Set.of_list !avoid) s (Proofview.Goal.env gl) in
          avoid := fresh::(!avoid); fresh
      in
      Proofview.Goal.enter begin fun gl ->
      let fresh_first_intros = List.map (fun id -> fresh_id id gl) first_intros in
      let freshn = fresh_id (Id.of_string "x") gl in
      let freshm = fresh_id (Id.of_string "y") gl in
      let freshz = fresh_id (Id.of_string "Z") gl in
  (* try with *)
      Tacticals.New.tclTHENLIST [ intros_using fresh_first_intros;
                     intro_using freshn ;
                     induct_on (EConstr.mkVar freshn);
                     intro_using freshm;
                     destruct_on (EConstr.mkVar freshm);
                     intro_using freshz;
                     intros;
                     Tacticals.New.tclTRY (
                      Tacticals.New.tclORELSE reflexivity my_discr_tac
                     );
                     simpl_in_hyp (freshz,Locus.InHyp);
(*
repeat ( apply andb_prop in z;let z1:= fresh "Z" in destruct z as [z1 z]).
*)
                    Tacticals.New.tclREPEAT (
                      Tacticals.New.tclTHENLIST [
                         Simple.apply_in freshz (EConstr.of_constr (andb_prop()));
                         Proofview.Goal.enter begin fun gl ->
                           let fresht = fresh_id (Id.of_string "Z") gl in
                            destruct_on_as (EConstr.mkVar freshz)
                                  (IntroOrPattern [[CAst.make @@ IntroNaming (IntroIdentifier fresht);
                                    CAst.make @@ IntroNaming (IntroIdentifier freshz)]])
                         end
                        ]);
(*
  Ci a1 ... an = Ci b1 ... bn
 replace bi with ai; auto || replace bi with ai by  apply typeofbi_prod ; auto
*)
                      Proofview.Goal.enter begin fun gl ->
                        let concl = Proofview.Goal.concl gl in
                        let sigma = Tacmach.New.project gl in
                        match EConstr.kind sigma concl with
                        | App (c,ca) -> (
                          match EConstr.kind sigma c with
                          | Ind (indeq, u) ->
                              if GlobRef.equal (IndRef indeq) Coqlib.(lib_ref "core.eq.type")
                              then
                                Tacticals.New.tclTHEN
                                  (do_replace_bl mode bl_scheme_key ind
				     (!avoid)
                                     nparrec (ca.(2))
                                     (ca.(1)))
                                  Auto.default_auto
                              else
                                Tacticals.New.tclZEROMSG (str "Failure while solving Boolean->Leibniz.")
                          | _ -> Tacticals.New.tclZEROMSG (str" Failure while solving Boolean->Leibniz.")
                        )
                        | _ -> Tacticals.New.tclZEROMSG (str "Failure while solving Boolean->Leibniz.")
                      end

                    ]
      end

let bl_scheme_kind_aux = ref (fun _ -> failwith "Undefined")

let side_effect_of_mode = function
  | Declare.UserAutomaticRequest -> false
  | Declare.InternalTacticRequest -> true
  | Declare.UserIndividualRequest -> false

let make_bl_scheme mode mind =
  let mib = Global.lookup_mind mind in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    user_err 
      (str "Automatic building of boolean->Leibniz lemmas not supported");
  let ind = (mind,0) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let lnonparrec,lnamesparrec = (* TODO subst *)
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  let bl_goal, eff = compute_bl_goal ind lnamesparrec nparrec in
  let ctx = UState.make (Global.universes ()) in
  let side_eff = side_effect_of_mode mode in
  let bl_goal = EConstr.of_constr bl_goal in
  let (ans, _, ctx) = Pfedit.build_by_tactic ~side_eff (Global.env()) ctx bl_goal
    (compute_bl_tact mode (!bl_scheme_kind_aux()) (ind, EConstr.EInstance.empty) lnamesparrec nparrec)
  in
  ([|ans|], ctx), eff

let bl_scheme_kind = declare_mutual_scheme_object "_dec_bl" make_bl_scheme

let _ = bl_scheme_kind_aux := fun () -> bl_scheme_kind

(**********************************************************************)
(* Leibniz->Boolean *)

let compute_lb_goal ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
  let eq = eq () and tt = tt () and bb = bb () in
  let avoid = List.fold_right (Nameops.Name.fold_right (fun id l -> Id.Set.add id l)) (List.map RelDecl.get_name lnamesparrec) Id.Set.empty in
  let eqI, eff = eqI ind lnamesparrec in
    let create_input c =
      let x = next_ident_away (Id.of_string "x") avoid and
          y = next_ident_away (Id.of_string "y") avoid in
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
      List.fold_left (fun a decl -> mkNamedProd
                (match (RelDecl.get_name decl) with Name s -> s | Anonymous ->  Id.of_string "A")
                (RelDecl.get_type decl)  a) eq_input lnamesparrec
    in
      let n = next_ident_away (Id.of_string "x") avoid and
          m = next_ident_away (Id.of_string "y") avoid in
      let u = Univ.Instance.empty in
      create_input (
        mkNamedProd n (mkFullInd (ind,u) nparrec) (
          mkNamedProd m (mkFullInd (ind,u) (nparrec+1)) (
            mkArrow
              (mkApp(eq,[|mkFullInd (ind,u) (nparrec+2);mkVar n;mkVar m|]))
              (mkApp(eq,[|bb;mkApp(eqI,[|mkVar n;mkVar m|]);tt|]))
        ))), eff

let compute_lb_tact mode lb_scheme_key ind lnamesparrec nparrec =
  let list_id = list_id lnamesparrec in
    let avoid = ref [] in
      let first_intros =
        ( List.map (fun (s,_,_,_) -> s ) list_id ) @
        ( List.map (fun (_,seq,_,_) -> seq) list_id ) @
        ( List.map (fun (_,_,_,slb) -> slb) list_id )
      in
      let fresh_id s gl =
          let fresh = fresh_id_in_env (Id.Set.of_list !avoid) s (Proofview.Goal.env gl) in
          avoid := fresh::(!avoid); fresh
      in
      Proofview.Goal.enter begin fun gl ->
      let fresh_first_intros = List.map (fun id -> fresh_id id gl) first_intros in
      let freshn = fresh_id (Id.of_string "x") gl in
      let freshm = fresh_id (Id.of_string "y") gl in
      let freshz = fresh_id (Id.of_string "Z") gl in
  (* try with *)
      Tacticals.New.tclTHENLIST [ intros_using fresh_first_intros;
                     intro_using freshn ;
                     induct_on (EConstr.mkVar freshn);
                     intro_using freshm;
                     destruct_on (EConstr.mkVar freshm);
                     intro_using freshz;
                     intros;
                     Tacticals.New.tclTRY (
                      Tacticals.New.tclORELSE reflexivity my_discr_tac
                     );
                     my_inj_tac freshz;
		     intros; simpl_in_concl;
                     Auto.default_auto;
                     Tacticals.New.tclREPEAT (
                      Tacticals.New.tclTHENLIST [apply (EConstr.of_constr (andb_true_intro()));
                                  simplest_split ;Auto.default_auto ]
                      );
                      Proofview.Goal.enter begin fun gls ->
                        let concl = Proofview.Goal.concl gls in
                        let sigma = Tacmach.New.project gl in
                        (* assume the goal to be eq (eq_type ...) = true *)
                        match EConstr.kind sigma concl with
                        | App(c,ca) -> (match (EConstr.kind sigma ca.(1)) with
                          | App(c',ca') ->
                              let n = Array.length ca' in
                              do_replace_lb mode lb_scheme_key
				(!avoid)
                                nparrec
                                ca'.(n-2) ca'.(n-1)
                          | _ ->
                              Tacticals.New.tclZEROMSG (str "Failure while solving Leibniz->Boolean.")
                        )
                        | _ ->
                            Tacticals.New.tclZEROMSG (str "Failure while solving Leibniz->Boolean.")
                      end
                    ]
      end

let lb_scheme_kind_aux = ref (fun () -> failwith "Undefined")

let make_lb_scheme mode mind =
  let mib = Global.lookup_mind mind in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    user_err 
      (str "Automatic building of Leibniz->boolean lemmas not supported");
  let ind = (mind,0) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  let lb_goal, eff = compute_lb_goal ind lnamesparrec nparrec in
  let ctx = UState.make (Global.universes ()) in
  let side_eff = side_effect_of_mode mode in
  let lb_goal = EConstr.of_constr lb_goal in
  let (ans, _, ctx) = Pfedit.build_by_tactic ~side_eff (Global.env()) ctx lb_goal
    (compute_lb_tact mode (!lb_scheme_kind_aux()) ind lnamesparrec nparrec)
  in
  ([|ans|], ctx), eff

let lb_scheme_kind = declare_mutual_scheme_object "_dec_lb" make_lb_scheme

let _ = lb_scheme_kind_aux := fun () -> lb_scheme_kind

(**********************************************************************)
(* Decidable equality *)

let check_not_is_defined () =
  try ignore (Coqlib.lib_ref "core.not.type")
  with Not_found -> raise (UndefinedCst "not")

(* {n=m}+{n<>m}  part  *)
let compute_dec_goal ind lnamesparrec nparrec =
  check_not_is_defined ();
  let eq = eq () and tt = tt () and bb = bb () in
  let list_id = list_id lnamesparrec in
  let avoid = List.fold_right (Nameops.Name.fold_right (fun id l -> Id.Set.add id l)) (List.map RelDecl.get_name lnamesparrec) Id.Set.empty in
    let create_input c =
      let x = next_ident_away (Id.of_string "x") avoid and
          y = next_ident_away (Id.of_string "y") avoid in
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
      List.fold_left (fun a decl -> mkNamedProd
                (match RelDecl.get_name decl with Name s -> s | Anonymous ->  Id.of_string "A")
                (RelDecl.get_type decl) a) eq_input lnamesparrec
    in
      let n = next_ident_away (Id.of_string "x") avoid and
          m = next_ident_away (Id.of_string "y") avoid in
        let eqnm = mkApp(eq,[|mkFullInd ind (2*nparrec+2);mkVar n;mkVar m|]) in
        create_input (
          mkNamedProd n (mkFullInd ind (2*nparrec)) (
            mkNamedProd m (mkFullInd ind (2*nparrec+1)) (
              mkApp(sumbool(),[|eqnm;mkApp (UnivGen.constr_of_monomorphic_global @@ Coqlib.lib_ref "core.not.type",[|eqnm|])|])
          )
        )
      )

let compute_dec_tact ind lnamesparrec nparrec =
  let eq = eq () and tt = tt ()
  and ff = ff () and bb = bb () in
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
      let fresh = fresh_id_in_env (Id.Set.of_list !avoid) s (Proofview.Goal.env gl) in
      avoid := fresh::(!avoid); fresh
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
      Tacticals.New.tclZEROMSG (str "Error during the decidability part, boolean to leibniz equality is required.")
  end >>= fun (blI,eff') ->
  begin try
          let c, eff = find_scheme lb_scheme_kind ind in
          Proofview.tclUNIT (mkConst c,eff) with
    Not_found ->
      Tacticals.New.tclZEROMSG (str "Error during the decidability part, leibniz to boolean equality is required.")
  end >>= fun (lbI,eff'') ->
  let eff = (Safe_typing.concat_private eff'' (Safe_typing.concat_private eff' eff)) in
  Tacticals.New.tclTHENLIST [
        Proofview.tclEFFECTS eff;
        intros_using fresh_first_intros;
        intros_using [freshn;freshm];
	(*we do this so we don't have to prove the same goal twice *)
        assert_by (Name freshH) (EConstr.of_constr (
          mkApp(sumbool(),[|eqtrue eqbnm; eqfalse eqbnm|])
	))
	  (Tacticals.New.tclTHEN (destruct_on (EConstr.of_constr eqbnm)) Auto.default_auto);

        Proofview.Goal.enter begin fun gl ->
          let freshH2 = fresh_id (Id.of_string "H") gl in
	  Tacticals.New.tclTHENS (destruct_on_using (EConstr.mkVar freshH) freshH2) [
	    (* left *)
	    Tacticals.New.tclTHENLIST [
	      simplest_left;
              apply (EConstr.of_constr (mkApp(blI,Array.map mkVar xargs)));
              Auto.default_auto
            ]
            ;

	    (*right *)
            Proofview.Goal.enter begin fun gl ->
            let freshH3 = fresh_id (Id.of_string "H") gl in
            Tacticals.New.tclTHENLIST [
	      simplest_right ;
              unfold_constr (Coqlib.lib_ref "core.not.type");
              intro;
              Equality.subst_all ();
              assert_by (Name freshH3)
		(EConstr.of_constr (mkApp(eq,[|bb;mkApp(eqI,[|mkVar freshm;mkVar freshm|]);tt|])))
		(Tacticals.New.tclTHENLIST [
                  apply (EConstr.of_constr (mkApp(lbI,Array.map mkVar xargs)));
                  Auto.default_auto
		]);
	      Equality.general_rewrite_bindings_in true
	                      Locus.AllOccurrences true false
                              (List.hd !avoid)
                              ((EConstr.mkVar (List.hd (List.tl !avoid))),
                                NoBindings
                              )
                              true;
              my_discr_tac
	    ]
            end
	  ]
        end
  ]
  end

let make_eq_decidability mode mind =
  let mib = Global.lookup_mind mind in
  if not (Int.equal (Array.length mib.mind_packets) 1) then
    raise DecidabilityMutualNotSupported;
  let ind = (mind,0) in
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let u = Univ.Instance.empty in
  let ctx = UState.make (Global.universes ()) in
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) mib.mind_params_ctxt in
  let side_eff = side_effect_of_mode mode in
  let (ans, _, ctx) = Pfedit.build_by_tactic ~side_eff (Global.env()) ctx
    (EConstr.of_constr (compute_dec_goal (ind,u) lnamesparrec nparrec))
    (compute_dec_tact ind lnamesparrec nparrec)
  in
  ([|ans|], ctx), Safe_typing.empty_private_constants

let eq_dec_scheme_kind =
  declare_mutual_scheme_object "_eq_dec" make_eq_decidability

(* The eq_dec_scheme proofs depend on the equality and discr tactics
   but the inj tactics, that comes with discr, depends on the
   eq_dec_scheme... *)

let _ = Equality.set_eq_dec_scheme_kind eq_dec_scheme_kind
