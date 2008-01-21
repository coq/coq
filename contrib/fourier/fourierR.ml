(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)



(* La tactique Fourier ne fonctionne de mani�re s�re que si les coefficients 
des in�quations et �quations sont entiers. En attendant la tactique Field.
*)

open Term
open Tactics
open Clenv
open Names
open Libnames
open Tacticals
open Fourier
open Contradiction

(* arnaud: trucs factices *)
let pf_concl _ = Util.anomaly "FourierR.pf_concl: fantome"
let pf_hyps _ = Util.anomaly "FourierR.pf_hyps: fantome"
module Refiner =
  struct
    let abstract_extended_tactic = Tacticals.abstract_extended_tactic
  end
(* arnaud: /trucs factices *)

(******************************************************************************
Op�rations sur les combinaisons lin�aires affines.
La partie homog�ne d'une combinaison lin�aire est en fait une table de hash 
qui donne le coefficient d'un terme du calcul des constructions, 
qui est z�ro si le terme n'y est pas. 
*)

type flin = {fhom:(constr , rational)Hashtbl.t;
             fcste:rational};;

let flin_zero () = {fhom=Hashtbl.create 50;fcste=r0};;

let flin_coef f x = try (Hashtbl.find f.fhom x) with _-> r0;;

let flin_add f x c = 
    let cx = flin_coef f x in
    Hashtbl.remove f.fhom x;
    Hashtbl.add f.fhom x (rplus cx c);
    f
;;
let flin_add_cste f c = 
    {fhom=f.fhom;
     fcste=rplus f.fcste c}
;;

let flin_one () = flin_add_cste (flin_zero()) r1;;

let flin_plus f1 f2 = 
    let f3 = flin_zero() in
    Hashtbl.iter (fun x c -> let _=flin_add f3 x c in ()) f1.fhom;
    Hashtbl.iter (fun x c -> let _=flin_add f3 x c in ()) f2.fhom;
    flin_add_cste (flin_add_cste f3 f1.fcste) f2.fcste;
;;

let flin_minus f1 f2 = 
    let f3 = flin_zero() in
    Hashtbl.iter (fun x c -> let _=flin_add f3 x c in ()) f1.fhom;
    Hashtbl.iter (fun x c -> let _=flin_add f3 x (rop c) in ()) f2.fhom;
    flin_add_cste (flin_add_cste f3 f1.fcste) (rop f2.fcste);
;;
let flin_emult a f =
    let f2 = flin_zero() in
    Hashtbl.iter (fun x c -> let _=flin_add f2 x (rmult a c) in ()) f.fhom;
    flin_add_cste f2 (rmult a f.fcste);
;;
    
(*****************************************************************************)
open Vernacexpr

type ineq = Rlt | Rle | Rgt | Rge

let string_of_R_constant kn = 
  match Names.repr_con kn with
    | MPfile dir, sec_dir, id when 
	sec_dir = empty_dirpath && 
	string_of_dirpath dir = "Coq.Reals.Rdefinitions" 
	-> string_of_label id
    | _ -> "constant_not_of_R"

let rec string_of_R_constr c =
 match kind_of_term c with
   Cast (c,_,_) -> string_of_R_constr c
  |Const c -> string_of_R_constant c
  | _ -> "not_of_constant"

let rec rational_of_constr c =
  match kind_of_term c with
  | Cast (c,_,_) -> (rational_of_constr c)
  | App (c,args) ->
      (match (string_of_R_constr c) with
	 | "Ropp" -> 
	     rop (rational_of_constr args.(0))
	 | "Rinv" -> 
	     rinv (rational_of_constr args.(0))
	 | "Rmult" -> 
	     rmult (rational_of_constr args.(0))
                   (rational_of_constr args.(1))
	 | "Rdiv" -> 
	     rdiv (rational_of_constr args.(0))
                  (rational_of_constr args.(1))
	 | "Rplus" -> 
	     rplus (rational_of_constr args.(0))
                   (rational_of_constr args.(1))
	 | "Rminus" -> 
	     rminus (rational_of_constr args.(0))
                    (rational_of_constr args.(1))
	 | _ -> failwith "not a rational")
  | Const kn ->
      (match (string_of_R_constant kn) with
	       "R1" -> r1
              |"R0" -> r0
              |  _ -> failwith "not a rational")
  |  _ -> failwith "not a rational"
;;

let rec flin_of_constr c =
  try(
    match kind_of_term c with
  | Cast (c,_,_) -> (flin_of_constr c)
  | App (c,args) ->
      (match (string_of_R_constr c) with
	   "Ropp" -> 
             flin_emult (rop r1) (flin_of_constr args.(0))
	 | "Rplus"-> 
             flin_plus (flin_of_constr args.(0))
	               (flin_of_constr args.(1))
	 | "Rminus"->
             flin_minus (flin_of_constr args.(0))
	                (flin_of_constr args.(1))
	 | "Rmult"->
	     (try (let a=(rational_of_constr args.(0)) in
                     try (let b = (rational_of_constr args.(1)) in
			    (flin_add_cste (flin_zero()) (rmult a b)))
		     with _-> (flin_add (flin_zero())
				 args.(1) 
				 a))
	      with _-> (flin_add (flin_zero())
			  args.(0) 
			  (rational_of_constr args.(1))))
	 | "Rinv"->
	     let a=(rational_of_constr args.(0)) in
	       flin_add_cste (flin_zero()) (rinv a)
	 | "Rdiv"->
	     (let b=(rational_of_constr args.(1)) in
		try (let a = (rational_of_constr args.(0)) in
		       (flin_add_cste (flin_zero()) (rdiv a b)))
		with _-> (flin_add (flin_zero())
		            args.(0) 
                            (rinv b)))
         |_->assert false)
  | Const c ->
        (match (string_of_R_constant c) with
	       "R1" -> flin_one ()
              |"R0" -> flin_zero ()
              |_-> assert false)
  |_-> assert false)
  with _ -> flin_add (flin_zero())
                     c
	             r1
;;

let flin_to_alist f =
    let res=ref [] in
    Hashtbl.iter (fun x c -> res:=(c,x)::(!res)) f;
    !res
;;

(* Repr�sentation des hypoth�ses qui sont des in�quations ou des �quations.
*)
type hineq={hname:constr; (* le nom de l'hypoth�se *)
            htype:string; (* Rlt, Rgt, Rle, Rge, eqTLR ou eqTRL *)
            hleft:constr;
            hright:constr;
            hflin:flin;
            hstrict:bool}
;;

(* Transforme une hypothese h:t en in�quation flin<0 ou flin<=0
*)
let ineq1_of_constr (h,t) =
    match (kind_of_term t) with
       App (f,args) ->
         (match kind_of_term f with
           Const c when Array.length args = 2 ->
             let t1= args.(0) in
             let t2= args.(1) in
            (match (string_of_R_constant c) with
		 "Rlt" -> [{hname=h;
                           htype="Rlt";
		           hleft=t1;
			   hright=t2;
			   hflin= flin_minus (flin_of_constr t1)
                                             (flin_of_constr t2);
			   hstrict=true}]
		|"Rgt" -> [{hname=h;
                           htype="Rgt";
		           hleft=t2;
			   hright=t1;
			   hflin= flin_minus (flin_of_constr t2)
                                             (flin_of_constr t1);
			   hstrict=true}]
		|"Rle" -> [{hname=h;
                           htype="Rle";
		           hleft=t1;
			   hright=t2;
			   hflin= flin_minus (flin_of_constr t1)
                                             (flin_of_constr t2);
			   hstrict=false}]
		|"Rge" -> [{hname=h;
                           htype="Rge";
		           hleft=t2;
			   hright=t1;
			   hflin= flin_minus (flin_of_constr t2)
                                             (flin_of_constr t1);
			   hstrict=false}]
                |_->assert false)
          | Ind (kn,i) ->
	      if IndRef(kn,i) = Coqlib.glob_eq then
		           let t0= args.(0) in
                           let t1= args.(1) in
                           let t2= args.(2) in
		    (match (kind_of_term t0) with
                         Const c ->
			   (match (string_of_R_constant c) with
			      "R"->
                         [{hname=h;
                           htype="eqTLR";
		           hleft=t1;
			   hright=t2;
			   hflin= flin_minus (flin_of_constr t1)
                                             (flin_of_constr t2);
			   hstrict=false};
                          {hname=h;
                           htype="eqTRL";
		           hleft=t2;
			   hright=t1;
			   hflin= flin_minus (flin_of_constr t2)
                                             (flin_of_constr t1);
			   hstrict=false}]
                           |_-> assert false)
                         |_-> assert false)
	      else
		assert false
          |_-> assert false)
        |_-> assert false
;;

(* Applique la m�thode de Fourier � une liste d'hypoth�ses (type hineq)
*)

let fourier_lineq lineq1 = 
   let nvar=ref (-1) in
   let hvar=Hashtbl.create 50 in (* la table des variables des in�quations *)
   List.iter (fun f ->
               Hashtbl.iter (fun x c ->
				 try (Hashtbl.find hvar x;())
				 with _-> nvar:=(!nvar)+1;
   				          Hashtbl.add hvar x (!nvar))
                            f.hflin.fhom)
             lineq1;
   let sys= List.map (fun h->
               let v=Array.create ((!nvar)+1) r0 in
               Hashtbl.iter (fun x c -> v.(Hashtbl.find hvar x)<-c) 
                  h.hflin.fhom;
               ((Array.to_list v)@[rop h.hflin.fcste],h.hstrict))
             lineq1 in
   unsolvable sys
;;

(*********************************************************************)
(* Defined constants *)

let get = Lazy.force
let constant = Coqlib.gen_constant "Fourier"

(* Standard library *)
open Coqlib
let coq_sym_eqT = lazy (build_coq_sym_eq ())
let coq_False = lazy (build_coq_False ())
let coq_not = lazy (build_coq_not ())
let coq_eq = lazy (build_coq_eq ())

(* Rdefinitions *)
let constant_real = constant ["Reals";"Rdefinitions"]

let coq_Rlt = lazy (constant_real "Rlt")
let coq_Rgt = lazy (constant_real "Rgt")
let coq_Rle = lazy (constant_real "Rle")
let coq_Rge = lazy (constant_real "Rge")
let coq_R = lazy (constant_real "R")
let coq_Rminus = lazy (constant_real "Rminus")
let coq_Rmult = lazy (constant_real "Rmult")
let coq_Rplus = lazy (constant_real "Rplus")
let coq_Ropp = lazy (constant_real "Ropp")
let coq_Rinv = lazy (constant_real "Rinv")
let coq_R0 = lazy (constant_real "R0")
let coq_R1 = lazy (constant_real "R1")

(* RIneq *)
let coq_Rinv_1 = lazy (constant ["Reals";"RIneq"] "Rinv_1")

(* Fourier_util *)
let constant_fourier = constant ["fourier";"Fourier_util"]

let coq_Rlt_zero_1 = lazy (constant_fourier "Rlt_zero_1")
let coq_Rlt_zero_pos_plus1 = lazy (constant_fourier "Rlt_zero_pos_plus1")
let coq_Rle_zero_pos_plus1 = lazy (constant_fourier "Rle_zero_pos_plus1")
let coq_Rlt_mult_inv_pos = lazy (constant_fourier "Rlt_mult_inv_pos")
let coq_Rle_zero_zero = lazy (constant_fourier "Rle_zero_zero")
let coq_Rle_zero_1 = lazy (constant_fourier "Rle_zero_1")
let coq_Rle_mult_inv_pos = lazy (constant_fourier "Rle_mult_inv_pos")
let coq_Rnot_lt0 = lazy (constant_fourier "Rnot_lt0")
let coq_Rle_not_lt = lazy (constant_fourier "Rle_not_lt")
let coq_Rfourier_gt_to_lt = lazy (constant_fourier "Rfourier_gt_to_lt")
let coq_Rfourier_ge_to_le = lazy (constant_fourier "Rfourier_ge_to_le")
let coq_Rfourier_eqLR_to_le = lazy (constant_fourier "Rfourier_eqLR_to_le")
let coq_Rfourier_eqRL_to_le = lazy (constant_fourier "Rfourier_eqRL_to_le")

let coq_Rfourier_not_ge_lt = lazy (constant_fourier "Rfourier_not_ge_lt")
let coq_Rfourier_not_gt_le = lazy (constant_fourier "Rfourier_not_gt_le")
let coq_Rfourier_not_le_gt = lazy (constant_fourier "Rfourier_not_le_gt")
let coq_Rfourier_not_lt_ge = lazy (constant_fourier "Rfourier_not_lt_ge")
let coq_Rfourier_lt = lazy (constant_fourier "Rfourier_lt")
let coq_Rfourier_le = lazy (constant_fourier "Rfourier_le")
let coq_Rfourier_lt_lt = lazy (constant_fourier "Rfourier_lt_lt")
let coq_Rfourier_lt_le = lazy (constant_fourier "Rfourier_lt_le")
let coq_Rfourier_le_lt = lazy (constant_fourier "Rfourier_le_lt")
let coq_Rfourier_le_le = lazy (constant_fourier "Rfourier_le_le")
let coq_Rnot_lt_lt = lazy (constant_fourier "Rnot_lt_lt")
let coq_Rnot_le_le = lazy (constant_fourier "Rnot_le_le")
let coq_Rlt_not_le = lazy (constant_fourier "Rlt_not_le")

(******************************************************************************
Construction de la preuve en cas de succ�s de la m�thode de Fourier,
i.e. on obtient une contradiction.
*)
let is_int x = (x.den)=1
;;

(* fraction = couple (num,den) *)
let rec rational_to_fraction x= (x.num,x.den)
;;
    
(* traduction -3 -> (Ropp (Rplus R1 (Rplus R1 R1)))
*)
let int_to_real n =
   let nn=abs n in
   if nn=0
   then get coq_R0
   else
     (let s=ref (get coq_R1) in
      for i=1 to (nn-1) do s:=mkApp (get coq_Rplus,[|get coq_R1;!s|]) done;
      if n<0 then mkApp (get coq_Ropp, [|!s|]) else !s)
;;
(* -1/2 -> (Rmult (Ropp R1) (Rinv (Rplus R1 R1)))
*)
let rational_to_real x =
   let (n,d)=rational_to_fraction x in
   mkApp (get coq_Rmult,
     [|int_to_real n;mkApp(get coq_Rinv,[|int_to_real d|])|])
;;

(* preuve que 0<n*1/d
*)
let tac_zero_inf_pos gl (n,d) =
   let tacn=ref (apply (get coq_Rlt_zero_1)) in
   let tacd=ref (apply (get coq_Rlt_zero_1)) in
   for i=1 to n-1 do 
       tacn:=(tclTHEN (apply (get coq_Rlt_zero_pos_plus1)) !tacn); done;
   for i=1 to d-1 do
       tacd:=(tclTHEN (apply (get coq_Rlt_zero_pos_plus1)) !tacd); done;
   (tclTHENS (apply (get coq_Rlt_mult_inv_pos)) [!tacn;!tacd])
;;

(* preuve que 0<=n*1/d
*)
let tac_zero_infeq_pos gl (n,d)=
   let tacn=ref (if n=0 
                 then (apply (get coq_Rle_zero_zero))
                 else (apply (get coq_Rle_zero_1))) in
   let tacd=ref (apply (get coq_Rlt_zero_1)) in
   for i=1 to n-1 do 
       tacn:=(tclTHEN (apply (get coq_Rle_zero_pos_plus1)) !tacn); done;
   for i=1 to d-1 do
       tacd:=(tclTHEN (apply (get coq_Rlt_zero_pos_plus1)) !tacd); done;
   (tclTHENS (apply (get coq_Rle_mult_inv_pos)) [!tacn;!tacd])
;;
  
(* preuve que 0<(-n)*(1/d) => False 
*)
let tac_zero_inf_false gl (n,d) =
    if n=0 then (apply (get coq_Rnot_lt0))
    else
     (tclTHEN (apply (get coq_Rle_not_lt))
	      (tac_zero_infeq_pos gl (-n,d)))
;;

(* preuve que 0<=(-n)*(1/d) => False 
*)
let tac_zero_infeq_false gl (n,d) =
     (tclTHEN (apply (get coq_Rlt_not_le))
	      (tac_zero_inf_pos gl (-n,d)))
;;

let create_meta () = mkMeta(Evarutil.new_meta());;
   
let my_cut c gl=
     let concl = pf_concl gl in
       apply_type (mkProd(Anonymous,c,concl)) [create_meta()] gl
;;

let exact = exact_check;;

let tac_use h = match h.htype with
               "Rlt" -> exact h.hname
              |"Rle" -> exact h.hname
              |"Rgt" -> (tclTHEN (apply (get coq_Rfourier_gt_to_lt))
                                (exact h.hname))
              |"Rge" -> (tclTHEN (apply (get coq_Rfourier_ge_to_le))
                                (exact h.hname))
              |"eqTLR" -> (tclTHEN (apply (get coq_Rfourier_eqLR_to_le))
                                (exact h.hname))
              |"eqTRL" -> (tclTHEN (apply (get coq_Rfourier_eqRL_to_le))
                                (exact h.hname))
              |_->assert false
;;

(*
let is_ineq (h,t) =
    match (kind_of_term t) with
	App (f,args) ->
	  (match (string_of_R_constr f) with
	       "Rlt" -> true
	     | "Rgt" -> true
	     | "Rle" -> true
	     | "Rge" -> true
(* Wrong:not in Rdefinitions: *) | "eqT" ->
                (match (string_of_R_constr args.(0)) with
			     "R" -> true
			   | _ -> false)
             | _ ->false)
      |_->false
;;
*)

let list_of_sign s = List.map (fun (x,_,z)->(x,z)) s;;

let mkAppL a =
   let l = Array.to_list a in
   mkApp(List.hd l, Array.of_list (List.tl l))
;;

(* R�solution d'in�quations lin�aires dans R *)
let rec fourier gl=
    Coqlib.check_required_library ["Coq";"fourier";"Fourier"];
    let goal = strip_outer_cast (pf_concl gl) in
    let fhyp=id_of_string "new_hyp_for_fourier" in
    (* si le but est une in�quation, on introduit son contraire,
       et le but � prouver devient False *)
    try (let tac =
     match (kind_of_term goal) with
      App (f,args) ->
      (match (string_of_R_constr f) with
	     "Rlt" -> 
	       (tclTHEN
	         (tclTHEN (apply (get coq_Rfourier_not_ge_lt))
			  (intro_using  fhyp))
		 fourier)
	    |"Rle" -> 
	     (tclTHEN
	      (tclTHEN (apply (get coq_Rfourier_not_gt_le))
		       (intro_using  fhyp))
			fourier)
	    |"Rgt" -> 
	     (tclTHEN
	      (tclTHEN (apply (get coq_Rfourier_not_le_gt))
		       (intro_using  fhyp))
	      fourier)
	    |"Rge" -> 
	     (tclTHEN
	      (tclTHEN (apply (get coq_Rfourier_not_lt_ge))
		       (intro_using  fhyp))
	      fourier)
	    |_->assert false)
        |_->assert false
      in tac gl)
     with _ -> 
    (* les hypoth�ses *)
    let hyps = List.map (fun (h,t)-> (mkVar h,t))
                        (list_of_sign (pf_hyps gl)) in
    let lineq =ref [] in
    List.iter (fun h -> try (lineq:=(ineq1_of_constr h)@(!lineq))
		        with _ -> ())
              hyps;
    (* lineq = les in�quations d�coulant des hypoth�ses *)
    if !lineq=[] then Util.error "No inequalities";
    let res=fourier_lineq (!lineq) in
    let tac=ref tclIDTAC in
    if res=[]
    then (print_string "Tactic Fourier fails.\n";
		       flush stdout)
    (* l'algorithme de Fourier a r�ussi: on va en tirer une preuve Coq *)
    else (match res with
        [(cres,sres,lc)]->
    (* lc=coefficients multiplicateurs des in�quations
       qui donnent 0<cres ou 0<=cres selon sres *)
	(*print_string "Fourier's method can prove the goal...";flush stdout;*)
          let lutil=ref [] in
	  List.iter 
            (fun (h,c) ->
			  if c<>r0
        		  then (lutil:=(h,c)::(!lutil)(*;
				print_rational(c);print_string " "*)))
                    (List.combine (!lineq) lc); 
       (* on construit la combinaison lin�aire des in�quation *)
             (match (!lutil) with
          (h1,c1)::lutil ->
	  let s=ref (h1.hstrict) in
	  let t1=ref (mkAppL [|get coq_Rmult;
	                  rational_to_real c1;
			  h1.hleft|]) in
	  let t2=ref (mkAppL [|get coq_Rmult;
	                  rational_to_real c1;
			  h1.hright|]) in
	  List.iter (fun (h,c) ->
	       s:=(!s)||(h.hstrict);
	       t1:=(mkAppL [|get coq_Rplus;
	                     !t1;
                             mkAppL [|get coq_Rmult;
                                      rational_to_real c;
			              h.hleft|] |]);
	       t2:=(mkAppL [|get coq_Rplus;
	                     !t2;
                             mkAppL [|get coq_Rmult;
                                      rational_to_real c;
			              h.hright|] |]))
               lutil;
          let ineq=mkAppL [|if (!s) then get coq_Rlt else get coq_Rle;
			      !t1;
			      !t2 |] in
	   let tc=rational_to_real cres in
       (* puis sa preuve *)
           let tac1=ref (if h1.hstrict 
                         then (tclTHENS (apply (get coq_Rfourier_lt))
                                 [tac_use h1;
                                  tac_zero_inf_pos  gl
                                      (rational_to_fraction c1)])
                         else (tclTHENS (apply (get coq_Rfourier_le))
                                 [tac_use h1;
				  tac_zero_inf_pos  gl
                                      (rational_to_fraction c1)])) in
           s:=h1.hstrict;
           List.iter (fun (h,c)-> 
             (if (!s)
	      then (if h.hstrict
	            then tac1:=(tclTHENS (apply (get coq_Rfourier_lt_lt))
			       [!tac1;tac_use h; 
			        tac_zero_inf_pos  gl
                                      (rational_to_fraction c)])
	            else tac1:=(tclTHENS (apply (get coq_Rfourier_lt_le))
			       [!tac1;tac_use h; 
			        tac_zero_inf_pos  gl
                                      (rational_to_fraction c)]))
	      else (if h.hstrict
	            then tac1:=(tclTHENS (apply (get coq_Rfourier_le_lt))
			       [!tac1;tac_use h; 
			        tac_zero_inf_pos  gl
                                      (rational_to_fraction c)])
	            else tac1:=(tclTHENS (apply (get coq_Rfourier_le_le))
			       [!tac1;tac_use h; 
			        tac_zero_inf_pos  gl
                                      (rational_to_fraction c)])));
	     s:=(!s)||(h.hstrict))
              lutil;
           let tac2= if sres
                      then tac_zero_inf_false gl (rational_to_fraction cres)
                      else tac_zero_infeq_false gl (rational_to_fraction cres)
           in
           tac:=(tclTHENS (my_cut ineq) 
                     [tclTHEN (change_in_concl None
			       (mkAppL [| get coq_not; ineq|]
				       ))
		      (tclTHEN (apply (if sres then get coq_Rnot_lt_lt
					       else get coq_Rnot_le_le))
			    (tclTHENS (Equality.replace
				       (mkAppL [|get coq_Rminus;!t2;!t1|]
					       )
				       tc)
		 	       [tac2;
                                (tclTHENS
				  (Equality.replace
				    (mkApp (get coq_Rinv, 
				      [|get coq_R1|]))
				    (get coq_R1))
(* en attendant Field, �a peut aider Ring de remplacer 1/1 par 1 ... *)	

      			        [tclORELSE
                                   (Ring.polynom [])
                                   tclIDTAC;
					  (tclTHEN (apply (get coq_sym_eqT))
						(apply (get coq_Rinv_1)))]
                               
					 )
				]));
                       !tac1]);
	   tac:=(tclTHENS (cut (get coq_False))
				  [tclTHEN intro (contradiction None);
				   !tac])
      |_-> assert false) |_-> assert false
	  );
(*    ((tclTHEN !tac (tclFAIL 1 (* 1 au hasard... *))) gl) *)
      (!tac gl) 
(*      ((tclABSTRACT None !tac) gl) *)

;;

(*
let fourier_tac x gl =
     fourier gl
;;

let v_fourier = add_tactic "Fourier" fourier_tac
*)

