
(* $Id$ *)

(* Autor: Cesar A. Munnoz H *)

open Pp
open Util
open Names
open Generic
open Term
open Sign
open Environ
open Declare
open Tacmach
open Reduction
open Tacticals
open Tactics
open Pattern
open Auto
(* Chet's code *)
open Proof_trees
open Clenv
open Pattern

let hlset_subset hls1 hls2 =
  List.for_all (fun e -> List.exists (fun e' -> eq_constr e e') hls2) hls1

let hlset_eq hls1 hls2 =
  hlset_subset hls1 hls2 & hlset_subset hls2 hls1
  
let eq_gls g1 g2 =
    eq_constr (pf_concl g1) (pf_concl g2)
 &  (let hl1 = vals_of_sign (pf_untyped_hyps g1)
     and hl2 = vals_of_sign (pf_untyped_hyps g2) in 
     hlset_eq hl1 hl2)

let gls_memb bTS g = List.exists (eq_gls g) bTS

let gls_add g bTS =
  if gls_memb bTS g then error "backtrack in tauto";
  g::bTS

let classically cltac = function
  | (Some _ as cls) -> (tclTHEN (cltac cls) (clear_clause cls))
  | None -> cltac None

let somatch m pat = somatch None (get_pat pat) m
let module_mark   = ["Logic"]
let mmk           = make_module_marker ["Prelude"]
let false_pattern = put_pat mmk "False"
let true_pattern = put_pat mmk "True"
let and_pattern   = put_pat mmk "(and ? ?)"
let or_pattern    = put_pat mmk "(or ? ?)"
let eq_pattern    = put_pat mmk "(eq ? ? ?)"
let pi_pattern    = put_pat mmk "(x:?)((?)@[x])"
let imply_pattern = put_pat mmk "?1->?2"
let iff_pattern   = put_pat mmk "(iff ? ?)"
let not_pattern   = put_pat mmk "(not ?1)"
let mkIMP a b     = soinstance imply_pattern [a;b]    

let is_atomic m =
 (not (is_conjunction m)     ||
      (is_disjunction m)     ||
      (somatches m pi_pattern)  ||
      (somatches m not_pattern))
      
let hypothesis = function Some id -> exact (VAR id) | None -> assert false

(* Steps of the procedure *)

(* 1. A,Gamma |- A *)
let dyck_hypothesis = compose hypothesis in_some

(* 2. False,Gamma |- G *)
let dyck_absurdity_elim = contradiction_on_hyp

(*3. A,B,Gamma |- G
  ---------------
  A/\B,Gamma |- G
 *)
let dyck_and_elim = compose (classically dAnd) in_some

(*4. Gamma |- A  Gamma |- B
  -----------------------
  Gamma |- A /\ B
 *)
let dyck_and_intro = (dAnd None)


(*5. A,Gamma |- G    B,Gamma|- G
  ---------------------------
  A\/B,Gamma |- G
 *)

let dyck_or_elim = compose (classically (dorE false)) in_some

(*6. Gamma |- A
  ----------
  Gamma |- A\/B
 *)
let dyck_or_introleft = (dorE false)


(*7. Gamma |-B
  ---------
  Gamma |- A\/B
 *)
let dyck_or_introright = (dorE true)


(*8. A,Gamma |- B
  --------------
  Gamma |- A -> B
 *)
let dyck_imply_intro = (dImp None) 


(*9.
    B,A,Gamma |- G
    --------------
    A->B,A,Gamma |- G  (A Atomique)
 *)
let atomic_imply_bot_pattern = put_pat mmk "?1->?2"

let atomic_imply_step cls gls =
  let mvb = somatch (clause_type cls gls) atomic_imply_bot_pattern in 
  if not (is_atomic (List.assoc 1 mvb)) then
    error "atomic_imply_step"; 
  (tclTHENS (dImp cls) ([clear_clause cls;assumption])) gls

let dyck_atomic_imply_elim = compose (atomic_imply_step) in_some

(*10.
    C ->(D-> B),Gamma |- G
    -----------------------
    (C/\D)->B,Gamma |- G
 *)

let and_imply_step cls gls =
  let mvb = somatch (clause_type cls gls) imply_pattern in
  let a = List.assoc 1 mvb
  and b = List.assoc 2 mvb in
  let l =  match match_with_conjunction a with
    | Some (_,l) -> l
    | None        -> error "and_imply_step"
  in 
  (tclTHENS (cut_intro (List.fold_right mkIMP l b))
     [clear_clause cls ;
      (tclTHENS (tclTHEN (tclDO (List.length l) intro) (dImp cls))
         [assumption;
          (tclTHEN (dAnd None) assumption)])]) gls

let dyck_and_imply_elim = compose (and_imply_step) in_some

(*11.
    C->B,D->B,Gamma |-G
    --------------------
    (C\/D)->B,Gamma |- G
*)

let or_imply_step cls gls =
  let mvb = somatch (clause_type cls gls) imply_pattern in
  let a = List.assoc 1 mvb
  and b = List.assoc 2 mvb in
  let l =  match match_with_disjunction a with
    | Some (_,l) -> l
    | None        -> error "and_imply_step"
  in 
  (tclTHENS (cut_in_parallel (List.map (fun x -> (mkIMP x b)) l))
     (clear_clause cls::
      (List.map 
         (fun i -> (tclTHENS (tclTHEN intro (dImp cls)) 
                      [assumption ;
                       (tclTHEN (one_constructor i []) assumption)]))
         (interval 1 (List.length l))))) gls

let dyck_or_imply_elim = compose (or_imply_step) in_some

(*12.
B,Gamma|- G   D->B,Gamma |- C->D
----------------------------------
(C->D)->B,Gamma |- G
*)

let back_thru_2 id =
  applist(VAR id,[DOP0(Meta(new_meta()));DOP0(Meta(new_meta()))])

let back_thru_1 id =
  applist(VAR id,[DOP0(Meta(new_meta()))])

let exact_last_hyp = onLastHyp (fun h -> exact (VAR (out_some h)))

let imply_imply_bot_pattern = put_pat mmk "(?1->?2)->?3"

let imply_imply_step cls gls =
  let h0 = out_some cls in (* (C->D)->B *)
  let mvb = somatch (clause_type cls gls) imply_imply_bot_pattern in
  let c = List.assoc 1 mvb 
  and d = List.assoc 2 mvb
  and b = List.assoc 3 mvb
  in
  tclTHENS (cut_intro b)
    [clear_clause cls; (* B |- G *)
     tclTHENS (cut_intro (mkIMP (mkIMP d b) (mkIMP c d)))
       [onLastHyp
	  (fun h1opt (*(D->B)->(C->D)*) ->
	     let h1 = out_some h1opt in
             (tclTHENS (refine (back_thru_1 h0))
		[tclTHENS (tclTHEN intro (* C *) (refine (back_thru_2 h1)))
		   [tclTHENS (tclTHEN intro (* D *) (refine (back_thru_1 h0)))
		      [tclTHEN intro (* C *) assumption];
		    exact_last_hyp]]));
	(tclTHEN (clear_clause cls) (intro))
       ]
    ] gls

let dyck_imply_imply_elim = compose (imply_imply_step) in_some

(*14.
    B,Gamma |-G
    --------------------
    True->B,Gamma |- G
*)

let true_imply_step cls gls =
  let mvb = somatch (clause_type cls gls) imply_pattern in
  let a = List.assoc 1 mvb 
  and b = List.assoc 2 mvb in
  let l =  match match_with_unit_type a with
  (* match_with_unit_type retournait un constr list option avec un seul
     element dans la liste; maintenant il renvoie un constr option *)
  (*           Some (_::l) -> l *)
    | Some _ -> []
    | None        -> error "true_imply_step" 
  in 
  let h0 = out_some cls in  
  (tclTHENS (cut_intro b)
     [(clear_clause cls);
      (tclTHEN (apply(VAR h0)) (one_constructor 1 []))]) gls
  
let dyck_true_imply_elim = compose (true_imply_step) in_some

(* Chet's original algorithm 
let rec prove g =
    tclCOMPLETE
    ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tclORELSE 
     ((tryAllHyps (clauseTacThen ((comp(dyck_hypothesis) (out_some))) prove)))
     ((tryAllHyps (clauseTacThen ((comp(dyck_absurdity_elim) (out_some))) prove)))))
     ((tryAllHyps (clauseTacThen ((comp(dyck_and_elim) (out_some))) prove)))))
     ((tryAllHyps (clauseTacThen ((comp(dyck_or_elim) (out_some))) prove)))))
     ((tryAllHyps (clauseTacThen ((comp(dyck_atomic_imply_elim) (out_some))) prove)))))
     ((tryAllHyps (clauseTacThen ((comp(dyck_and_imply_elim) (out_some))) prove)))))
     ((tryAllHyps (clauseTacThen ((comp(dyck_or_imply_elim) (out_some))) prove)))))
     ((tryAllHyps (clauseTacThen ((comp(dyck_imply_imply_elim) (out_some))) prove)))))
     (((tclTHEN (dyck_and_intro) (prove))))))
     (((tclTHEN (dyck_or_introleft) (prove))))))
     (((tclTHEN (dyck_or_introright) (prove))))))
     (((tclTHEN (dyck_imply_intro) (prove)))))) g

*)

(* Cesar's code *)

let trans x = ([],Nametab.sp_of_id CCI (id_of_string x))

let flat_map f =
  let rec flat_map_f = function
    | [] -> [] 
    | x::l -> f x @ flat_map_f l
  in 
  flat_map_f

type formula =
  | FVar  of string 
  | FAnd  of formula*formula
  | FOr   of formula*formula
  | FImp  of formula*formula
  | FEqu  of formula*formula
  | FNot  of formula
  | FEq   of formula*formula*formula
  | FPred of constr (* Predicado proposicional *)
  | FFalse
  | FTrue
     (* La siguiente no puede aparecer en una formula de entrada *)
     (* Representa una formula atomica cuando aparece en un principal de una
	regla *)
  | FLis of formula list (* Lista de formulas *)
  | FAto of string       (* Formula atomica *)
  | FLisfor of string  (* Variable para una lista de formulas *)
	                    (* En el antecedente se llama GAMA, 
			       en el sucedente DELTA *)

(* Terminos en calculo lambda *)
type termino =
  | TVar of string
  | TApl of formula*formula*termino*termino
  | TFun of string*formula*termino
  | TPar of formula*formula*termino*termino 
  | TInl of formula*formula*termino 
  | TInr of formula*formula*termino
  | TFst of formula*formula*termino
  | TSnd of formula*formula*termino 
  | TCase of formula list * termino list 
  | TZ of formula * termino 
  | TExi of string
  | TRefl of formula * formula (*Reflexividad de la igualdad *) 
  | TSim  of formula * formula * formula * termino
      (*Simetria de la igualdad *)
  | TTrue
    (* Los siguientes terminos se usan solamente en las sustituciones *)
  | TSum of termino*termino (* Suma de terminos *)
  | TLis of termino list  (* Lista de terminos *) 
  | TLister of string     (* Variable para una lista de terminos *)
			     (* En el antecendete se llama Gama, 
			        en el sucedente Delta *)
  | TZero of formula    (* Milagro               *)

(* Es una formula asociada con un termino del calculo lambda, o los 
   multiconjuntos Gama y Delta *)
type formulaT = termino*formula

(* La primera componente es el antecedente, la segunda es sucedente *)
type sequente = formulaT list * formulaT list

(* Substitucion de variable por una formula *)
type subsF = (string*formula) list

(* Substitucion de variable por un lambda termino *)
type subsT = (string*termino) list

type regla = { 
  tip: string;  (* Tipo de la formula principal *)
  heu: bool;    (* Si es una regla heuristica o no *)
  ant: bool;    (* Si principal es antecedente o sucedente *)
  pri: formulaT;(* Formula principal de la regla *)
  pre: sequente list; (* Premisas de la regla *)
  res: sequente;(* Restricciones para la aplicacion de una regla*)
  def: subsT;   (* Definicion de los terminos del lado derecho *)
  sub: subsT;   (* Substitucion que se aplica al lado derecho de la
		   conclusion para obetener el lambda termino *)
  ren: string list; (* Variables que se deben renombrar *)
  vardelta:bool;    (* Si se usa la variable proposicional DELTA *) 
  ssi:bool;         (* Si la regla es reversible o no *)
  rendelta: string list } (* Renombramientos de delta *)
       (* Note que si Res = A |- B, entonces la conclusion de la regla es
          A,Gama,Pri' |- B, Pri'',Delta 
	  Si ant = true Pri'= Pri
	  Si ant =false Pri''=Pri*)

(* Substitucion Formula Termino para aplicar una regla *)
type sFT = { 
  sReg : regla ref; (*Apuntador a la regla *)
  sFor : subsF;     (*Substitucion de Formulas *)
  sGam : formulaT list;   (* Lista de formulas de Gamma *)
  sDel : formulaT list;   (* Lista de formulas de Delta *)    
  sRen : (string*subsT) list; (* Renombramientos de variables *)
  sTer : subsT;   (* Susbstitucion de terminos  *)
  sDef : subsT } (* Definicion de terminos     *) 

type subsFT = SNil | SCons of sFT

type reglaSub = RNil | RCons of (sFT*regla list*formulaT list*sequente)

(* De un arbol de demostracion *)
type nodo = { 
  seq: sequente ref; (* Sequente que se resuelve *)
  reg: regla ref;    (* Regla usada para resolver *)
  sd:  subsT;        (* Substitucion que define los lambda terminos *)
  st:  subsT }       (* Substitucion que calcula el lambda termino  *)

(* Arbol de demostracion *)  
type arbol = Nil | Cons of arbol * nodo * arbol

(* Demostracion *)
(* Si el secuente es valido Arb es un arbol de demostracion y Lisbut
   es vacio, sino Lisbut es un contexto en el cual Arb es valido *)
type demostracion = { arb : arbol; lisbut : formulaT list }

(* Definicion de excepcion para rescribir terminos *)
exception NoAplica
exception TacticFailure 

(* ------------------ Sistema de Gentzen Intuisionista -------------------*)
(* Gama,Delta son metavariables de conjuntos de reglas
   A,B son variables de formulas  *)

let gama = (TLister "Gama",FLisfor "GAMA")
let delta = (TLister "Delta",FLisfor "DELTA")
let delta' = (TLister "Delta'",FLisfor "DELTA")
let delta'' = (TLister "Delta''",FLisfor "DELTA")

let curry(a,b,c,a_0,b_0,p) = TFun(a_0,a,TFun(b_0,b,TApl(FAnd(a,b),c,p,
                                         TPar(a,b,TVar a_0,TVar b_0))))
let left(a,b,c,a_0,p) = TFun(a_0,a,TApl(FOr(a,b),c,p,TInl(a,b,TVar a_0)))
let right(a,b,c,b_0,p) = TFun(b_0,b,TApl(FOr(a,b),c,p,TInr(a,b,TVar b_0)))
let imp2(a,b,c,a_0,b_0,p) = TFun(a_0,a,TApl(FImp(b,a),c,p,TFun(b_0,b,TVar a_0)))

(* Regla inicial   *) 
(*    / A,Gama |- A,Delta *) 
let inic = {
  tip="inic";
  heu=false;
  ant=true;
  pri= TVar "#x",FAto "#A";
  pre=[];
  res=([],[TVar "#x",FVar "#A"]);
  def=["Delta",TZero(FLisfor "DELTA")];
  sub=[];
  ren=["#x"];
  vardelta = true;
  ssi = true;
  rendelta=[] }

(* Regla l_false   *) 
(*    / Gama,False |- Delta *) 
let l_false = {
  tip="false";
  heu=false;
  ant=true;
  pri= TVar "#x",FFalse;
  pre=[];
  res=([],[]);
  def=["Delta",TZ(FLisfor "DELTA",TVar "#x")];
  sub=[];
  ren=["#x"];
  vardelta = true;
  ssi = true;
  rendelta=[]}

(* Regla r_true   *) 
(*    / Gama |- True,Delta *) 
let r_true = {
  tip="true";
  heu=false;
  ant=false;
  pri= TTrue,FTrue;
  pre=[];
  res=([],[]);
  def=["Delta",TZero(FLisfor "DELTA")];
  sub=[];
  ren=[];
  vardelta = true;
  ssi = true;
  rendelta=[]}

(* Regla l_and     *)
(* A,B,Gama |- Delta / FAnd(A,B),Gama |- Delta *)
let l_and = {
  tip="l_and";
  heu=false;
  ant=true;
  pri= TVar "#xy",FAnd(FVar "#A",FVar "#B");
  pre=[[TVar "#x",FVar "#A";TVar "#y",FVar "#B";gama],[delta]];
  res=([],[]);
  def=[];
  sub=["#x",TFst(FVar "#A",FVar "#B",TVar "#xy");
       "#y",TSnd(FVar "#A",FVar "#B",TVar "#xy")];
  ren=["#x";"#y"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla r_and     *)
(* Gama |- A,Delta'  Gama |- B,Delta'' /  Gama |- A/\B,Delta *)
let r_and = {
  tip="r_and";
  heu=false;
  ant=false;
  pri= TPar(FVar "#A",FVar "#B",TVar "#x",TVar "#y"), 
  FAnd(FVar "#A",FVar "#B");
  pre=[[gama],[TVar "#x",FVar "#A";delta'];[gama],
       [TVar "#y",FVar "#B";delta'']];
  res=([],[]);
  def=["Delta",TSum(TLister "Delta'",TLister "Delta''")];
  sub=[];
  ren=["#x";"#y"];
  vardelta = true;
  ssi = true;
  rendelta=["Delta'";"Delta''"]}

(* Regla l_or     *)
(* A,Gama |- Delta'  B,Gama |- Delta'' / A\/B,Gama |- Delta *)
let l_or = {
  tip="l_or";
  heu=false;
  ant=true;
  pri= TVar "#xy",FOr(FVar "#A",FVar "#B");
  pre=[[TVar "#x",FVar "#A";gama],[delta'];
       [TVar "#y",FVar "#B";gama],[delta'']];
  res=([],[]);
  sub=[];
  def=["Delta", TCase([FVar "#A";FVar "#B";FLisfor "DELTA"],
		      [TFun("#x",FVar "#A",TLister "Delta'");
		       TFun("#y",FVar "#B",TLister "Delta''");
		       TVar "#xy"])];
  ren=["#x";"#y";"#xy"];
  vardelta = true;
  ssi = true;
  rendelta=["Delta'";"Delta''"]}

(* Regla r_or     *)
(* Gama |- A,B,Delta / Gama |- A\/B,Delta *)
let r_or = {
  tip="r_or";
  heu=false;
  ant=false;
  pri= TSum(TInl(FVar "#A",FVar "#B",TVar "#x"),
            TInr(FVar "#A",FVar "#B",TVar "#y")),
  FOr(FVar "#A",FVar "#B");
  pre=[[gama],
       [TVar "#x",FVar "#A";TVar "#y",FVar "#B";delta]];
  res=([],[]);
  sub=[];
  def=[];
  ren=["#x";"#y"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla l_imp1    *)
(* A,B,Gama |- Delta / A->B,A,Gama |- Delta (A es un atomo) *)
let l_imp1 = {
  tip="l_imp1";
  heu=false;
  ant=true;
  pri= TVar "#p",FImp(FAto "#A",FVar "#B");
  pre=[[TVar "#x",FVar "#B";gama],
       [delta]];
  res=([TVar "#a",FVar "#A"],[]);
  def=[];
  sub=["#x",TApl(FVar "#A",FVar "#B",TVar "#p",TVar "#a")];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla l_imp2   *)
(* C->(D->B),Gama |- Delta / C/\D->B,Gama |- Delta *)
let l_imp2 = {
  tip="l_imp2";
  heu=false;
  ant=true;
  pri= TVar "#p",FImp(FAnd(FVar "#C",FVar "#D"),FVar "#B");
  pre=[[TVar "#x",FImp(FVar "#C",FImp(FVar "#D",FVar "#B"));gama],
       [delta]];
  res=([],[]);
  def=[];
  sub=["#x",curry(FVar "#C",FVar "#D",FVar "#B","#c","#d",TVar "#p")];
  ren=["#x";"#c";"#d"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla l_imp3   *)
(* C->B,D->B,Gama |- Delta / C\/D->B,Gama |- Delta *)
let l_imp3 = {
  tip="l_imp3";
  heu=false;
  ant=true;
  pri= TVar "#p",FImp(FOr(FVar "#C",FVar "#D"),FVar "#B");
  pre=[[TVar "#x",FImp(FVar "#C",FVar "#B");TVar "#y",
        FImp(FVar "#D",FVar "#B");gama],
       [delta]];
  res=([],[]);
  def=[];
  sub=["#x",left(FVar "#C",FVar "#D",FVar "#B","#c",TVar "#p"); 
       "#y",right(FVar "#C",FVar "#D",FVar "#B","#d",TVar "#p")];
  ren=["#x";"#y";"#c";"#d"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla l_imp4   *)
(* D->B,Gama |- C->D,Delta   B,Gama |- Delta / (C->D)->B,Gama |- Delta *)
let l_imp4 = {
  tip="l_imp4";
  heu=false;
  ant=true;
  pri= TVar "#p",FImp(FImp(FVar "#C",FVar "#D"),FVar "#B");
  pre=[[TVar "#x",FVar "#B";gama],[delta];
       [TVar "#z",FImp(FVar "#D",FVar "#B");gama],[TVar "#y",
						   FImp(FVar "#C",FVar "#D")]];
  res=([],[]);
  def=[];
  sub=["#x",
       TApl(FImp(FVar "#C",FVar "#D"),FVar "#B",TVar "#p",
            TApl(FVar "#D",FVar "#B",
                 TFun("#z",FImp(FVar "#D",FVar "#B"),TVar "#y"),
		 imp2(FVar "#D",FVar "#C",FVar "#B","#d","#c",TVar "#p")))];
  ren=["#x";"#y";"#z";"#d";"#c"];
  vardelta = false;
  ssi = false;
  rendelta=[]}

(* Regla l_imp5   *)
(* (A->False)->B,Gama |- Delta /  Not(A)->B,Gama |- Delta *) 
let l_imp5 = {
  tip="l_imp5";
  heu=false;
  ant=true;
  pri= TVar "#x",FImp(FNot(FVar "#A"),FVar "#B");
  pre=[[TVar "#x",FImp(FImp(FVar "#A",FFalse),FVar "#B");gama],
       [delta]];
  res=([],[]);
  def=[];
  sub=[];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla l_imp6   *)
(* (C->D/\D->C)->B,Gama |- Delta  / (C<->D)->B,Gama |- Delta *) 
let l_imp6 = {
  tip="l_imp6";
  heu=false;
  ant=true;
  pri= TVar "#x",FImp(FEqu(FVar "#C",FVar "#D"),FVar "#B");
  pre=[[TVar "#x",
	FImp(FAnd(FImp(FVar "#C",FVar "#D"),
		  FImp(FVar "#D",FVar "#C")),FVar "#B");gama],[delta]];
  res=([],[]);
  def=[];
  sub=[];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla l_imp7   *)
(* B,Gama |- Delta  / True->B,Gama |- Delta *)
let l_imp7 = {
  tip="l_imp7";
  heu=false;
  ant=true;
  pri= TVar "#t",FImp(FTrue,FVar "#B");
  pre=[[TVar "#x",FVar "#B";gama],[delta]];
  res=([],[]);
  def=[];
  sub=["#x",TApl(FTrue,FVar "#B",TVar "#t",TTrue)];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla r_imp     *)
(* A,Gama |- B  / Gama |- A->B,Delta *)
let r_imp = {
  tip="r_imp";
  heu=false;
  ant=false;
  pri= TFun("#x",FVar "#A",TVar "#y"),FImp(FVar "#A",FVar "#B");
  pre=[[TVar "#x",FVar "#A";gama],[TVar "#y",FVar "#B"]];
  res=([],[]);
  def=["Delta",TZero(FLisfor "DELTA")];
  sub=[];
  ren=["#x";"#y"];
  vardelta = true;
  ssi = false;
  rendelta=[]}

(* Regla l_not     *)
(* A->False,Gama |- Delta / Not(A),Gama |- Delta *)
let l_not = {
  tip="l_not";
  heu=false;
  ant=true;
  pri= TVar "#x",FNot(FVar "#A");
  pre=[[TVar "#x",FImp(FVar "#A",FFalse);gama],[delta]];
  res=([],[]);
  def=[];
  sub=[];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla r_not     *)
(* Gama |- A->False,Delta   / Gama |- Not(A),Delta *)
let r_not = {
  tip="r_not";
  heu=false;
  ant=false;
  pri= TVar "#x",FNot(FVar "#A");
  pre=[[gama],[TVar "#x",FImp(FVar "#A",FFalse);delta]];
  res=([],[]);
  def=[];
  sub=[];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla l_equ     *)
(* A->B/\B->A,Gama |- Delta / A<->B,Gama |- Delta *)
let l_equ = {
  tip="l_equ";
  heu=false;
  ant=true;
  pri= TVar "#x",FEqu(FVar "#A",FVar "#B");
  pre=[[TVar "#x",FAnd(FImp(FVar "#A",FVar "#B"),
		       FImp(FVar "#B",FVar "#A"));gama],[delta]];
  res=([],[]);
  def=[];
  sub=[];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Regla r_equ     *)
(* Gama |- A->B/\B->A,Delta   / Gama |- A<->B,Delta *)
let r_equ = {
  tip="r_equ";
  heu=false;
  ant=false;
  pri= TVar "#x",FEqu(FVar "#A",FVar "#B");
  pre=[[gama],
       [TVar "#x",FAnd(FImp(FVar "#A",FVar "#B"),
		       FImp(FVar "#B",FVar "#A"));delta]];
  res=([],[]);
  def=[];
  sub=[];
  ren=["#x"];
  vardelta = false;
  ssi = true;
  rendelta=[]}

(* Definicion de la regla VACIA *)
let vACIA = {
  tip="vacia";
  heu=false;
  ant=false;
  pri=gama;
  pre=[];
  res=([],[]);
  def=[];
  sub=[];
  ren=[];
  vardelta = false;
  ssi = false;
  rendelta=[]}

(*---------------------- Reglas heuristicas ------------------------------*)

(* Regla simetria de igualdad *) 
(*    / a=b,Gama |- b=a,Delta *) 
let sim = {
  tip="sim";
  heu=true;
  ant=true;
  pri= TVar "#x",FEq(FVar "#A",FVar "#a",FVar "#b");
  pre=[];
  res=([],[TSim(FVar "#A",FVar "#a",FVar"#b",TVar"#x"),
           FEq(FVar "#A",FVar "#b",FVar "#a")]);
  def=["Delta",TZero(FLisfor "DELTA")];
  sub=[];
  ren=["#x";"#a";"#b"];
  vardelta = true;
  ssi = true;
  rendelta=[]}

(* Regla r_refl   *) 
(*    / Gama |- <t>a=a,Delta *) 
let r_refl = {
  tip="refl";
  heu=true;
  ant=false;
  pri= TRefl(FVar "#A",FVar "#a"),FEq(FVar "#A",FVar "#a",FVar "#a");
  pre=[];
  res=([],[]);
  def=["Delta",TZero(FLisfor "DELTA")];
  sub=[];
  ren=["#a"];
  vardelta = true;
  ssi = true;
  rendelta=[]}

let sistema = [inic;l_false;r_true;l_and;r_and;l_imp1;l_imp2;l_imp3;
	       l_imp5;l_imp6;l_imp7;l_not;r_not;l_equ;r_equ;r_imp;
               l_or;r_or;l_imp4]
			    
(*----------- Proyecciones del tipos de datos Sequente ----------------------*) 

(* Antecedente de un sequente *)
let ante (a,_)  = a

(* Sucedente de un sequente *)
let suce (_,s) = s

(*----------- Constructores de los  tipos de datos  ----------------------*) 

(* Simplifica una substitucion es decir elemina las substituciones 
   inutiles *)
let rec simple = function
  | [] -> []
  | ((x,_) as a)::z -> 
      if String.get x 0 = '#' then simple z else a::simple z

(* Construye un node de demostracion *)
let consd a l = {arb=a;lisbut=l}

(* Construye un nodo de un arbol *)
let consa s r sd st = {seq = ref s;reg = ref r;sd = simple sd; 
                       st= simple st}  

(* Construye un nodo de sustitucion *)
let conss r sf sg sd ren sdef ster =
  SCons({sReg=ref r;sFor=sf;sGam=sg;sDel=sd; 
         sRen=ren;sDef=sdef;sTer=ster})

(*----------------------- Aplicacion de Reglas ------------------------------*)

(* Buscar un nombre de variable en una sustitucion, retorna la lista
   que contiene la formula que la variable sustituye *)
let rec busque n = function
  | [] -> []
  | (x,f)::y -> if x=n then [f] else busque n y 

(* Aplicar una substitucion a una formula, retorna otra formula *)
let rec apl_f s = function  
  | (FVar y) as x -> (match busque y s with 
			| [] -> x
			| a::_ -> a ) 
  | (FLisfor y) as x -> (match busque y s with
			   | [] -> x
			   | a::_ -> a)
  | FAnd (a,b)   -> FAnd(apl_f s a, apl_f s b) 
  | FOr  (a,b)   -> FOr(apl_f s a, apl_f s b) 
  | FImp (a,b)   -> FImp(apl_f s a, apl_f s b) 
  | FEqu (a,b)   -> FEqu(apl_f s a, apl_f s b) 
  | FEq  (a,b,c) -> FEq(apl_f s a, apl_f s b,apl_f s c) 
  | FNot a -> FNot(apl_f s a) 
  | x -> x

(* Aplicar una sustitucion a una lista de formulas *)
let apl_lf s l = List.map (apl_f s) l 

(* Encuentra un unificador de primer orden de dos formulas proposicionales,
   retorna la pareja (e,u), donde e indica exito o fracaso
   y u es el unificador principal (si no existe es [] vacia ) *)
let rec unif_f = function
  | FAnd(a,b),FAnd(x,y) -> unif_lf([a;b],[x;y]) 
  | FOr(a,b),FOr(x,y)   -> unif_lf([a;b],[x;y]) 
  | FImp(a,b),FImp(x,y) -> unif_lf([a;b],[x;y])
  | FEqu(a,b),FEqu(x,y) -> unif_lf([a;b],[x;y])
  | FEq(a,b,c),FEq(x,y,z) -> unif_lf([a;b;c],[x;y;z])
  | FVar(a),x -> (true,[a,x]) 
  | FAto(a),(FPred(_) as x) -> (true,[a,x])
  | FAto(a),(FEq(_) as x)   -> (true,[a,x])
  | FPred(a),FPred(x)   -> (eq_constr a x,[])
  | FNot(a),FNot(x)     -> unif_f(a,x)
  | FFalse,FFalse       -> (true,[])
  | FTrue,FTrue         -> (true,[])
  | _                   -> (false,[]) 

and unif_lf = function
  | ([],[]) -> (true,[])
  | (x::y,a::b) -> 
      let (e,u) = unif_f (x,a) in
      if e then 
	let (e1,u1) = unif_lf (apl_lf u y,b) in
	if e1 then (true,u@u1) else (false,[])
      else 
	(false,[]) 
  | _ -> (false,[])

(* Aplicar una substitucion a un lamda termino, retorna otro lambda termino *)
let rec apl_t st sf = function
  | (TVar y) as x     -> (match busque y st with
		            | []   -> x 
                            | a::_ -> a ) 
  | (TLister y) as x  -> (match busque y st with
		            | []   -> x 
                            | a::_ -> a ) 
  | TApl(f1,f2,t1,t2) -> TApl (apl_f sf f1,apl_f sf f2,
                               apl_t st sf t1,apl_t st sf t2) 
  | TFun(x,f,y)       -> (match busque x st with
			    | []   -> TFun(x,apl_f sf f,apl_t st sf y)
                            | [TVar n] -> TFun(n,apl_f sf f,apl_t st sf y)
			    | _  -> raise TacticFailure)
  | TCase(lf,lt)    -> TCase(List.map (apl_f sf) lf,List.map (apl_t st sf) lt) 
  | TPar(f1,f2,t1,t2) -> TPar(apl_f sf f1,apl_f sf f2,
			      apl_t st sf t1,apl_t st sf t2)
  | TInl(f1,f2,t)     -> TInl(apl_f sf f1,apl_f sf f2,apl_t st sf t)
  | TInr(f1,f2,t)     -> TInr(apl_f sf f1,apl_f sf f2,apl_t st sf t)
  | TFst(f1,f2,t)     -> TFst(apl_f sf f1,apl_f sf f2,apl_t st sf t)
  | TSnd(f1,f2,t)     -> TSnd(apl_f sf f1,apl_f sf f2,apl_t st sf t)
  | TRefl(f1,f2)      -> TRefl(apl_f sf f1,apl_f sf f2)
  | TSim(f1,f2,f3,t)  -> TSim(apl_f sf f1,apl_f sf f2,
                              apl_f sf f3,apl_t st sf t)
  | TLis lt           -> TLis (List.map (apl_t st sf) lt) 
  | TSum(t1,t2)       -> TSum (apl_t st sf t1,apl_t st sf t2) 
  | TZ(f,t)           -> TZ(apl_f sf f,apl_t st sf t)
  | (TExi y) as x     -> (match busque y st with
		            | []   -> x 
                            | a::_ -> a ) 
  | TZero f           -> TZero(apl_f sf f)
  | t                 -> t 

(* Aplicar substitucion gama delta y una substitucion de terminos lambda 
   a una lista de formulasT, retorna una lista de formulasT *)
let rec apl_lft (s,gama_0,delta_0) st rendelta = 
  (* Aplicar una substitucion gama delta y una substitucion de terminos a una 
     formulaT, retorna una lista de formulasT *)
  let apl_fm = function
    | (_,FLisfor "GAMA") -> gama_0
    | (TLister x,FLisfor "DELTA") ->
	(match busque x rendelta with 
	   | [] -> delta_0 
	   | a::_ -> apl_lft ([],[],[]) a [] delta_0) 
    | (_,FLisfor "DELTA") -> delta_0
    | (t,f) -> [apl_t st [] t,apl_f s f] 
  in
  flat_map apl_fm 

(* Aplicar substitucion gama delta y una substitucion de terminos lambda a un 
   sequente, retorna un nuevo sequente*)
let apl sf st rendelta = function 
    (l1,l2) -> (apl_lft sf st rendelta l1,apl_lft sf st rendelta l2)  

(* Aplicar la regla r, dada una substitucion. 
   Retorna una lista de sequentes *) 
let aplr_s subs = List.map (apl (subs.sFor,subs.sGam,subs.sDel)
                              subs.sDef subs.sRen) !(subs.sReg).pre 
		    
(* Componer dos substituciones de lambda terminos. Aplica la primera
   sobre la segunda *)
let rec comp_st st = function 
  | [] -> st 
  | (x,y)::z -> (x,apl_t st [] y)::comp_st st z

(* Renombrar las variables izquierdas de una sustitucion *) 
let rec ren_izq ren = function 
  | [] -> [] 
  | ((x,y) as a)::z -> match busque x ren with
      | [TVar a] ->  (a,y)::ren_izq ren z 
      | _ -> a::ren_izq ren z

(* Indica si dos formulas son iguales *)
let iguales_f f1 f2 =
  let (e,u) = unif_f(f1,f2) in
  e & u = []

(*------------------- Unificador para lambda terminos --------------------*)

(* Encuentra un unificador de primer orden de dos lambda terminos,
   retorna la pareja (e,u), donde e indica exito o fracaso
   y u es el unificador principal (si no existe es [] vacia ).
   TPara los terminos que contienen formulas recibe el unificador de
   ellas *)
let rec unif_t sf = function
  | (TVar x,((TVar y) as y_0))   -> 
      if (x = y) then (true,[]) else (true,[x,apl_t [] sf y_0])
  | (TVar x, y)                  -> (true,[x,apl_t [] sf y])
  | TApl(f,ff,t,tt),TApl(f1,ff1,t1,tt1) -> 
      unif_lft sf [f;ff][f1;ff1][t;tt][t1;tt1]
  | TZ(f,t), TZ(f1,t1)           -> unif_lft sf [f][f1][t][t1]  
  | (TExi x,((TExi y) as y_0))   -> 
      if (x = y) then (true,[]) else (true,[x,apl_t [] sf y_0])
  | TZero f, TZero f1            -> unif_lft sf [f][f1][][] 
  | TTrue,TTrue                  -> (true,[])
  | TFun(x,f,t),TFun(a,f1,t1)    -> unif_lft sf [f][f1][t][t1] 
  | TPar(f,ff,t,tt),TPar(f1,ff1,t1,tt1) -> 
      unif_lft sf [f;ff][f1;ff1] [t;tt][t1;tt1]
  | TInl(f,ff,t),TInl(f1,ff1,t1) -> unif_lft sf [f;ff][f1;ff1][t][t1]  
  | TInr(f,ff,t),TInr(f1,ff1,t1) -> unif_lft sf [f;ff][f1;ff1][t][t1] 
  | TFst(f,ff,t),TFst(f1,ff1,t1) -> unif_lft sf [f;ff][f1;ff1][t][t1]
  | TSnd(f,ff,t),TSnd(f1,ff1,t1) -> unif_lft sf [f;ff][f1;ff1][t][t1] 
  | TRefl(f,ff),TRefl(f1,ff1)    -> unif_lft sf [f;ff][f1;ff1][][] 
  | TSim(f1,f2,f3,t),TSim(f1',f2',f3',t') ->
      unif_lft sf [f1;f2;f3] [f1';f2';f3'][t][t'] 
  | _                            -> (false,[])

and iguales_lf sf = function
  | ([],[]) -> true
  | (x::y,a::b) -> 
      if iguales_f (apl_f sf x) (apl_f sf a) then
	iguales_lf sf (y,b)
      else 
	false 
  | _ -> false 

and unif_lt sf = function
  | ([],[]) -> (true,[])
  | (x::y,a::b) -> 
      let (e,u) = unif_t sf (x,a) in
      if e then 
	let (e1,u1) = unif_lt sf (y,b) in
	if e1 then (true,u@u1)
        else (false,[])
      else 
	(false,[]) 
  | _ -> (false,[]) 

and unif_lft sf lf lf1 lt lt1 =
  if iguales_lf sf (lf,lf1) then 
    unif_lt sf (lt,lt1)
  else 
    (false,[]) 

(* Indica si dos terminos son iguales *)
let iguales_t t1 t2 =
  let (e,u) = unif_t [] (t1,t2) in
  e & u = []

(* Indica si dos formulas son iguales. Retorna una pareja con el exito
   y un unificador de los dos lambda terminos *)
let iguales_unif uf tr ts fr fs =
  if iguales_f fr fs then
    let (e,ut) = unif_t uf (ts,tr) in
    if e then
      (true,ut)
    else
      raise TacticFailure 
  else 
    (false,[])

(* Crear una nueva variable *) 
let hipvar = ref ((id_of_string "#")::[])

let genvar () = 
  let id = next_ident_away 
             (id_of_string "H") 
             !hipvar in
  (hipvar := id::(!hipvar); string_of_id id)
  
(* Lista de terminos de una substitucion *)
let listerm = List.map snd 

(* Lista de variables de una lista de formulasS *)
let rec lisvar = function 
  | [] -> []
  | (TVar x,_)::y -> x::lisvar y
  | (TExi x,_)::y -> x::lisvar y
  | _::y -> lisvar y

(* Lista de formulas de una lista de formulasS *)
let rec lisfor = function 
  | [] -> []
  | (TVar _,x)::y -> x::lisfor y
  | (TExi _,x)::y -> x::lisfor y
  | _::y -> lisfor y

(* Recibe una lista de variables, retorna un renombramiento de ellas *)
let renombra = List.map (function x -> (x,TVar(genvar())))

(* Obtiene un renombramiento de todas las metavariables delta *)
let renombradelta s rend= 
  let l = lisvar (suce s) in
  List.map (function x -> (x,renombra l)) rend

(* Obtiene una substitucion de las metavariables delta, por lista de
   terminos *)
let rec subsdelta = function
  | [] -> []
  | (x,y)::y_0 -> match listerm y with
      | [] -> [] 
      | [a] -> (x,a)::subsdelta y_0
      | a -> (x,TLis a)::subsdelta y_0

(* Indica si una formula pertenece a una lista de formulasT.
   Retorna una pareja con el exito y una unificacion de los lambda terminos *)
let rec pertenece uf ant tr fr = function 
  | [] -> (false,[])
  | (TLister _,_)::y -> pertenece uf ant tr fr y 
  | (ts,fs)::y -> 
      let (e,ut) = 
	if ant then
	  iguales_unif uf ts tr fr fs 
	else
	  iguales_unif uf tr ts fr fs 
      in
      if e then 
	(true,ut)
      else 
	pertenece uf ant tr fr y

(* Indica si la primera lista de formulasT contiene la segunda.
   Retorna una pareja con el exito y una unificacion de los lambda terminos *)
let rec contiene uf ant l = function 
  | [] -> (true,[])
  | (TLister _,_)::y -> contiene uf ant l y 
  | (tr,fr)::y -> 
      let (e1,s1) = pertenece uf ant tr fr l in
      if e1 then 
	let (e2,s2) = contiene uf ant l y in
	if e2 then
	  (true,s1@s2)
        else
	  (false,[])
      else 
	(false,[]) 

(* Decide si un secuente cumple con las restricciones de aplicacion de una
   regla. Recibe el unificador de la regla con la restriccion. Retorna una
   pareja con el exito y las unificaciones de lambda terminos del antecedente
   y el sucedente del secuente *)
let cumple uf res = function (seql,seqr) -> 
  let (resl,resr) = apl (uf,[],[]) [] [] res  in
  let (e1,s1) = contiene uf true seql resl in 
  if e1 then
    let (e2,s2) = contiene uf false seqr resr in
    if e2 then
      (true,s1,s2)
    else
      (false,[],[])
  else
    (false,[],[])

(* Compone una substitucion de formulas con una substitucion de terminos *)
let rec comp_sfst uf = function
  | [] -> []
  | (x,y)::z -> (x,apl_t [] uf y)::comp_sfst uf z

(* Crea una substitucion para las variables de un lambda termino, basado
   en la regla que aplica *)
let cree_sub s uf ter t ul ur r =
  let lv =  
    if r.vardelta then ["DELTA",FLis(lisfor (suce s))] else [] 
  in      
  let rendelta = renombradelta s r.rendelta in
  let ren = (renombra r.ren) @ (subsdelta rendelta) in
  let sd0 = 
    if r.ant then 
      ur (* Calcular definicion basica *) 
    else 
      match unif_t uf (t,ter) with
        | (false,_) -> raise(TacticFailure)
	| (_,u)     -> ur@u 
  in
  let sd1 = comp_st r.def sd0 in
  let sd2 = comp_sfst (uf@lv) sd1 in (*Susbstituir var. proposicionales *)
  let sd  = comp_st ren sd2 in (* Componer con un renombramiento *) 
  let st0 = 
    if r.ant then    (* Calcular sustitucion basica *)
      match unif_t uf (ter,t) with
        | (false,_) -> raise(TacticFailure)
        | (_,u)     -> ul@u  
    else 
      ul
  in
  let st1 = comp_st st0 r.sub in
  let st2 = comp_sfst (uf@lv) st1 in (*Susbstituir var. proposicionales *)
  let st3 = ren_izq ren st2 in (* Componer con un renombramiento *) 
  let st = comp_st ren st3 in
  (sd,st,rendelta)

(* Decide se una regla dada es aplicable sobre un termino (tf)
   de un secuente y un lado de reduccion o. Retorna la sustitucion
   apropiada para la regla o SNil si no existe *)

let rec aplicable s lf tf o = function
    ({ant=ant;pri=ter,pri;res=res}) as r ->
      if o<>ant then 
	SNil
      else
 	(match tf with 
	   | (TLister _,_) -> SNil
	   | (t,f) ->
               let (ef,uf) = unif_f(pri,f) in
	       if ef then
		 let (et,ul,ur) = cumple uf res s in 
		 if et then
		   let (gam,del) = if ant then (lf,suce s) 
		   else (ante s,lf) in
                   let (sd,st,rn) = cree_sub s uf ter t ul ur r in 
                   conss r uf gam del rn sd st  
                 else SNil
               else SNil)

(* Dado una regla, retorna una posicion donde la regla sea aplicable. RNil
   si no existe *)
let rec escoja_termino r s o rseq lacum = function
  | [] -> 
      if o=0 then
	escoja_termino r s 2 [] lacum rseq
      else if o=1 then
        escoja_termino r s 2 [] [] rseq
      else 
	RNil
  | t::y -> 
      let oo = if o=0 then 1 else o in
      (match aplicable s (lacum@y) t (oo=1) r with
         | SNil -> escoja_termino r s oo rseq (lacum@[t]) y
         | SCons(s) -> 
             if oo=1 then RCons(s,[],lacum,(y,rseq))
             else RCons(s,[],lacum,([],y)))

(* Dado un secuente y un sistema de reglas
   retorna una sustitucion apropiada para la regla, o RNil si no existe *)
let rec escoja_regla s (lrseq,lac) = function  
  | []   -> RNil 
  | (r::y) as lreg ->
      (match escoja_termino r s 0 (suce lrseq) lac (ante lrseq) with
         | RNil -> escoja_regla s (s,[]) y
         | RCons(subs,_,lanew,lrnew) -> RCons(subs,lreg,lanew,lrnew))

(* Si una formula proposicional existe en una lista de formulas *)
let rec existeprop f = function
  | [] -> false
  | x::y -> if iguales_f f x then true else existeprop f y

(* Buscar una formula proposicional en una lista de formulasT,
   retorna el termino o TZero si no la encuentra *)
let rec busqueprop f = function
  | [] -> TZero(FFalse)
  | (tt,ff)::y -> if iguales_f f ff then tt else busqueprop f y

(* Crear un termino como aplicaciones sucesivas del subobjetivo sobre las
   hipotesis *)
let rec ter_subobjetivo lisprop subobj = function
  | [] -> (fst subobj)
  | (x,f)::y ->
      if existeprop f lisprop then 
        ter_subobjetivo lisprop subobj y 
      else 
        (match snd(subobj) with
           | FImp(a,b) -> ter_subobjetivo (f::lisprop)
		 (TApl(a,b,fst(subobj),x),b) y
           | _ -> TZero(FFalse))

(* Convierte la lista del succedente en una disyuncion *)
let rec disyuncion = function
  | []   -> FFalse
  | [a]  -> a
  | x::y -> FOr(x,disyuncion y)

(* Convierte la lista del antecedente en una implicacion *)
let rec implicacion dis vp = function 
  | [] -> dis
  | x::y -> 
      if (existeprop x vp) then 
	implicacion dis vp y
      else 
	FImp(x,implicacion dis vp y)

(* Lista de proposiciones de un secuente sin repetidos *)
let rec it_propos lisacum = function
  | [] -> lisacum
  | (_,f)::y -> 
      if (existeprop f lisacum) then 
	it_propos lisacum y  
      else 
	it_propos (lisacum@[f]) y

let proposiciones = it_propos []

(* Generar una subobjetivo de la demostracion de tal manera que 
   la validez del sequente original sea equivalente a la validez del
   subobjetivo *)
let subobjetivo s vp = 
  let dis = disyuncion (proposiciones (suce s)) in
  let ter = TExi(genvar()) in
  (ter,implicacion dis vp (proposiciones (ante s))),dis

(* Crea una substitucion que supone un subobjetivo demostrado *)
let rec termino_caso fapp f = function
  | FOr(a,b) ->
      let id1 = genvar() in
      let t1 = TVar(id1) in
      let id2 = genvar() in
      let t2 = TVar(id2) in
      if iguales_f a f then
        TCase([a;b;f],[TFun(id1,a,t1);TFun(id2,b,TZero(f));fapp])
      else
        TCase([a;b;f],[TFun(id1,a,TZero(f));TFun(id2,b,termino_caso t2 f b);
                       fapp])
  | _ -> fapp

let rec it_subs_subobj subs sec fapp tip = function 
  | [] -> subs
  | ((TVar x,f) as a)::y -> 
      let t = busqueprop f sec in
      if t <> TZero(FFalse) then 
        it_subs_subobj ((x,apl_t subs [] t)::subs) sec fapp tip y
      else 
        it_subs_subobj ((x,termino_caso fapp f tip)::subs) (a::sec) 
          fapp tip y
  | _ -> assert false

let subs_subobj fapp tip s = it_subs_subobj [] [] fapp tip s

let rec esta_en_case l = function
  | TApl(_,_,t1,t2) ->
      (esta_en_case l t1) or (esta_en_case l t2)
  | TFun(_,_,t) -> 
      esta_en_case l t
  | TPar(_,_,t1,t2) -> 
      (esta_en_case l t1) or (esta_en_case l t2)
  | TInl(_,_,t) -> 
      esta_en_case l t
  | TInr(_,_,t) -> 
      esta_en_case l t
  | TFst(_,_,t) -> 
      esta_en_case l t
  | TSnd(_,_,t) -> 
      esta_en_case l t
  | TZ(_,t) -> 
      esta_en_case l t
  | TSum(t1,t2) -> 
      (esta_en_case l t1) or (esta_en_case l t2)
  | TCase([f1;f2;f3],[t1;t2;t3]) ->
      (match l with
         | [ff1;ff2;ff3] ->
             if (iguales_f f1 ff1) & (iguales_f f2 ff2) & 
	       (iguales_f f3 ff3) then
		 true 
             else
               (esta_en_case l t1) or (esta_en_case l t2)
	 | _ -> assert false)
  | _ -> false

let rec busque_termino t = function
  | [] -> (false,"",false)
  | (x,v,o)::y -> if iguales_t t x then (true,v,o) else busque_termino t y 

(* Sistema de reglas para simplificar terminos *)
let rec sistreg lcase = function
  | TApl(_,_,TFun (x,_,t),t1)  -> apl_t [x,t1] [] t
  | TFst(_,_,TPar(_,_,t,_)) -> t
  | TSnd(_,_,TPar(_,_,_,t)) -> t
  (* Simplificacion con TZero *)
  | TApl(_,f,TZero _,t) -> TZero f
  | TApl(_,f,t,TZero _) -> TZero f
  | TFun(x,f1,TZero f2) -> TZero (FImp(f1,f2))
  | TPar(f1,f2,TZero _,t2) -> TZero (FAnd(f1,f2)) 
  | TPar(f1,f2,t1,TZero _) -> TZero (FAnd(f1,f2)) 
  | TInl(f1,f2,TZero _) -> TZero (FOr(f1,f2))
  | TInr(f1,f2,TZero _) -> TZero (FOr(f1,f2))
  | TFst(f1,f2,TZero _) -> TZero f1
  | TSnd(f1,f2,TZero _) -> TZero f2
  | TZ(f,TZero _) -> TZero f
  | TSum(TZero _,t) -> t
  | TSum(t,TZero _) -> t
  | TCase([_;_;f],[_;_;TZero _]) -> TZero f
  | TSum(TFun(v1,ff1,t1),TFun(v2,ff2,t2)) ->
      TFun(v1,ff1,TSum(t1,apl_t [v2,(TVar v1)][] t2)) 
  (* Simplificacion del case *)
  | TApl(f1,f2,TCase([a;b;FImp(c,d)],[TFun(v1,ff1,t1);
                                      TFun(v2,ff2,t2);t3]),t) ->
      TCase([a;b;f2],[TFun(v1,ff1,TApl(c,d,t1,t));
                      TFun(v2,ff2,TApl(c,d,t2,t));t3])
  | TApl(f1,f2,t,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3])) ->
      TCase([a;b;f2],[TFun(v1,ff1,TApl(f1,f2,t,t1));
                      TFun(v2,ff2,TApl(f1,f2,t,t2));t3])
  | TPar(f1,f2,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3]),t) ->
      TCase([a;b;FAnd(f1,f2)],[TFun(v1,ff1,TPar(f1,f2,t1,t));
                               TFun(v2,ff2,TPar(f1,f2,t2,t));t3])
  | TPar(f1,f2,t,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3])) ->
      TCase([a;b;FAnd(f1,f2)],[TFun(v1,ff1,TPar(f1,f2,t,t1));
                               TFun(v2,ff2,TPar(f1,f2,t,t2));t3])
  | TInl(f1,f2,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3])) ->
      TCase([a;b;FOr(f1,f2)],[TFun(v1,ff1,TInl(f1,f2,t1));
                              TFun(v2,ff2,TInl(f1,f2,t2));t3])
  | TInr(f1,f2,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3])) ->
      TCase([a;b;FOr(f1,f2)],[TFun(v1,ff1,TInr(f1,f2,t1));
                              TFun(v2,ff2,TInr(f1,f2,t2));t3])
  | TFst(f1,f2,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3])) ->
      TCase([a;b;f1],[TFun(v1,ff1,TFst(f1,f2,t1));
                      TFun(v2,ff2,TFst(f1,f2,t2));t3])
  | TSnd(f1,f2,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3])) ->
      TCase([a;b;f2],[TFun(v1,ff1,TSnd(f1,f2,t1));
                      TFun(v2,ff2,TSnd(f1,f2,t2));t3])
  | TZ(f,TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3])) ->
      TCase([a;b;f],[TFun(v1,ff1,TZ(f,t1));
                     TFun(v2,ff2,TZ(f,t2));t3])
  | TSum((TCase([a;b;c],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3]) as tC1),
         (TCase([a';b';c'],
                [TFun(v1',ff1',t1');TFun(v2',ff2',t2');t3']) as tC2)) ->
      if (iguales_f a a') & (iguales_f b b') then
        TCase([a;b;c],[TFun(v1,ff1,TSum(t1,apl_t [v1',(TVar v1)] [] t1'));
                       TFun(v2,ff2,TSum(t2,apl_t [v2',(TVar v2)] [] t2'));
                       TSum(t3,t3')])
      else if (esta_en_case [a;b;c] t1') or (esta_en_case [a;b;c] t2') then
        TCase([a';b';c'],[TFun(v1',ff1',TSum(t1',tC1));
                          TFun(v2',ff2',TSum(t2',tC1));t3'])
      else
        TCase([a;b;c],[TFun(v1,ff1,TSum(t1,tC2));TFun(v2,ff2,TSum(t2,tC2));t3])
  | TCase([_;_;f],[TFun(_,_,TZero _);TFun(_,_,TZero _);_]) -> TZero(f)
  | TCase([a;b;f],[TFun(v1,f1,t1) as tt1;TFun(v2,f2,t2) as tt2;t]) -> 
      if iguales_t t1 t2 then t2
      else 
        let (exi,var,ori) = busque_termino t lcase in
        if exi then
          if ori then apl_t [v1,TVar var][] t1
          else apl_t [v1, TVar var] [] t2
        else raise(NoAplica)
  | TSum(t1,t2)-> 
      if (iguales_t t1 t2) then t1
      else raise (NoAplica)
  | TPar(_,_,TFst(_,_,t1),TSnd(_,_,t2)) -> 
      if iguales_t t1 t2 then
        t1
      else raise(NoAplica)
  | _ -> raise(NoAplica)
  
(* Aplicacion de una regla sobre un termino, si no pudo aplicar retorna
   NoAplica. Estrategia mas izquierdo, menos profundo *)

let pr l = List.hd l

let sn l = List.hd(List.tl l)

let rec it_apl_listsistr lcase lacum siapl = function
  | [] -> (lacum,siapl)
  | x::y -> 
      let (xp,exi) = 
	try (apl_sistr lcase x,true) with NoAplica -> (x,false) 
      in
      it_apl_listsistr lcase (lacum@[xp]) (exi or siapl) y

and apl_listsistr lcase l = it_apl_listsistr lcase [] false l
			      
and apl_sistr_try lcase x =
  try (apl_sistr lcase x,true) with NoAplica -> (x,false)

and apl_sistr lcase a =
  try 
    sistreg lcase a 
  with NoAplica -> 
    (match a with
       | TApl(f1,f2,t1,t2) ->
           let (lt,exi) = apl_listsistr lcase [t1;t2] in
           if exi then TApl(f1,f2,pr lt,sn lt)
           else raise(NoAplica)
       | TFun(x,f,t) -> 
           let (lt,exi) = apl_listsistr lcase [t] in
           if exi then TFun(x,f,pr lt)
           else raise(NoAplica)
       | TPar(f1,f2,t1,t2) -> 
           let (lt,exi) = apl_listsistr lcase [t1;t2] in
           if exi then TPar(f1,f2,pr lt,sn lt)
           else raise(NoAplica)
       | TInl(f1,f2,t) -> 
           let (lt,exi) = apl_listsistr lcase [t] in
           if exi then TInl(f1,f2,pr lt)
           else raise(NoAplica)
       | TInr(f1,f2,t) -> 
           let (lt,exi) = apl_listsistr lcase [t] in
           if exi then TInr(f1,f2,pr lt)
           else raise(NoAplica)
       | TFst(f1,f2,t) -> 
           let (lt,exi) = apl_listsistr lcase [t] in
           if exi then TFst(f1,f2,pr lt)
           else raise(NoAplica)
       | TSnd(f1,f2,t) -> 
           let (lt,exi) = apl_listsistr lcase [t] in
           if exi then TSnd(f1,f2,pr lt)
           else raise(NoAplica)
       | TZ(f,t) -> 
           let (lt,exi) = apl_listsistr lcase [t] in
           if exi then TZ(f,pr lt)
           else raise(NoAplica)
       | TSum(t1,t2) -> 
           let (lt,exi) = apl_listsistr lcase [t1;t2] in
           if exi then TSum(pr lt,sn lt)
           else raise(NoAplica)
       | TCase([f1;f2;f3],[TFun(v1,ff1,t1);TFun(v2,ff2,t2);t3]) ->
           let (t1',exi1) = apl_sistr_try ((t3,v1,true)::lcase) t1 in
           let (t2',exi2) = apl_sistr_try ((t3,v2,false)::lcase) t2 in
           let (t3',exi3) = apl_sistr_try lcase t3 in
           if (exi1 or exi2 or exi3) then 
             TCase([f1;f2;f3],[TFun(v1,ff1,t1');
                               TFun(v2,ff2,t2');t3'])
           else raise(NoAplica)
       | _ -> raise(NoAplica))

(* Indica si hay un zero en el termino *)
let rec tiene_zero = function
  | TApl(_,_,t,t1)  -> tiene_zero(t) or tiene_zero(t1)
  | TFun(_,_,t)     -> tiene_zero(t)  
  | TPar(_,_,t,t1)  -> tiene_zero(t) or tiene_zero(t1)
  | TInl(_,_,t)     -> tiene_zero(t)  
  | TInr(_,_,t)     -> tiene_zero(t)  
  | TFst(_,_,t)     -> tiene_zero(t)  
  | TSnd(_,_,t)     -> tiene_zero(t)  
  | TCase(_,[t;t1;t2]) -> tiene_zero (t) or tiene_zero (t1) or 
      tiene_zero(t2)    
  | TZ(_,t)         -> tiene_zero(t)
  | TZero(f)        -> true
  | a               -> false

(* Elemento de la posicion p de una lista *) 
let rec lis_pos p = function
  | [] -> raise(TacticFailure)
  | x::y -> if (p=0) then x else lis_pos (p-1) y

(* Genera una copia de una formula con reemplazo de los terminos de tipo
   FLis por las formulas que aparecen en la posicion p'esima de las
   listas respectivas *) 
let rec copia_f p = function
  | FAnd(a,b) ->  FAnd(copia_f p a,copia_f p b) 
  | FEqu(a,b) ->  FEqu(copia_f p a,copia_f p b)
  | FOr(a,b)  ->  FOr(copia_f p a,copia_f p b) 
  | FImp(a,b) ->  FImp(copia_f p a,copia_f p b) 
  | FNot(a)   ->  FNot(copia_f p a)  
  | FLis lf  ->  lis_pos p lf
  | a        ->  a

(* Genera una copia de un termino con reemplazo de los terminos de tipo
   Lista por los terminos que aparecen en la posicion p'esima de las listas
   respectivas *)
let rec copia_t sinplus p = function
  | TApl(f,f1,t,t1)  -> TApl(copia_f p f,copia_f p f1,
                             copia_t sinplus p t,copia_t sinplus p t1)
  | TFun(x,f,t) -> TFun(x,copia_f p f,copia_t sinplus p t)  
  | TPar(f,f1,t,t1) -> TPar(copia_f p f,copia_f p f1,
                            copia_t sinplus p t,copia_t sinplus p t1) 
  | TInl(f,f1,t)  -> TInl(copia_f p f,copia_f p f1,copia_t sinplus p t)  
  | TInr(f,f1,t)  -> TInr(copia_f p f,copia_f p f1,copia_t sinplus p t) 
  | TFst(f,f1,t)  -> TFst(copia_f p f,copia_f p f1,copia_t sinplus p t) 
  | TSnd(f,f1,t)  -> TSnd(copia_f p f,copia_f p f1,copia_t sinplus p t) 
  | TLis lt       -> lis_pos p lt 
  | TSum(t,t1)    -> let s = copia_t sinplus p t in
                     let s1 = copia_t sinplus p t1 in
                     if sinplus then
                       if tiene_zero s then s1
                       else s
                     else TSum(s,s1)
  | TCase(lf,lt)  -> 
      TCase(List.map (copia_f p) lf,List.map (copia_t sinplus p) lt) 
  | TZ(f,t)       -> TZ(copia_f p f,copia_t sinplus p t)
  | TZero(f)      -> TZero(copia_f p f)
  | a             -> a
	
(* Reescribe un lambda termino con constructores TZero y TSum a un lambda
   termino *)
let rec normal t =
  try normal(apl_sistr [] t) with NoAplica -> copia_t true 0 t
 
(*-------------------- Procedimiento de decision  --------------------------*)

(* Indica que no debe buscar mas en el arbol *)
let no_back rev = function
    {arb=a;lisbut=l} -> (a <> Nil) & (l=[] or rev)       
		       
(* Funcion que dice si un sequente es demostrable o no. Retorna 
   un arbol de demostracion del sequente, o vacio. *)
let rec naive intu vp =  function 
    (l,r) as s -> naive_s s intu (s,[]) vp sistema

(* Dado un secuente s y un subsecuente (en el cual busca una formula
   para aplicarle una regla), encuentra un elemento de demostracion. 
   Si intu es true genera subojetivos equivalentes al original en caso 
   de no encontrar la demostracion. Si es false, retorna el arbol Vacio*)

and naive_s s intu seq_acum vp listareg =
  (match escoja_regla s seq_acum listareg with
     | RNil -> 
         if intu then 
           let obj = subobjetivo s vp in
           let fapp = ter_subobjetivo vp (fst obj) (ante s) in 
           let subs_sub = subs_subobj fapp (snd obj) (suce s) in
	   consd (Cons(Nil,consa s vACIA subs_sub [],Nil)) 
             [fst obj]
         else consd Nil []
     | RCons(subs,lreg,lanew,lrnew) ->
         let reversible = !(subs.sReg).ssi or subs.sDel = [] in
	 ( match aplr_s subs with 
             | []  -> 
                 consd(Cons(Nil,
                            consa s !(subs.sReg) subs.sDef subs.sTer,
                            Nil)) []
             | [a] -> 
                 let {arb=a1;lisbut=l1} as al = (naive intu vp a) in
                 if no_back reversible al then
                   consd (Cons(a1,
                               consa s !(subs.sReg) subs.sDef subs.sTer,
                               Nil)) l1
                 else if (not (reversible)) then 
		   naive_s s intu (lrnew,lanew) vp lreg
                 else  
		   consd Nil []
             | a::(b::_) ->  
                 let {arb=a1;lisbut=l1} as al1 = naive intu vp a in
                 let {arb=a2;lisbut=l2} as al2 = naive intu vp b in
                 if (no_back reversible al1) & (no_back reversible al2) then
                   consd (Cons(a1,
                               consa s !(subs.sReg) subs.sDef subs.sTer,
                               a2)) (l1@l2) 
                 else if (not (reversible)) then 
		   naive_s s intu (lrnew,lanew) vp lreg
                 else 
		   consd Nil []))

(* Crea nuevas substituciones para cada variable del sucedente *)
let rec nuevas_subs t p = function 
  | [] -> [] 
  | x::y -> (x,copia_t false p t) :: nuevas_subs t (p+1) y 

(* Busca todos lo Delta que aparecen en el lado izquierdo de la
   sustitucion y lo reemplaza por las variables del sucedente del secuente *)
let rec remplacedelta lisv = function 
  | [] -> []
  | ("Delta",t)::y -> nuevas_subs t 0 lisv @ remplacedelta lisv y 
  | x::y -> x :: remplacedelta lisv y 

(* Calcula una lista de susbtituciones sobre las variables que aparecen al
   en el sucedente del secuente de un arbol de demostracion. De tal forma
   que al componerlas y aplicarlas se obtienen los lambda terminos que expresan
   la demostracion*) 
let rec subs_t = function
  | Nil -> []
  | Cons(a,{seq=seq;sd=sd0;st=st0;reg=r},b) ->
      let sd = if (!r.rendelta <> []) or (!r.vardelta) then  
	remplacedelta (lisvar (suce !seq)) sd0  
      else sd0 in 
      let st = if (!r.rendelta <> []) or (!r.vardelta) then  
	remplacedelta (lisvar (suce !seq)) st0 
      else st0 in
      [sd] @ (subs_t a) @ [st] @ (subs_t b)

(* Funcion que compone recursivamente una substitucion con una lista
   de substituciones *)
let rec componga_r s = function 
  | [] -> s
  | x::y -> componga_r (comp_st x s) y

(* Dado un arbol de demostracion de un secuente, calcula los lambda terminos 
   que expresan la demostracion *)
let lterm = function
  | Nil -> []
  | (Cons(_,{seq=seq},_)) as a ->
      List.map (function (x,y) -> (x,normal y)) (componga_r [] (subs_t a))

(*--------------------- Interface con Coq  ---------------------------------*)
(*-- Convierte una formula cci a una formula notacion Tauto --*)

let (tAUTOFAIL : tactic) = fun _ -> errorlabstrm "TAUTOFAIL"
                                          [< 'sTR "Tauto failed.">]

let is_imp_term t =
  match t with
    | DOP2(Prod,_,DLAM(_,b)) -> (not((dependent (Rel 1) b)))
    | _ -> false

(* Chet's code depends on the names of the logical constants. *)

let tauto_of_cci_fmla gls cciterm = 
  let rec tradrec cciterm =
    if matches gls cciterm and_pattern then
      match dest_match gls cciterm and_pattern with
	| [a;b] -> FAnd(tradrec a,tradrec b)
	| _ -> assert false
    else if matches gls cciterm or_pattern then
      match dest_match gls cciterm or_pattern with
	| [a;b] -> FOr(tradrec a,tradrec b)
	| _ -> assert false
    else if matches gls cciterm iff_pattern then
      match dest_match gls cciterm iff_pattern with
        | [a;b] -> FEqu(tradrec a,tradrec b)
	| _ -> assert false
    else if matches gls cciterm eq_pattern then
      match dest_match gls cciterm eq_pattern with
        | [a;b;c] -> FEq(FPred a,FPred b, FPred c)
	| _ -> assert false
    else if matches gls cciterm not_pattern then
      match dest_match gls cciterm not_pattern with
        | [a] -> FNot(tradrec a)
	| _ -> assert false
    else if matches gls cciterm false_pattern then
      FFalse
    else if matches gls cciterm true_pattern then
      FTrue
    else if is_imp_term cciterm then
      match cciterm with
        | DOP2(Prod,a,DLAM(_,b)) -> FImp(tradrec a,tradrec (Generic.pop b))
	| _ -> assert false
    else FPred cciterm
  in 
  tradrec (whd_betaiota (pf_env gls) (project gls) cciterm)   

(*-- Retorna una lista de todas las variables proposicionales que
  aparescan en una lista de formulasS --*)
let rec lisvarprop = function 
  | [] -> []
  | (_,((FPred x) as fx))::y -> fx::lisvarprop y
  | _::y -> lisvarprop y

(*-- Dado el ambiente COQ construye el lado izquierdo de un secuente
     (hipotesis) --*)
let rec constr_lseq gls = function
  | ([],[]) -> []
  | (idx::idy,hx::hy) -> 
      (match (pf_type_of gls hx) with
         | DOP0 (Sort (Prop Null)) -> 
             (TVar(string_of_id idx),tauto_of_cci_fmla gls hx)
             :: constr_lseq gls (idy,hy)
         |_-> constr_lseq gls (idy,hy))
  | _ -> []

(*-- Dado un estado COQ construye el lado derecho de un secuente
     (conclusion) --*)
let constr_rseq gls but = [TVar(genvar()),
                           tauto_of_cci_fmla gls but]

(*-- Calula la posicion de la lista de un elemento --*) 
let rec pos_lis x = function 
  | [] -> raise TacticFailure
  | a::r -> if (x=a) then 1 else 1 + (pos_lis x r) 

(*-- Construye un termino constr dado una formula tauto --*)
let rec cci_of_tauto_fml env = 
  let cAnd = global_reference CCI (id_of_string "and") 
  and cOr =  global_reference CCI (id_of_string "or")  
  and cFalse = global_reference CCI (id_of_string "False") 
  and cTrue = global_reference CCI (id_of_string "True") 
  and cEq = global_reference CCI (id_of_string "eq") in
  function
    | FAnd(a,b) ->  applistc cAnd 
                    [cci_of_tauto_fml env a;cci_of_tauto_fml env b]
    | FOr(a,b)  ->  applistc cOr 
                    [cci_of_tauto_fml env a; cci_of_tauto_fml env b]
    | FEq(a,b,c)->  applistc cEq
                    [cci_of_tauto_fml env a; cci_of_tauto_fml env b;
                     cci_of_tauto_fml env c]
    | FImp(a,b) ->  mkArrow (cci_of_tauto_fml env a) (cci_of_tauto_fml env b) 
    | FPred a   ->  a  
    | FFalse    ->  cFalse
    | FTrue     ->  cTrue
    | FLis lf   ->  raise TacticFailure 
    | FVar a    ->  raise TacticFailure 
    | FAto a    ->  raise TacticFailure
    | FLisfor a ->  raise TacticFailure
    | _         ->  anomaly "Tauto:cci_of_tauto_fml"

let search env id =
  try
    (match lookup_id id (Environ.context env) with
       | RELNAME (n,_) -> Rel n
       | GLOBNAME _    -> VAR id)
  with Not_found ->
    global_reference CCI id

(*-- Construye un termino constr de un termino tauto --*)
let cci_of_tauto_term env t =
  let cFalse_ind = global_reference CCI (id_of_string "False_ind")  
  and cconj = global_reference CCI (id_of_string "conj")  
  and cor_ind = global_reference CCI (id_of_string "or_ind") 
  and cor_introl = global_reference CCI (id_of_string "or_introl") 
  and cor_intror = global_reference CCI (id_of_string "or_intror") 
  and cproj1 = global_reference CCI (id_of_string "proj1") 
  and cproj2 = global_reference CCI (id_of_string "proj2")
  and crefl  = global_reference CCI (id_of_string "refl_equal") 
  and csim   = global_reference CCI (id_of_string "sym_eq") 
  and ci     = global_reference CCI (id_of_string "I") 
  in  
  let rec ter_constr l = function
    | TVar x            -> (try (try Rel(pos_lis x l)
                                 with TacticFailure -> 
                                   search env (id_of_string x))
                            with _ -> raise TacticFailure)
    | TZ(f,x)           -> applistc cFalse_ind
          [cci_of_tauto_fml env f;ter_constr l x]
    | TSum(t1,t2)       -> ter_constr l t1 
    | TExi (x)          -> (try search env (id_of_string x) with
				_ -> raise TacticFailure)
    | TApl(_,_,t1,t2)   -> applistc (ter_constr l t1) [ter_constr l t2]
    | TPar(f1,f2,t1,t2) -> applistc cconj
          [cci_of_tauto_fml env f1;cci_of_tauto_fml env f2;
           ter_constr l t1;ter_constr l t2]
    | TInl(f1,f2,t)     -> applistc cor_introl
          [cci_of_tauto_fml env f1;cci_of_tauto_fml env f2;
           ter_constr l t]
    | TInr(f1,f2,t)     -> applistc cor_intror
          [cci_of_tauto_fml env f1;cci_of_tauto_fml env f2;
           ter_constr l t]
    | TFst(f1,f2,t)     -> applistc cproj1
          [cci_of_tauto_fml env f1;cci_of_tauto_fml env f2;
           ter_constr l t]
    | TSnd(f1,f2,t)     -> applistc cproj2
          [cci_of_tauto_fml env f1;cci_of_tauto_fml env f2;
           ter_constr l t]
    | TRefl(f1,f2)      -> applistc crefl
          [cci_of_tauto_fml env f1;cci_of_tauto_fml env f2]
    | TSim(f1,f2,f3,t) -> applistc csim
          [cci_of_tauto_fml env f1;cci_of_tauto_fml env f2;
           cci_of_tauto_fml env f3;ter_constr l t]
    | TCase(lf,lt)      -> applistc cor_ind
          ((List.map (cci_of_tauto_fml env) lf)@
           (List.map (ter_constr l) lt))
    | TFun(n,f,t)       ->  
	Environ.lambda_name env
	  (Name(id_of_string n ), cci_of_tauto_fml env f,ter_constr (n::l) t)
    | TTrue             -> ci
    | TLis _            -> raise TacticFailure
    | TLister _         -> raise TacticFailure
    | TZero _           -> raise TacticFailure
  in 
  ter_constr [] t 

let cutUsing id t = (tclTHENS (Tactics.cut t) ([intro_using id;tclIDTAC]))

let cut_in_parallelUsing idlist l = 
  let rec prec l_0 = function
    | [] -> tclIDTAC
    | h::t -> 
	(tclTHENS (cutUsing (id_of_string (List.hd l_0)) h) 
	   ([prec (List.tl l_0) t;tclIDTAC]))
  in 
  prec (List.rev idlist) (List.rev l)

let exacto tt gls = 
  match (try cci_of_tauto_term (pf_env gls) tt with
             _ -> (DOP0 Prod)) with (* Efectivamente, es cualquier cosa!! *)
    | (DOP0 Prod) -> tAUTOFAIL gls  (* Esto confirma el comentario anterior *)
    | t -> (exact t) gls
    
let subbuts l hyp = cut_in_parallelUsing
                      (lisvar l) 
                      (List.map (cci_of_tauto_fml (gLOB hyp)) (lisfor l))

let t_exacto = ref (TVar "#")

let tautoOR ti gls =
  let hyp = pf_untyped_hyps gls in
  let thyp = pf_hyps gls in
  hipvar := ids_of_sign hyp; 
  let but = pf_concl gls in
  let seq = (constr_lseq gls (ids_of_sign hyp,vals_of_sign hyp),
	     constr_rseq gls but) in 
  let vp = lisvarprop (ante seq) in
  match naive ti vp seq with
    | {arb=Nil} -> 
        tAUTOFAIL gls     
    | {arb=arb;lisbut=l} ->
        let se = apl ([],[],[]) (lterm arb) [] seq in
        let tt = fst(List.hd(suce se)) in
        (t_exacto := tt;
         subbuts l thyp gls)

let exact_Idtac = function 
  | 0 -> exacto (!t_exacto)
  | _ -> tclIDTAC

let tautoOR_0 gl = 
  tclORELSE
    (tclTHEN_i (tautoOR false) exact_Idtac 0)
    tAUTOFAIL gl

let intuitionOR = 
  tclTRY (tclTHEN 
	    (tclTHEN_i (tautoOR true) exact_Idtac 0)  
	    default_full_auto)

(*--- Mixed code Chet-Cesar ---*)

let rec prove  tauto_intu g   =
  (tclORELSE (tryAllHyps (clauseTacThen
                            (compose dyck_hypothesis out_some) 
			    (prove tauto_intu)))
  (tclORELSE (tryAllHyps (clauseTacThen
                            (compose dyck_absurdity_elim out_some)
			    (prove tauto_intu)))
  (tclORELSE (tryAllHyps (clauseTacThen
                          (compose dyck_and_elim out_some) (prove tauto_intu)))
  (tclORELSE (tryAllHyps (flush stdout;clauseTacThen
                          (compose dyck_atomic_imply_elim out_some)
                          (prove tauto_intu)))
  (tclORELSE (tryAllHyps (clauseTacThen
                          (compose dyck_and_imply_elim out_some)
			    (prove tauto_intu)))
  (tclORELSE (tryAllHyps (clauseTacThen
                            (compose dyck_or_imply_elim out_some)
			    (prove tauto_intu)))
  (tclORELSE (tclTHEN dyck_and_intro (prove tauto_intu))
  (tclORELSE (tclTHEN dyck_imply_intro (prove tauto_intu))
  (tclORELSE (tryAllHyps (flush stdout;clauseTacThen
                          (compose dyck_or_elim out_some) (prove tauto_intu)))
  (tclORELSE (tryAllHyps (clauseTacThen (* 28/5/99, ajout par HH *)
			    (compose dyck_imply_imply_elim out_some)
			    (prove tauto_intu)))
   tauto_intu)))))))))) g

let tauto gls = 
  let strToOccs x = ([],Nametab.sp_of_id CCI (id_of_string x)) in  
  (tclTHEN (onAllClausesLR 
              (unfold_option [strToOccs "not";strToOccs "iff"])) 
     (prove tautoOR_0)) gls

let intuition gls =
  let strToOccs x = ([],Nametab.sp_of_id CCI (id_of_string x)) in  
  (tclTHEN 
     ((tclTHEN (onAllClausesLR 
		  (unfold_option [strToOccs "not";strToOccs "iff"])) 
	 (prove intuitionOR))) intros) gls

let tauto_tac = hide_atomic_tactic "Tauto" tauto

let intuition_tac = hide_atomic_tactic "Intuition" intuition
