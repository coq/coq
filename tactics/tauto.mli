
(* $Id$ *)

(* Mars 1993 *)
(* Autor: Cesar A. Munnoz H *)

open Tacmach
open Term

(* Prototipo *)
(* Estructuras de Datos *)

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
  | FLisfor of string    (* Variable para una lista de formulas *)
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
  | TZero of formula    (* Milagro *)

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
  rendelta: string list} (* Renombramientos de delta *)
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
  st:  subsT }      (* Substitucion que calcula el lambda termino  *)
	      
(* Arbol de demostracion *)  
type arbol = Nil | Cons of arbol * nodo * arbol

(* Demostracion *)
(* Si el secuente es valido Arb es un arbol de demostracion y Lisbut
   es vacio, sino Lisbut es un contexto en el cual Arb es valido *)
type demostracion = { arb : arbol; lisbut : formulaT list }

(* Definicion de excepcion para rescribir terminos *)
exception NoAplica
exception TacticFailure 

val tauto_tac : tactic
val intuition : tactic
val intuition_tac : tactic
val tauto : tactic

