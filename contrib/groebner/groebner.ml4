(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)

open Pp
open Util
open Names
open Term
open Closure
open Environ
open Libnames
open Tactics
open Rawterm
open Tacticals
open Tacexpr
open Pcoq
open Tactic
open Constr
open Proof_type
open Coqlib
open Tacmach
open Mod_subst
open Tacinterp
open Libobject
open Printer
open Declare
open Decl_kinds
open Entries

open Num
open Unix
open Utile
open Entiers
open Ideal

let num_0 = Int 0
and num_1 = Int 1
and num_2 = Int 2
and num_10 = Int 10

let numdom r =
  let r' = Ratio.normalize_ratio (ratio_of_num r) in
  num_of_big_int(Ratio.numerator_ratio r'),
  num_of_big_int(Ratio.denominator_ratio r')

(* ------------------------------------------------------------------------- *)
(*  term??                                                                   *)
(* ------------------------------------------------------------------------- *)

type vname = string

type term =
  | Zero
  | Const of Num.num
  | Var of vname
  | Opp of term
  | Add of (term * term)
  | Sub of (term * term)
  | Mul of (term * term)
  | Pow of (term * int)

let unconstr = mkRel 1

let tpexpr =
  lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PExpr")
let ttconst = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEc")
let ttvar = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEX")
let ttadd = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEadd")  
let ttsub = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEsub")
let ttmul = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEmul")
let ttopp = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEopp")
let ttpow = lazy (gen_constant "CC" ["setoid_ring";"Ring_polynom"] "PEpow")

let tlist = lazy (gen_constant "CC" ["Lists";"List"] "list")
let lnil = lazy (gen_constant "CC" ["Lists";"List"] "nil")
let lcons = lazy (gen_constant "CC" ["Lists";"List"] "cons")

let tz = lazy (gen_constant "CC" ["ZArith";"BinInt"] "Z")
let z0 = lazy (gen_constant "CC" ["ZArith";"BinInt"] "Z0")
let zpos = lazy (gen_constant "CC" ["ZArith";"BinInt"] "Zpos")
let zneg = lazy(gen_constant "CC" ["ZArith";"BinInt"] "Zneg")

let pxI = lazy(gen_constant "CC" ["NArith";"BinPos"] "xI")
let pxO = lazy(gen_constant "CC" ["NArith";"BinPos"] "xO")
let pxH = lazy(gen_constant "CC" ["NArith";"BinPos"] "xH")

let nN0 = lazy (gen_constant "CC" ["NArith";"BinNat"] "N0")
let nNpos = lazy(gen_constant "CC" ["NArith";"BinNat"] "Npos")

let mkt_app name l =  mkApp (Lazy.force name, Array.of_list l)

let tlp () = mkt_app tlist [mkt_app tpexpr [Lazy.force tz]]
let tllp () = mkt_app tlist [tlp()]

let rec mkt_pos n = 
  if n =/ num_1 then Lazy.force pxH
  else if mod_num n num_2 =/ num_0 then
    mkt_app pxO [mkt_pos (quo_num n num_2)]
  else
    mkt_app pxI [mkt_pos (quo_num n num_2)]

let mkt_n n =
  if n=num_0
  then Lazy.force nN0
  else mkt_app nNpos [mkt_pos n]

let mkt_z z  = 
  if z =/ num_0 then  Lazy.force z0
  else if z >/ num_0 then
    mkt_app zpos [mkt_pos z]
  else
    mkt_app zneg [mkt_pos ((Int 0) -/ z)]

let rec mkt_term t  =  match t with
| Zero -> mkt_term (Const num_0)
| Const r -> let (n,d) = numdom r in
  mkt_app  ttconst [Lazy.force tz; mkt_z n]     
| Var v -> mkt_app ttvar [Lazy.force tz; mkt_pos (num_of_string v)]     
| Opp t1 -> mkt_app  ttopp [Lazy.force tz; mkt_term t1]
| Add (t1,t2) -> mkt_app  ttadd [Lazy.force tz; mkt_term t1; mkt_term t2]
| Sub (t1,t2) -> mkt_app  ttsub [Lazy.force tz; mkt_term t1; mkt_term t2]
| Mul (t1,t2) -> mkt_app  ttmul [Lazy.force tz; mkt_term t1; mkt_term t2]
| Pow (t1,n) ->  if (n = 0) then 
    mkt_app ttconst [Lazy.force tz; mkt_z num_1]     
else
    mkt_app ttpow [Lazy.force tz; mkt_term t1; mkt_n (num_of_int n)]

let rec parse_pos p =
  match kind_of_term p with
| App (a,[|p2|]) ->
    if a = Lazy.force pxO then num_2 */ (parse_pos p2)
    else num_1 +/ (num_2 */ (parse_pos p2))
| _ -> num_1

let parse_z z =
  match kind_of_term z with
| App (a,[|p2|]) ->
    if a = Lazy.force zpos then parse_pos p2 else (num_0 -/ (parse_pos p2))
| _ -> num_0

let parse_n z =
  match kind_of_term z with
| App (a,[|p2|]) ->
    parse_pos p2
| _ -> num_0

let rec parse_term p =
  match kind_of_term p with
| App (a,[|_;p2|]) ->
    if a = Lazy.force ttvar then Var (string_of_num (parse_pos p2))
    else if a = Lazy.force ttconst then Const (parse_z p2)
    else if a = Lazy.force ttopp then Opp (parse_term p2)
    else Zero
| App (a,[|_;p2;p3|]) ->
    if a = Lazy.force ttadd then Add (parse_term p2, parse_term p3)
    else if a = Lazy.force ttsub then Sub (parse_term p2, parse_term p3)
    else if a = Lazy.force ttmul then Mul (parse_term p2, parse_term p3)
    else if a = Lazy.force ttpow then
      Pow (parse_term p2, int_of_num (parse_n p3))
    else Zero
| _ -> Zero

let rec parse_request lp = 
  match kind_of_term lp with
    | App (_,[|_|])  -> []
    | App (_,[|_;p;lp1|])  -> 
	(parse_term p)::(parse_request lp1)
    |_-> assert false

let nvars = ref 0

let set_nvars_term t =
  let rec aux t =
    match t with
    | Zero -> ()
    | Const r -> ()
    | Var v -> let n = int_of_string v in
      nvars:= max (!nvars) n
    | Opp t1 -> aux t1
    | Add (t1,t2) -> aux t1; aux t2
    | Sub (t1,t2) -> aux t1; aux t2
    | Mul (t1,t2) -> aux t1; aux t2
    | Pow (t1,n) ->  aux t1
  in aux t

let string_of_term p =
  let rec aux p =
    match p with
    | Zero -> "0"
    | Const r -> string_of_num r
    | Var v -> "x"^v
    | Opp t1 -> "(-"^(aux t1)^")"
    | Add (t1,t2) -> "("^(aux t1)^"+"^(aux t2)^")"
    | Sub (t1,t2) ->  "("^(aux t1)^"-"^(aux t2)^")"
    | Mul (t1,t2) ->  "("^(aux t1)^"*"^(aux t2)^")"
    | Pow (t1,n) ->  (aux t1)^"^"^(string_of_int n)
  in aux p

(* terme vers polynome creux *)
(* les variables d'indice <=np sont dans les coeff *)

let term_pol_sparse np t=
  let d = !nvars in
  let rec aux t =
    match t with
    | Zero -> zeroP
    | Const r ->
	if r = num_0
	then zeroP
	else polconst d (Polynom.Pint (Polynom.coef_of_num r))
    | Var v ->
	let v = int_of_string v in
	if v <= np
	then polconst d (Polynom.x v)
	else gen d v
    | Opp t1 ->  oppP (aux t1)
    | Add (t1,t2) -> plusP d (aux t1) (aux t2)
    | Sub (t1,t2) -> plusP d (aux t1) (oppP (aux t2))
    | Mul (t1,t2) -> multP d (aux t1) (aux t2)
    | Pow (t1,n) ->  puisP d (aux t1) n
  in (*info ("conversion de: "^(string_of_term t)^"\n");*)
  let res= aux t in
  (*info ("donne: "^(stringP res)^"\n");*)
  res

(* polynome recusrsif vers terme *)

let polrec_to_term p =
  let rec aux p =
  match p with
   |Polynom.Pint n -> Const (Polynom.num_of_coef n)
   |Polynom.Prec (v,coefs) ->
     let res = ref Zero in
     Array.iteri
      (fun i c ->
	 res:=Add(!res, Mul(aux c,
			    Pow (Var (string_of_int v),
				 i))))
      coefs;
     !res
  in aux p

(* on approche la forme de Horner utilisee par la tactique ring. *)

let pol_sparse_to_term n2 p =
  let rec aux p =
    match p with
    |[] ->  Const (num_of_string "0")
    |(a,m)::p1 ->
	let n = (Array.length m)-1 in
	let (i0,e0) =
	  (List.fold_left
	     (fun (r,d) (a,m) ->
	       let i0= ref 0 in
	       for k=1 to n do
		 if m.(k)>0
		 then i0:=k
	       done;
	       if !i0 = 0
	       then (r,d)
	       else if !i0 > r
	       then (!i0, m.(!i0))
	       else if !i0 = r && m.(!i0)<d
	       then (!i0, m.(!i0))
	       else (r,d))
	     (0,0)
	     p) in
	if i0=0
	then
	  let mp = ref (polrec_to_term a) in
          if p1=[]
	  then !mp
	  else Add(!mp,aux p1)
	else (
	  let p1=ref [] in
	  let p2=ref [] in
	  List.iter
	    (fun (a,m) ->
	      if m.(i0)>=e0
	      then (m.(i0)<-m.(i0)-e0;
		    p1:=(a,m)::(!p1))
	      else p2:=(a,m)::(!p2))
	    p;
	  let vm =
	    if e0=1
	    then Var (string_of_int (i0))
	    else Pow (Var (string_of_int (i0)),e0) in
	  Add(Mul(vm, aux (List.rev (!p1))), aux (List.rev (!p2))))
  in let pp = aux p in

  pp


let rec remove_list_tail l i =
  let rec aux l i =
    if l=[]
    then []
    else if i<0
    then l
    else if i=0
    then List.tl l
    else
      match l with
      |(a::l1) ->
	  a::(aux l1 (i-1))
      |_ -> assert false
  in
  List.rev (aux (List.rev l) i)

(*
   lq = [cn+m+1 n+m ...cn+m+1 1]
   lci=[[cn+1 n,...,cn1 1]
   ...
   [cn+m n+m-1,...,cn+m 1]]

   enleve les polynomes intermediaires inutiles pour calculer le dernier 
 *)

let remove_zeros zero lci =
  let n = List.length (List.hd lci) in
  let m=List.length lci in
  let u = Array.create m false in
  let rec utiles k =
    if k>=m
    then ()
    else (
      u.(k)<-true;
      let lc = List.nth lci k in
      for i=0 to List.length lc - 1 do
	if not (zero (List.nth lc i))
	then utiles (i+k+1);
      done)
  in utiles 0;
  let lr = ref [] in
  for i=0 to m-1 do
    if u.(i)
    then lr:=(List.nth lci i)::(!lr)
  done;
  let lr=List.rev !lr in
  let lr = List.map
      (fun lc ->
	let lcr=ref lc in
	for i=0 to m-1 do
	  if not u.(i)
	  then lcr:=remove_list_tail !lcr (m-i+(n-m))
	done;
	!lcr)
      lr in
  info ("spolynomes inutiles: "
	^string_of_int (m-List.length lr)^"\n");
  info ("spolynomes utiles: "
	^string_of_int (List.length lr)^"\n");
  lr

let theoremedeszeros lpol p =
  let t1 = Unix.gettimeofday() in
  let m = !nvars in
  let (c,lp0,p,lci,lc) = in_ideal m lpol p in
  let lpc = List.rev !poldepcontent in
  info ("temps: "^Format.sprintf "@[%10.3f@]s\n" (Unix.gettimeofday ()-.t1));
  if lc<>[]
  then (c,lp0,p,lci,lc,1,lpc)
  else (c,[],zeroP,[],[],0,[])


let theoremedeszeros_termes lp =
  nvars:=0;(* mise a jour par term_pol_sparse *)
  List.iter set_nvars_term  lp;
  match lp with
  | Const (Int nparam)::lp ->
      (let m= !nvars in
      let lvar=ref [] in
      for i=m downto 1 do lvar:=["x"^string_of_int i^""]@(!lvar); done;
      name_var:=!lvar;

      let lp = List.map (term_pol_sparse nparam) lp in 
      match lp with
      | [] -> assert false
      | p::lp1 ->
	  let lpol = List.rev lp1 in
	  let (c,lp0,p,lci,lq,d,lct)=  theoremedeszeros lpol p in

	  let lci1 = List.rev lci in
	  match remove_zeros (fun x -> x=zeroP) (lq::lci1) with
	  | [] -> assert false 
	  | (lq::lci) ->
	      (* lci commence par les nouveaux polynomes *)
	      let m= !nvars in
	      let lci = List.rev lci in
	      let c = pol_sparse_to_term m [c, Array.create (m+1) 0] in
	      let lp0 = List.map (pol_sparse_to_term m) lp0 in
	      let p = (Pow ((pol_sparse_to_term m p),d)) in
	      let lci = List.map (fun lc -> List.map (pol_sparse_to_term m) lc) lci in
	      let lq = List.map (pol_sparse_to_term m) lq in
	      info ("nombre de parametres: "^string_of_int nparam^"\n");
	      info "terme calcule\n";
	      (c,lp0,p,lci,lq)
      )
  |_ -> assert false




let groebner lpol =
  let lp= parse_request lpol in
  let (c,lp0,p,lci,lq) = theoremedeszeros_termes lp in
  let res = [p::lp0;c::lq]@lci in
  let res = List.map (fun lx -> List.map mkt_term lx) res in
  let res =
    List.fold_right
      (fun lt r ->
	 let ltterm =
	   List.fold_right
	     (fun t r ->
		mkt_app lcons [mkt_app tpexpr [Lazy.force tz];t;r])
	     lt
	     (mkt_app lnil [mkt_app tpexpr [Lazy.force tz]]) in
	 mkt_app lcons [tlp ();ltterm;r])
      res
      (mkt_app lnil [tlp ()]) in
  info "terme calcule\n";
  res

(*
open Util
open Term
open Tactics
open Coqlib
open Utile
open Groebner
*)

let groebner_compute t gl =
  let lpol = groebner t in
  let a =
    mkApp(gen_constant "CC" ["Init";"Logic"] "refl_equal",[|tllp ();lpol|]) in
  generalize [a] gl

TACTIC EXTEND groebner_compute
| [ "groebner_compute"  constr(lt) ] ->
    [ groebner_compute lt ]
END


