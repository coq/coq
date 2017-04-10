(* Printing *)

let pr x =
  if !Flags.debug then (Format.printf "@[%s@]" x; flush(stdout);)else ()

let prn x =
  if !Flags.debug then (Format.printf "@[%s\n@]" x; flush(stdout);) else ()

let prt0 s = () (* print_string s;flush(stdout)*)

let prt s =
  if !Flags.debug then (print_string (s^"\n");flush(stdout)) else ()

let sinfo s = if !Flags.debug then Feedback.msg_debug (Pp.str s)
let info s = if !Flags.debug then Feedback.msg_debug (Pp.str (s ()))

(* Lists *)

let rec list_mem_eq eq x l =
  match l with
    [] -> false
   |y::l1 -> if (eq x y) then true else (list_mem_eq eq x l1)

let set_of_list_eq eq l =
   let res = ref [] in
   List.iter (fun x -> if not (list_mem_eq eq x (!res)) then res:=x::(!res)) l;
   List.rev !res

(**********************************************************************
  Eléments minimaux pour un ordre partiel de division.
  E est un ensemble, avec une multiplication
  et une division partielle div (la fonction div peut échouer),
  constant est un prédicat qui définit un sous-ensemble C de E.
*)
(*
  Etant donnée une partie A de E, on calcule une partie B de E disjointe de C
  telle que:
    - les éléments de A sont des produits d'éléments de B et d'un de C.
    - B est minimale pour cette propriété.
*)

let facteurs_liste div constant lp =
   let lp = List.filter (fun x -> not (constant x)) lp in
   let rec factor lmin lp = (* lmin: ne se divisent pas entre eux *)
      match lp with
        [] -> lmin
       |p::lp1 ->
         (let l1 = ref [] in
          let p_dans_lmin = ref false in
          List.iter (fun q -> try (let r = div p q in
                                   if not (constant r)
				   then l1:=r::(!l1)
                                   else p_dans_lmin:=true)
			      with e when CErrors.noncritical e -> ())
                     lmin;
          if !p_dans_lmin
          then factor lmin lp1
          else if (!l1)=[]
          (* aucun q de lmin ne divise p *)
          then (let l1=ref lp1 in
		let lmin1=ref [] in
                List.iter (fun q -> try (let r = div q p in
					 if not (constant r)
					 then l1:=r::(!l1))
				    with e when CErrors.noncritical e ->
                                      lmin1:=q::(!lmin1))
                          lmin;
	        factor (List.rev (p::(!lmin1))) !l1)
          (* au moins un q de lmin divise p non trivialement *)
          else factor lmin ((!l1)@lp1))
    in
    factor [] lp


(* On suppose que tout élément de A est produit d'éléments de B et d'un de C:
   A et B sont deux tableaux,  rend un tableau de couples
      (élément de C, listes d'indices l)
   tels que A.(i) = l.(i)_1*Produit(B.(j), j dans l.(i)_2)
   zero est un prédicat sur E tel que (zero x) => (constant x):
         si (zero x) est vrai on ne decompose pas x
   c est un élément quelconque de E.
*)
let factorise_tableau div zero c f l1 =
    let res = Array.make (Array.length f) (c,[]) in
    Array.iteri (fun i p ->
      let r = ref p in
      let li = ref [] in
      if not (zero p)
      then
      Array.iteri (fun j q ->
	              try (while true do
                               let rr = div !r q in
      	                       li:=j::(!li);
                               r:=rr;
			   done)
                      with e when CErrors.noncritical e -> ())
                  l1;
      res.(i)<-(!r,!li))
     f;
    (l1,res)


(* exemples:

let l =  [1;2;6;24;720]
and div1 = (fun a b -> if a mod b =0 then a/b else failwith "div")
and constant = (fun x -> x<2)
and zero = (fun x -> x=0)


let f = facteurs_liste div1 constant l


factorise_tableau div1 zero 0 (Array.of_list l) (Array.of_list f)

*)


