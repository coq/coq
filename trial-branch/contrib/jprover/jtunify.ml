(*
 * Unification procedures for JProver. See jall.mli for more
 * information on JProver.
 *
 * ----------------------------------------------------------------
 *
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.
 *
 * See the file doc/index.html for information on Nuprl,
 * OCaml, and more information about this system.
 *
 * Copyright (C) 2000 Stephan Schmitt
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Stephan Schmitt <schmitts@spmail.slu.edu>
 * Modified by: Aleksey Nogin <nogin@cs.cornell.edu>
 *)

exception Not_unifiable
exception Failed

let jprover_bug = Invalid_argument "Jprover bug (Jtunify module)"

(* ************ T-STRING UNIFICATION *********************************)


(* ******* printing ********** *)

let rec list_to_string s =
   match s with
      [] -> ""
    | f::r ->
         f^"."^(list_to_string r)

let rec print_eqlist eqlist =
   match eqlist with
      [] ->
         print_endline ""
    | (atnames,f)::r ->
         let (s,t) = f in
         let ls = list_to_string s
         and lt = list_to_string t in
         begin
            print_endline ("Atom names: "^(list_to_string atnames));
            print_endline (ls^" = "^lt);
            print_eqlist r
         end

let print_equations eqlist =
   begin
      Format.open_box 0;
      Format.force_newline ();
      print_endline "Equations:";
      print_eqlist eqlist;
      Format.force_newline ();
   end

let rec print_subst sigma =
   match sigma with
      [] ->
         print_endline ""
    | f::r ->
         let (v,s) = f in
         let ls = list_to_string s in
         begin
            print_endline (v^" = "^ls);
            print_subst r
         end

let print_tunify sigma =
   let (n,subst) = sigma in
   begin
      print_endline " ";
      print_endline ("MaxVar = "^(string_of_int (n-1)));
      print_endline " ";
      print_endline "Substitution:";
      print_subst subst;
      print_endline " "
   end

 (*****************************************************)

let is_const name  =
  (String.get name 0) = 'c'

let is_var name  =
  (String.get name 0) = 'v'

let r_1 s ft rt =
   (s = []) && (ft = []) && (rt = [])

let r_2 s ft rt =
   (s = []) && (ft = []) && (List.length rt >= 1)

let r_3 s ft rt =
   ft=[] && (List.length s >= 1) && (List.length rt >= 1) && (List.hd s = List.hd rt)

let r_4 s ft rt =
   ft=[]
      && (List.length s >= 1)
      && (List.length rt >= 1)
      && is_const (List.hd s)
      && is_var (List.hd rt)

let r_5 s ft rt =
   rt=[]
      && (List.length s >= 1)
      && is_var (List.hd s)

let r_6 s ft rt =
   ft=[]
      && (List.length s >= 1)
      && (List.length rt >= 1)
      && is_var (List.hd s)
      && is_const (List.hd rt)

let r_7 s ft rt =
   List.length s >= 1
      && (List.length rt >= 2)
      && is_var (List.hd s)
      && is_const (List.hd rt)
      && is_const (List.hd (List.tl rt))

let r_8 s ft rt =
  ft=[]
    && List.length s >= 2
    && List.length rt >= 1
    && let v = List.hd s
       and v1 = List.hd rt in
         (is_var v) & (is_var v1) & (v <> v1)

let r_9 s ft rt =
   (List.length s >= 2) && (List.length ft >= 1) && (List.length rt >= 1)
      && let v = (List.hd s)
         and v1 = (List.hd rt) in
         (is_var v) & (is_var v1) & (v <> v1)

let r_10 s ft rt =
   (List.length s >= 1) && (List.length rt >= 1)
   && let v = List.hd s
      and x = List.hd rt in
      (is_var v) && (v <> x)
      && (((List.tl s) =[]) or (is_const x) or ((List.tl rt) <> []))

let rec com_subst slist ((ov,ovlist) as one_subst) =
   match slist with
      [] -> raise jprover_bug
    | f::r ->
         if f = ov then
            (ovlist @ r)
         else
            f::(com_subst r one_subst)

let rec combine subst ((ov,oslist) as one_subst)  =
   match subst with
      [] -> []
    | ((v, slist) as f) :: r ->
         let rest_combine = (combine r one_subst) in
         if (List.mem ov slist) then  (* subst assumed to be idemponent *)
            let com_element = com_subst slist one_subst in
            ((v,com_element)::rest_combine)
         else
            (f::rest_combine)

let compose ((n,subst) as _sigma) ((ov,oslist) as one_subst) =
   let com = combine subst one_subst in
(* begin
   print_endline "!!!!!!!!!test print!!!!!!!!!!";
   print_subst [one_subst];
   print_subst subst;
   print_endline "!!!!!!!!! END test print!!!!!!!!!!";
*)
   if List.mem one_subst subst then
      (n,com)
   else
(* ov may multiply as variable in subst with DIFFERENT values *)
(* in order to avoid explicit atom instances!!! *)
      (n,(com @ [one_subst]))
(* end *)

let rec apply_element fs ft (v,slist) =
   match (fs,ft) with
      ([],[]) ->
         ([],[])
    | ([],(ft_first::ft_rest)) ->
         let new_ft_first =
            if ft_first = v then
               slist
            else
               [ft_first]
         in
         let (emptylist,new_ft_rest) = apply_element [] ft_rest (v,slist) in
         (emptylist,(new_ft_first @ new_ft_rest))
    | ((fs_first::fs_rest),[]) ->
         let new_fs_first =
            if fs_first = v then
               slist
            else
               [fs_first]
         in
         let (new_fs_rest,emptylist) = apply_element fs_rest [] (v,slist) in
         ((new_fs_first @ new_fs_rest),emptylist)
    | ((fs_first::fs_rest),(ft_first::ft_rest)) ->
         let new_fs_first =
            if fs_first = v then
               slist
            else
               [fs_first]
         and new_ft_first =
            if ft_first = v then
               slist
            else
               [ft_first]
         in
         let (new_fs_rest,new_ft_rest) = apply_element fs_rest ft_rest (v,slist) in
         ((new_fs_first @ new_fs_rest),(new_ft_first @ new_ft_rest))

let rec shorten us ut =
   match (us,ut) with
      ([],_) | (_,[])  -> (us,ut) (*raise jprover_bug*)
    | ((fs::rs),(ft::rt)) ->
         if fs = ft then
            shorten rs rt
         else
            (us,ut)

let rec apply_subst_list eq_rest (v,slist) =
   match eq_rest with
      [] ->
         (true,[])
    | (atomnames,(fs,ft))::r ->
         let (n_fs,n_ft) = apply_element fs ft (v,slist) in
         let (new_fs,new_ft) = shorten n_fs n_ft in (* delete equal first elements *)
         match (new_fs,new_ft) with
            [],[] ->
               let (bool,new_eq_rest) = apply_subst_list r (v,slist) in
               (bool,((atomnames,([],[]))::new_eq_rest))
          | [],(fft::rft) ->
               if (is_const fft) then
                  (false,[])
               else
                  let (bool,new_eq_rest) = apply_subst_list r (v,slist) in
                  (bool,((atomnames,([],new_ft))::new_eq_rest))
          | (ffs::rfs),[] ->
               if (is_const ffs) then
                  (false,[])
               else
                  let (bool,new_eq_rest) = apply_subst_list r (v,slist) in
                  (bool,((atomnames,(new_fs,[]))::new_eq_rest))
          | (ffs::rfs),(fft::rft) ->
               if (is_const ffs) & (is_const fft) then
                  (false,[])
        (* different first constants cause local fail *)
               else
        (* at least one of firsts is a variable *)
                  let (bool,new_eq_rest) = apply_subst_list r (v,slist) in
                  (bool,((atomnames,(new_fs,new_ft))::new_eq_rest))

let apply_subst eq_rest (v,slist) atomnames =
   if (List.mem v atomnames) then (* don't apply subst to atom variables !! *)
      (true,eq_rest)
   else
      apply_subst_list eq_rest (v,slist)


(* let all_variable_check eqlist = false   needs some discussion with Jens! -- NOT done *)

(*
 let rec all_variable_check eqlist =
  match eqlist with
    [] -> true
   | ((_,(fs,ft))::rest_eq) ->
     if (fs <> []) & (ft <> []) then
      let fs_first = List.hd fs
      and ft_first = List.hd ft
      in
      if (is_const fs_first) or (is_const ft_first) then
        false
      else
        all_variable_check rest_eq
     else
      false
*)

let rec  tunify_list eqlist init_sigma =
   let rec tunify atomnames fs ft rt rest_eq sigma =
      let apply_r1 fs ft rt rest_eq sigma =
      (* print_endline "r1"; *)
         tunify_list rest_eq sigma

      in
      let apply_r2 fs ft rt rest_eq sigma =
      (* print_endline "r2"; *)
         tunify atomnames rt fs ft rest_eq sigma

      in
      let apply_r3 fs ft rt rest_eq sigma =
      (* print_endline "r3"; *)
         let rfs =  (List.tl fs)
         and rft =  (List.tl rt) in
         tunify atomnames rfs ft rft rest_eq sigma

      in
      let apply_r4 fs ft rt rest_eq sigma =
      (* print_endline "r4"; *)
         tunify atomnames rt ft fs rest_eq sigma

      in
      let apply_r5 fs ft rt rest_eq sigma =
      (* print_endline "r5"; *)
         let v = (List.hd fs) in
         let new_sigma = compose sigma (v,ft) in
         let (bool,new_rest_eq) = apply_subst rest_eq (v,ft) atomnames in
         if (bool=false) then
            raise Not_unifiable
         else
            tunify atomnames (List.tl fs) rt rt new_rest_eq new_sigma

      in
      let apply_r6 fs ft rt rest_eq sigma =
      (* print_endline "r6"; *)
         let v = (List.hd fs) in
         let new_sigma = (compose sigma (v,[])) in
         let (bool,new_rest_eq) = apply_subst rest_eq (v,[]) atomnames in
         if (bool=false) then
            raise Not_unifiable
         else
            tunify atomnames (List.tl fs) ft rt new_rest_eq new_sigma

      in
      let apply_r7 fs ft rt rest_eq sigma =
      (* print_endline "r7"; *)
         let v = (List.hd fs)
         and c1 = (List.hd rt)
         and c2t =(List.tl rt) in
         let new_sigma = (compose sigma (v,(ft @ [c1]))) in
         let (bool,new_rest_eq) = apply_subst rest_eq (v,(ft @ [c1])) atomnames in
         if bool=false then
            raise Not_unifiable
         else
            tunify atomnames (List.tl fs) []  c2t new_rest_eq new_sigma
      in
      let apply_r8 fs ft rt rest_eq sigma =
      (* print_endline "r8"; *)
         tunify atomnames  rt [(List.hd fs)] (List.tl fs) rest_eq sigma

      in
      let apply_r9 fs ft rt rest_eq sigma =
      (* print_endline "r9"; *)
         let v = (List.hd fs)
         and (max,subst) = sigma in
         let v_new = ("vnew"^(string_of_int max)) in
         let new_sigma = (compose ((max+1),subst) (v,(ft @ [v_new]))) in
         let (bool,new_rest_eq) = apply_subst rest_eq (v,(ft @ [v_new])) atomnames in
         if (bool=false) then
            raise Not_unifiable
         else
            tunify atomnames rt [v_new] (List.tl fs) new_rest_eq new_sigma

      in
      let apply_r10 fs ft rt rest_eq sigma =
      (* print_endline "r10"; *)
         let x = List.hd rt in
         tunify atomnames fs (ft @ [x]) (List.tl rt) rest_eq sigma

      in
      if r_1 fs ft rt then
         apply_r1 fs ft rt rest_eq sigma
      else if r_2 fs ft rt then
         apply_r2 fs ft rt rest_eq sigma
      else if r_3 fs ft rt then
         apply_r3 fs ft rt rest_eq sigma
      else if r_4 fs ft rt then
         apply_r4 fs ft rt rest_eq sigma
      else if r_5 fs ft rt then
         apply_r5 fs ft rt rest_eq sigma
      else if r_6 fs ft rt then
         (try
            apply_r6 fs ft rt rest_eq sigma
         with Not_unifiable ->
            if r_7 fs ft rt then (* r7 applicable if r6 was and tr6 = C2t' *)
               (try
                  apply_r7 fs ft rt rest_eq sigma
               with Not_unifiable ->
                  apply_r10 fs ft rt rest_eq sigma (* r10 always applicable if r6 was *)
               )
            else
      (* r10 could be represented only once if we would try it before r7.*)
      (* but looking at the transformation rules, r10 should be tried at last in any case *)
               apply_r10 fs ft rt rest_eq sigma  (* r10 always applicable r6 was *)
         )
      else if r_7 fs ft rt then  (* not r6 and r7 possible if z <> [] *)
         (try
            apply_r7 fs ft rt rest_eq sigma
         with Not_unifiable ->
            apply_r10 fs ft rt rest_eq sigma  (* r10 always applicable if r7 was *)
         )
      else if r_8 fs ft rt then
         (try
            apply_r8 fs ft rt rest_eq sigma
         with Not_unifiable ->
            if r_10 fs ft rt then (* r10 applicable if r8 was and tr8 <> [] *)
               apply_r10 fs ft rt rest_eq sigma
            else
               raise Not_unifiable (* simply back propagation *)
         )
      else if r_9 fs ft rt then
         (try
            apply_r9 fs ft rt rest_eq sigma
         with Not_unifiable ->
            if r_10 fs ft rt then (* r10 applicable if r9 was and tr9 <> [] *)
               apply_r10 fs ft rt rest_eq sigma
            else
               raise Not_unifiable (* simply back propagation *)
         )
      else if r_10 fs ft rt then  (* not ri, i<10, and r10 possible if for instance *)
                         (* (s=[] and x=v1) or (z<>[] and xt=C1V1t') *)
         apply_r10 fs ft rt rest_eq sigma
      else  (* NO rule applicable *)
         raise Not_unifiable
   in
   match eqlist with
      [] ->
         init_sigma
    | f::rest_eq ->
         let (atomnames,(fs,ft)) = f in
         tunify atomnames fs [] ft rest_eq init_sigma

let rec test_apply_eq atomnames eqs eqt subst =
   match subst with
      [] -> (eqs,eqt)
    | (f,flist)::r ->
         let (first_appl_eqs,first_appl_eqt) =
            if List.mem f atomnames then
               (eqs,eqt)
            else
               (apply_element eqs eqt (f,flist))
         in
         test_apply_eq atomnames first_appl_eqs first_appl_eqt r

let rec test_apply_eqsubst eqlist subst =
   match eqlist with
      [] -> []
    | f::r ->
         let (atomnames,(eqs,eqt)) = f in
         let applied_element  = test_apply_eq atomnames eqs eqt subst in
         (atomnames,applied_element)::(test_apply_eqsubst r subst)

let ttest us ut ns nt eqlist orderingQ atom_rel =
   let (short_us,short_ut) = shorten us ut in (* apply intial rule R3 *)
                                           (* to eliminate common beginning *)
   let new_element = ([ns;nt],(short_us,short_ut)) in
   let full_eqlist =
      if List.mem new_element eqlist then
         eqlist
      else
         new_element::eqlist
   in
   let sigma = tunify_list full_eqlist (1,[]) in
   let (n,subst) = sigma in
   let test_apply  = test_apply_eqsubst full_eqlist subst in
   begin
      print_endline "";
      print_endline "Final equations:";
      print_equations full_eqlist;
      print_endline "";
      print_endline "Final substitution:";
      print_tunify sigma;
      print_endline "";
      print_endline "Applied equations:";
      print_equations test_apply
   end

let do_stringunify us ut ns nt equations =
   let (short_us,short_ut) = shorten us ut in (* apply intial rule R3 to eliminate common beginning *)
   let new_element = ([ns;nt],(short_us,short_ut)) in
   let full_eqlist =
      if List.mem new_element equations then
         equations
      else
         new_element::equations
   in
(*  print_equations full_eqlist; *)
   (try
      let new_sigma = tunify_list full_eqlist (1,[]) in
      (new_sigma,(1,full_eqlist))
   with Not_unifiable ->
      raise Failed            (* new connection please *)
   )


(* type of one unifier: int * (string * string) list  *)
