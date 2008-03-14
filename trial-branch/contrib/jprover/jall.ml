(*
 * JProver first-order automated prover. See the interface file
 * for more information and a list of references for JProver.
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

open Jterm
open Opname
open Jlogic
open Jtunify

let ruletable = Jlogic.ruletable

let free_var_op = make_opname ["free_variable"; "Jprover"]
let jprover_op = make_opname ["jprover"; "string"]

module JProver (JLogic : JLogicSig) =
struct
   type polarity = I | O

   type connective = And | Or | Neg | Imp | All | Ex | At | Null

   type ptype = Alpha | Beta | Gamma | Delta | Phi | Psi | PNull

   type stype =
      Alpha_1 | Alpha_2 | Beta_1 | Beta_2 | Gamma_0 | Delta_0
    | Phi_0 | Psi_0 | PNull_0

   type pos  = {name : string;
                address : int list;
                op :  connective;
                pol : polarity;
                pt : ptype;
                st : stype;
                label : term}

   type 'pos ftree =
      Empty
    | NodeAt of 'pos
    | NodeA of 'pos * ('pos ftree) array

   type atom  = {aname : string;
                 aaddress : int list;
                 aprefix : string list;
                 apredicate :  operator;
                 apol : polarity;
                 ast : stype;
                 alabel : term}

   type atom_relations = atom * atom list * atom list
(* all atoms except atom occur in [alpha_set] and [beta_set] of atom*)

(* beta proofs *)

   type bproof = BEmpty
    | RNode of string list * bproof
    | CNode of (string * string)
    | BNode of string * (string list * bproof) * (string list * bproof)
    | AtNode of string * (string * string)

(* Assume only constants for instantiations, not adapted to terms yet *)
   type inf = rule * term  * term

(* proof tree for pretty print and permutation *)
   type 'inf ptree =
      PEmpty
    | PNodeAx of 'inf
    | PNodeA of 'inf * 'inf ptree
    | PNodeB of 'inf * 'inf ptree * 'inf ptree

   module OrderedAtom =
   struct
      type t = atom
      let compare a1 a2 = if (a1.aname) = (a2.aname) then 0 else
      if (a1.aname) < (a2.aname) then -1 else 1
   end

   module AtomSet = Set.Make(OrderedAtom)

   module OrderedString =
   struct
      type t = string
      let compare a1 a2 = if a1 = a2 then 0 else
      if a1 < a2 then -1 else 1
   end

   module StringSet = Set.Make(OrderedString)

(*i   let _ =
      show_loading "Loading Jall%t" i*)

   let debug_jprover =
      create_debug (**)
         { debug_name = "jprover";
           debug_description = "Display Jprover operations";
           debug_value = false
         }

   let jprover_bug = Invalid_argument "Jprover bug (Jall module)"

(*****************************************************************)

(************* printing function *************************************)

(************ printing T-string unifiers ****************************)

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

(********* printing atoms and their relations ***********************)

   let print_stype st =
      match st with
         Alpha_1 -> Format.print_string "Alpha_1"
       | Alpha_2 -> Format.print_string "Alpha_2"
       | Beta_1  -> Format.print_string "Beta_1"
       | Beta_2  -> Format.print_string "Beta_2"
       | Gamma_0 -> Format.print_string "Gamma_0"
       | Delta_0 -> Format.print_string "Delta_0"
       | Phi_0   -> Format.print_string "Phi_0"
       | Psi_0   -> Format.print_string "Psi_0"
       | PNull_0 -> Format.print_string "PNull_0"

   let print_pol pol =
      if pol = O then
         Format.print_string "O"
      else
         Format.print_string "I"

   let rec print_address int_list =
      match int_list with
         [] ->
            Format.print_string ""
       | hd::rest ->
            begin
               Format.print_int hd;
               print_address rest
            end

   let rec print_prefix prefix_list =
      match prefix_list with
         [] -> Format.print_string ""
       | f::r ->
            begin
               Format.print_string f;
               print_prefix r
            end

   let print_atom at tab =
      let ({aname=x; aaddress=y; aprefix=z; apredicate=p; apol=a; ast=b; alabel=label}) = at in
      begin
         Format.print_string ("{aname="^x^"; address=");
         print_address y;
         Format.print_string "; ";
         Format.force_newline ();
         Format.print_break (tab+1) (tab+1);
         Format.print_string "prefix=";
         print_prefix z;
         Format.print_string "; predicate=<abstr>; ";
         Format.print_break (tab+1) (tab+1);
         Format.print_break (tab+1) (tab+1);
         Format.print_string "pol=";
         print_pol a;
         Format.print_string "; stype=";
         print_stype b;
         Format.print_string "; arguments=[<abstr>]";
         Format.print_string "\n    alabel=";
         print_term stdout label;
         Format.print_string "}"
      end

   let rec print_atom_list set tab =
      match set with
         []  -> Format.print_string ""
       | (f::r) ->
            begin
               Format.force_newline ();
               Format.print_break (tab) (tab);
               print_atom f tab;
               print_atom_list r (tab)
            end

   let rec print_atom_info atom_relation =
      match atom_relation with
         [] -> Format.print_string ""
       | (a,b,c)::r ->
            begin
               Format.print_string "atom:";
               Format.force_newline ();
               Format.print_break 3 3;
               print_atom a 3;
               Format.force_newline ();
               Format.print_break 0 0;
               Format.print_string "alpha_set:";
               print_atom_list b 3;
               Format.force_newline ();
               Format.print_break 0 0;
               Format.print_string "beta_set:";
               print_atom_list c 3;
               Format.force_newline ();
               Format.force_newline ();
               Format.print_break 0 0;
               print_atom_info r
            end

(*************** print formula tree, tree ordering etc. ***********)

   let print_ptype pt =
      match pt with
         Alpha -> Format.print_string "Alpha"
       | Beta  -> Format.print_string "Beta"
       | Gamma -> Format.print_string "Gamma"
       | Delta -> Format.print_string "Delta"
       | Phi   -> Format.print_string "Phi"
       | Psi   -> Format.print_string "Psi"
       | PNull -> Format.print_string "PNull"

   let print_op op =
      match op with
         At   -> Format.print_string "Atom"
       | Neg  -> Format.print_string "Neg"
       | And  -> Format.print_string "And"
       | Or   -> Format.print_string  "Or"
       | Imp  -> Format.print_string  "Imp"
       | Ex   -> Format.print_string "Ex"
       | All  -> Format.print_string "All"
       | Null -> Format.print_string "Null"

   let print_position position tab =
      let ({name=x; address=y; op=z; pol=a; pt=b; st=c; label=t}) = position in
      begin
         Format.print_string ("{name="^x^"; address=");
         print_address y;
         Format.print_string "; ";
         Format.force_newline ();
         Format.print_break (tab+1) 0;
(*   Format.print_break 0 3; *)
         Format.print_string "op=";
         print_op z;
         Format.print_string "; pol=";
         print_pol a;
         Format.print_string "; ptype=";
         print_ptype b;
         Format.print_string "; stype=";
         print_stype c;
         Format.print_string ";";
         Format.force_newline ();
         Format.print_break (tab+1) 0;
         Format.print_string "label=";
         Format.print_break 0 0;
         Format.force_newline ();
         Format.print_break tab 0;
         print_term stdout t;
         Format.print_string "}"
      end

   let rec pp_ftree_list tree_list tab =
      let rec pp_ftree ftree new_tab =
         let dummy = String.make (new_tab-2) ' ' in
         match ftree with
            Empty -> Format.print_string ""
          | NodeAt(position) ->
               begin
                  Format.force_newline ();
                  Format.print_break new_tab 0;
                  print_string (dummy^"AtomNode: ");
(*     Format.force_newline ();
   Format.print_break 0 3;
*)
                  print_position position new_tab;
                  Format.force_newline ();
                  Format.print_break new_tab 0
               end
          | NodeA(position,subtrees) ->
               let tree_list = Array.to_list subtrees in
               begin
                  Format.force_newline ();
                  Format.print_break new_tab 0;
                  Format.print_break 0 0;
                  print_string (dummy^"InnerNode: ");
                  print_position position new_tab;
                  Format.force_newline ();
                  Format.print_break 0 0;
                  pp_ftree_list tree_list (new_tab-3)
               end
      in
      let new_tab = tab+5 in
      match tree_list with
         [] -> Format.print_string ""
       | first::rest ->
            begin
               pp_ftree first new_tab;
               pp_ftree_list rest tab
            end

   let print_ftree ftree =
      begin
         Format.open_box 0;
         Format.print_break 3 0;
         pp_ftree_list [ftree] 0;
         Format.print_flush ()
      end

   let rec stringlist_to_string stringlist =
      match stringlist with
         [] -> "."
       | f::r ->
            let  rest_s = stringlist_to_string r in
            (f^"."^rest_s)

   let rec print_stringlist slist =
      match slist with
         [] ->
            Format.print_string ""
       | f::r ->
            begin
               Format.print_string (f^".");
               print_stringlist r
            end

   let rec pp_bproof_list tree_list tab =
      let rec pp_bproof ftree new_tab =
         let dummy = String.make (new_tab-2) ' ' in
         match ftree with
            BEmpty -> Format.print_string ""
          | CNode((c1,c2)) ->
               begin
                  Format.open_box 0;
                  Format.force_newline ();
                  Format.print_break (new_tab-10) 0;
                  Format.open_box 0;
                  Format.force_newline ();
                  Format.print_string (dummy^"CloseNode: connection = ("^c1^","^c2^")");
                  Format.print_flush();
(*      Format.force_newline ();
   Format.print_break 0 3;
*)
                  Format.open_box 0;
                  Format.print_break new_tab 0;
                  Format.print_flush()
               end
          | AtNode(posname,(c1,c2)) ->
               begin
                  Format.open_box 0;
                  Format.force_newline ();
                  Format.print_break (new_tab-10) 0;
                  Format.open_box 0;
                  Format.force_newline ();
                  Format.print_string (dummy^"AtNode: pos = "^posname^" conneciton = ("^c1^","^c2^")");
                  Format.print_flush();
(*      Format.force_newline ();
   Format.print_break 0 3;
*)
                  Format.open_box 0;
                  Format.print_break new_tab 0;
                  Format.print_flush()
               end
          | RNode(alpha_layer,bproof) ->
               let alpha_string = stringlist_to_string alpha_layer in
               begin
                  Format.open_box 0;
                  Format.force_newline ();
                  Format.print_break new_tab 0;
                  Format.print_break 0 0;
                  Format.force_newline ();
                  Format.print_flush();
                  Format.open_box 0;
                  print_string (dummy^"RootNode: "^alpha_string);
                  Format.print_flush();
                  Format.open_box 0;
                  Format.print_break 0 0;
                  Format.print_flush();
                  pp_bproof_list [bproof] (new_tab-3)
               end
          | BNode(posname,(alph1,bproof1),(alph2,bproof2)) ->
               let alpha_string1 = stringlist_to_string alph1
               and alpha_string2 = stringlist_to_string alph2 in
               begin
                  Format.open_box 0;
                  Format.force_newline ();
                  Format.print_break new_tab 0;
                  Format.print_break 0 0;
                  Format.force_newline ();
                  Format.print_flush();
                  Format.open_box 0;
                  print_string (dummy^"BetaNode: pos = "^posname^" layer1 = "^alpha_string1^" layer2 = "^alpha_string2);
                  Format.print_flush();
                  Format.open_box 0;
                  Format.print_break 0 0;
                  Format.print_flush();
                  pp_bproof_list [bproof1;bproof2] (new_tab-3)
               end
      in
      let new_tab = tab+5 in
      match tree_list with
         [] -> Format.print_string ""
       | first::rest ->
            begin
               pp_bproof first new_tab;
               pp_bproof_list rest tab
            end

   let rec print_pairlist pairlist =
      match pairlist with
         [] -> Format.print_string ""
       | (a,b)::rest ->
            begin
               Format.print_break 1 1;
               Format.print_string ("("^a^","^b^")");
               print_pairlist rest
            end

   let print_beta_proof bproof =
      begin
         Format.open_box 0;
         Format.force_newline ();
         Format.force_newline ();
         Format.print_break 3 0;
         pp_bproof_list [bproof] 0;
         Format.force_newline ();
         Format.force_newline ();
         Format.force_newline ();
         Format.print_flush ()
      end

   let rec print_treelist treelist =
      match treelist with
         [] ->
            print_endline "END";
       | f::r ->
            begin
               print_ftree f;
               Format.open_box 0;
               print_endline "";
               print_endline "";
               print_endline "NEXT TREE";
               print_endline "";
               print_endline "";
               print_treelist r;
               Format.print_flush ()
            end

   let rec print_set_list set_list =
      match set_list with
         [] -> ""
       | f::r ->
            (f.aname)^" "^(print_set_list r)

   let print_set  set =
      let set_list = AtomSet.elements set in
      if set_list = [] then "empty"
      else
         print_set_list set_list

   let print_string_set  set =
      let set_list = StringSet.elements set in
      print_stringlist set_list

   let rec print_list_sets list_of_sets =
      match list_of_sets with
         [] -> Format.print_string ""
       | (pos,fset)::r ->
            begin
               Format.print_string (pos^": ");   (* first element = node which successors depend on *)
               print_stringlist (StringSet.elements fset);
               Format.force_newline ();
               print_list_sets r
            end

   let print_ordering list_of_sets =
      begin
         Format.open_box 0;
         print_list_sets list_of_sets;
         Format.print_flush ()
      end

   let rec print_triplelist triplelist =
      match triplelist with
         [] -> Format.print_string ""
       | ((a,b),i)::rest ->
            begin
               Format.print_break 1 1;
               Format.print_string ("(("^a^","^b^"),"^(string_of_int i)^")");
               print_triplelist rest
            end

   let print_pos_n  pos_n =
      Format.print_int pos_n

   let print_formula_info ftree ordering pos_n =
      begin
         print_ftree ftree;
         Format.open_box 0;
         Format.force_newline ();
         print_ordering ordering;
         Format.force_newline ();
         Format.force_newline ();
         Format.print_string "number of positions: ";
         print_pos_n pos_n;
         Format.force_newline ();
         print_endline "";
         print_endline "";
         Format.print_flush ()
      end

(* print sequent proof tree *)

   let pp_rule (pos,r,formula,term) tab =
      let rep = ruletable r in
      if List.mem rep ["Alll";"Allr";"Exl";"Exr"] then
         begin
            Format.open_box 0;
(*          Format.force_newline (); *)
            Format.print_break tab 0;
            Format.print_string (pos^": "^rep^" ");
            Format.print_flush ();
(*          Format.print_break tab 0;
   Format.force_newline ();
   Format.print_break tab 0;
*)

            Format.open_box 0;
            print_term stdout formula;
            Format.print_flush ();
            Format.open_box 0;
            Format.print_string "  ";
            Format.print_flush ();
            Format.open_box 0;
            print_term stdout term;
            Format.force_newline ();
            Format.force_newline ();
            Format.print_flush ()
         end
      else
         begin
            Format.open_box 0;
            Format.print_break tab 0;
            Format.print_string (pos^": "^rep^" ");
            Format.print_flush ();
            Format.open_box 0;
(*          Format.print_break tab 0; *)
            Format.force_newline ();
(*          Format.print_break tab 0; *)
            print_term stdout formula;
            Format.force_newline ()
         end

   let last addr =
      if addr = ""
      then ""
      else
         String.make 1 (String.get addr (String.length addr-1))

   let rest addr =
      if addr = ""
      then ""
      else
         String.sub addr 0 ((String.length addr) - 1)

   let rec get_r_chain addr =
      if addr = "" then
         0
      else
         let l = last addr in
         if l = "l" then
            0
         else (* l = "r" *)
            let rs = rest addr in
            1 + (get_r_chain rs)

   let rec tpp seqtree tab addr =
      match seqtree with
       | PEmpty -> raise jprover_bug
       | PNodeAx(rule) ->
            let (pos,r,p,pa) = rule in
            begin
               pp_rule (pos,r,p,pa) tab;
(*      Format.force_newline (); *)
(*      let mult = get_r_chain addr in  *)
(*        Format.print_break 100 (tab - (3 * mult)) *)
            end
       | PNodeA(rule,left) ->
            let (pos,r,p,pa) = rule in
            begin
               pp_rule (pos,r,p,pa) tab;
               tpp left tab addr
            end
       | PNodeB(rule,left,right) ->
            let (pos,r,p,pa) = rule in
            let newtab = tab + 3 in
            begin
               pp_rule (pos,r,p,pa) tab;
(*             Format.force_newline (); *)
(*             Format.print_break 100 newtab; *)
               (tpp left newtab (addr^"l"));
               (tpp right newtab (addr^"r"))
            end

   let tt seqtree =
      begin
         Format.open_box 0;
         tpp seqtree 0 "";
         Format.force_newline ();
         Format.close_box ();
         Format.print_newline ()
      end

(************ END printing functions  *********************************)

(************ Beta proofs and redundancy deletion **********************)

   let rec remove_dups_connections connection_list =
      match connection_list with
         [] -> []
       | (c1,c2)::r ->
            if (List.mem (c1,c2) r) or (List.mem (c2,c1) r) then
  (* only one direction variant of a connection stays *)
               remove_dups_connections r
            else
               (c1,c2)::(remove_dups_connections r)

   let rec remove_dups_list list =
      match list with
         [] -> []
       | f::r ->
            if List.mem f  r then
               remove_dups_list r
            else
               f::(remove_dups_list r)

   let beta_pure alpha_layer connections beta_expansions =
      let (l1,l2) = List.split connections in
      let test_list = l1 @ l2 @ beta_expansions in
      begin
(*       Format.open_box 0;
         print_endline "";
         print_stringlist alpha_layer;
         Format.print_flush();
         Format.open_box 0;
         print_endline "";
         print_stringlist test_list;
         print_endline "";
         Format.print_flush();
*)
         not (List.exists (fun x -> (List.mem x test_list)) alpha_layer)
      end

   let rec apply_bproof_purity  bproof =
      match bproof with
         BEmpty ->
            raise jprover_bug
       | CNode((c1,c2)) ->
            bproof,[(c1,c2)],[]
       | AtNode(_,(c1,c2)) ->
            bproof,[(c1,c2)],[]
       | RNode(alpha_layer,subproof) ->
            let (opt_subproof,min_connections,beta_expansions) =
               apply_bproof_purity  subproof in
            (RNode(alpha_layer,opt_subproof),min_connections,beta_expansions)
       | BNode(pos,(alph1,subp1),(alph2,subp2)) ->
            let (opt_subp1,min_conn1,beta_exp1) = apply_bproof_purity subp1 in
            if beta_pure alph1 min_conn1 beta_exp1 then
               begin
(*       print_endline ("Left layer of "^pos); *)
                  (opt_subp1,min_conn1,beta_exp1)
               end
            else
               let (opt_subp2,min_conn2,beta_exp2) = apply_bproof_purity subp2 in
               if beta_pure alph2 min_conn2 beta_exp2 then
                  begin
(*       print_endline ("Right layer of "^pos); *)
                     (opt_subp2,min_conn2,beta_exp2)
                  end
               else
                  let min_conn = remove_dups_connections (min_conn1 @ min_conn2)
                  and beta_exp = remove_dups_list ([pos] @ beta_exp1 @ beta_exp2) in
                  (BNode(pos,(alph1,opt_subp1),(alph2,opt_subp2)),min_conn,beta_exp)

   let bproof_purity bproof =
      let (opt_bproof,min_connections,_) = apply_bproof_purity bproof in
      opt_bproof,min_connections

(*********** split permutation *****************)

   let rec apply_permutation bproof rep_name direction act_blayer =
      match bproof with
         BEmpty | RNode(_,_) ->
            raise jprover_bug
       | AtNode(cx,(c1,c2)) ->
            bproof,act_blayer
       | CNode((c1,c2)) ->
            bproof,act_blayer
       | BNode(pos,(alph1,subp1),(alph2,subp2)) ->
            if rep_name = pos then
               let (new_blayer,replace_branch) =
                  if direction = "left" then
                     (alph1,subp1)
                  else (* direciton = "right" *)
                     (alph2,subp2)
               in
               (match replace_branch with
                  CNode((c1,c2)) ->
                     (AtNode(c1,(c1,c2))),new_blayer (* perform atom expansion at c1 *)
                | _ ->
                     replace_branch,new_blayer
               )
            else
               let pproof1,new_blayer1 = apply_permutation subp1 rep_name direction act_blayer in
               let pproof2,new_blayer2 = apply_permutation subp2 rep_name direction new_blayer1 in
               (BNode(pos,(alph1,pproof1),(alph2,pproof2))),new_blayer2

   let split_permutation pname opt_bproof =
      match opt_bproof with
         RNode(alayer,BNode(pos,(alph1,opt_subp1),(alph2,opt_subp2))) ->
            if pos = pname then
(* if topmost beta expansion agrees with pname, then *)
(* only split the beta proof and give back the two subproofs *)
               let (osubp1,min_con1) = bproof_purity opt_subp1
               and (osubp2,min_con2) = bproof_purity opt_subp2 in
(* there will be no purity reductions in the beta subproofs. We use this *)
(* predicate to collect the set of used leaf-connections in each subproof*)
               ((RNode((alayer @ alph1),osubp1),min_con1),
                (RNode((alayer @ alph2),osubp2),min_con2)
               )
(* we combine the branch after topmost beta expansion at pos into one root alpha layer *)
(* -- the beta expansion node pos will not be needed in this root layer *)
            else
               let perm_bproof1,balph1 = apply_permutation
                     (BNode(pos,(alph1,opt_subp1),(alph2,opt_subp2))) pname "left" []
               and perm_bproof2,balph2 = apply_permutation
                     (BNode(pos,(alph1,opt_subp1),(alph2,opt_subp2))) pname "right" [] in

               begin
(*                print_endline " ";
                  print_beta_proof perm_bproof1;
                  print_endline" " ;
                  print_beta_proof perm_bproof2;
                  print_endline" ";
*)
                  let (osubp1,min_con1) = bproof_purity perm_bproof1
                  and (osubp2,min_con2) = bproof_purity perm_bproof2 in
                  ((RNode((alayer @ balph1),osubp1),min_con1),
                   (RNode((alayer @ balph2),osubp2),min_con2)
                  )
               end
(* we combine the branch after the NEW topmost beta expansion at bpos *)
(* into one root alpha layer -- the beta expansion node bpos will not be *)
(* needed in this root layer *)
       | _ ->
            raise jprover_bug

(*********** END split permutation *****************)

   let rec list_del list_el el_list  =
      match el_list with
         [] ->
            raise jprover_bug
       | f::r ->
            if list_el = f then
               r
            else
               f::(list_del list_el r)

   let rec list_diff del_list check_list =
      match del_list with
         [] ->
            []
       | f::r ->
            if List.mem f check_list then
               list_diff r check_list
            else
               f::(list_diff r check_list)

(* let rec compute_alpha_layer ftree_list =
      match ftree_list with
         [] ->
            [],[],[]
       | f::r ->
            (match f with
               Empty ->
                  raise jprover_bug
             | NodeAt(pos) ->
                  let pn = pos.name
                  and (rnode,ratom,borderings) = compute_alpha_layer r in
                  ((pn::rnode),(pn::ratom),borderings)
             | NodeA(pos,suctrees) ->
                  let pn = pos.name in
                  if pos.pt = Beta then
                     let (rnode,ratom,borderings) = compute_alpha_layer r in
                     ((pn::rnode),(ratom),(f::borderings))
                  else
                     let suclist = Array.to_list suctrees in
                     compute_alpha_layer (suclist @ r)
            )

   let rec compute_connection alpha_layer union_atoms connections =
      match connections with
         [] -> ("none","none")
       | (c,d)::r ->
            if (List.mem c union_atoms) & (List.mem d union_atoms) then
               let (c1,c2) =
                  if List.mem c alpha_layer then
                     (c,d)
                  else
                     if List.mem d alpha_layer then
                        (d,c) (* then, d is supposed to occur in [alpha_layer] *)
                     else
                        raise (Invalid_argument "Jprover bug: connection match failure")
               in
               (c1,c2)
            else
               compute_connection alpha_layer union_atoms r

   let get_beta_suctrees btree =
      match btree with
         Empty | NodeAt(_) -> raise jprover_bug
       | NodeA(pos,suctrees) ->
            let b1tree = suctrees.(0)
            and b2tree = suctrees.(1) in
            (pos.name,b1tree,b2tree)

   let rec build_beta_proof alpha_layer union_atoms beta_orderings connections =
      let (c1,c2) = compute_connection alpha_layer union_atoms connections in
(* [c1] is supposed to occur in the lowmost alpha layer of the branch, *)
(* i.e. [aplha_layer] *)
      if (c1,c2) = ("none","none") then
         (match beta_orderings with
            [] -> raise jprover_bug
          | btree::r ->
               let (beta_pos,suctree1,suctree2) = get_beta_suctrees btree in
               let (alpha_layer1, atoms1, bordering1) = compute_alpha_layer [suctree1]
               and (alpha_layer2, atoms2, bordering2) = compute_alpha_layer [suctree2] in
               let bproof1,beta1,closure1 =
                  build_beta_proof alpha_layer1 (atoms1 @ union_atoms)
                     (bordering1 @ r) connections
               in
               let bproof2,beta2,closure2 =
                  build_beta_proof alpha_layer2 (atoms2 @ union_atoms)
                     (bordering2 @ r) connections in
               (BNode(beta_pos,(alpha_layer1,bproof1),(alpha_layer2,bproof2))),(1+beta1+beta2),(closure1+closure2)
         )
      else
         CNode((c1,c2)),0,1

   let construct_beta_proof ftree connections =
      let (root_node,root_atoms,beta_orderings) = compute_alpha_layer [ftree]
      in
      let beta_proof,beta_exp,closures =
         build_beta_proof root_node root_atoms beta_orderings connections in
      (RNode(root_node,beta_proof)),beta_exp,closures
*)


(* *********** New Version with direct computation from extension proof **** *)
(* follows a DIRECT step from proof histories via pr-connection orderings to opt. beta-proofs *)

   let rec compute_alpha_layer ftree_list =
      match ftree_list with
         [] ->
            []
       | f::r ->
            (match f with
               Empty ->
                  raise jprover_bug
             | NodeAt(pos) ->
                  let rnode = compute_alpha_layer r in
                  (pos.name::rnode)
             | NodeA(pos,suctrees) ->
                  if pos.pt = Beta then
                     let rnode = compute_alpha_layer r in
                     (pos.name::rnode)
                  else
                     let suclist = Array.to_list suctrees in
                     compute_alpha_layer (suclist @ r)
            )

   let rec compute_beta_difference c1_context c2_context act_context =
      match c1_context,c2_context with
         ([],c2_context) ->
            (list_diff c2_context act_context)
(* both connection partners in the same submatrix; [c1] already isolated *)
       | ((fc1::rc1),[]) ->
            []  (* [c2] is a reduction step, i.e. isolated before [c1] *)
       | ((fc1::rc1),(fc2::rc2)) ->
            if fc1 = fc2 then    (* common initial beta-expansions *)
               compute_beta_difference rc1 rc2 act_context
            else
               (list_diff c2_context act_context)

   let rec non_closed beta_proof_list =
      match beta_proof_list with
         [] ->
            false
       | bpf::rbpf ->
            (match bpf with
               RNode(_,_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
             | AtNode(_,_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
             | BEmpty -> true
             | CNode(_) -> non_closed rbpf
             | BNode(pos,(_,bp1),(_,bp2)) -> non_closed ([bp1;bp2] @ rbpf)
            )

   let rec cut_context pos context =
      match context with
         [] ->
            raise (Invalid_argument "Jprover bug: invalid context element")
       | (f,num)::r ->
            if pos = f then
               context
            else
               cut_context pos r

   let compute_tree_difference beta_proof c1_context =
      match beta_proof with
         RNode(_,_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
       | CNode(_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
       | AtNode(_,_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
       | BEmpty -> c1_context
       | BNode(pos,_,_) ->
(*    print_endline ("actual root: "^pos); *)
            cut_context pos c1_context

   let print_context conn bcontext =
      begin
         Format.open_box 0;
         Format.print_string conn;
         Format.print_string ":    ";
         List.iter (fun x -> let (pos,num) = x in Format.print_string (pos^" "^(string_of_int num)^"")) bcontext;
         print_endline " ";
         Format.print_flush ()
      end

   let rec build_opt_beta_proof beta_proof ext_proof beta_atoms beta_layer_list act_context =
      let rec add_c2_tree (c1,c2) c2_diff_context =
         match c2_diff_context with
            [] ->
               (CNode(c1,c2),0)
          | (f,num)::c2_diff_r ->
               let next_beta_proof,next_exp =
                  add_c2_tree (c1,c2) c2_diff_r in
               let (layer1,layer2) = List.assoc f beta_layer_list in
               let new_bproof =
                  if num = 1 then
                     BNode(f,(layer1,next_beta_proof),(layer2,BEmpty))
                  else (* num = 2*)
                     BNode(f,(layer1,BEmpty),(layer2,next_beta_proof))
               in
               (new_bproof,(next_exp+1))
      in
      let rec add_beta_expansions (c1,c2) rest_ext_proof c1_diff_context c2_diff_context new_act_context =
         match c1_diff_context with
            [] ->
               let (n_c1,n_c2) =
                  if c2_diff_context = [] then  (* make sure that leaf-connection is first element *)
                     (c1,c2)
                  else
                     (c2,c1)
               in
               let c2_bproof,c2_exp = add_c2_tree (n_c1,n_c2) c2_diff_context in
               if c2_exp <> 0 then (* at least one open branch was generated to isloate [c2] *)
                  begin
(*   print_endline "start with new beta-proof"; *)
                     let new_bproof,new_exp,new_closures,new_rest_proof  =
                        build_opt_beta_proof c2_bproof rest_ext_proof beta_atoms beta_layer_list (act_context @ new_act_context) in
                     (new_bproof,(new_exp+c2_exp),(new_closures+1),new_rest_proof)
                  end
               else
                  begin
(*   print_endline "proceed with old beta-proof"; *)
                     (c2_bproof,c2_exp,1,rest_ext_proof)
                  end
          | (f,num)::c1_diff_r ->
               let (layer1,layer2) = List.assoc f beta_layer_list in
               let next_beta_proof,next_exp,next_closures,next_ext_proof =
                  add_beta_expansions (c1,c2) rest_ext_proof c1_diff_r c2_diff_context new_act_context in
               let new_bproof =
                  if num = 1 then
                     BNode(f,(layer1,next_beta_proof),(layer2,BEmpty))
                  else (* num = 2*)
                     BNode(f,(layer1,BEmpty),(layer2,next_beta_proof))
               in
               (new_bproof,(next_exp+1),next_closures,next_ext_proof)

      in
      let rec insert_connection beta_proof (c1,c2) rest_ext_proof c1_diff_context c2_diff_context act_context =
         begin
(*   print_context c1 c1_diff_context;
   print_endline "";
   print_context c2 c2_diff_context;
   print_endline "";
*)
            match beta_proof with
               RNode(_,_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
             | CNode(_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
             | AtNode(_,_) -> raise (Invalid_argument "Jprover bug: invalid beta-proof")
             | BEmpty ->
                  add_beta_expansions (c1,c2) rest_ext_proof c1_diff_context c2_diff_context act_context
             | BNode(pos,(layer1,sproof1),(layer2,sproof2)) ->
(*   print_endline (c1^" "^c2^" "^pos); *)
                  (match c1_diff_context with
                     [] ->
                        raise (Invalid_argument "Jprover bug: invalid beta-proof")
                   | (f,num)::rest_context -> (* f = pos must hold!! *)
                        if num = 1 then
                           let (next_bproof,next_exp,next_closure,next_ext_proof) =
                              insert_connection sproof1 (c1,c2) rest_ext_proof rest_context c2_diff_context act_context in
                           (BNode(pos,(layer1,next_bproof),(layer2,sproof2)),next_exp,next_closure,next_ext_proof)
                        else (* num = 2 *)
                           let (next_bproof,next_exp,next_closure,next_ext_proof) =
                              insert_connection sproof2 (c1,c2) rest_ext_proof rest_context c2_diff_context act_context in
                           (BNode(pos,(layer1,sproof1),(layer2,next_bproof)),next_exp,next_closure,next_ext_proof)
                  )
         end

      in
      match ext_proof with
         [] ->
            beta_proof,0,0,[]
       | (c1,c2)::rproof ->
(*  print_endline ("actual connection: "^c1^" "^c2); *)
            let c1_context = List.assoc c1 beta_atoms
            and c2_context = List.assoc c2 beta_atoms in
            let c2_diff_context = compute_beta_difference c1_context c2_context act_context
            and c1_diff_context = compute_tree_difference beta_proof c1_context in (* wrt. actual beta-proof *)
            let (next_beta_proof,next_exp,next_closures,next_ext_proof) =
               insert_connection beta_proof (c1,c2) rproof c1_diff_context c2_diff_context c1_diff_context in
            if non_closed [next_beta_proof] then  (* at least one branch was generated to isolate [c1] *)
               let rest_beta_proof,rest_exp,rest_closures,rest_ext_proof =
                  build_opt_beta_proof next_beta_proof next_ext_proof beta_atoms beta_layer_list act_context in
               rest_beta_proof,(next_exp+rest_exp),(next_closures+rest_closures),rest_ext_proof
            else
               next_beta_proof,next_exp,next_closures,next_ext_proof

   let rec annotate_atoms beta_context atlist treelist =
      let rec annotate_tree beta_context tree atlist =
         match tree with
            Empty ->
               (atlist,[],[])
          | NodeAt(pos) ->
               if List.mem pos.name atlist then
                  let new_atlist = list_del pos.name atlist in
                  (new_atlist,[(pos.name,beta_context)],[])
               else
                  (atlist,[],[])
          | NodeA(pos,suctrees) ->
               if pos.pt = Beta then
                  let s1,s2 = suctrees.(0),suctrees.(1) in
                  let alayer1 = compute_alpha_layer [s1]
                  and alayer2 = compute_alpha_layer [s2]
                  and new_beta_context1 = beta_context @ [(pos.name,1)]
                  and new_beta_context2 = beta_context @ [(pos.name,2)] in
                  let atlist1,annotates1,blayer_list1 =
                     annotate_atoms new_beta_context1 atlist [s1] in
                  let atlist2,annotates2,blayer_list2 =
                     annotate_atoms new_beta_context2 atlist1 [s2]
                  in
                  (atlist2,(annotates1 @ annotates2),((pos.name,(alayer1,alayer2))::(blayer_list1 @ blayer_list2)))
               else
                  annotate_atoms beta_context atlist (Array.to_list suctrees)
      in
      match treelist with
         [] -> (atlist,[],[])
       | f::r ->
            let (next_atlist,f_annotates,f_beta_layers) = annotate_tree beta_context f atlist in
            let (rest_atlist,rest_annotates,rest_beta_layers) = (annotate_atoms beta_context next_atlist r)
            in
            (rest_atlist, (f_annotates  @ rest_annotates),(f_beta_layers @ rest_beta_layers))

   let construct_opt_beta_proof ftree ext_proof =
      let con1,con2 = List.split ext_proof in
      let con_atoms = remove_dups_list (con1 @ con2) in
      let (empty_atoms,beta_atoms,beta_layer_list) = annotate_atoms [] con_atoms [ftree] in
      let root_node = compute_alpha_layer [ftree] in
      let (beta_proof,beta_exp,closures,_) =
         build_opt_beta_proof BEmpty ext_proof beta_atoms beta_layer_list [] in
      (RNode(root_node,beta_proof)),beta_exp,closures

(************* permutation ljmc -> lj *********************************)

(* REAL PERMUTATION STAFF *)

   let subf1 n m  subrel = List.mem ((n,m),1) subrel
   let subf2 n m  subrel = List.mem ((n,m),2) subrel
   let tsubf n m  tsubrel = List.mem (n,m) tsubrel

(* Transforms all normal form layers in an LJ proof *)

   let rec modify prooftree (subrel,tsubrel) =
      match prooftree with
         PEmpty ->
            raise jprover_bug
       | PNodeAx((pos,inf,form,term)) ->
            prooftree,pos
       | PNodeA((pos,inf,form,term),left)  ->
            let t,qpos = modify left (subrel,tsubrel) in
            if List.mem inf [Impr;Negr;Allr] then
               PNodeA((pos,inf,form,term),t),pos    (* layer bound *)
            else if qpos = "Orl-True" then
               PNodeA((pos,inf,form,term),t),qpos
            else if List.mem inf [Andl;Alll;Exl] then
               PNodeA((pos,inf,form,term),t),qpos  (* simply propagation *)
            else if inf = Exr then
               if (subf1 pos qpos subrel) then
                  PNodeA((pos,inf,form,term),t),pos
               else t,qpos
            else if inf = Negl then
               if (subf1 pos qpos subrel) then
                  PNodeA((pos,inf,form,term),t),""  (* empty string *)
               else t,qpos
            else                     (* x = Orr *)
               if (subf1 pos qpos subrel) then
                  PNodeA((pos,Orr1,form,term),t),pos    (* make Orr for LJ *)
               else if (subf2 pos qpos subrel) then
                  PNodeA((pos,Orr2,form,term),t),pos     (* make Orr for LJ *)
               else t,qpos
       | PNodeB((pos,inf,form,term),left,right) ->
            let t,qpos = modify left (subrel,tsubrel) in
            if inf = Andr then
               if (or) (qpos = "Orl-True") (subf1 pos qpos subrel) then
                  let s,rpos = modify right (subrel,tsubrel) in  (* Orl-True -> subf *)
                  if (or) (rpos = "Orl-True") (subf2 pos rpos subrel) then
                     PNodeB((pos,inf,form,term),t,s),pos
                  else s,rpos
               else t,qpos                (* not subf -> not Orl-True *)
            else if inf = Impl then
               if  (subf1 pos qpos subrel) then
                  let s,rpos = modify right (subrel,tsubrel) in
                  PNodeB((pos,inf,form,term),t,s),"" (* empty string *)
               else t,qpos
            else                           (* x = Orl *)
               let s,rpos = modify right (subrel,tsubrel) in
               PNodeB((pos,inf,form,term),t,s),"Orl-True"

(* transforms the subproof into an LJ proof between
   the beta-inference rule (excluded) and
   layer boundary in the branch ptree *)

   let rec rec_modify ptree (subrel,tsubrel) =
      match ptree with
         PEmpty ->
            raise jprover_bug
       | PNodeAx((pos,inf,form,term)) ->
            ptree,pos
       | PNodeA((pos,inf,form,term),left)  ->
            if List.mem inf [Impr;Negr;Allr] then
               ptree,pos    (* layer bound, stop transforming! *)
            else
               let t,qpos = rec_modify left (subrel,tsubrel) in
               if List.mem inf [Andl;Alll;Exl] then
                  PNodeA((pos,inf,form,term),t),qpos   (* simply propagation*)
               else if inf = Exr then
                  if (subf1 pos qpos subrel) then
                     PNodeA((pos,inf,form,term),t),pos
                  else t,qpos
               else if inf = Negl then
                  if (subf1 pos qpos subrel) then
                     PNodeA((pos,inf,form,term),t),""  (* empty string *)
                  else t,qpos
               else                     (* x = Orr *)
                  if (subf1 pos qpos subrel) then
                     PNodeA((pos,Orr1,form,term),t),pos    (* make Orr for LJ *)
                  else if (subf2 pos qpos subrel) then
                     PNodeA((pos,Orr2,form,term),t),pos     (* make Orr for LJ *)
                  else t,qpos
       | PNodeB((pos,inf,form,term),left,right) ->
            let t,qpos = rec_modify left (subrel,tsubrel) in
            if inf = Andr then
               if (subf1 pos qpos subrel) then
                  let s,rpos = rec_modify right (subrel,tsubrel) in
                  if (subf2 pos rpos subrel) then
                     PNodeB((pos,inf,form,term),t,s),pos
                  else s,rpos
               else t,qpos
            else (* x = Impl since x= Orl cannot occur in the partial layer ptree *)

               if  (subf1 pos qpos subrel) then
                  let s,rpos = rec_modify right (subrel,tsubrel) in
                  PNodeB((pos,inf,form,term),t,s),"" (* empty string *)
               else t,qpos

   let weak_modify rule ptree (subrel,tsubrel) =   (* recall rule = or_l  *)
      let (pos,inf,formlua,term) = rule in
      if inf = Orl then
         ptree,true
      else
         let ptreem,qpos = rec_modify ptree (subrel,tsubrel) in
         if (subf1 pos qpos subrel) then  (* weak_modify will always be applied on left branches *)
            ptreem,true
         else
            ptreem,false

(* Now, the permutation stuff .... *)

(* Permutation schemes *)

(* corresponds to local permutation lemma -- Lemma 3 in the paper -- *)
(* with eigenvariablen renaming and branch modification *)

(* eigenvariablen renaming and branch modification over *)
(* the whole proofs, i.e. over layer boundaries, too *)


(* global variable vor eigenvariable renaming during permutations *)

   let eigen_counter = ref 1

(* append renamed paramater "r" to non-quantifier subformulae
   of renamed quantifier formulae *)

   let make_new_eigenvariable term =
      let op = (dest_term term).term_op in
      let opa = (dest_op op).op_params in
      let oppar = dest_param opa in
      match oppar with
         | String ofname::_ ->
            let new_eigen_var = (ofname^"_r"^(string_of_int (!eigen_counter))) in
            eigen_counter := !eigen_counter + 1;
            mk_string_term jprover_op new_eigen_var
         | _ -> raise jprover_bug


   let replace_subterm term oldt rept  =
      let v_term = var_subst term oldt "dummy_var" in
      subst1 v_term "dummy_var" rept

   let rec eigen_rename old_parameter new_parameter ptree =
      match ptree with
         PEmpty ->
            raise jprover_bug
       | PNodeAx((pos,inf,form,term)) ->
            let new_form = replace_subterm form old_parameter new_parameter in
            PNodeAx((pos,inf,new_form,term))
       | PNodeA((pos,inf,form,term), left) ->
            let new_form = replace_subterm form old_parameter new_parameter
            and new_term = replace_subterm term old_parameter new_parameter in
            let ren_left = eigen_rename old_parameter new_parameter left in
            PNodeA((pos,inf,new_form,new_term), ren_left)
       | PNodeB((pos,inf,form,term),left, right) ->
            let new_form = replace_subterm form old_parameter new_parameter in
            let ren_left  = eigen_rename old_parameter new_parameter left  in
            let ren_right  = eigen_rename old_parameter new_parameter right  in
            PNodeB((pos,inf,new_form,term), ren_left, ren_right)

   let rec update_ptree rule subtree direction tsubrel =
      match subtree with
         PEmpty ->
            raise jprover_bug
       | PNodeAx(r) ->
            subtree
       | PNodeA((pos,inf,formula,term), left) ->
            if (pos,inf,formula,term) = rule then
               left
          (* don't delete rule if subformula belongs to renamed instance of quantifiers; *)
          (* but this can never occur now since (renamed) formula is part of rule *)
            else
               let (posn,infn,formn,termn) = rule in
               if (&) (List.mem infn [Exl;Allr] ) (term = termn) then
    (* this can only occur if eigenvariable rule with same term as termn has been permuted; *)
    (* the application of the same eigenvariable introduction on the same subformula with *)
    (* different instantiated variables might occur! *)
    (* termn cannot occur in terms of permuted quantifier rules due to substitution split *)
    (* during reconstruciton of the ljmc proof *)
                  let new_term =  make_new_eigenvariable term in
(*              print_endline "Eigenvariable renaming!!!"; *)
                  eigen_rename termn new_term subtree
               else
                  let left_del =
                     update_ptree rule left direction tsubrel
                  in
                  PNodeA((pos,inf,formula,term), left_del)
       | PNodeB((pos,inf,formula,term), left, right) ->
            if (pos,inf,formula,term) = rule then
               if direction = "l" then
                  left
               else
                  right   (* direction = "r" *)
            else
               let left_del = update_ptree rule left direction tsubrel in
               let right_del = update_ptree rule right direction tsubrel in
               PNodeB((pos,inf,formula,term),left_del,right_del)

   let permute r1 r2 ptree  la tsubrel =
(*  print_endline "permute in"; *)
      match ptree,la with
         PNodeA(r1, PNodeA(r2,left)),la ->
(*        print_endline "1-o-1";   *)
            PNodeA(r2, PNodeA(r1,left))
                                     (* one-over-one *)
       | PNodeA(r1, PNodeB(r2,left,right)),la ->
(*        print_endline "1-o-2";   *)
            PNodeB(r2, PNodeA(r1,left), PNodeA(r1,right))
                                     (* one-over-two *)
       | PNodeB(r1, PNodeA(r2,left), right),"l" ->
(*        print_endline "2-o-1 left";   *)
            let right_u = update_ptree r2 right "l" tsubrel in
            PNodeA(r2, PNodeB(r1, left, right_u))
                                     (* two-over-one left *)
       | PNodeB(r1, left, PNodeA(r2,right)),"r" ->
(*        print_endline "2-o-1 right";   *)
            let left_u = update_ptree r2 left "l" tsubrel in
            PNodeA(r2, PNodeB(r1, left_u, right))
                                     (* two-over-one right *)
       | PNodeB(r1, PNodeB(r2,left2,right2), right),"l" ->
(*        print_endline "2-o-2 left"; *)
            let right_ul = update_ptree r2 right "l" tsubrel in
            let right_ur  = update_ptree  r2 right "r" tsubrel in
            PNodeB(r2,PNodeB(r1,left2,right_ul),PNodeB(r1,right2,right_ur))
                                     (* two-over-two left *)
       | PNodeB(r1, left, PNodeB(r2,left2,right2)),"r" ->
(*        print_endline "2-o-2 right"; *)
            let left_ul = update_ptree r2 left "l" tsubrel in
            let left_ur  = update_ptree  r2 left "r"  tsubrel in
            PNodeB(r2,PNodeB(r1,left_ul,left2),PNodeB(r1,left_ur, right2))
                                     (* two-over-two right *)
       | _ -> raise jprover_bug

(* permute layers, isolate addmissible branches *)

(* computes if an Andr is d-generatives *)

   let layer_bound rule =
      let (pos,inf,formula,term) = rule in
      if List.mem inf [Impr;Negr;Allr] then
         true
      else
         false

   let rec orl_free ptree  =
      match ptree with
         PEmpty ->
            raise jprover_bug
       | PNodeAx(rule) ->
            true
       | PNodeA(rule,left) ->
            if layer_bound rule then
               true
            else
               orl_free left
       | PNodeB(rule,left,right) ->
            let (pos,inf,formula,term) =  rule in
            if inf = Orl then
               false
            else
               (&) (orl_free left) (orl_free right)

   let rec dgenerative rule dglist ptree tsubrel =
      let (pos,inf,formula,term) = rule in
      if List.mem inf [Exr;Orr;Negl] then
         true
      else if inf = Andr then
         if dglist = [] then
            false
         else
            let first,rest = (List.hd dglist),(List.tl dglist) in
            let (pos1,inf1,formula1,term1) = first in
            if tsubf pos1 pos tsubrel then
               true
            else
               dgenerative rule rest ptree tsubrel
      else if inf = Impl then
         not (orl_free ptree)
      else
         false


(* to compute a topmost addmissible pair r,o  with
   the address addr of r in the proof tree
*)

   let rec top_addmissible_pair ptree dglist act_r act_o act_addr tsubrel dummyt =
      let rec search_pair ptree dglist act_r act_o act_addr tsubrel =
         match ptree with
            PEmpty -> raise jprover_bug
          | PNodeAx(_) -> raise jprover_bug
          | PNodeA(rule, left) ->
(*      print_endline "alpha"; *)
               if (dgenerative rule dglist left tsubrel) then  (* r = Exr,Orr,Negl *)
                  let newdg = (@) [rule] dglist   in
                  search_pair left newdg act_r rule act_addr tsubrel
               else                   (* Impr, Allr, Notr only for test *)
                  search_pair left dglist act_r act_o act_addr tsubrel
          | PNodeB(rule,left,right) ->
(*      print_endline "beta";  *)
               let (pos,inf,formula,term) = rule in
               if List.mem inf [Andr;Impl] then
                  let bool = dgenerative rule dglist left tsubrel in
                  let newdg,newrule =
                     if bool then
                        ((@) [rule] dglist),rule
                     else
                        dglist,act_o
                  in
                  if orl_free left then
                     search_pair right newdg act_r newrule (act_addr^"r") tsubrel
                  else  (* not orl_free *)
                     let left_r,left_o,left_addr =
                        search_pair left newdg act_r newrule (act_addr^"l") tsubrel in
                     if left_o =  ("",Orr,dummyt,dummyt) then
                        top_addmissible_pair right dglist act_r act_o (act_addr^"r") tsubrel dummyt
                     else  left_r,left_o,left_addr
               else  (* r = Orl *)
                  if orl_free left then
                     top_addmissible_pair right dglist rule act_o (act_addr^"r") tsubrel dummyt
                  else
                     let left_r,left_o,left_addr
                           = search_pair left dglist rule act_o (act_addr^"l") tsubrel in
                     if left_o =  ("",Orr,dummyt,dummyt) then
                        top_addmissible_pair right dglist rule act_o (act_addr^"r") tsubrel dummyt
                     else
                        left_r,left_o,left_addr
      in
(*  print_endline "top_addmissible_pair in"; *)
      if orl_free ptree then                  (* there must be a orl BELOW an layer bound *)
         begin
(*    print_endline "orl_free"; *)
            act_r,act_o,act_addr
         end
      else
         begin
(*    print_endline "orl_full"; *)
            search_pair ptree dglist act_r act_o act_addr tsubrel
         end

   let next_direction addr act_addr =
      String.make 1 (String.get addr (String.length act_addr))
        (* get starts with count 0*)

   let change_last addr d =
      let split = (String.length addr) - 1 in
      let prec,last =
         (String.sub addr 0 split),(String.sub addr split 1) in
      prec^d^last

   let last addr =
      if addr = ""
      then ""
      else
         String.make 1 (String.get addr (String.length addr-1))

   let rest addr =
      if addr = ""
      then ""
      else
         String.sub addr 0 ((String.length addr) - 1)

   let rec permute_layer ptree dglist (subrel,tsubrel) =
      let rec permute_branch r addr act_addr ptree dglist (subrel,tsubrel) =
(*   print_endline "pbranch in"; *)
         let la = last act_addr in  (* no ensure uniqueness at 2-over-x *)
         match ptree,la with
            PNodeA(o,PNodeA(rule,left)),la ->   (* one-over-one *)
(*       print_endline " one-over-one ";                  *)
               let permute_result = permute o rule ptree la tsubrel in
               begin match permute_result with
                  PNodeA(r2,left2) ->
                     let pbleft = permute_branch r addr act_addr left2 dglist (subrel,tsubrel) in
                     PNodeA(r2,pbleft)
                | _ -> raise jprover_bug
               end
          | PNodeA(o,PNodeB(rule,left,right)),la ->                (* one-over-two *)
(*     print_endline " one-over-two ";                  *)
               if rule = r then  (* left,right are or_l free *)
                  permute o rule ptree  la tsubrel (* first termination case *)
               else
                  let d = next_direction addr act_addr in
                  if d = "l" then
                     let permute_result = permute o rule ptree la tsubrel in
                     (match permute_result with
                        PNodeB(r2,left2,right2) ->
                           let pbleft = permute_branch r addr (act_addr^d) left2 dglist (subrel,tsubrel) in
                           let plright = permute_layer right2 dglist (subrel,tsubrel) in
                           PNodeB(r2,pbleft,plright)
                      | _ -> raise jprover_bug
                     )
                  else  (* d = "r", that is left of rule is or_l free *)
                     let left1,bool = weak_modify rule left (subrel,tsubrel) in
                     if bool then  (* rule is relevant *)
                        let permute_result = permute o rule (PNodeA(o,PNodeB(rule,left1,right))) la tsubrel in
                        (match permute_result with
                           PNodeB(r2,left2,right2) ->
                              let pbright = permute_branch r addr (act_addr^d) right2 dglist (subrel,tsubrel) in
                              PNodeB(r2,left2,pbright)
                         | _ -> raise jprover_bug
                        )
                     else          (* rule is not relevant *)
                        PNodeA(o,left1)  (* optimized termination case (1) *)
          | PNodeB(o,PNodeA(rule,left),right1),"l" ->               (* two-over-one, left *)
(*       print_endline " two-over-one, left "; *)
               let permute_result = permute o rule ptree la tsubrel in
               (match permute_result with
                  PNodeA(r2,left2) ->
                     let pbleft = permute_branch r addr act_addr left2 dglist (subrel,tsubrel) in
                     PNodeA(r2,pbleft)
                | _ -> raise jprover_bug
               )
          | PNodeB(o,left1,PNodeA(rule,left)),"r" ->                (* two-over-one, right *)
                                                (* left of o is or_l free *)
(*      print_endline " two-over-one, right"; *)
               let leftm,bool = weak_modify o left1 (subrel,tsubrel) in
               if bool then  (* rule is relevant *)
                  let permute_result = permute o rule (PNodeB(o,leftm,PNodeA(rule,left))) la tsubrel in
                  (match permute_result with
                     PNodeA(r2,left2) ->
                        let pbleft = permute_branch r addr act_addr left2 dglist (subrel,tsubrel) in
                        PNodeA(r2,pbleft)
                   | _ -> raise jprover_bug
                  )
               else          (* rule is not relevant *)
                  leftm  (* optimized termination case (2) *)
          | PNodeB(o,PNodeB(rule,left,right),right1),"l" ->             (* two-over-two, left *)
(*     print_endline " two-over-two, left"; *)
               if rule = r then   (* left,right are or_l free *)
                  let permute_result = permute o rule ptree  la tsubrel in
                  (match permute_result with
                     PNodeB(r2,PNodeB(r3,left3,right3),PNodeB(r4,left4,right4)) ->
(*        print_endline "permute 2-o-2, left ok"; *)
                        let leftm3,bool3 = weak_modify r3 left3 (subrel,tsubrel) in
                        let leftm4,bool4 = weak_modify r4 left4 (subrel,tsubrel) in
                        let plleft,plright =
                           if (&) bool3 bool4 then   (* r3 and r4 are relevant *)
                              (permute_layer (PNodeB(r3,leftm3,right3)) dglist (subrel,tsubrel)),
                              (permute_layer (PNodeB(r4,leftm4,right4)) dglist (subrel,tsubrel))
                           else if (&) bool3 (not bool4) then   (* only r3 is relevant *)
                              begin
(*               print_endline "two-over-two left: bool3 and not bool4"; *)
                                 (permute_layer (PNodeB(r3,leftm3,right3)) dglist (subrel,tsubrel)),
                                 leftm4
                              end
                           else if (&) (not bool3) bool4 then   (* only r4 is relevant *)
                              leftm3,
                              (permute_layer (PNodeB(r4,leftm4,right4)) dglist (subrel,tsubrel))
                           else    (* neither r3 nor r4 are relevant *)
                              leftm3,leftm4
                        in
                        PNodeB(r2,plleft,plright)
                   | _ -> raise jprover_bug
                  )
               else
                  let d = next_direction addr act_addr in
                  let newadd = change_last act_addr d in
                  if d = "l" then
                     let permute_result = permute o rule ptree la tsubrel in
                     (match permute_result with
                        PNodeB(r2,left2,right2) ->
                           let pbleft = permute_branch r addr newadd left2 dglist (subrel,tsubrel) in
                           let plright = permute_layer right2 dglist (subrel,tsubrel) in
                           PNodeB(r2,pbleft,plright)
                      | _ -> raise jprover_bug
                     )
                  else  (* d = "r", that is left is or_l free *)
                     let left1,bool = weak_modify rule left (subrel,tsubrel) in
                     if bool then  (* rule is relevant *)
                        let permute_result =
                           permute o rule (PNodeB(o,PNodeB(rule,left1,right),right1)) la tsubrel in
                        (match permute_result with
                           PNodeB(r2,PNodeB(r3,left3,right3),right2) ->
                              let pbright = permute_branch r addr newadd right2 dglist (subrel,tsubrel) in
                              let leftm3,bool3 = weak_modify r3 left3 (subrel,tsubrel) in
                              let plleft =
                                 if bool3 (* r3 relevant *) then
                                    permute_layer (PNodeB(r3,leftm3,right3)) dglist (subrel,tsubrel)
                                 else  (* r3 redundant *)
                                    leftm3
                              in
                              PNodeB(r2,plleft,pbright)  (* further opt. NOT possible *)
                         | _ -> raise jprover_bug
                        )
                     else          (* rule is not relevant *)
                        permute_layer (PNodeB(o,left1,right1)) dglist (subrel,tsubrel) (* further opt. possible *)
                                                           (* combine with orl_free *)
          | PNodeB(o,left1,PNodeB(rule,left,right)),"r" ->             (* two-over-two, right *)
(*      print_endline " two-over-two, right"; *)
               let leftm1,bool = weak_modify o left1 (subrel,tsubrel) in  (* left1 is or_l free *)
               if bool then  (* o is relevant, even after permutations *)
                  if rule = r then  (* left, right or_l free *)
                     permute o rule (PNodeB(o,leftm1,PNodeB(rule,left,right))) la tsubrel
                  else
                     let d = next_direction addr act_addr in
                     let newadd = change_last act_addr d in
                     if d = "l" then
                        let permute_result  =
                           permute o rule (PNodeB(o,leftm1,PNodeB(rule,left,right))) la tsubrel in
                        (match permute_result with
                                 PNodeB(r2,left2,right2) ->
                              let pbleft = permute_branch r addr newadd left2 dglist (subrel,tsubrel) in
                              let plright = permute_layer right2 dglist (subrel,tsubrel) in
                              PNodeB(r2,pbleft,plright)
                         | _ -> raise jprover_bug
                        )
                     else  (* d = "r", that is left is or_l free *)
                        let leftm,bool = weak_modify rule left (subrel,tsubrel) in
                        if bool then  (* rule is relevant *)
                           let permute_result =
                              permute o rule (PNodeB(o,leftm1,PNodeB(rule,left,right))) la tsubrel in
                           (match permute_result with
                                PNodeB(r2,left2,right2) ->
                                 let pbright = permute_branch r addr newadd right2 dglist (subrel,tsubrel) in
                                 PNodeB(r2,left2,pbright)  (* left2 or_l free *)
                            | _ -> raise jprover_bug
                           )
                        else (* rule is not relevant *)
                           PNodeB(o,leftm1,leftm)

               else
                  leftm1
          | _ -> raise jprover_bug
      in
      let rec trans_add_branch r o addr act_addr ptree dglist (subrel,tsubrel) =
         match ptree with
            (PEmpty| PNodeAx(_)) -> raise jprover_bug
          | PNodeA(rule,left) ->
               if (dgenerative rule dglist left tsubrel) then
                  let newdg = (@) [rule] dglist in
                  if rule = o then
                     begin
(*             print_endline "one-rule is o"; *)
                        permute_branch r addr act_addr ptree dglist (subrel,tsubrel)
                     end
                  else
                     begin
(*             print_endline "alpha - but not o"; *)
                        let tptree = trans_add_branch r o addr act_addr left newdg (subrel,tsubrel) in
                        permute_layer (PNodeA(rule,tptree)) dglist (subrel,tsubrel)
                (* r may not longer be valid for rule *)
                     end
               else
                  let tptree =  trans_add_branch r o addr act_addr left dglist (subrel,tsubrel) in
                  PNodeA(rule,tptree)
          | PNodeB(rule,left,right) ->
               let d = next_direction addr act_addr in
               let bool = (dgenerative rule dglist left tsubrel) in
               if rule = o then
                  begin
(*          print_endline "two-rule is o"; *)
                     permute_branch r addr (act_addr^d) ptree dglist (subrel,tsubrel)
                  end
               else
                  begin
(*         print_endline ("beta - but not o: address "^d); *)
                     let dbranch =
                        if d = "l" then
                           left
                        else   (* d = "r" *)
                           right
                     in
                     let tptree =
                        if bool then
                           let newdg = (@) [rule] dglist in
                           (trans_add_branch r o addr (act_addr^d) dbranch newdg (subrel,tsubrel))
                        else
                           (trans_add_branch r o addr (act_addr^d) dbranch dglist (subrel,tsubrel))
                     in
                     if d = "l" then
                        permute_layer (PNodeB(rule,tptree,right)) dglist (subrel,tsubrel)
                     else  (* d = "r" *)
                        begin
(*            print_endline "prob. a redundant call";  *)
                           let back  = permute_layer (PNodeB(rule,left,tptree)) dglist  (subrel,tsubrel) in
(*             print_endline "SURELY a redundant call"; *)
                           back
                        end
                  end
      in
(*  print_endline "permute_layer in"; *)
      let dummyt = mk_var_term "dummy" in
      let r,o,addr =
         top_addmissible_pair ptree dglist ("",Orl,dummyt,dummyt) ("",Orr,dummyt,dummyt) "" tsubrel dummyt in
      if r = ("",Orl,dummyt,dummyt) then
         ptree
      else  if o = ("",Orr,dummyt,dummyt) then  (* Orr is a dummy for no d-gen. rule *)
         ptree
      else
(*
         let (x1,x2,x3,x4) = r
         and (y1,y2,y3,y4) = o in
   print_endline ("top or_l: "^x1);
   print_endline ("or_l address: "^addr);
   print_endline ("top dgen-rule: "^y1);
*)
         trans_add_branch r o addr "" ptree dglist (subrel,tsubrel)

(* Isolate layer and outer recursion structure *)
(* uses weaker layer boundaries: ONLY critical inferences *)

   let rec trans_layer ptree (subrel,tsubrel) =
      let rec isol_layer ptree (subrel,tsubrel) =
         match ptree with
            PEmpty -> raise jprover_bug
          | PNodeAx(inf) ->
               ptree
          | PNodeA((pos,rule,formula,term),left) ->
               if List.mem  rule [Allr;Impr;Negr] then
                  let tptree = trans_layer left (subrel,tsubrel) in
                  PNodeA((pos,rule,formula,term),tptree)
               else
                  let tptree = isol_layer  left (subrel,tsubrel) in
                  PNodeA((pos,rule,formula,term),tptree)
          | PNodeB(rule,left,right) ->
               let tptree_l = isol_layer  left (subrel,tsubrel)
               and tptree_r = isol_layer  right (subrel,tsubrel) in
               PNodeB(rule,tptree_l,tptree_r)
      in
      begin
(*   print_endline "trans_layer in"; *)
         let top_tree = isol_layer  ptree (subrel,tsubrel) in
         let back = permute_layer  top_tree [] (subrel,tsubrel) in
(*     print_endline "translauer out"; *)
         back
      end

(* REAL PERMUTATION STAFF  --- End *)

(* build the proof tree from a list of inference rules *)

   let rec unclosed subtree =
      match subtree with
         PEmpty -> true
       | PNodeAx(y) -> false
       | PNodeA(y,left) -> (unclosed left)
       | PNodeB(y,left,right) -> (or) (unclosed left) (unclosed right)

   let rec extend prooftree element =
      match prooftree with
         PEmpty ->
            let (pos,rule,formula,term) = element in
            if rule = Ax then
               PNodeAx(element)
            else
               if List.mem rule [Andr; Orl; Impl] then
                  PNodeB(element,PEmpty,PEmpty)
               else
                  PNodeA(element,PEmpty)
       | PNodeAx(y) ->
            PEmpty           (* that's only for  exhaustive pattern matching *)
       | PNodeA(y, left) ->
            PNodeA(y, (extend left element))
       | PNodeB(y, left, right) ->
            if (unclosed left) then
               PNodeB(y, (extend left element), right)
            else
               PNodeB(y, left, (extend right element))

   let rec bptree prooftree nodelist nax=
      match nodelist with
         [] -> prooftree,nax
       | ((_,pos),(rule,formula,term))::rest -> (* kick away the first argument *)
            let newax =
               if rule = Ax then
                  1
               else
                  0
            in
            bptree (extend prooftree (pos,rule,formula,term)) rest (nax+newax)


   let bproof nodelist =
      bptree PEmpty nodelist 0

   let rec get_successor_pos treelist =
      match treelist with
         [] -> []
       | f::r ->
            (
             match f with
                Empty -> get_successor_pos r
              | NodeAt(_) -> raise jprover_bug
              | NodeA(pos,_) ->
                   pos::(get_successor_pos r)
            )

   let rec get_formula_tree ftreelist f predflag =
      match ftreelist with
         [] -> raise jprover_bug
       | ftree::rest_trees ->
            (match ftree with
               Empty -> get_formula_tree rest_trees f predflag
             | NodeAt(_) -> get_formula_tree rest_trees f predflag
             | NodeA(pos,suctrees) ->
                  if predflag = "pred" then
                     if pos.pt = Gamma then
                        let succs = get_successor_pos (Array.to_list suctrees) in
                        if List.mem f succs then
                           NodeA(pos,suctrees),succs
                        else
                           get_formula_tree ((Array.to_list suctrees) @ rest_trees) f predflag
                     else
                        get_formula_tree ((Array.to_list suctrees) @ rest_trees) f predflag
                  else (* predflag = "" *)
                     if pos = f then
                        NodeA(pos,suctrees),[]
                     else
                        get_formula_tree ((Array.to_list suctrees) @ rest_trees) f predflag
            )

   let rec get_formula_treelist ftree po =
      match po with
         [] -> []
       | f::r ->
(* a posistion in po has either stype Gamma_0,Psi_0,Phi_0 (non-atomic), or it has *)
(* ptype Alpha (or on the right), since there was a deadlock for proof reconstruction in LJ*)
            if List.mem f.st [Phi_0;Psi_0] then
               let (stree,_) = get_formula_tree [ftree] f "" in
               stree::(get_formula_treelist ftree r)
            else
               if f.st = Gamma_0 then
                  let (predtree,succs) = get_formula_tree [ftree] f "pred" in
                  let new_po = list_diff r succs in
                  predtree::(get_formula_treelist ftree new_po)
               else
                  if f.pt = Alpha then (* same as first case, or on the right *)
                     let (stree,_) = get_formula_tree [ftree] f "" in
                     stree::(get_formula_treelist ftree r)
                  else raise (Invalid_argument "Jprover bug: non-admissible open position")

   let rec build_formula_rel dir_treelist slist predname =

      let rec build_renamed_gamma_rel dtreelist predname posname d =
         match dtreelist with
            [] -> [],[]
          | (x,ft)::rdtlist ->
               let rest_rel,rest_ren = build_renamed_gamma_rel rdtlist predname posname d  in
               (
                match ft with
                   Empty ->   (* may have empty successors due to purity in former reconstruction steps *)
                      rest_rel,rest_ren
                 | NodeAt(_) ->
                      raise jprover_bug (* gamma_0 position never is atomic *)
                 | NodeA(spos,suctrees) ->
                      if List.mem spos.name slist then
(* the gamma_0 position is really unsolved *)
(* this is only relevant for the gamma_0 positions in po *)
                         let new_name = (posname^"_"^spos.name) (* make new unique gamma name *) in
                         let new_srel_el = ((predname,new_name),d)
                         and new_rename_el = (spos.name,new_name)  (* gamma_0 position as key first *) in
                         let (srel,sren) = build_formula_rel [(x,ft)] slist new_name in
                         ((new_srel_el::srel) @ rest_rel),((new_rename_el::sren) @ rest_ren)
                      else
                         rest_rel,rest_ren
               )


      in
      match dir_treelist with
         [] -> [],[]
       | (d,f)::dir_r ->
            let (rest_rel,rest_renlist) = build_formula_rel dir_r slist predname in
            match f with
               Empty ->
                  print_endline "Hello, an empty subtree!!!!!!";
                  rest_rel,rest_renlist
             | NodeAt(pos) ->
                  (((predname,pos.name),d)::rest_rel),rest_renlist
             | NodeA(pos,suctrees) ->
                  (match pos.pt with
                     Alpha | Beta ->
                        let dtreelist =
                           if (pos.pt = Alpha) & (pos.op = Neg) then
                              [(1,suctrees.(0))]
                           else
                              let st1 = suctrees.(0)
                              and st2 = suctrees.(1) in
                              [(1,st1);(2,st2)]
                        in
                        let (srel,sren) = build_formula_rel dtreelist slist pos.name in
                        ((((predname,pos.name),d)::srel) @ rest_rel),(sren @ rest_renlist)
                   | Delta ->
                        let st1 = suctrees.(0) in
                        let (srel,sren) = build_formula_rel [(1,st1)] slist pos.name in
                        ((((predname,pos.name),d)::srel) @ rest_rel),(sren @ rest_renlist)
                   | Psi| Phi ->
                        let succlist = Array.to_list suctrees in
                        let dtreelist = (List.map (fun x -> (d,x)) succlist) in
                        let (srel,sren) = build_formula_rel dtreelist slist predname in
                        (srel @ rest_rel),(sren @ rest_renlist)
                   | Gamma ->
                        let succlist = (Array.to_list suctrees) in
                        let dtreelist = (List.map (fun x -> (1,x)) succlist) in
(*                if (nonemptys suctrees 0 n) = 1  then
   let (srel,sren) = build_formula_rel dtreelist slist pos.name in
   ((((predname,pos.name),d)::srel) @ rest_rel),(sren @ rest_renlist)
   else (* we have more than one gamma instance, which means renaming *)
*)
                        let (srel,sren) = build_renamed_gamma_rel dtreelist predname pos.name d in
                        (srel @ rest_rel),(sren @ rest_renlist)
                   | PNull ->
                        raise jprover_bug
                  )

   let rec rename_gamma ljmc_proof rename_list =
      match ljmc_proof with
         [] -> []
       | ((inst,pos),(rule,formula,term))::r ->
            if List.mem rule [Alll;Exr] then
               let new_gamma = List.assoc inst rename_list in
               ((inst,new_gamma),(rule,formula,term))::(rename_gamma r rename_list)
            else
               ((inst,pos),(rule,formula,term))::(rename_gamma r rename_list)

   let rec compare_pair (s,sf) list =
      if list = [] then
         list
      else
         let (s_1,sf_1),restlist = (List.hd list),(List.tl list) in
         if sf = s_1 then
            (@) [(s,sf_1)] (compare_pair (s,sf) restlist)
         else
            compare_pair (s,sf) restlist

   let rec compare_pairlist list1 list2 =
      if list1 = [] then
         list1
      else
         let (s1,sf1),restlist1  =  (List.hd list1),(List.tl list1) in
         (@) (compare_pair (s1,sf1) list2) (compare_pairlist restlist1 list2)

   let rec trans_rec pairlist translist =
      let tlist = compare_pairlist pairlist translist in
      if tlist = [] then
         translist
      else
         (@) (trans_rec pairlist tlist) translist

   let transitive_closure subrel =
      let pairlist,nlist = List.split subrel in
      trans_rec pairlist pairlist

   let pt ptree subrel =
      let tsubrel = transitive_closure subrel in
      let transptree = trans_layer ptree (subrel,tsubrel) in
      print_endline "";
      fst (modify transptree (subrel,tsubrel))
(*     let mtree = fst (modify transptree (subrel,tsubrel)) in *)
(*       pretty_print mtree ax *)

   let rec make_node_list ljproof =
      match ljproof with
         PEmpty ->
            raise jprover_bug
       | PNodeAx((pos,inf,form,term)) ->
            [(("",pos),(inf,form,term))]
       | PNodeA((pos,inf,form,term),left) ->
            let left_list =  make_node_list left in
            (("",pos),(inf,form,term))::left_list
       | PNodeB((pos,inf,form,term),left,right) ->
            let left_list =  make_node_list left
            and right_list =  make_node_list right in
            (("",pos),(inf,form,term))::(left_list @ right_list)

   let  permute_ljmc ftree po slist ljmc_proof =
 (* ftree/po are the formula tree / open positions of the sequent that caused deadlock and permutation *)
(*  print_endline "!!!!!!!!!!!!!Permutation TO DO!!!!!!!!!"; *)
 (* the open positions in po are either phi_0, psi_0, or gamma_0 positions *)
 (* since proof reconstruction was a deadlock in LJ *)
      let po_treelist = get_formula_treelist ftree po in
      let dir_treelist = List.map (fun x -> (1,x)) po_treelist in
      let (formula_rel,rename_list) = build_formula_rel dir_treelist slist "dummy" in
      let renamed_ljmc_proof = rename_gamma ljmc_proof rename_list in
      let (ptree,ax) =  bproof renamed_ljmc_proof in
      let ljproof = pt ptree formula_rel in
           (* this is a direct formula relation, comprising left/right subformula *)
      begin
(*   print_treelist po_treelist; *)
(*   print_endline "";
   print_endline "";
*)
(*   print_triplelist formula_rel; *)
(*   print_endline "";
   print_endline "";
   tt ljproof;
*)
(*   print_pairlist rename_list; *)
(*   print_endline "";
   print_endline "";
*)
         make_node_list ljproof
      end

(************** PROOF RECONSTRUCTION without redundancy deletion ******************************)

   let rec init_unsolved treelist =
      match treelist with
         [] -> []
       | f::r ->
            begin match f with
               Empty -> []
             | NodeAt(pos) ->
                  (pos.name)::(init_unsolved r)
             | NodeA(pos,suctrees) ->
                  let new_treelist = (Array.to_list suctrees) @ r in
                  (pos.name)::(init_unsolved new_treelist)
            end

(* only the unsolved positions will be represented --> skip additional root position *)

   let build_unsolved ftree =
      match ftree with
         Empty | NodeAt _ ->
            raise jprover_bug
       | NodeA(pos,suctrees) ->
            ((pos.name),init_unsolved (Array.to_list suctrees))

(*
   let rec collect_variables tree_list =
      match tree_list with
         [] -> []
       | f::r ->
            begin match f with
               Empty -> []
             | NodeAt(pos) ->
                  if pos.st = Gamma_0 then
                     pos.name::collect_variables r
                  else
                     collect_variables r
             | NodeA(pos,suctrees) ->
                  let new_tree_list = (Array.to_list suctrees) @ r in
                  if pos.st = Gamma_0 then
                     pos.name::collect_variables new_tree_list
                  else
                     collect_variables new_tree_list
            end

   let rec extend_sigmaQ sigmaQ vlist =
      match vlist with
         [] -> []
       | f::r ->
            let vf = mk_var_term f in
            if List.exists (fun x -> (fst x = vf)) sigmaQ then
               extend_sigmaQ sigmaQ r
            else
(* first and second component are var terms in meta-prl *)
               [(vf,vf)] @ (extend_sigmaQ sigmaQ r)

   let build_sigmaQ sigmaQ ftree =
      let vlist = collect_variables [ftree] in
      sigmaQ @ (extend_sigmaQ sigmaQ vlist)
*)

(* subformula relation subrel is assumed to be represented in pairs
   (a,b) *)

   let rec delete e list =     (* e must not necessarily occur in list *)
      match list with
         [] -> []               (* e must not necessarily occur in list *)
       | first::rest ->
            if e = first then
               rest
            else
               first::(delete e rest)

   let rec key_delete fname pos_list =   (* in key_delete, f is a pos name (key) but sucs is a list of positions *)
      match pos_list with
         [] -> []               (* the position with name f  must not necessarily occur in pos_list *)
       | f::r ->
            if fname = f.name then
               r
            else
               f::(key_delete fname r)

   let rec get_roots treelist =
      match treelist with
         [] -> []
       | f::r ->
            match f with
               Empty -> (get_roots r)    (* Empty is posible below alpha-nodes after purity *)
             | NodeAt(pos) -> pos::(get_roots r)
             | NodeA(pos,trees) ->  pos::(get_roots r)

   let rec comp_ps padd ftree =
      match ftree with
         Empty -> raise (Invalid_argument "Jprover bug: empty formula tree")
       | NodeAt(pos) ->
            []
       | NodeA(pos,strees) ->
            match padd with
               [] -> get_roots (Array.to_list strees)
             | f::r ->
                  if r = [] then
                     pos::(comp_ps r (Array.get strees (f-1)))
                  else
                     comp_ps r (Array.get strees (f-1))

(* computes a list: first element predecessor, next elements successoes of p *)

   let tpredsucc p ftree =
      let padd = p.address in
      comp_ps padd ftree

(* set an element in an array, without side effects *)

   let myset array int element =
      let length = Array.length array in
      let firstpart = Array.sub array 0 (int) in
      let secondpart = Array.sub array (int+1) (length-(int+1)) in
      (Array.append firstpart (Array.append [|element|] secondpart))

   let rec compute_open treelist slist =
      match treelist with
         [] -> []
       | first::rest ->
            let elements =
               match first with
                  Empty -> []
                | NodeAt(pos) ->
                     if (List.mem (pos.name) slist) then
                        [pos]
                     else
                        []
                | NodeA(pos,suctrees) ->
                     if (List.mem (pos.name) slist) then
                        [pos]
                     else
                        compute_open (Array.to_list suctrees) slist
            in
            elements @ (compute_open rest slist)

   let rec select_connection pname connections slist =
      match connections with
         [] -> ("none","none")
       | f::r ->
            let partner =
               if (fst f) = pname then
                  (snd f)
               else
                  if (snd f) = pname then
                     (fst f)
                  else
                     "none"
            in
            if ((partner = "none") or (List.mem partner slist)) then
               select_connection pname r slist
            else
               f

   let rec replace_element element element_set redord =
      match redord with
         [] -> raise jprover_bug   (* element occurs in redord *)
       | (f,fset)::r ->
            if f = element then
               (f,element_set)::r
            else
               (f,fset)::(replace_element element element_set r)

   let rec collect_succ_sets sucs redord =
      match redord with
         [] -> StringSet.empty
       | (f,fset)::r ->
            let new_sucs = key_delete f sucs in
            if (List.length sucs) = (List.length new_sucs) then   (* position with name f did not occur in sucs -- no deletion *)
               (collect_succ_sets sucs r)
            else
               StringSet.union (StringSet.add f fset) (collect_succ_sets new_sucs r)

   let replace_ordering psucc_name sucs redord =
      let new_psucc_set = collect_succ_sets sucs redord in
(*   print_string_set new_psucc_set; *)
      replace_element psucc_name new_psucc_set redord

   let rec update pname redord =
      match redord with
         [] -> []
       | (f,fset)::r ->
            if pname=f then
               r
            else
               (f,fset)::(update pname r)

(*  rule construction *)

   let rec selectQ_rec spos_var csigmaQ =
      match csigmaQ  with
         [] ->  mk_var_term spos_var   (* dynamic completion of csigmaQ *)
       | (var,term)::r ->
            if spos_var=var then
               term
            else
               selectQ_rec spos_var r

   let selectQ spos_name csigmaQ =
      let spos_var = spos_name^"_jprover" in
      selectQ_rec spos_var csigmaQ

   let apply_sigmaQ term sigmaQ =
      let sigma_vars,sigma_terms = List.split sigmaQ in
      (subst term sigma_vars sigma_terms)

   let build_rule pos spos csigmaQ orr_flag calculus =
      let inst_label = apply_sigmaQ (pos.label) csigmaQ in
      match pos.op,pos.pol with
         Null,_ -> raise (Invalid_argument "Jprover: no rule")
       | At,O -> Ax,(inst_label),xnil_term (* to give back a term *)
       | At,I -> Ax,(inst_label),xnil_term
       | And,O -> Andr,(inst_label),xnil_term
       | And,I -> Andl,(inst_label),xnil_term
       | Or,O ->
            if calculus = "LJ" then
               let or_rule =
                  if orr_flag = 1 then
                     Orr1
                  else
                     Orr2
               in
               or_rule,(inst_label),xnil_term
            else
               Orr,(inst_label),xnil_term
       | Or,I -> Orl,(inst_label),xnil_term
       | Neg,O -> Negr,(inst_label),xnil_term
       | Neg,I -> Negl,(inst_label),xnil_term
       | Imp,O -> Impr,(inst_label),xnil_term
       | Imp,I -> Impl,(inst_label),xnil_term
       | All,I -> Alll,(inst_label),(selectQ spos.name csigmaQ)  (* elements of csigmaQ is (string * term) *)
       | Ex,O -> Exr,(inst_label), (selectQ  spos.name csigmaQ)
       | All,O -> Allr,(inst_label),(mk_string_term jprover_op spos.name) (* must be a proper term *)
       | Ex,I -> Exl,(inst_label),(mk_string_term jprover_op spos.name) (* must be a proper term *)


(* %%%%%%%%%%%%%%%%%%%% Split begin %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% *)

   let rec nonemptys treearray j n =
      if j = n then
         0
      else
         let count =
            if (Array.get treearray j) <> Empty then
               1
            else
               0
         in
         count + (nonemptys treearray (j+1) n)

   let rec collect_pure ftreelist (flist,slist) =

      let rec collect_itpure ftree (flist,slist) =
         match ftree with
            Empty ->  (* assumed that not all brother trees are Empty *)
               []
          | NodeAt(pos) -> (* that may NOT longer be an inner node *)
               if ((List.mem (pos.name) flist) or (List.mem (pos.name) slist)) then
                  []
               else
                  [pos]
          | NodeA(pos,treearray) ->
               collect_pure (Array.to_list treearray) (flist,slist)
      in
      match ftreelist with
         [] -> []
       | f::r ->
            (collect_itpure f (flist,slist)) @ (collect_pure r (flist,slist))

   let rec update_list testlist list =
      match testlist with
         [] -> list
       | f::r ->
            let newlist = delete f list in    (* f may not occur in list; then newlist=list *)
            update_list r newlist

   let rec update_pairlist p pairlist =
      match pairlist with
         [] -> []
       | f::r ->
            if ((fst f) = p) or ((snd f) = p) then
               update_pairlist p r
            else
               f::(update_pairlist p r)

   let rec update_connections slist connections =
      match slist with
         [] -> connections
       | f::r ->
            let connew = update_pairlist f connections in
            update_connections r connew

   let rec update_redord delset redord =   (* delset is the set of positions to be deleted *)
      match redord with
         [] -> []
       | (f,fset)::r ->
            if (StringSet.mem f delset) then
               update_redord delset r   (* delete all key elements f from redord which are in delset *)
            else
               let new_fset  = StringSet.diff fset delset in  (* no successor of f from delset should remain in fset *)
               (f,new_fset)::(update_redord delset r)

   let rec get_position_names treelist =
      match treelist with
         [] -> []
       | deltree::rests ->
            match deltree with
               Empty -> get_position_names rests
             | NodeAt(pos) ->
                  (pos.name)::get_position_names rests
             | NodeA(pos,strees) ->
                  (pos.name)::(get_position_names ((Array.to_list strees) @ rests))

   let rec slist_to_set slist =
      match slist with
         [] ->
            StringSet.empty
       | f::r ->
            StringSet.add f (slist_to_set r)

   let rec print_purelist pr =
      match pr with
         [] ->
            begin
               print_string ".";
               print_endline " ";
            end
       | f::r ->
            print_string ((f.name)^", ");
            print_purelist r

   let update_relations deltree redord connections unsolved_list =
      let pure_names = get_position_names [deltree] in
      begin
(*        print_ftree deltree;
   Format.open_box 0;
   print_endline " ";
   print_stringlist pure_names;
   Format.force_newline ();
   Format.print_flush ();
*)
         let rednew = update_redord (slist_to_set pure_names) redord
         and connew = update_connections pure_names connections
         and unsolnew = update_list pure_names unsolved_list in
         (rednew,connew,unsolnew)
      end

   let rec collect_qpos ftreelist uslist =
      match ftreelist with
         [] -> [],[]
       | ftree::rest ->
            match ftree with
               Empty ->
                  collect_qpos rest uslist
             | NodeAt(pos) ->
                  let (rest_delta,rest_gamma) = collect_qpos rest uslist in
                  if (pos.st = Gamma_0) & (List.mem pos.name uslist) then
                     rest_delta,(pos.name::rest_gamma)
                  else
                     if (pos.st = Delta_0) & (List.mem pos.name uslist) then
                        (pos.name::rest_delta),rest_gamma
                     else
                        rest_delta,rest_gamma
             | NodeA(pos,suctrees) ->
                  let (rest_delta,rest_gamma) = collect_qpos ((Array.to_list suctrees) @ rest) uslist in
                  if (pos.st = Gamma_0) & (List.mem pos.name uslist) then
                     rest_delta,(pos.name::rest_gamma)
                  else
                     if (pos.st = Delta_0) & (List.mem pos.name uslist) then
                        (pos.name::rest_delta),rest_gamma
                     else
                        rest_delta,rest_gamma

   let rec do_split gamma_diff sigmaQ =
      match sigmaQ with
         [] -> []
       | (v,term)::r ->
            if (List.mem (String.sub v 0 (String.index v '_')) gamma_diff) then
               do_split gamma_diff r
            else
               (v,term)::(do_split gamma_diff r)

(* make a term list out of a bterm list *)

   let rec collect_subterms = function
      [] -> []
    | bt::r ->
         let dbt = dest_bterm bt in
         (dbt.bterm)::(collect_subterms r)

  let rec collect_delta_terms = function
      [] -> []
    | t::r ->
         let dt = dest_term t in
         let top = dt.term_op
         and tterms = dt.term_terms in
         let dop = dest_op top in
         let don = dest_opname dop.op_name in
         let doa = dest_param dop.op_params in
         match don with
            [] ->
               let sub_terms = collect_subterms tterms in
               collect_delta_terms (sub_terms @ r)
          | op1::opr ->
               if op1 = "jprover" then
                  match doa with
                     [] -> raise (Invalid_argument "Jprover: delta position missing")
                   | String delta::_ ->
                        delta::(collect_delta_terms r)
                   | _ ->  raise (Invalid_argument "Jprover: delta position error")
               else
                  let sub_terms = collect_subterms tterms in
                  collect_delta_terms (sub_terms @ r)



   let rec check_delta_terms (v,term) ass_delta_diff dterms =
      match ass_delta_diff with
         [] -> term,[]
       | (var,dname)::r ->
            if List.mem dname dterms then
               let new_var =
                  if var = "" then
                     v
                  else
                     var
               in
               let replace_term = mk_string_term jprover_op dname in
               let next_term = var_subst term replace_term new_var in
               let (new_term,next_diffs) = check_delta_terms (v,next_term) r dterms in
               (new_term,((new_var,dname)::next_diffs))
            else
               let (new_term,next_diffs) = check_delta_terms (v,term) r dterms in
               (new_term,((var,dname)::next_diffs))


   let rec localize_sigma zw_sigma ass_delta_diff =
      match zw_sigma with
         [] -> []
       | (v,term)::r ->
            let dterms = collect_delta_terms [term] in
            let (new_term,new_ass_delta_diff) = check_delta_terms (v,term) ass_delta_diff dterms in
            (v,new_term)::(localize_sigma r new_ass_delta_diff)

   let subst_split ft1 ft2 ftree uslist1 uslist2 uslist sigmaQ =
      let delta,gamma = collect_qpos [ftree] uslist
      and delta1,gamma1 = collect_qpos [ft1] uslist1
      and  delta2,gamma2 = collect_qpos [ft2] uslist2 in
      let delta_diff1 = list_diff delta delta1
      and delta_diff2 = list_diff delta delta2
      and gamma_diff1 = list_diff gamma gamma1
      and gamma_diff2 = list_diff gamma gamma2 in
      let zw_sigma1 = do_split gamma_diff1 sigmaQ
      and zw_sigma2 = do_split gamma_diff2 sigmaQ in
      let ass_delta_diff1 = List.map (fun x -> ("",x)) delta_diff1
      and ass_delta_diff2 = List.map (fun x -> ("",x)) delta_diff2 in
      let sigmaQ1 = localize_sigma zw_sigma1 ass_delta_diff1
      and sigmaQ2 = localize_sigma zw_sigma2 ass_delta_diff2 in
      (sigmaQ1,sigmaQ2)

   let rec reduce_tree addr actual_node ftree beta_flag =
      match addr with
         [] -> (ftree,Empty,actual_node,beta_flag)
       | a::radd ->
            match ftree with
               Empty ->
                  print_endline "Empty purity tree";
                  raise jprover_bug
             | NodeAt(_) ->
                  print_endline "Atom purity tree";
                  raise jprover_bug
             | NodeA(pos,strees) ->
(*       print_endline pos.name; *)
    (* the associated node occurs above f (or the empty address) and hence, is neither atom nor empty tree *)

                  let nexttree = (Array.get strees (a-1)) in
                  if (nonemptys strees 0 (Array.length strees)) < 2  then
                     begin
(*          print_endline "strees 1 or non-empties < 2"; *)
                        let (ft,dt,an,bf) =  reduce_tree radd actual_node nexttree beta_flag in
                        let nstrees = myset strees (a-1) ft in
(*            print_endline ("way back "^pos.name); *)
                        (NodeA(pos,nstrees),dt,an,bf)
                     end
                  else  (* nonemptys >= 2 *)
                     begin
(*             print_endline "nonempties  >= 2 "; *)
                        let (new_act,new_bf) =
                           if pos.pt = Beta then
                              (actual_node,true)
                           else
                              ((pos.name),false)
                        in
                        let (ft,dt,an,bf) = reduce_tree radd new_act nexttree new_bf in
                        if an = pos.name then
                           let nstrees = myset strees (a-1) Empty in
(*                 print_endline ("way back assocnode "^pos.name); *)
                           (NodeA(pos,nstrees),nexttree,an,bf)
                        else  (* has been replaced / will be replaced below / above pos *)
                           let nstrees = myset strees (a-1) ft in
(*                 print_endline ("way back "^pos.name); *)
                           (NodeA(pos,nstrees),dt,an,bf)
                     end

   let rec purity ftree redord connections unsolved_list =

      let rec purity_reduction pr ftree redord connections unsolved_list =
         begin
(*        Format.open_box 0;
   print_endline " ";
   print_purelist pr;
   Format.force_newline ();
   Format.print_flush ();
*)
            match pr with
               [] -> (ftree,redord,connections,unsolved_list)
             | f::r ->
(*   print_endline ("pure position "^(f.name)); *)
                  let (ftnew,deltree,assocn,beta_flag) = reduce_tree f.address "" ftree false
                  in
(*     print_endline ("assoc node "^assocn); *)
                  if assocn = "" then
                     (Empty,[],[],[])  (* should not occur in the final version *)
                  else
                     let (rednew,connew,unsolnew) = update_relations deltree redord connections unsolved_list in
                     begin
(*        Format.open_box 0;
   print_endline " ";
   print_pairlist connew;
   Format.force_newline ();
   Format.print_flush ();
*)
                        if beta_flag = true then
                           begin
(*          print_endline "beta_flag true"; *)
                              purity ftnew rednew connew unsolnew
  (* new pure positions may occur; old ones may not longer exist *)
                           end
                        else
                           purity_reduction r ftnew rednew connew unsolnew (* let's finish the old pure positions *)
                     end
         end

      in
      let flist,slist = List.split connections in
      let pr = collect_pure [ftree] (flist,slist) in
      purity_reduction pr ftree redord connections unsolved_list

   let rec betasplit addr ftree redord connections unsolved_list =
      match ftree with
         Empty  ->
            print_endline "bsplit Empty tree";
            raise jprover_bug
       | NodeAt(_) ->
            print_endline "bsplit Atom tree";
            raise jprover_bug   (* the beta-node should actually occur! *)
       | NodeA(pos,strees) ->
            match addr with
               [] ->    (* we are at the beta node under consideration *)
                  let st1tree = (Array.get strees 0)
                  and st2tree = (Array.get strees 1) in
                  let (zw1red,zw1conn,zw1uslist) = update_relations st2tree redord connections unsolved_list
                  and (zw2red,zw2conn,zw2uslist) = update_relations st1tree redord connections unsolved_list in
                  ((NodeA(pos,[|st1tree;Empty|])),zw1red,zw1conn,zw1uslist),
                  ((NodeA(pos,[|Empty;st2tree|])),zw2red,zw2conn,zw2uslist)
             | f::rest ->
                  let nexttree  = Array.get strees (f-1) in
                  let (zw1ft,zw1red,zw1conn,zw1uslist),(zw2ft,zw2red,zw2conn,zw2uslist) =
                     betasplit rest nexttree redord connections unsolved_list in
(*          let scopytrees = Array.copy strees in  *)
                  let zw1trees = myset strees (f-1) zw1ft
                  and zw2trees = myset strees (f-1) zw2ft in
                  (NodeA(pos,zw1trees),zw1red,zw1conn,zw1uslist),(NodeA(pos,zw2trees),zw2red,zw2conn,zw2uslist)




   let split addr pname ftree redord connections unsolved_list opt_bproof =
      let (opt_bp1,min_con1),(opt_bp2,min_con2) = split_permutation pname opt_bproof in
      begin
(*
   print_endline "Beta proof 1: ";
   print_endline "";
   print_beta_proof opt_bp1;
   print_endline "";
   print_endline ("Beta proof 1 connections: ");
   Format.open_box 0;
   print_pairlist min_con1;
   print_endline ".";
   Format.print_flush();
   print_endline "";
   print_endline "";
   print_endline "Beta proof 2: ";
   print_endline "";
   print_beta_proof opt_bp2;
   print_endline "";
   print_endline ("Beta proof 2 connections: ");
   Format.open_box 0;
   print_pairlist min_con2;
   print_endline ".";
   Format.print_flush();
   print_endline "";
*)
         let  (zw1ft,zw1red,zw1conn,zw1uslist),(zw2ft,zw2red,zw2conn,zw2uslist) =
            betasplit addr ftree redord connections unsolved_list in
(* zw1conn and zw2conn are not longer needed when using beta proofs *)
(*   print_endline "betasp_out"; *)
         let ft1,red1,conn1,uslist1 =  purity zw1ft zw1red min_con1 zw1uslist in
(*   print_endline "purity_one_out"; *)
         let ft2,red2,conn2,uslist2 =  purity zw2ft zw2red min_con2 zw2uslist in
(*        print_endline "purity_two_out"; *)
(* again, min_con1 = conn1 and min_con2 = conn2 should hold *)
         begin
(* print_endline "";
   print_endline "";
   print_endline ("Purity 1 connections: ");
   Format.open_box 0;
   print_pairlist conn1;
   print_endline ".";
   print_endline "";
   Format.print_flush();
   print_endline "";
   print_endline "";
   print_endline ("Purity 2 connections: ");
   Format.open_box 0;
   print_pairlist conn2;
   print_endline ".";
   print_endline "";
   Format.print_flush();
   print_endline "";
   print_endline "";
*)
            (ft1,red1,conn1,uslist1,opt_bp1),(ft2,red2,conn2,uslist2,opt_bp2)
         end
      end


(* %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Splitting end %%%%%%%%%%%%%%%%  *)


(* for wait labels we collect all solved atoms with pol=0 *)

   let rec collect_solved_O_At ftreelist slist =
      match ftreelist with
         [] ->
            []
       | f::r ->
            match f with
               Empty ->    (* may become possible after purity *)
                  collect_solved_O_At r slist
             | NodeAt(pos) ->
                  if ((List.mem (pos.name) slist) or (pos.pol = I)) then  (* recall slist is the unsolved list *)
                     collect_solved_O_At r slist
                  else
    (* here, we have pos solved and pos.pol = O) *)
                     pos::(collect_solved_O_At r slist)
             | NodeA(pos,treearray) ->
                  collect_solved_O_At ((Array.to_list treearray) @ r) slist

   let rec red_ord_block pname redord =
      match redord with
         [] -> false
       | (f,fset)::r ->
            if ((f = pname) or (not (StringSet.mem pname fset))) then
               red_ord_block pname r
            else
               true   (* then, we have (StringSet.mem pname fset) *)

   let rec check_wait_succ_LJ faddress ftree =
      match ftree with
         Empty -> raise jprover_bug
       | NodeAt(pos) -> raise jprover_bug (* we have an gamma_0 position or an or-formula *)
       | NodeA(pos,strees) ->
            match faddress with
               [] ->
                  if pos.op = Or then
                     match (strees.(0),strees.(1)) with
                        (Empty,Empty) -> raise (Invalid_argument "Jprover: redundancies occur")
                      | (Empty,_) -> (false,2)   (* determines the Orr2 rule *)
                      | (_,Empty) -> (false,1)   (* determines the Orr1 ruke *)
                      | (_,_)  -> (true,0)    (* wait-label is set *)
                  else
                     (false,0)
             | f::r ->
                  if r = [] then
                     if (pos.pt = Gamma) & ((nonemptys strees 0 (Array.length strees)) > 1)  then
                        (true,0)             (* we are at a gamma position (exr) with one than one successor -- wait label in LJ*)
                     else
                        check_wait_succ_LJ r (Array.get strees (f-1))
                  else
                     check_wait_succ_LJ r (Array.get strees (f-1))

   let blocked f po redord ftree connections slist logic calculus opt_bproof =
(* print_endline ("Blocking check "^(f.name)); *)
      if (red_ord_block (f.name) redord) then
         begin
(*     print_endline "wait-1 check positive"; *)
            true,0
         end
      else
         if logic = "C" then
            false,0  (* ready, in C only redord counts *)
         else
            let pa_O = collect_solved_O_At [ftree] slist      (* solved atoms in ftree *)
            and po_test = (delete f po) in
            if calculus = "LJmc" then (* we provide dynamic wait labels for both sequent calculi *)
(*       print_endline "wait-2 check"; *)
               if (f.st = Psi_0)  &  (f.pt <> PNull) &
                  ((pa_O <> []) or (List.exists (fun x -> x.pol = O) po_test)) then
                  begin
(*          print_endline "wait-2 positive"; *)
                     true,0 (* wait_2 label *)
                  end
               else
                  begin
(*            print_endline "wait-2 negative"; *)
                     false,0
                  end
            else  (* calculus is supposed to be LJ *)
               if calculus = "LJ" then
                  if  ((f.st = Phi_0)  & ((f.op=Neg) or (f.op=Imp)) &
                       ((pa_O <> []) or (List.exists (fun x -> x.pol = O) po_test))
                      )
         (* this would cause an impl or negl rule with an non-empty succedent *)
                  then
                     if (f.op=Neg) then
                        true,0
                     else  (* (f.op=Imp) *)
              (* In case of an impl rule on A => B, the wait_label must NOT be set
                 iff all succedent formulae depend exclusively on B. For this, we
                 perform a split operation and determine, if in the A-subgoal
                 all succedent formulae are pure, i.e.~have been deleted from treds.
                 Otherwise, in case of A-dependent succedent formulae, the
                 wait_label must be set.
              *)
                        let ((_,min_con1),_) = split_permutation f.name opt_bproof in
                        let slist_fake = delete f.name slist in
                        let  ((zw1ft,zw1red,_,zw1uslist),_) =
                           betasplit (f.address) ftree redord connections slist_fake in
                        let ft1,_,_,uslist1 =  purity zw1ft zw1red min_con1 zw1uslist in
(*                   print_endline "wait label purity_one_out"; *)
                        let ft1_root = (List.hd (List.tl (tpredsucc f ft1))) in
(*                 print_endline ("wait-root "^(ft1_root.name)); *)
                        let po_fake = compute_open [ft1] uslist1 in
                        let po_fake_test = delete ft1_root po_fake
                        and pa_O_fake = collect_solved_O_At [ft1] uslist1 in
(*                  print_purelist (po_fake_test @ pa_O_fake); *)
                        if ((pa_O_fake <> []) or (List.exists (fun x -> x.pol = O) po_fake_test)) then
                           true,0
                        else
                           false,0
                  else
                     if ((f.pol=O) & ((f.st=Gamma_0) or (f.op=Or))) then
                        let (bool,orr_flag) = check_wait_succ_LJ f.address ftree in
                        (bool,orr_flag)
        (* here is determined if orr1 or orr2 will be performed, provided bool=false) *)
        (* orr_flag can be 1 or 2 *)
                     else
                        false,0
               else
                  raise (Invalid_argument "Jprover: calculus should be LJmc or LJ")

   let rec get_beta_preference list actual =
      match list with
         [] -> actual
       | (f,int)::r ->
            if f.op = Imp then
               (f,int)
            else
(*     if f.op = Or then
   get_beta_preference r (f,int)
   else
*)
               get_beta_preference r actual

   exception Gamma_deadlock

   let rec select_pos search_po po redord ftree connections slist logic calculus candidates
         opt_bproof =
      match search_po with
         [] ->
            (match candidates with
               [] ->
                  if calculus = "LJ" then
                     raise Gamma_deadlock  (* permutation may be necessary *)
                  else
                     raise (Invalid_argument "Jprover bug: overall deadlock") (* this case should not occur *)
             | c::rest ->
                  get_beta_preference (c::rest) c
            )
       | f::r ->  (* there exist an open position *)
            let (bool,orr_flag) = (blocked f po redord ftree connections slist logic calculus
                                      opt_bproof)
            in
            if (bool = true) then
               select_pos r po redord  ftree connections slist logic calculus candidates opt_bproof
            else
               if f.pt = Beta then
     (* search for non-splitting rules first *)
(*      let beta_candidate =
   if candidates = []
   then
   [(f,orr_flag)]
   else
   !!!!  but preserve first found candidate !!!!!!!
   candidates
   in
   !!!!!!! this strategy is not sure the best -- back to old !!!!!!!!!
*)
                  select_pos r po redord  ftree connections slist logic calculus
                     ((f,orr_flag)::candidates) opt_bproof
               else
                  (f,orr_flag)

(* let rec get_position_in_tree pname treelist =
      match treelist with
         [] -> raise jprover_bug
       | f::r ->
            begin match f with
               Empty -> get_position_in_tree pname r
             | NodeAt(pos) ->
                  if pos.name = pname then
                     pos
                  else
                     get_position_in_tree pname r
             | NodeA(pos,suctrees) ->
                  get_position_in_tree pname ((Array.to_list suctrees) @ r)
            end
*)

(* total corresponds to tot in the thesis,
   tot simulates the while-loop, solve is the rest *)

   let rec total  ftree redord connections csigmaQ slist logic calculus opt_bproof =
      let rec tot  ftree redord connections po slist =
         let rec solve  ftree redord connections p po slist (pred,succs) orr_flag =
            let newslist = delete (p.name) slist in
            let rback =
               if p.st = Gamma_0 then
                  begin
(*          print_endline "that's the gamma rule";  *)
                     [((p.name,pred.name),(build_rule pred p csigmaQ orr_flag calculus))]
                  end
               else
                  []
            in
(*        print_endline "gamma check finish";  *)
            let pnew =
               if p.pt <> Beta then
                  succs @ (delete  p po)
               else
                  po
            in
            match p.pt with
               Gamma ->
                  rback @ (tot  ftree redord connections pnew newslist)
             | Psi   ->
                  if p.op = At then
                     let succ = List.hd succs in
                     rback @ (solve ftree redord connections succ pnew newslist (p,[]) orr_flag)  (* solve atoms immediately *)
                  else
                     rback @ (tot  ftree redord connections pnew newslist)
             | Phi   ->
                  if p.op = At then
                     let succ = List.hd succs in
                     rback @ (solve ftree redord connections succ pnew newslist (p,[]) orr_flag)  (* solve atoms immediately *)
                  else
                     rback @ (tot  ftree redord connections pnew newslist)
             | PNull ->
                  let new_redord = update p.name redord in
                  let (c1,c2) = select_connection (p.name) connections newslist in
                  if (c1= "none" & c2 ="none") then
                     rback @ (tot  ftree new_redord connections pnew newslist)
                  else
                     let (ass_pos,inst_pos) =
(* need the pol=O position ass_pos of the connection for later permutation *)
(* need the pol=I position inst_pos for NuPRL instantiation *)
                        if p.name = c1 then
                           if p.pol = O then
                              (c1,c2)
                           else
                              (c2,c1)
                        else (* p.name = c2 *)
                           if p.pol = O then
                              (c2,c1)
                           else
                              (c1,c2)
                     in
                     rback @ [(("",ass_pos),(build_rule p p csigmaQ orr_flag calculus))]
   (* one possibility of recursion end *)
             | Alpha ->
                  rback @ ((("",p.name),(build_rule p p csigmaQ orr_flag calculus))::(tot  ftree redord connections pnew newslist))
             | Delta ->
                  let sp = List.hd succs in
                  rback @ ((("",p.name),(build_rule p sp csigmaQ orr_flag calculus))::(tot ftree redord connections pnew newslist))
             | Beta  ->
(*             print_endline "split_in"; *)
                  let (ft1,red1,conn1,uslist1,opt_bproof1),(ft2,red2,conn2,uslist2,opt_bproof2) =
                     split (p.address) (p.name) ftree redord connections newslist opt_bproof in
                  let (sigmaQ1,sigmaQ2) = subst_split ft1 ft2 ftree uslist1 uslist2 newslist csigmaQ in
(*           print_endline "split_out"; *)
                  let p1 = total  ft1 red1 conn1 sigmaQ1 uslist1 logic calculus opt_bproof1 in
(*           print_endline "compute p1 out";              *)
                  let p2 = total  ft2 red2 conn2 sigmaQ2 uslist2 logic calculus opt_bproof2 in
(*           print_endline "compute p2 out";              *)
                  rback @ [(("",p.name),(build_rule p p csigmaQ orr_flag calculus))] @ p1 @ p2  (* second possibility of recursion end *)
         in
         begin try
            let (p,orr_flag) = select_pos po po redord ftree connections slist logic
                  calculus [] opt_bproof
    (* last argument for guiding selection strategy *)
            in
(*    print_endline ((p.name)^" "^(string_of_int orr_flag)); *)
            let predsuccs = tpredsucc p ftree in
            let pred = List.hd predsuccs
            and succs = List.tl predsuccs in
            let redpo = update (p.name) redord in   (* deletes the entry (p,psuccset) from the redord *)
            let rednew =
               if (p.pt = Delta) then                 (* keep the tree ordering for the successor position only *)
                  let psucc = List.hd succs in
                  let ppsuccs = tpredsucc psucc ftree in
                  let sucs = List.tl ppsuccs in
                  replace_ordering (psucc.name) sucs redpo (* union the succsets of psucc *)
               else
                  redpo
            in
(*      print_endline "update ok"; *)
            solve ftree rednew connections p po slist (pred,succs) orr_flag
         with Gamma_deadlock ->
            let ljmc_subproof =  total ftree redord connections csigmaQ slist "J" "LJmc" opt_bproof
            in
            eigen_counter := 1;
            permute_ljmc ftree po slist ljmc_subproof
           (* the permuaiton result will be appended to the lj proof constructed so far *)
         end
      in
      let po  = compute_open [ftree] slist in
      tot ftree redord connections po slist

   let reconstruct ftree redord sigmaQ ext_proof logic calculus =
      let min_connections = remove_dups_connections ext_proof in
      let (opt_bproof,beta_exp,closures) = construct_opt_beta_proof ftree ext_proof in
(* let connections = remove_dups_connections ext_proof in
   let bproof,beta_exp,closures = construct_beta_proof ftree connections in
   let (opt_bproof,min_connections) = bproof_purity bproof in
*)
      if !debug_jprover then
         begin
            print_endline "";
            print_endline ("Beta proof with number of closures = "^(string_of_int closures)^" and number of beta expansions = "^(string_of_int beta_exp));
(*   print_endline "";
   print_endline "";
   print_beta_proof bproof;
   print_endline "";
   print_endline "";
   print_endline "Optimal beta proof: ";
   print_endline "";
   print_endline "";
   print_beta_proof opt_bproof;
   print_endline "";
   print_endline "";
   print_endline ("Beta proof connections: ");
   Format.open_box 0;
   print_pairlist min_connections;
   print_endline ".";
   Format.print_flush(); *)
            print_endline "";
         end;
      let  (newroot_name,unsolved_list) =  build_unsolved ftree in
      let redord2 = (update newroot_name redord) in   (* otherwise we would have a deadlock *)
      let (init_tree,init_redord,init_connections,init_unsolved_list) =
         purity ftree redord2 min_connections unsolved_list in
      begin
(*   print_endline "";
   print_endline "";
   print_endline ("Purity connections: ");
   Format.open_box 0;
   print_pairlist init_connections;
   print_endline ".";
   print_endline "";
   Format.print_flush();
   print_endline "";
   print_endline "";
*)
(* it should hold: min_connections = init_connections *)
         total init_tree init_redord init_connections sigmaQ
            init_unsolved_list logic calculus opt_bproof
      end

(* ***************** REDUCTION ORDERING -- both types **************************** *)

   exception Reflexive

   let rec transitive_irreflexive_closure addset const ordering =
      match ordering with
         [] ->
            []
       | (pos,fset)::r ->
            if (pos = const) or (StringSet.mem const fset) then
(* check reflexsivity during transitive closure wrt. addset ONLY!!! *)
               if StringSet.mem pos addset then
                  raise Reflexive
               else
                  (pos,(StringSet.union fset addset))::(transitive_irreflexive_closure addset const r)
            else
               (pos,fset)::(transitive_irreflexive_closure addset const r)

   let rec search_set var ordering =
(* print_endline var; *)
      match ordering with
         [] ->
            raise (Invalid_argument "Jprover: element in ordering missing")
       | (pos,fset)::r ->
            if pos = var then
               StringSet.add pos fset
            else
               search_set var r

   let add_sets var const ordering =
      let addset =  search_set var ordering  in
      transitive_irreflexive_closure addset const ordering

(* ************* J ordering ********************************************** *)

   let rec add_arrowsJ (v,vlist) ordering =
      match vlist with
         [] -> ordering
       | f::r ->
            if ((String.get f 0)='c') then
               let new_ordering = add_sets v f ordering in
               add_arrowsJ (v,r) new_ordering
            else
               add_arrowsJ (v,r) ordering

   let rec add_substJ replace_vars replace_string ordering atom_rel =
      match replace_vars with
         [] -> ordering
       | v::r ->
            if (String.get v 1 = 'n') (* don't integrate new variables *)
                  or (List.exists (fun (x,_,_) -> (x.aname = v)) atom_rel) then   (* no reduction ordering at atoms *)
               (add_substJ r replace_string ordering atom_rel)
            else
               let next_ordering = add_arrowsJ (v,replace_string) ordering in
               (add_substJ r replace_string next_ordering atom_rel)

   let build_orderingJ replace_vars replace_string ordering atom_rel =
      try
         add_substJ replace_vars replace_string ordering atom_rel
      with Reflexive ->        (* only possible in the FO case *)
         raise Not_unifiable    (*search for alternative string unifiers *)

   let rec build_orderingJ_list substJ ordering atom_rel =
      match substJ with
         [] -> ordering
       | (v,vlist)::r ->
            let next_ordering = build_orderingJ [v] vlist ordering atom_rel in
            build_orderingJ_list r next_ordering atom_rel

(* ************* J ordering  END ********************************************** *)

(* ************* quantifier ordering ********************************************** *)

   let rec add_arrowsQ v clist ordering =
      match clist with
         [] -> ordering
       | f::r ->
            let new_ordering = add_sets v f ordering in
            add_arrowsQ v r new_ordering

   let rec print_sigmaQ sigmaQ =
      match sigmaQ with
         [] ->
            print_endline "."
       | (v,term)::r ->
            begin
               Format.open_box 0;
               print_endline " ";
               print_string (v^" = ");
               print_term stdout term;
               Format.force_newline ();
               Format.print_flush ();
               print_sigmaQ r
            end

   let rec print_term_list tlist =
      match tlist with
         [] -> print_string "."
       | t::r ->
            begin
               print_term stdout t;
               print_string "   ";
               print_term_list r
            end

   let rec add_sigmaQ new_elements ordering  =
      match new_elements with
         [] -> ([],ordering)
       | (v,termlist)::r ->
            let dterms = collect_delta_terms termlist in
            begin
               let new_ordering = add_arrowsQ  v dterms ordering in
               let (rest_pairs,rest_ordering) = add_sigmaQ r new_ordering in
                   ((v,dterms)::rest_pairs),rest_ordering
            end

   let build_orderingQ new_elements ordering =
(* new_elements is of type (string * term list) list, since one variable can receive more than *)
(* a single term due to substitution multiplication *)
      try
(*   print_endline "build orderingQ in"; *)  (* apple *)
         add_sigmaQ new_elements ordering;
      with Reflexive ->
         raise Failed                (* new connection, please *)


(* ************* quantifier ordering  END ********************************************** *)

(* ****** Quantifier unification ************** *)

(* For multiplication we assume always idempotent substitutions sigma, tau! *)

   let rec collect_assoc inst_vars tauQ  =
      match inst_vars with
         [] -> []
       | f::r ->
            let f_term = List.assoc f tauQ in
            f_term::(collect_assoc r tauQ)

   let rec rec_apply sigmaQ tauQ tau_vars tau_terms =
      match sigmaQ with
         [] -> [],[]
       | (v,term)::r ->
            let app_term = subst term tau_vars tau_terms in
            let old_free = free_vars_list term
            and new_free = free_vars_list app_term  in
            let inst_vars = list_diff old_free new_free in
            let inst_terms = collect_assoc inst_vars tauQ in
            let (rest_sigma,rest_sigma_ordering) = rec_apply r tauQ tau_vars tau_terms in
            if inst_terms  = [] then
               ((v,app_term)::rest_sigma),rest_sigma_ordering
            else
               let ordering_v = String.sub v 0 (String.index v '_') in
               ((v,app_term)::rest_sigma),((ordering_v,inst_terms)::rest_sigma_ordering)

(* let multiply sigmaQ tauQ =
   let tau_vars,tau_terms = List.split tauQ
   and sigma_vars,sigma_terms = List.split sigmaQ in
   let apply_terms  = rec_apply sigma_terms tau_vars tau_terms in
   (List.combine sigma_vars apply_terms) @ tauQ
*)

   let multiply sigmaQ tauQ =
      let (tau_vars,tau_terms) = List.split tauQ in
      let (new_sigmaQ,sigma_ordering)  = rec_apply sigmaQ tauQ tau_vars tau_terms in
      let tau_ordering_terms = (List.map (fun x -> [x]) tau_terms) (* for extending ordering_elements *) in
      let tau_ordering_vars = (List.map (fun x -> String.sub x 0 (String.index x '_')) tau_vars) in
      let tau_ordering  = (List.combine tau_ordering_vars tau_ordering_terms) in
      ((new_sigmaQ @ tauQ),
       (sigma_ordering @ tau_ordering)
      )

   let apply_2_sigmaQ term1 term2 sigmaQ =
      let sigma_vars,sigma_terms = List.split sigmaQ in
      (subst term1 sigma_vars sigma_terms),(subst term2 sigma_vars sigma_terms)

   let jqunify term1 term2 sigmaQ =
      let app_term1,app_term2 = apply_2_sigmaQ term1 term2 sigmaQ in
      try
         let tauQ = unify_mm app_term1 app_term2 StringSet.empty in
         let (mult,oel) = multiply sigmaQ tauQ in
         (mult,oel)
      with
         RefineError _  ->  (* any unification failure *)
(*    print_endline "fo-unification fail"; *)
            raise Failed   (* new connection, please *)

(* ************ T-STRING UNIFICATION ******************************** *)

   let rec combine subst (ov,oslist)  =
      match subst with
         [] -> [],[]
       | f::r ->
            let (v,slist) = f in
            let rest_vlist,rest_combine = (combine r (ov,oslist)) in
            if (List.mem ov slist) then  (* subst assumed to be idemponent *)
               let com_element = com_subst slist (ov,oslist) in
               (v::rest_vlist),((v,com_element)::rest_combine)
            else
               (rest_vlist,(f::rest_combine))

   let compose sigma one_subst =
      let (n,subst)=sigma
      and (ov,oslist) = one_subst in
      let (trans_vars,com) = combine subst (ov,oslist)
      in
(*    begin
   print_endline "!!!!!!!!!test print!!!!!!!!!!";
   print_subst [one_subst];
   print_subst subst;
   print_endline "!!!!!!!!! END test print!!!!!!!!!!";
*)
      if List.mem one_subst subst then
         (trans_vars,(n,com))
      else
(* ov may multiply as variable in subst with DIFFERENT values *)
(* in order to avoid explicit atom instances!!! *)
         (trans_vars,(n,(com @ [one_subst])))
(*   end *)

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
         ([],_) -> (us,ut)
       | (_,[])  -> (us,ut)
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

   let all_variable_check eqlist = false   (* needs some discussion with Jens! -- NOT done *)

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

   let rec  tunify_list eqlist init_sigma orderingQ atom_rel =

      let rec tunify atomnames fs ft rt rest_eq sigma ordering =

         let apply_r1 fs ft rt rest_eq sigma =
(* print_endline "r1"; *)
            tunify_list rest_eq sigma ordering atom_rel

         in
         let apply_r2 fs ft rt rest_eq sigma =
(* print_endline "r2"; *)
            tunify atomnames rt fs ft rest_eq sigma ordering

         in
         let apply_r3 fs ft rt rest_eq sigma =
(* print_endline "r3"; *)
            let rfs =  (List.tl fs)
            and rft =  (List.tl rt) in
            tunify atomnames rfs ft rft rest_eq sigma ordering

         in
         let apply_r4 fs ft rt rest_eq sigma =
(* print_endline "r4"; *)
            tunify atomnames rt ft fs rest_eq sigma ordering

         in
         let apply_r5 fs ft rt rest_eq sigma =
(* print_endline "r5"; *)
            let v = (List.hd fs) in
            let (compose_vars,new_sigma) = compose sigma (v,ft) in
            let (bool,new_rest_eq) = apply_subst rest_eq (v,ft) atomnames in
            if (bool=false) then
               raise Not_unifiable
            else
               let new_ordering = build_orderingJ (v::compose_vars) ft ordering atom_rel in
               tunify atomnames (List.tl fs) rt rt new_rest_eq new_sigma new_ordering

         in
         let apply_r6 fs ft rt rest_eq sigma =
(* print_endline "r6"; *)
            let v = (List.hd fs) in
            let (_,new_sigma) = (compose sigma (v,[])) in
            let (bool,new_rest_eq) = apply_subst rest_eq (v,[]) atomnames in
            if (bool=false) then
               raise Not_unifiable
            else
     (* no relation update since [] has been replaced for v *)
               tunify atomnames (List.tl fs) ft rt new_rest_eq new_sigma ordering

         in
         let apply_r7 fs ft rt rest_eq sigma =
(* print_endline "r7"; *)
            let v = (List.hd fs)
            and c1 = (List.hd rt)
            and c2t =(List.tl rt) in
            let (compose_vars,new_sigma) = (compose sigma (v,(ft @ [c1]))) in
            let (bool,new_rest_eq) = apply_subst rest_eq (v,(ft @ [c1])) atomnames in
            if bool=false then
               raise Not_unifiable
            else
               let new_ordering = build_orderingJ (v::compose_vars) (ft @ [c1]) ordering atom_rel in
               tunify atomnames (List.tl fs) []  c2t new_rest_eq new_sigma new_ordering


         in
         let apply_r8 fs ft rt rest_eq sigma =
(* print_endline "r8"; *)
            tunify atomnames  rt [(List.hd fs)] (List.tl fs) rest_eq sigma ordering

         in
         let apply_r9 fs ft rt rest_eq sigma =
(* print_endline "r9"; *)
            let v = (List.hd fs)
            and (max,subst) = sigma in
            let v_new = ("vnew"^(string_of_int max)) in
            let (compose_vars,new_sigma) = (compose ((max+1),subst) (v,(ft @ [v_new]))) in
            let (bool,new_rest_eq) = apply_subst rest_eq (v,(ft @ [v_new])) atomnames in
            if (bool=false) then
               raise Not_unifiable
            else
               let new_ordering =
                  build_orderingJ (v::compose_vars) (ft @ [v_new]) ordering atom_rel in
                 tunify atomnames rt [v_new] (List.tl fs) new_rest_eq new_sigma new_ordering

         in
         let apply_r10 fs ft rt rest_eq sigma =
(* print_endline "r10"; *)
            let x = List.hd rt in
            tunify atomnames fs (ft @ [x]) (List.tl rt) rest_eq sigma ordering

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


         else
            if r_10 fs ft rt then  (* not ri, i<10, and r10 possible if for instance *)
                         (* (s=[] and x=v1) or (z<>[] and xt=C1V1t') *)
               apply_r10 fs ft rt rest_eq sigma
            else  (* NO rule applicable *)
               raise Not_unifiable
      in
      match eqlist with
         [] ->
            init_sigma,orderingQ
       | f::rest_eq ->
            begin
(*  Format.open_box 0;
   print_equations [f];
   Format.print_flush ();
*)
               let (atomnames,(fs,ft)) = f in
               tunify atomnames fs [] ft rest_eq init_sigma orderingQ
            end

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
   let (sigma,_) = tunify_list full_eqlist (1,[]) orderingQ atom_rel in
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

let do_stringunify us ut ns nt equations fo_eqlist orderingQ atom_rel qmax =
   let (short_us,short_ut) = shorten us ut in (* apply intial rule R3 to eliminate common beginning *)
   let new_element = ([ns;nt],(short_us,short_ut)) in
   let full_eqlist =
      if List.mem new_element equations then
         equations @ fo_eqlist
      else
         (new_element::equations) @ fo_eqlist
   in
   try
(*  print_equations full_eqlist; *)
(* max-1 new variables have been used for the domain equations *)
      let (new_sigma,new_ordering) = tunify_list full_eqlist (1,[]) orderingQ atom_rel in
(* sigmaQ will not be returned in eqlist *)
      (new_sigma,(qmax,full_eqlist),new_ordering)
   with Not_unifiable ->
      raise Failed            (* new connection please *)

let rec one_equation gprefix dlist delta_0_prefixes n =
   match dlist with
      [] -> ([],n)
    | f::r ->
         let fprefix = List.assoc f delta_0_prefixes  in
         let (sf1,sg) = shorten fprefix gprefix
         and v_new = ("vnewq"^(string_of_int n)) in
         let fnew = sf1 @ [v_new] in
         let (rest_equations,new_n) = one_equation gprefix r delta_0_prefixes (n+1) in
         (([],(fnew,sg))::rest_equations),new_n

let rec make_domain_equations fo_pairs (gamma_0_prefixes,delta_0_prefixes) n =
   match fo_pairs with
      [] -> ([],n)
    | (g,dlist)::r ->
         let gprefix = List.assoc g gamma_0_prefixes in
         let (gequations,max) = one_equation gprefix dlist delta_0_prefixes n in
         let (rest_equations,new_max) =
            make_domain_equations r (gamma_0_prefixes,delta_0_prefixes) max in
         (gequations @ rest_equations),new_max

(* type of one unifier: int * ((string * string list) list)  *)
(* global failure: (0,[]) *)

let stringunify ext_atom try_one eqlist fo_pairs logic orderingQ atom_rel qprefixes =
   if logic = "C" then
      ((0,[]),(0,[]),orderingQ)
   else
      let (qmax,equations) = eqlist
      and us  = ext_atom.aprefix
      and ut  = try_one.aprefix
      and ns = ext_atom.aname
      and nt = try_one.aname in
      if qprefixes = ([],[]) then  (* prop case *)
         begin
(*     print_endline "This is the prop case"; *)
            let (new_sigma,new_eqlist)  = Jtunify.do_stringunify us ut ns nt equations
       (* prop unification only *)
            in
            (new_sigma,new_eqlist,[]) (* assume the empty reduction ordering during proof search *)
         end
      else
         begin
(*     print_endline "This is the FO case"; *)
(* fo_eqlist encodes the domain condition on J quantifier substitutions *)
(* Again, always computed for the whole substitution sigmaQ *)
            let (fo_eqlist,new_max) = make_domain_equations fo_pairs qprefixes qmax in
            begin
(*    Format.open_box 0;
   print_string "domain equations in";
   print_equations fo_eqlist;
   print_string "domain equations out";
   Format.print_flush ();
*)
               do_stringunify us ut ns nt equations fo_eqlist orderingQ atom_rel new_max
            end
         end

(**************************************** add multiplicity *********************************)

let rec subst_replace subst_list t =
   match subst_list with
      [] -> t
    | (old_t,new_t)::r ->
         let inter_term = var_subst t  old_t "dummy"  in
         let new_term = subst1 inter_term "dummy" new_t in
         subst_replace r new_term

let rename_pos x m =
   let pref = String.get x 0 in
   (Char.escaped pref)^(string_of_int m)

let update_position position m replace_n subst_list mult =
   let ({name=x; address=y; op=z; pol=p; pt=a; st=b; label=t}) = position in
   let nx = rename_pos x m in
   let nsubst_list =
      if b=Gamma_0 then
         let vx = mk_var_term (x^"_jprover")
         and vnx = mk_var_term (nx^"_jprover") in
            (vx,vnx)::subst_list
      else
         if b=Delta_0 then
            let sx = mk_string_term jprover_op x
            and snx = mk_string_term jprover_op nx in
            (sx,snx)::subst_list
         else
            subst_list
   in
   let nt = subst_replace nsubst_list t in
   let add_array = Array.of_list y in
   let _ = (add_array.(replace_n) <- mult) in
   let new_add = Array.to_list add_array in
   ({name=nx; address=new_add; op=z; pol=p; pt=a; st=b; label=nt},m,nsubst_list)

let rec append_orderings list_of_lists =
   match list_of_lists with
      [] ->
         []
    | f::r ->
         f @ (append_orderings r)

let rec union_orderings first_orderings =
   match first_orderings with
      [] ->
         StringSet.empty
    | (pos,fset)::r ->
         StringSet.union (StringSet.add pos fset) (union_orderings r)

let rec select_orderings add_orderings =
   match add_orderings with
      [] -> []
    | f::r ->
         (List.hd f)::select_orderings r

let combine_ordering_list add_orderings pos_name =
   let first_orderings = select_orderings add_orderings in
   let pos_succs = union_orderings first_orderings in
   let rest_orderings  = append_orderings add_orderings in
   (pos_name,pos_succs)::rest_orderings

let rec copy_and_rename_tree last_tree replace_n pos_n mult subst_list =

   let rec rename_subtrees tree_list nposition s_pos_n nsubst_list =
      match tree_list with
         [] -> ([||],[],s_pos_n)
       | f::r ->
            let (f_subtree,f_ordering,f_pos_n) =
               copy_and_rename_tree f replace_n s_pos_n  mult nsubst_list in
            let (r_subtrees,r_ordering_list,r_pos_n) = rename_subtrees r nposition f_pos_n nsubst_list in
            ((Array.append [|f_subtree|] r_subtrees),(f_ordering::r_ordering_list),r_pos_n)

   in
   match last_tree with
      Empty -> raise (Invalid_argument "Jprover: copy tree")
    | NodeAt(position) ->   (* can never be a Gamma_0 position -> no replacements *)
         let (nposition,npos_n,_) = update_position position (pos_n+1) replace_n subst_list mult in
         ((NodeAt(nposition)),[(nposition.name,StringSet.empty)],npos_n)
    | NodeA(position, suctrees) ->
         let (nposition,npos_n,nsubst_list) = update_position position (pos_n+1) replace_n subst_list mult in
         let (new_suctrees, new_ordering_list, new_pos_n) =
            rename_subtrees (Array.to_list suctrees) nposition npos_n nsubst_list in
         let new_ordering = combine_ordering_list new_ordering_list (nposition.name) in
         ((NodeA(nposition,new_suctrees)),new_ordering,new_pos_n)

(* we construct for each pos a list orderings representing and correspondning to the array of succtrees *)

let rec add_multiplicity ftree pos_n  mult logic =
   let rec parse_subtrees tree_list s_pos_n =
      match tree_list with
         [] -> ([||],[],s_pos_n)
       | f::r ->
            let (f_subtree,f_ordering,f_pos_n) = add_multiplicity f s_pos_n  mult logic in
            let (r_subtrees,r_ordering_list,r_pos_n) = parse_subtrees r f_pos_n in
            ((Array.append [|f_subtree|] r_subtrees),(f_ordering::r_ordering_list),r_pos_n)

   in
   match ftree with
      Empty -> raise (Invalid_argument "Jprover: add mult")
    | NodeAt(pos) -> (ftree,[(pos.name,StringSet.empty)],pos_n)
    | NodeA(pos,suctrees) ->
         let (new_suctrees, new_ordering_list, new_pos_n) = parse_subtrees (Array.to_list suctrees) pos_n in
         if (((pos.pt = Phi) & (((pos.op <> At) & (logic="J")) or ((pos.op = All) & (logic = "C"))))
          (* no explicit atom-instances *)
                or ((pos.pt = Gamma) & (pos.st <> Phi_0))) then   (* universal quantifiers are copied *)
                                                                (* at their Phi positions *)
            let replace_n = (List.length pos.address)  (* points to the following argument in the array_of_address *)
            and last = (Array.length new_suctrees) - 1 in (* array first element has index 0 *)
            let last_tree = new_suctrees.(last) in
            let (add_tree,add_ordering,final_pos_n) =
               copy_and_rename_tree last_tree replace_n new_pos_n mult [] in
            let final_suctrees = Array.append new_suctrees [|add_tree|]
            and add_orderings = List.append new_ordering_list [add_ordering] in
            let final_ordering = combine_ordering_list add_orderings (pos.name) in
            ((NodeA(pos,final_suctrees)),final_ordering,final_pos_n)
         else
            let final_ordering = combine_ordering_list new_ordering_list (pos.name) in
            ((NodeA(pos,new_suctrees)),final_ordering,new_pos_n)


(**************  Path checker   ****************************************************)

let rec get_sets atom atom_sets =
   match atom_sets with
      [] -> raise (Invalid_argument "Jprover bug: atom not found")
    | f::r ->
         let (a,b,c) = f in
         if atom = a then f
         else
            get_sets atom r

let rec get_connections a alpha tabulist =
   match alpha with
      [] -> []
    | f::r ->
         if (a.apredicate = f.apredicate) & (a.apol <> f.apol) & (not (List.mem f tabulist)) then
            (a,f)::(get_connections a r tabulist)
         else
            (get_connections a r tabulist)

let rec connections atom_rel tabulist =
   match atom_rel with
      [] -> []
    | f::r ->
         let (a,alpha,beta) = f in
         (get_connections a alpha tabulist) @ (connections r (a::tabulist))

let check_alpha_relation atom set atom_sets =
   let (a,alpha,beta) = get_sets atom atom_sets in
   AtomSet.subset set alpha

let rec extset  atom_sets path closed =
   match atom_sets with
      [] -> AtomSet.empty
    | f::r ->
         let (at,alpha,beta) = f in
         if (AtomSet.subset path alpha) & (AtomSet.subset closed beta) then
            AtomSet.add at (extset r path closed)
         else
            (extset r path closed)

let rec check_ext_list ext_list fail_set atom_sets =  (* fail_set consists of one atom only *)
   match ext_list with
      [] -> AtomSet.empty
    | f::r ->
         if (check_alpha_relation f fail_set atom_sets) then
            AtomSet.add f (check_ext_list r fail_set  atom_sets)
         else
            (check_ext_list r fail_set atom_sets)

let fail_ext_set ext_atom ext_set atom_sets =
   let ext_list = AtomSet.elements ext_set
   and fail_set  = AtomSet.add ext_atom AtomSet.empty in
   check_ext_list ext_list fail_set atom_sets

let rec ext_partners con path ext_atom (reduction_partners,extension_partners) atom_sets =
   match con with
      [] ->
         (reduction_partners,extension_partners)
    | f::r ->
         let (a,b) = f in
         if List.mem ext_atom [a;b] then
            let ext_partner =
               if ext_atom = a then b else a
            in
            let (new_red_partners,new_ext_partners) =
(* force reduction steps first *)
               if (AtomSet.mem ext_partner path) then
                  ((AtomSet.add ext_partner reduction_partners),extension_partners)
               else
                  if (check_alpha_relation ext_partner path atom_sets) then
                     (reduction_partners,(AtomSet.add ext_partner extension_partners))
                  else
                     (reduction_partners,extension_partners)
            in
            ext_partners r path ext_atom (new_red_partners,new_ext_partners) atom_sets
         else
            ext_partners r path ext_atom (reduction_partners,extension_partners) atom_sets

exception Failed_connections

let path_checker atom_rel atom_sets qprefixes init_ordering logic =

   let con = connections atom_rel [] in
   let rec provable path closed (orderingQ,reduction_ordering) eqlist (sigmaQ,sigmaJ) =

      let rec check_connections (reduction_partners,extension_partners) ext_atom =
         let try_one =
            if reduction_partners = AtomSet.empty then
               if extension_partners = AtomSet.empty then
                  raise Failed_connections
               else
                  AtomSet.choose extension_partners
            else
       (* force reduction steps always first!! *)
               AtomSet.choose reduction_partners
         in
(*         print_endline ("connection partner "^(try_one.aname)); *)
(*       print_endline ("partner path "^(print_set path));
*)
         (try
            let (new_sigmaQ,new_ordering_elements) = jqunify (ext_atom.alabel) (try_one.alabel) sigmaQ in
(* build the orderingQ incrementally from the new added substitution tau of new_sigmaQ *)
            let (relate_pairs,new_orderingQ) = build_orderingQ new_ordering_elements orderingQ in
(* we make in incremental reflexivity test during the string unification *)
            let (new_sigmaJ,new_eqlist,new_red_ordering) =
(* new_red_ordering = [] in propositional case *)
               stringunify ext_atom try_one eqlist relate_pairs logic new_orderingQ atom_rel qprefixes
            in
(*           print_endline ("make reduction ordering "^((string_of_int (List.length new_ordering)))); *)
            let new_closed = AtomSet.add ext_atom closed in
            let ((next_orderingQ,next_red_ordering),next_eqlist,(next_sigmaQ,next_sigmaJ),subproof) =
               if AtomSet.mem try_one path then
                  provable path new_closed (new_orderingQ,new_red_ordering) new_eqlist (new_sigmaQ,new_sigmaJ)
                     (* always use old first-order ordering for recursion *)
               else
                  let new_path = AtomSet.add ext_atom path
                  and extension = AtomSet.add try_one AtomSet.empty in
                  let ((norderingQ,nredordering),neqlist,(nsigmaQ,nsigmaJ),p1) =
                     provable new_path extension (new_orderingQ,new_red_ordering) new_eqlist (new_sigmaQ,new_sigmaJ) in
                  let ((nnorderingQ,nnredordering),nneqlist,(nnsigmaQ,nnsigmaJ),p2) =
                     provable path new_closed (norderingQ,nredordering) neqlist (nsigmaQ,nsigmaJ) in
                  ((nnorderingQ,nnredordering),nneqlist,(nnsigmaQ,nnsigmaJ),(p1 @ p2))
      (* first the extension subgoals = depth first; then other subgoals in same clause *)
            in
            ((next_orderingQ,next_red_ordering),next_eqlist,(next_sigmaQ,next_sigmaJ),(((ext_atom.aname),(try_one.aname))::subproof))
         with Failed ->
(*          print_endline ("new connection for "^(ext_atom.aname)); *)
(*            print_endline ("Failed"); *)
            check_connections ((AtomSet.remove try_one reduction_partners),
                               (AtomSet.remove try_one extension_partners)
                              ) ext_atom
         )

      in
      let rec check_extension  extset =
         if extset = AtomSet.empty then
            raise Failed             (* go directly to a new entry connection *)
         else
            let select_one = AtomSet.choose extset in
(*        print_endline ("extension literal "^(select_one.aname)); *)
(*        print_endline ("extension path "^(print_set path));*)
            let (reduction_partners,extension_partners) =
               ext_partners con path select_one (AtomSet.empty,AtomSet.empty) atom_sets in
            (try
               check_connections (reduction_partners,extension_partners) select_one
            with Failed_connections ->
(*         print_endline ("no connections for subgoal "^(select_one.aname)); *)
(*           print_endline ("Failed_connections"); *)
               let fail_ext_set = fail_ext_set select_one extset atom_sets in
               check_extension fail_ext_set
            )

      in
      let extset = extset atom_sets path closed in
      if extset = AtomSet.empty then
         ((orderingQ,reduction_ordering),eqlist,(sigmaQ,sigmaJ),[])
      else
         check_extension extset
   in
   if qprefixes = ([],[]) then
      begin
(*      print_endline "!!!!!!!!!!! prop prover !!!!!!!!!!!!!!!!!!"; *)
(* in the propositional case, the reduction ordering will be computed AFTER proof search *)
         let (_,eqlist,(_,(n,substJ)),ext_proof) =
            provable AtomSet.empty AtomSet.empty ([],[]) (1,[]) ([],(1,[])) in
         let orderingJ = build_orderingJ_list substJ init_ordering atom_rel in
         ((init_ordering,orderingJ),eqlist,([],(n,substJ)),ext_proof)
      end
   else
      provable AtomSet.empty AtomSet.empty (init_ordering,[]) (1,[]) ([],(1,[]))

(*************************** prepare and init prover *******************************************************)

let rec list_to_set list =
   match list with
      [] -> AtomSet.empty
    | f::r ->
         let rest_set = list_to_set r in
         AtomSet.add f rest_set

let rec make_atom_sets atom_rel =
   match atom_rel with
      [] -> []
    | f::r ->
         let (a,alpha,beta) =  f in
         (a,(list_to_set alpha),(list_to_set beta))::(make_atom_sets r)

let rec predecessor address_1 address_2 ftree =
   match ftree with
      Empty -> PNull            (* should not occur since every pair of atoms have a common predecessor *)
    | NodeAt(position) -> PNull (* should not occur as above *)
    | NodeA(position,suctrees) ->
         match address_1,address_2 with
            [],_ -> raise (Invalid_argument "Jprover: predecessors left")
          | _,[] -> raise (Invalid_argument "Jprover: predecessors right")
          | (f1::r1),(f2::r2) ->
               if f1 = f2 then
                  predecessor r1 r2 (suctrees.(f1-1))
               else
                  position.pt

let rec compute_sets element ftree alist =
   match alist with
      [] -> [],[]
    | first::rest ->
         if first = element then
            compute_sets element ftree rest    (* element is neithes alpha- nor beta-related to itself*)
         else
            let (alpha_rest,beta_rest) = compute_sets element ftree rest in
            if predecessor (element.aaddress) (first.aaddress) ftree = Beta then
               (alpha_rest,(first::beta_rest))
            else
               ((first::alpha_rest),beta_rest)

let rec compute_atomlist_relations worklist ftree alist =  (* last version of alist for total comparison *)
   let rec compute_atom_relations element ftree alist =
      let alpha_set,beta_set = compute_sets element ftree alist in
      (element,alpha_set,beta_set)
   in
   match worklist with
      [] -> []
    | first::rest ->
         let first_relations = compute_atom_relations first ftree alist in
         first_relations::(compute_atomlist_relations rest ftree alist)

let atom_record position prefix =
   let aname = (position.name) in
   let aprefix = (List.append prefix [aname]) in (* atom position is last element in prefix *)
   let aop = (dest_term position.label).term_op in
   ({aname=aname; aaddress=(position.address); aprefix=aprefix; apredicate=aop;
     apol=(position.pol); ast=(position.st); alabel=(position.label)})

let rec select_atoms_treelist treelist prefix =
   let rec select_atoms ftree prefix =
      match ftree with
         Empty -> [],[],[]
       | NodeAt(position) ->
            [(atom_record position prefix)],[],[]
       | NodeA(position,suctrees) ->
            let treelist = Array.to_list suctrees in
            let new_prefix =
               let prefix_element =
                  if List.mem (position.st) [Psi_0;Phi_0] then
                     [(position.name)]
                  else
                     []
               in
               (List.append prefix prefix_element)
            in
            let (gamma_0_element,delta_0_element) =
               if position.st = Gamma_0 then
                  begin
(*  Format.open_box 0;
   print_endline "gamma_0 prefixes ";
   print_string (position.name^" :");
   print_stringlist prefix;
   print_endline " ";
   Format.force_newline ();
   Format.print_flush ();
*)
                     [(position.name,prefix)],[]
                  end
               else
                  if position.st = Delta_0 then
                     begin
(* Format.open_box 0;
   print_endline "delta_0 prefixes ";
   print_string (position.name^" :");
   print_stringlist prefix;
   print_endline " ";
   Format.force_newline ();
   Format.print_flush ();
*)
                        [],[(position.name,prefix)]
                     end
                  else
                     [],[]
            in
            let (rest_alist,rest_gamma_0_prefixes,rest_delta_0_prefixes) =
               select_atoms_treelist treelist new_prefix in
            (rest_alist,(rest_gamma_0_prefixes @ gamma_0_element),
             (rest_delta_0_prefixes @ delta_0_element))

   in
   match treelist with
      [] -> [],[],[]
    | first::rest ->
         let (first_alist,first_gprefixes,first_dprefixes) = select_atoms first prefix
         and (rest_alist,rest_gprefixes,rest_dprefixes) = select_atoms_treelist rest prefix in
         ((first_alist @ rest_alist),(first_gprefixes @ rest_gprefixes),
          (first_dprefixes @ rest_dprefixes))

let prepare_prover ftree =
   let alist,gamma_0_prefixes,delta_0_prefixes = select_atoms_treelist [ftree] [] in
   let atom_rel = compute_atomlist_relations alist ftree alist in
   (atom_rel,(gamma_0_prefixes,delta_0_prefixes))

(* ************************ Build intial formula tree  and relations *********************************** *)
(* Building a formula tree and the tree ordering from the input formula, i.e. OCaml term *)

let make_position_name stype pos_n =
   let prefix =
      if List.mem stype [Phi_0;Gamma_0]
      then "v"
      else
         if List.mem stype [Psi_0;Delta_0]
         then "c"
         else
            "a"
   in
   prefix^(string_of_int pos_n)

let dual_pol pol =
   if pol = O then I else O

let check_subst_term (variable,old_term) pos_name stype =
   if (List.mem stype [Gamma_0;Delta_0]) then
      let new_variable =
         if stype = Gamma_0 then (mk_var_term (pos_name^"_jprover"))
         else
            (mk_string_term jprover_op pos_name)
      in
      (subst1 old_term variable new_variable) (* replace variable (non-empty) in t by pos_name *)
         (* pos_name is either a variable term or a constant, f.i. a string term *)
         (* !!! check unification module how handling eingenvariables as constants !!! *)
   else
      old_term

let rec build_ftree (variable,old_term) pol stype address pos_n =
   let pos_name = make_position_name stype pos_n in
   let term = check_subst_term (variable,old_term) pos_name stype in
   if JLogic.is_and_term term then
      let s,t = JLogic.dest_and term in
      let ptype,stype_1,stype_2 =
         if pol = O
         then Beta,Beta_1,Beta_2
         else
            Alpha,Alpha_1,Alpha_2
      in
      let position = {name=pos_name; address=address; op=And; pol=pol; pt=ptype; st=stype; label=term} in
      let subtree_left,ordering_left,posn_left = build_ftree ("",s) pol stype_1 (address@[1]) (pos_n+1) in
      let subtree_right,ordering_right,posn_right = build_ftree ("",t) pol stype_2 (address@[2])
            (posn_left+1) in
      let (succ_left,whole_left) = List.hd ordering_left
      and (succ_right,whole_right) = List.hd ordering_right in
      let pos_succs =
         (StringSet.add succ_left (StringSet.add succ_right (StringSet.union whole_left whole_right)))
      in
      (NodeA(position,[|subtree_left;subtree_right|]),
       ((position.name,pos_succs)::(ordering_left @ ordering_right)),
       posn_right
      )
   else
      if JLogic.is_or_term term then
         let s,t = JLogic.dest_or term in
         let ptype,stype_1,stype_2 =
            if pol = O
            then Alpha,Alpha_1,Alpha_2
            else
               Beta,Beta_1,Beta_2
         in
         let position = {name=pos_name; address=address; op=Or; pol=pol; pt=ptype; st=stype; label=term} in
         let subtree_left,ordering_left,posn_left = build_ftree ("",s) pol stype_1 (address@[1]) (pos_n+1) in
         let subtree_right,ordering_right,posn_right = build_ftree ("",t) pol stype_2 (address@[2])
               (posn_left+1) in
         let (succ_left,whole_left) = List.hd ordering_left
         and (succ_right,whole_right) = List.hd ordering_right in
         let pos_succs =
            StringSet.add succ_left (StringSet.add succ_right (StringSet.union whole_left whole_right)) in
         (NodeA(position,[|subtree_left;subtree_right|]),
          ((position.name),pos_succs) :: (ordering_left @ ordering_right),
          posn_right
         )
      else
         if JLogic.is_implies_term term then
            let s,t = JLogic.dest_implies term in
            let ptype_0,stype_0,ptype,stype_1,stype_2 =
               if pol = O
               then Psi,Psi_0,Alpha,Alpha_1,Alpha_2
               else
                  Phi,Phi_0,Beta,Beta_1,Beta_2
            in
            let pos2_name = make_position_name stype_0 (pos_n+1) in
            let sposition = {name=pos_name; address=address; op=Imp; pol=pol; pt=ptype_0; st=stype; label=term}
            and position = {name=pos2_name; address=address@[1]; op=Imp; pol=pol; pt=ptype; st=stype_0; label=term} in
            let subtree_left,ordering_left,posn_left = build_ftree ("",s) (dual_pol pol) stype_1 (address@[1;1])
                  (pos_n+2) in
            let subtree_right,ordering_right,posn_right = build_ftree ("",t) pol stype_2 (address@[1;2])
                  (posn_left+1) in
            let (succ_left,whole_left) = List.hd ordering_left
            and (succ_right,whole_right) = List.hd ordering_right in
            let pos_succs =
               StringSet.add succ_left (StringSet.add succ_right (StringSet.union whole_left whole_right)) in
            let pos_ordering = (position.name,pos_succs) :: (ordering_left @ ordering_right) in
            (NodeA(sposition,[|NodeA(position,[|subtree_left;subtree_right|])|]),
             ((sposition.name,(StringSet.add position.name pos_succs))::pos_ordering),
             posn_right
            )
         else
            if JLogic.is_not_term term then
               let s = JLogic.dest_not term in
               let ptype_0,stype_0,ptype,stype_1=
                  if pol = O
                  then Psi,Psi_0,Alpha,Alpha_1
                  else
                     Phi,Phi_0,Alpha,Alpha_1
               in
               let pos2_name = make_position_name stype_0 (pos_n+1) in
               let sposition = {name=pos_name; address=address; op=Neg; pol=pol; pt=ptype_0; st=stype; label=term}
               and position = {name=pos2_name; address=address@[1]; op=Neg; pol=pol; pt=ptype; st=stype_0; label=term} in
               let subtree_left,ordering_left,posn_left = build_ftree ("",s) (dual_pol pol) stype_1 (address@[1;1])
                     (pos_n+2) in
               let (succ_left,whole_left) = List.hd ordering_left in
               let pos_succs =
                  StringSet.add succ_left whole_left in
               let pos_ordering = (position.name,pos_succs) :: ordering_left in
               (NodeA(sposition,[|NodeA(position,[| subtree_left|])|]),
                ((sposition.name,(StringSet.add position.name pos_succs))::pos_ordering),
                posn_left
               )
            else
               if JLogic.is_exists_term term then
                  let v,s,t = JLogic.dest_exists term in  (* s is type of v and will be supressed here *)
                  let ptype,stype_1 =
                     if pol = O
                     then Gamma,Gamma_0
                     else
                        Delta,Delta_0
                  in
                  let position = {name=pos_name; address=address; op=Ex; pol=pol; pt=ptype; st=stype; label=term} in
                  let subtree_left,ordering_left,posn_left = build_ftree (v,t) pol stype_1 (address@[1]) (pos_n+1) in
                  let (succ_left,whole_left) = List.hd ordering_left in
                  let pos_succs =
                     StringSet.add succ_left whole_left in
                  (NodeA(position,[|subtree_left|]),
                   ((position.name,pos_succs) :: ordering_left),
                   posn_left
                  )
               else
                  if JLogic.is_all_term term then
                     let v,s,t = JLogic.dest_all term in
       (* s is type of v and will be supressed here *)
                     let ptype_0,stype_0,ptype,stype_1=
                        if pol = O
                        then Psi,Psi_0,Delta,Delta_0
                        else
                           Phi,Phi_0,Gamma,Gamma_0
                     in
                     let pos2_name = make_position_name stype_0 (pos_n+1) in
                     let sposition = {name=pos_name; address=address; op=All; pol=pol; pt=ptype_0; st=stype; label=term}
                     and position = {name=pos2_name; address=address@[1]; op=All; pol=pol; pt=ptype; st=stype_0; label=term} in
                     let subtree_left,ordering_left,posn_left = build_ftree (v,t) pol stype_1 (address@[1;1])
                           (pos_n+2) in
                     let (succ_left,whole_left) = List.hd ordering_left in
                     let pos_succs =
                        StringSet.add succ_left whole_left in
                     let pos_ordering = (position.name,pos_succs) :: ordering_left in
                     (NodeA(sposition,[|NodeA(position,[|subtree_left|])|]),
                      ((sposition.name,(StringSet.add position.name pos_succs))::pos_ordering),
                      posn_left
                     )
                  else      (* finally, term is atomic *)
                     let ptype_0,stype_0 =
                        if pol = O
                        then Psi,Psi_0
                        else
                           Phi,Phi_0
                     in
                     let pos2_name = make_position_name stype_0 (pos_n+1) in
                     let sposition = {name=pos_name; address=address; op=At; pol=pol; pt=ptype_0; st=stype; label=term}
                     and position = {name=pos2_name; address=address@[1]; op=At; pol=pol; pt=PNull; st=stype_0; label=term} in
                     (NodeA(sposition,[|NodeAt(position)|]),
                      [(sposition.name,(StringSet.add position.name StringSet.empty));(position.name,StringSet.empty)],
                      pos_n+1
                     )

let rec construct_ftree termlist treelist orderinglist pos_n goal =
   match termlist with
      [] ->
         let new_root = {name="w"; address=[]; op=Null; pol=O; pt=Psi; st=PNull_0; label=goal}
         and treearray = Array.of_list treelist in
         NodeA(new_root,treearray),(("w",(union_orderings orderinglist))::orderinglist),pos_n
    | ft::rest_terms ->
         let next_address = [((List.length treelist)+1)]
         and next_pol,next_goal =
            if rest_terms = []  then
               O,ft (* construct tree for the conclusion *)
            else
               I,goal
         in
         let new_tree,new_ordering,new_pos_n =
            build_ftree ("",ft) next_pol Alpha_1 next_address (pos_n+1) in
         construct_ftree rest_terms (treelist @ [new_tree])
            (orderinglist @ new_ordering) new_pos_n next_goal

(*************************** Main LOOP ************************************)
let unprovable = RefineError ("Jprover", StringError "formula is not provable")
let mult_limit_exn = RefineError ("Jprover", StringError "multiplicity limit reached")
let coq_exn = RefineError ("Jprover", StringError "interface for coq: error on ")

let init_prover ftree =
   let atom_relation,qprefixes = prepare_prover ftree in
(*      print_atom_info atom_relation;  *)  (* apple *)
   let atom_sets = make_atom_sets atom_relation in
   (atom_relation,atom_sets,qprefixes)


let rec try_multiplicity mult_limit ftree ordering pos_n mult logic =
   try
      let (atom_relation,atom_sets,qprefixes) = init_prover ftree in
      let ((orderingQ,red_ordering),eqlist,unifier,ext_proof) =
         path_checker atom_relation atom_sets qprefixes ordering logic in
      (ftree,red_ordering,eqlist,unifier,ext_proof)   (* orderingQ is not needed as return value *)
   with Failed ->
      match mult_limit with
         Some m when m == mult ->
            raise mult_limit_exn
       | _ ->
            let new_mult = mult+1 in
            begin
            Pp.msgnl (Pp.(++) (Pp.str "Multiplicity Fail: Trying new multiplicity ")
            (Pp.int new_mult));
(*
               Format.open_box 0;
               Format.force_newline ();
               Format.print_string "Multiplicity Fail: ";
               Format.print_string ("Try new multiplicity "^(string_of_int new_mult));
               Format.force_newline ();
               Format.print_flush ();
*)
               let (new_ftree,new_ordering,new_pos_n) =
                  add_multiplicity ftree pos_n new_mult logic in
               if (new_ftree = ftree) then
                  raise unprovable
               else
(*                  print_formula_info new_ftree new_ordering new_pos_n; *)  (* apple *)
                  try_multiplicity mult_limit new_ftree new_ordering new_pos_n new_mult logic
            end

let prove mult_limit termlist logic =
   let (ftree,ordering,pos_n) = construct_ftree termlist [] [] 0 (mk_var_term "dummy") in
(* pos_n = number of positions without new root "w" *)
(*   print_formula_info ftree ordering pos_n;   *)    (* apple *)
   try_multiplicity mult_limit ftree ordering pos_n 1 logic

(********** first-order type theory interface *******************)

let rec renam_free_vars termlist =
   match termlist
   with [] -> [],[]
    | f::r ->
         let var_names = free_vars_list f in
         let string_terms =
             List.map (fun x ->  (mk_string_term free_var_op x)) var_names
         in
         let mapping = List.combine var_names string_terms
         and new_f = subst f var_names string_terms in
         let (rest_mapping,rest_renamed) = renam_free_vars r in
         let unique_mapping = remove_dups_list (mapping @ rest_mapping) in
         (unique_mapping,(new_f::rest_renamed))

let rec apply_var_subst term var_subst_list =
   match var_subst_list with
      [] -> term
    | (v,t)::r ->
         let next_term = var_subst term t v in
         apply_var_subst next_term r

let rec make_equal_list n list_object =
   if n = 0 then
      []
   else
      list_object::(make_equal_list (n-1) list_object)

let rec create_output rule_list input_map =
   match rule_list with
      [] -> JLogic.empty_inf
    | f::r ->
         let (pos,(rule,term1,term2)) = f in
         let delta1_names = collect_delta_terms [term1]
         and delta2_names = collect_delta_terms [term2] in
         let unique_deltas = remove_dups_list (delta1_names @ delta2_names) in
         let delta_terms =
            List.map (fun x -> (mk_string_term jprover_op x)) unique_deltas in
         let delta_vars = List.map (fun x -> (x^"_jprover")) unique_deltas in
         let delta_map = List.combine delta_vars delta_terms in
         let var_mapping = (input_map @ delta_map) in
         let frees1 = free_vars_list term1
         and frees2 = free_vars_list term2 in
         let unique_object = mk_var_term "v0_jprover" in
         let unique_list1 = make_equal_list (List.length frees1) unique_object
         and unique_list2 = make_equal_list (List.length frees2) unique_object
         in
         let next_term1 = subst term1 frees1 unique_list1
         and next_term2 = subst term2 frees2 unique_list2 in
         let new_term1 = apply_var_subst next_term1 var_mapping
         and new_term2 = apply_var_subst next_term2 var_mapping
         and (a,b) = pos
         in

(* kick away the first argument, the position *)
         (JLogic.append_inf (create_output r input_map) (b,new_term1) (a,new_term2) rule)

let rec make_test_interface rule_list input_map =
   match rule_list with
      [] -> []
    | f::r ->
         let (pos,(rule,term1,term2)) = f in
         let delta1_names = collect_delta_terms [term1]
         and delta2_names = collect_delta_terms [term2] in
         let unique_deltas = remove_dups_list (delta1_names @ delta2_names) in
         let delta_terms =
            List.map (fun x -> (mk_string_term jprover_op x)) unique_deltas in
         let delta_vars = List.map (fun x -> (x^"_jprover")) unique_deltas in
         let delta_map = List.combine delta_vars delta_terms in
         let var_mapping = (input_map @ delta_map) in
         let frees1 = free_vars_list term1
         and frees2 = free_vars_list term2 in
         let unique_object = mk_var_term "v0_jprover" in
         let unique_list1 = make_equal_list (List.length frees1) unique_object
         and unique_list2 = make_equal_list (List.length frees2) unique_object
         in
         begin
(*
   print_endline "";
   print_endline "";
   print_stringlist frees1;
   print_endline "";
   print_stringlist frees2;
   print_endline "";
   print_endline "";
*)
            let next_term1 = subst term1 frees1 unique_list1
            and next_term2 = subst term2 frees2 unique_list2 in
            let new_term1 = apply_var_subst next_term1 var_mapping
            and new_term2 = apply_var_subst next_term2 var_mapping
            in
            (pos,(rule,new_term1,new_term2))::(make_test_interface r input_map)
         end

(**************************************************************)

let decomp_pos pos =
    let {name=n; address=a; label=l} = pos in
      (n,(a,l))

let rec build_formula_id ftree =
  let rec build_fid_list = function
     [] -> []
   | t::rest -> (build_formula_id t)@(build_fid_list rest)
  in
    match ftree with
        Empty  -> []
    | NodeAt(position) ->
        [decomp_pos position]
    | NodeA(position,subtrees) ->
        let tree_list = Array.to_list subtrees in
        (decomp_pos position)::(build_fid_list tree_list)

let rec encode1 = function      (* normal *)
      [] -> ""
    | i::r -> "_"^(string_of_int i)^(encode1 r)

let rec encode2 = function      (* move up *)
      [i] -> ""
    | i::r -> "_"^(string_of_int i)^(encode2 r)
    | _ -> raise coq_exn

let rec encode3 = function      (* move down *)
      [] -> "_1"
    | i::r -> "_"^(string_of_int i)^(encode3 r)

let lookup_coq str map =
  try
    let (il,t) = List.assoc str map in
        il
  with Not_found -> raise coq_exn

let create_coq_input inf map =
  let rec rec_coq_part inf =
    match inf with
        [] -> []
     |  (rule, (s1, t1), ((s2, t2) as k))::r ->
        begin
           match rule with
                Andl | Andr | Orl | Orr1 | Orr2 ->
                    (rule, (encode1 (lookup_coq s1 map), t1), k)::(rec_coq_part r)
             |  Impr | Impl | Negr | Negl | Ax ->
                    (rule, (encode2 (lookup_coq s1 map), t1), k)::(rec_coq_part r)
             | Exr ->
                    (rule, (encode1 (lookup_coq s1 map), t1),
                           (encode1 (lookup_coq s2 map), t2))::(rec_coq_part r)
             | Exl ->
                    (rule, (encode1 (lookup_coq s1 map), t1),
                           (encode3 (lookup_coq s1 map), t2))::(rec_coq_part r)
             | Allr | Alll ->
                    (rule, (encode2 (lookup_coq s1 map), t1),
                       (*    (s2, t2))::(rec_coq_part r) *)
                           (encode3 (lookup_coq s1 map), t2))::(rec_coq_part r)
             | _ -> raise coq_exn
        end
  in
    rec_coq_part inf

let gen_prover mult_limit logic calculus hyps concls =
   let (input_map,renamed_termlist) = renam_free_vars (hyps @ concls) in
   let (ftree,red_ordering,eqlist,(sigmaQ,sigmaJ),ext_proof) = prove mult_limit renamed_termlist logic in
   let sequent_proof = reconstruct ftree red_ordering sigmaQ ext_proof logic calculus in
      let idl = build_formula_id ftree in
(*      print_ftree ftree;   apple *)
         (* transform types and rename constants *)
     (* we can transform the eigenvariables AFTER proof reconstruction since *)
     (* new delta_0 constants may have been constructed during rule permutation *)
     (* from the LJmc to the LJ proof *)
     create_coq_input (create_output sequent_proof input_map) idl

let prover mult_limit hyps concl = gen_prover mult_limit "J" "LJ" hyps [concl]

(************* test with propositional proof reconstruction ************)

let rec count_axioms seq_list =
   match seq_list with
      [] -> 0
    | f::r ->
         let (rule,_,_) = f in
         if rule = Ax then
            1 + count_axioms r
         else
            count_axioms r

let do_prove mult_limit termlist logic calculus =
   try begin
      let (input_map,renamed_termlist) = renam_free_vars termlist in
      let (ftree,red_ordering,eqlist,(sigmaQ,sigmaJ),ext_proof) = prove mult_limit renamed_termlist logic in
      Format.open_box 0;
      Format.force_newline ();
      Format.force_newline ();
      Format.print_string "Extension proof ready";
      Format.force_newline ();
      Format.force_newline ();
      Format.print_string ("Length of Extension proof: "^((string_of_int (List.length ext_proof)))^
                           " Axioms");
      Format.force_newline ();
      Format.force_newline ();
      print_endline "Extension proof:";
      Format.open_box 0;
      print_pairlist ext_proof;       (* print list of type (string * string) list *)
      Format.force_newline ();
      Format.force_newline ();
      Format.force_newline ();
      Format.print_flush ();
      Format.print_flush ();
      Format.open_box 0;
      print_ordering red_ordering;
      Format.print_flush ();
      Format.open_box 0;
      Format.force_newline ();
(* ----------------------------------------------- *)
      Format.open_box 0;
      print_tunify sigmaJ;
      Format.print_flush ();
      print_endline "";
      print_endline "";
      print_sigmaQ sigmaQ;
      print_endline "";
      print_endline "";
      Format.open_box 0;
      let (qmax,equations) = eqlist in
      print_endline ("number of quantifier domains : "^(string_of_int (qmax-1)));
      print_endline "";
      print_equations equations;
      Format.print_flush ();
      print_endline "";
      print_endline "";
      print_endline ("Length of equations : "^((string_of_int (List.length equations))));
      print_endline "";
      print_endline "";
(* --------------------------------------------------------- *)
      Format.print_string "Break ... ";
      print_endline "";
      print_endline "";
      Format.print_flush ();
      let reconstr_proof = reconstruct ftree red_ordering sigmaQ ext_proof logic calculus in
      let sequent_proof = make_test_interface reconstr_proof input_map in
      Format.open_box 0;
      Format.force_newline ();
      Format.force_newline ();
      Format.print_string "Sequent proof ready";
      Format.force_newline ();
      Format.force_newline ();
      Format.print_flush ();
      let (ptree,count_ax) = bproof sequent_proof in
      Format.open_box 0;
      Format.print_string ("Length of sequent proof: "^((string_of_int count_ax))^" Axioms");
      Format.force_newline ();
      Format.force_newline ();
      Format.force_newline ();
      Format.force_newline ();
      Format.print_flush ();
      tt ptree;
      Format.print_flush ();
      print_endline "";
      print_endline ""
   end with exn -> begin
      print_endline "Jprover got an exception:";
      print_endline (Printexc.to_string exn)
   end

let test concl logic calculus =  (* calculus should be LJmc or LJ for J, and LK for C *)
   do_prove None [concl] logic calculus

(* for sequents *)

let seqtest list_term logic calculus =
   let bterms = (dest_term list_term).term_terms in
   let termlist = collect_subterms bterms in
   do_prove None termlist logic calculus

(*****************************************************************)

end (* of struct *)
