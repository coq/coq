(* -*- mode: coq; coq-prog-args: ("-R" "." "Fiat" "-top" "BooleanRecognizerMin" "-R" "." "Top") -*- *)
(* File reduced by coq-bug-finder from original input, then from 2475 lines to 729 lines, then from 746 lines to 658 lines, then from 675 lines to 658 lines *)
(* coqc version 8.5beta3 (November 2015) compiled on Nov 11 2015 18:23:0 with OCaml 4.01.0
   coqtop version 8.5beta3 (November 2015) *)
(* Variable P : forall n m : nat, n = m -> Prop. *)
(* Axiom Prefl : forall n : nat, P n n eq_refl. *)
Axiom proof_admitted : False.

Tactic Notation "admit" := case proof_admitted.

Require Coq.Program.Program.
Require Coq.Strings.String.
Require Coq.omega.Omega.
Module Export Fiat_DOT_Common.
Module Export Fiat.
Module Common.
Import Coq.Lists.List.
Export Coq.Program.Program.

Global Set Implicit Arguments.

Global Coercion is_true : bool >-> Sortclass.
Coercion bool_of_sum {A B} (b : sum A B) : bool := if b then true else false.

Fixpoint ForallT {T} (P : T -> Type) (ls : list T) : Type
  := match ls return Type with
     | nil => True
     | x::xs => (P x * ForallT P xs)%type
     end.
Fixpoint Forall_tails {T} (P : list T -> Type) (ls : list T) : Type
  := match ls with
     | nil => P nil
     | x::xs => (P (x::xs) * Forall_tails P xs)%type
     end.

End Common.

End Fiat.

End Fiat_DOT_Common.
Module Export Fiat_DOT_Parsers_DOT_StringLike_DOT_Core.
Module Export Fiat.
Module Export Parsers.
Module Export StringLike.
Module Export Core.
Import Coq.Relations.Relation_Definitions.
Import Coq.Classes.Morphisms.

Local Coercion is_true : bool >-> Sortclass.

Module Export StringLike.
  Class StringLike {Char : Type} :=
    {
      String :> Type;
      is_char : String -> Char -> bool;
      length : String -> nat;
      take : nat -> String -> String;
      drop : nat -> String -> String;
      get : nat -> String -> option Char;
      unsafe_get : nat -> String -> Char;
      bool_eq : String -> String -> bool;
      beq : relation String := fun x y => bool_eq x y
    }.

  Arguments StringLike : clear implicits.
  Infix "=s" := (@beq _ _) (at level 70, no associativity) : type_scope.
  Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
  Local Open Scope string_like_scope.

  Class StringLikeProperties (Char : Type) `{StringLike Char} :=
    {
      singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
      singleton_exists : forall s, length s = 1 -> exists ch, s ~= [ ch ];
      get_0 : forall s ch, take 1 s ~= [ ch ] <-> get 0 s = Some ch;
      get_S : forall n s, get (S n) s = get n (drop 1 s);
      unsafe_get_correct : forall n s ch, get n s = Some ch -> unsafe_get n s = ch;
      length_singleton : forall s ch, s ~= [ ch ] -> length s = 1;
      bool_eq_char : forall s s' ch, s ~= [ ch ] -> s' ~= [ ch ] -> s =s s';
      is_char_Proper :> Proper (beq ==> eq ==> eq) is_char;
      length_Proper :> Proper (beq ==> eq) length;
      take_Proper :> Proper (eq ==> beq ==> beq) take;
      drop_Proper :> Proper (eq ==> beq ==> beq) drop;
      bool_eq_Equivalence :> Equivalence beq;
      bool_eq_empty : forall str str', length str = 0 -> length str' = 0 -> str =s str';
      take_short_length : forall str n, n <= length str -> length (take n str) = n;
      take_long : forall str n, length str <= n -> take n str =s str;
      take_take : forall str n m, take n (take m str) =s take (min n m) str;
      drop_length : forall str n, length (drop n str) = length str - n;
      drop_0 : forall str, drop 0 str =s str;
      drop_drop : forall str n m, drop n (drop m str) =s drop (n + m) str;
      drop_take : forall str n m, drop n (take m str) =s take (m - n) (drop n str);
      take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str);
      bool_eq_from_get : forall str str', (forall n, get n str = get n str') -> str =s str'
    }.
Global Arguments StringLikeProperties _ {_}.
End StringLike.

End Core.

End StringLike.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_StringLike_DOT_Core.

Module Export Fiat_DOT_Parsers_DOT_ContextFreeGrammar_DOT_Core.
Module Export Fiat.
Module Export Parsers.
Module Export ContextFreeGrammar.
Module Export Core.
Import Coq.Strings.String.
Import Coq.Lists.List.
Export Fiat.Parsers.StringLike.Core.

Section cfg.
  Context {Char : Type}.

  Section definitions.

    Inductive item :=
    | Terminal (_ : Char)
    | NonTerminal (_ : string).

    Definition production := list item.
    Definition productions := list production.

    Record grammar :=
      {
        Start_symbol :> string;
        Lookup :> string -> productions;
        Start_productions :> productions := Lookup Start_symbol;
        Valid_nonterminals : list string;
        Valid_productions : list productions := map Lookup Valid_nonterminals
      }.
  End definitions.

  End cfg.

Arguments item _ : clear implicits.
Arguments production _ : clear implicits.
Arguments productions _ : clear implicits.
Arguments grammar _ : clear implicits.

End Core.

End ContextFreeGrammar.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_ContextFreeGrammar_DOT_Core.

Module Export Fiat_DOT_Parsers_DOT_BaseTypes.
Module Export Fiat.
Module Export Parsers.
Module Export BaseTypes.
Import Coq.Arith.Wf_nat.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      nonterminal_carrierT : Type;
      of_nonterminal : String.string -> nonterminal_carrierT;
      to_nonterminal : nonterminal_carrierT -> String.string;
      initial_nonterminals_data : nonterminals_listT;
      nonterminals_length : nonterminals_listT -> nat;
      is_valid_nonterminal : nonterminals_listT -> nonterminal_carrierT -> bool;
      remove_nonterminal : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT }.

  Class parser_removal_dataT' `{predata : parser_computational_predataT} :=
    { nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop
      := ltof _ nonterminals_length;
      nonterminals_length_zero : forall ls,
                                   nonterminals_length ls = 0
                                   -> forall nt, is_valid_nonterminal ls nt = false;
      remove_nonterminal_dec : forall ls nonterminal,
                                 is_valid_nonterminal ls nonterminal
                                 -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
      remove_nonterminal_noninc : forall ls nonterminal,
                                    ~nonterminals_listT_R ls (remove_nonterminal ls nonterminal);
      initial_nonterminals_correct : forall nonterminal,
                                       is_valid_nonterminal initial_nonterminals_data (of_nonterminal nonterminal) <-> List.In nonterminal (Valid_nonterminals G);
      initial_nonterminals_correct' : forall nonterminal,
                                       is_valid_nonterminal initial_nonterminals_data nonterminal <-> List.In (to_nonterminal nonterminal) (Valid_nonterminals G);
      to_of_nonterminal : forall nonterminal,
                            List.In nonterminal (Valid_nonterminals G)
                            -> to_nonterminal (of_nonterminal nonterminal) = nonterminal;
      of_to_nonterminal : forall nonterminal,
                            is_valid_nonterminal initial_nonterminals_data nonterminal
                            -> of_nonterminal (to_nonterminal nonterminal) = nonterminal;
      ntl_wf : well_founded nonterminals_listT_R
      := well_founded_ltof _ _;
      remove_nonterminal_1
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps'
          -> is_valid_nonterminal ls ps';
      remove_nonterminal_2
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
          <-> is_valid_nonterminal ls ps' = false \/ ps = ps' }.

  Class split_dataT :=
    { split_string_for_production
      : item Char -> production Char -> String -> list nat }.

  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_data :> split_dataT }.
End recursive_descent_parser.

End BaseTypes.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_BaseTypes.

Module Export Fiat_DOT_Common_DOT_List_DOT_Operations.
Module Export Fiat.
Module Export Common.
Module Export List.
Module Export Operations.

Import Coq.Lists.List.

Module Export List.
  Section InT.
    Context {A : Type} (a : A).

    Fixpoint InT (ls : list A) : Set
      := match ls return Set with
           | nil => False
           | b :: m => (b = a) + InT m
         end%type.
  End InT.

  End List.

End Operations.

End List.

End Common.

End Fiat.

End Fiat_DOT_Common_DOT_List_DOT_Operations.

Module Export Fiat_DOT_Parsers_DOT_StringLike_DOT_Properties.
Module Export Fiat.
Module Export Parsers.
Module Export StringLike.
Module Export Properties.

Section String.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Lemma take_length {str n}
  : length (take n str) = min n (length str).
admit.
Defined.

  End String.

End Properties.

End StringLike.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_StringLike_DOT_Properties.

Module Export Fiat_DOT_Parsers_DOT_ContextFreeGrammar_DOT_Properties.
Module Export Fiat.
Module Export Parsers.
Module Export ContextFreeGrammar.
Module Export Properties.

Local Open Scope list_scope.
Definition production_is_reachableT {Char} (G : grammar Char) (p : production Char)
  := { nt : _
   & { prefix : _
     & List.In nt (Valid_nonterminals G)
       * List.InT
            (prefix ++ p)
            (Lookup G nt) } }%type.

End Properties.

End ContextFreeGrammar.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_ContextFreeGrammar_DOT_Properties.

Module Export Fiat_DOT_Parsers_DOT_MinimalParse.
Module Export Fiat.
Module Export Parsers.
Module Export MinimalParse.
Import Coq.Lists.List.
Import Fiat.Parsers.ContextFreeGrammar.Core.

Local Coercion is_true : bool >-> Sortclass.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT}
          {rdata' : @parser_removal_dataT' _ G predata}.

  Inductive minimal_parse_of
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      productions Char -> Type :=
  | MinParseHead : forall len0 valid str pat pats,
                     @minimal_parse_of_production len0 valid str pat
                     -> @minimal_parse_of len0 valid str (pat::pats)
  | MinParseTail : forall len0 valid str pat pats,
                     @minimal_parse_of len0 valid str pats
                     -> @minimal_parse_of len0 valid str (pat::pats)
  with minimal_parse_of_production
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      production Char -> Type :=
  | MinParseProductionNil : forall len0 valid str,
                              length str = 0
                              -> @minimal_parse_of_production len0 valid str nil
  | MinParseProductionCons : forall len0 valid str n pat pats,
                               length str <= len0
                               -> @minimal_parse_of_item len0 valid (take n str) pat
                               -> @minimal_parse_of_production len0 valid (drop n str) pats
                               -> @minimal_parse_of_production len0 valid str (pat::pats)
  with minimal_parse_of_item
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      item Char -> Type :=
  | MinParseTerminal : forall len0 valid str ch,
                         str ~= [ ch ]
                         -> @minimal_parse_of_item len0 valid str (Terminal ch)
  | MinParseNonTerminal
    : forall len0 valid str (nt : String.string),
        @minimal_parse_of_nonterminal len0 valid str nt
        -> @minimal_parse_of_item len0 valid str (NonTerminal nt)
  with minimal_parse_of_nonterminal
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      String.string -> Type :=
  | MinParseNonTerminalStrLt
    : forall len0 valid (nt : String.string) str,
        length str < len0
        -> is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)
        -> @minimal_parse_of (length str) initial_nonterminals_data str (Lookup G nt)
        -> @minimal_parse_of_nonterminal len0 valid str nt
  | MinParseNonTerminalStrEq
    : forall len0 str valid nonterminal,
        length str = len0
        -> is_valid_nonterminal initial_nonterminals_data (of_nonterminal nonterminal)
        -> is_valid_nonterminal valid (of_nonterminal nonterminal)
        -> @minimal_parse_of len0 (remove_nonterminal valid (of_nonterminal nonterminal)) str (Lookup G nonterminal)
        -> @minimal_parse_of_nonterminal len0 valid str nonterminal.

End cfg.

End MinimalParse.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_MinimalParse.

Module Export Fiat_DOT_Parsers_DOT_CorrectnessBaseTypes.
Module Export Fiat.
Module Export Parsers.
Module Export CorrectnessBaseTypes.
Import Coq.Lists.List.
Import Fiat.Parsers.ContextFreeGrammar.Core.
Import Fiat_DOT_Common.Fiat.Common.
Section general.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.

  Definition split_list_completeT_for {data : @parser_computational_predataT}
             {len0 valid}
             (it : item Char) (its : production Char)
             (str : String)
             (pf : length str <= len0)
             (split_list : list nat)

    := ({ n : nat
              & (minimal_parse_of_item (G := G) (predata := data) len0 valid (take n str) it)
                * (minimal_parse_of_production (G := G) len0 valid (drop n str) its) }%type)
       -> ({ n : nat
                 & (In (min (length str) n) (map (min (length str)) split_list))
                   * (minimal_parse_of_item (G := G) len0 valid (take n str) it)
                   * (minimal_parse_of_production (G := G) len0 valid (drop n str) its) }%type).

  Definition split_list_completeT {data : @parser_computational_predataT}
             (splits : item Char -> production Char -> String -> list nat)
    := forall len0 valid str (pf : length str <= len0) nt,
         is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)
         -> ForallT
              (Forall_tails
                 (fun prod
                  => match prod return Type with
                       | nil => True
                       | it::its
                         => @split_list_completeT_for data len0 valid it its str pf (splits it its str)
                     end))
              (Lookup G nt).

  Class boolean_parser_completeness_dataT' {data : boolean_parser_dataT} :=
    { split_string_for_production_complete
      : split_list_completeT split_string_for_production }.
End general.

End CorrectnessBaseTypes.

End Parsers.

End Fiat.

End Fiat_DOT_Parsers_DOT_CorrectnessBaseTypes.

Module Export Fiat.
Module Export Parsers.
Module Export ContextFreeGrammar.
Module Export Valid.
Export Fiat.Parsers.StringLike.Core.

Section cfg.
  Context {Char : Type} {HSL : StringLike Char} (G : grammar Char)
          {predata : parser_computational_predataT}.

  Definition item_valid (it : item Char)
    := match it with
         | Terminal _ => True
         | NonTerminal nt' => is_true (is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt'))
       end.

  Definition production_valid pat
    := List.Forall item_valid pat.

  Definition productions_valid pats
    := List.Forall production_valid pats.

  Definition grammar_valid
    := forall nt,
         List.In nt (Valid_nonterminals G)
         -> productions_valid (Lookup G nt).
End cfg.

End Valid.

Section app.
  Context {Char : Type} {HSL : StringLike Char} (G : grammar Char)
          {predata : parser_computational_predataT}.

  Lemma hd_production_valid
        (it : item Char)
        (its : production Char)
        (H : production_valid (it :: its))
  : item_valid it.
admit.
Defined.

  Lemma production_valid_cons
        (it : item Char)
        (its : production Char)
        (H : production_valid (it :: its))
  : production_valid its.
admit.
Defined.

  End app.

Import Coq.Lists.List.
Import Coq.omega.Omega.
Import Fiat_DOT_Common.Fiat.Common.
Import Fiat.Parsers.ContextFreeGrammar.Valid.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} (G : grammar Char).
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ G data}
          {rdata : @parser_removal_dataT' _ G _}
          {gvalid : grammar_valid G}.

  Local Notation dec T := (T + (T -> False))%type (only parsing).

  Local Notation iffT x y := ((x -> y) * (y -> x))%type (only parsing).

  Lemma dec_prod {A B} (HA : dec A) (HB : dec B) : dec (A * B).
admit.
Defined.

  Lemma dec_In {A} {P : A -> Type} (HA : forall a, dec (P a)) ls
  : dec { a : _ & (In a ls * P a) }.
admit.
Defined.

      Section item.
        Context {len0 valid}
                (str : String)
                (str_matches_nonterminal'
                 : nonterminal_carrierT -> bool)
                (str_matches_nonterminal
                 : forall nt : nonterminal_carrierT,
                     dec (minimal_parse_of_nonterminal (G := G) len0 valid str (to_nonterminal nt))).

        Section valid.
          Context (Hmatches
                   : forall nt,
                       is_valid_nonterminal initial_nonterminals_data nt
                       -> str_matches_nonterminal nt = str_matches_nonterminal' nt :> bool)
                  (it : item Char)
                  (Hvalid : item_valid it).

          Definition parse_item'
          : dec (minimal_parse_of_item (G := G) len0 valid str it).
          Proof.
            clear Hvalid.
            refine (match it return dec (minimal_parse_of_item len0 valid str it) with
                      | Terminal ch => if Sumbool.sumbool_of_bool (str ~= [ ch ])
                                       then inl (MinParseTerminal _ _ _ _ _)
                                       else inr (fun _ => !)
                      | NonTerminal nt => if str_matches_nonterminal (of_nonterminal nt)
                                          then inl (MinParseNonTerminal _)
                                          else inr (fun _ => !)
                    end);
              clear str_matches_nonterminal Hmatches;
              admit.
          Defined.
        End valid.

        End item.
        Context {len0 valid}
                (parse_nonterminal
                 : forall (str : String) (len : nat) (Hlen : length str = len) (pf : len <= len0) (nt : nonterminal_carrierT),
                     dec (minimal_parse_of_nonterminal (G := G) len0 valid str (to_nonterminal nt))).

        Lemma dec_in_helper {ls it its str}
        : iffT {n0 : nat &
                     (In (min (length str) n0) (map (min (length str)) ls) *
                      minimal_parse_of_item (G := G) len0 valid (take n0 str) it *
                      minimal_parse_of_production (G := G) len0 valid (drop n0 str) its)%type}
               {n0 : nat &
                     (In n0 ls *
                      (minimal_parse_of_item (G := G) len0 valid (take n0 str) it *
                       minimal_parse_of_production (G := G) len0 valid (drop n0 str) its))%type}.
admit.
Defined.

        Lemma parse_production'_helper {str it its} (pf : length str <= len0)
        : dec {n0 : nat &
                    (minimal_parse_of_item (G := G) len0 valid (take n0 str) it *
                     minimal_parse_of_production (G := G) len0 valid (drop n0 str) its)%type}
          -> dec (minimal_parse_of_production (G := G) len0 valid str (it :: its)).
admit.
Defined.
        Local Ltac t_parse_production_for := repeat
                      match goal with
              | [ H : (beq_nat _ _) = true |- _ ] => apply EqNat.beq_nat_true in H
              | _ => progress subst
              | _ => solve [ constructor; assumption ]
              | [ H : minimal_parse_of_production _ _ _ nil |- _ ] => (inversion H; clear H)
              | [ H : minimal_parse_of_production _ _ _ (_::_) |- _ ] => (inversion H; clear H)
              | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
              | _ => progress simpl in *
              | _ => discriminate
              | [ H : forall x, (_ * _)%type -> _ |- _ ] => specialize (fun x y z => H x (y, z))
              | _ => solve [ eauto with nocore ]
              | _ => solve [ apply Min.min_case_strong; omega ]
              | _ => omega
              | [ H : production_valid (_::_) |- _ ]
                => let H' := fresh in
                   pose proof H as H';
                     apply production_valid_cons in H;
                     apply hd_production_valid in H'
            end.

        Definition parse_production'_for
                 (splits : item Char -> production Char -> String -> list nat)
                 (Hsplits : forall str it its (Hreachable : production_is_reachableT G (it::its)) pf', split_list_completeT_for (len0 := len0) (G := G) (valid := valid) it its str pf' (splits it its str))
                 (str : String)
                 (len : nat)
                 (Hlen : length str = len)
                 (pf : len <= len0)
                 (prod : production Char)
                 (Hreachable : production_is_reachableT G prod)
        : dec (minimal_parse_of_production (G := G) len0 valid str prod).
        Proof.
          revert prod Hreachable str len Hlen pf.
          refine
            ((fun pf_helper =>
               list_rect
                 (fun prod =>
                    forall (Hreachable : production_is_reachableT G prod)
                           (str : String)
                           (len : nat)
                           (Hlen : length str = len)
                           (pf : len <= len0),
                      dec (minimal_parse_of_production (G := G) len0 valid str prod))
                 (
                   fun Hreachable str len Hlen pf
                   => match Utils.dec (beq_nat len 0) with
                        | left H => inl _
                        | right H => inr (fun p => _)
                      end)
                 (fun it its parse_production' Hreachable str len Hlen pf
                  => parse_production'_helper
                       _
                       (let parse_item := (fun n pf => parse_item' (parse_nonterminal (take n str) (len := min n len) (eq_trans take_length (f_equal (min _) Hlen)) pf) it) in
                        let parse_item := (fun n => parse_item n (Min.min_case_strong n len (fun k => k <= len0) (fun Hlen => (Nat.le_trans _ _ _ Hlen pf)) (fun Hlen => pf))) in
                        let parse_production := (fun n => parse_production' (pf_helper it its Hreachable) (drop n str) (len - n) (eq_trans (drop_length _ _) (f_equal (fun x => x - _) Hlen)) (Nat.le_trans _ _ _ (Nat.le_sub_l _ _) pf)) in
                        match dec_In
                                (fun n => dec_prod (parse_item n) (parse_production n))
                                (splits it its str)
                        with
                          | inl p => inl (existT _ (projT1 p) (snd (projT2 p)))
                          | inr p
                            => let pf' := (Nat.le_trans _ _ _ (Nat.eq_le_incl _ _ Hlen) pf) in
                               let H := (_ : split_list_completeT_for (G := G) (len0 := len0) (valid := valid) it its str pf' (splits it its str)) in
                               inr (fun p' => p (fst dec_in_helper (H p')))
                        end)
              )) _);
            [ clear parse_nonterminal Hsplits splits rdata cdata
            | clear parse_nonterminal Hsplits splits rdata cdata
            | ..
            | admit ].
          abstract t_parse_production_for.
          abstract t_parse_production_for.
          abstract t_parse_production_for.
          abstract t_parse_production_for.
        Defined.
