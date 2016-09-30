(* Lifted from https://coq.inria.fr/bugs/show_bug.cgi?id=4187 *)
(* File reduced by coq-bug-finder from original input, then from 715 lines to 696 lines *)
(* coqc version 8.4pl5 (December 2014) compiled on Dec 28 2014 03:23:16 with OCaml 4.01.0
   coqtop version 8.4pl5 (December 2014) *)
Set Asymmetric Patterns.
Axiom proof_admitted : False.
Tactic Notation "admit" := case proof_admitted.
Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Global Set Implicit Arguments.
Global Generalizable All Variables.
Coercion is_true : bool >-> Sortclass.
Coercion bool_of_sumbool {A B} (x : {A} + {B}) : bool := if x then true else false.
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

Module Export ADTSynthesis_DOT_Common_DOT_Wf.
Module Export ADTSynthesis.
Module Export Common.
Module Export Wf.

Section wf.
  Section wf_prod.
    Context A B (RA : relation A) (RB : relation B).
Definition prod_relation : relation (A * B).
exact (fun ab a'b' =>
           RA (fst ab) (fst a'b') \/ (fst a'b' = fst ab /\ RB (snd ab) (snd a'b'))).
Defined.

    Fixpoint well_founded_prod_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : well_founded RB) {struct wf_A}
    : Acc prod_relation (a, b)
      := match wf_A with
           | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc RB b') : Acc prod_relation (a, b')
                              := Acc_intro
                                   _
                                   (fun ab =>
                                      match ab as ab return prod_relation ab (a, b') -> Acc prod_relation ab with
                                        | (a'', b'') =>
                                          fun pf =>
                                            match pf with
                                              | or_introl pf'
                                                => @well_founded_prod_relation_helper
                                                     _ _
                                                     (fa _ pf')
                                                     wf_B
                                              | or_intror (conj pfa pfb)
                                                => match wf_B' with
                                                     | Acc_intro fb
                                                       => eq_rect
                                                            _
                                                            (fun a'' => Acc prod_relation (a'', b''))
                                                            (wf_B_rec _ (fb _ pfb))
                                                            _
                                                            pfa
                                                   end
                                            end
                                      end)
                             ) b (wf_B b)
         end.

    Definition well_founded_prod_relation : well_founded RA -> well_founded RB -> well_founded prod_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_prod_relation_helper; auto.
    Defined.
  End wf_prod.

  Section wf_projT1.
    Context A (B : A -> Type) (R : relation A).
Definition projT1_relation : relation (sigT B).
exact (fun ab a'b' =>
           R (projT1 ab) (projT1 a'b')).
Defined.

    Definition well_founded_projT1_relation : well_founded R -> well_founded projT1_relation.
    Proof.
      intros wf [a b]; hnf in *.
      induction (wf a) as [a H IH].
      constructor.
      intros y r.
      specialize (IH _ r (projT2 y)).
      destruct y.
      exact IH.
    Defined.
  End wf_projT1.
End wf.

Section Fix3.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c, D a b c -> Type)
          (F : forall x : A, (forall y : A, R y x -> forall b c d, P y b c d) -> forall b c d, P x b c d).
Definition Fix3 a b c d : @P a b c d.
exact (@Fix { a : A & { b : B a & { c : C b & D c } } }
            (fun x y => R (projT1 x) (projT1 y))
            (well_founded_projT1_relation Rwf)
            (fun abcd => P (projT2 (projT2 (projT2 abcd))))
            (fun x f => @F (projT1 x) (fun y r b c d => f (existT _ y (existT _ b (existT _ c d))) r) _ _ _)
            (existT _ a (existT _ b (existT _ c d)))).
Defined.
End Fix3.

End Wf.

End Common.

End ADTSynthesis.

End ADTSynthesis_DOT_Common_DOT_Wf.

Module Export ADTSynthesis_DOT_Parsers_DOT_StringLike_DOT_Core.
Module Export ADTSynthesis.
Module Export Parsers.
Module Export StringLike.
Module Export Core.
Import Coq.Setoids.Setoid.
Import Coq.Classes.Morphisms.



Module Export StringLike.
  Class StringLike {Char : Type} :=
    {
      String :> Type;
      is_char : String -> Char -> bool;
      length : String -> nat;
      take : nat -> String -> String;
      drop : nat -> String -> String;
      bool_eq : String -> String -> bool;
      beq : relation String := fun x y => bool_eq x y
    }.

  Arguments StringLike : clear implicits.
  Infix "=s" := (@beq _ _) (at level 70, no associativity) : type_scope.
  Notation "s ~= [ ch ]" := (is_char s ch) (at level 70, no associativity) : string_like_scope.
  Local Open Scope string_like_scope.

  Definition str_le `{StringLike Char} (s1 s2 : String)
    := length s1 < length s2 \/ s1 =s s2.
  Infix "≤s" := str_le (at level 70, right associativity).

  Class StringLikeProperties (Char : Type) `{StringLike Char} :=
    {
      singleton_unique : forall s ch ch', s ~= [ ch ] -> s ~= [ ch' ] -> ch = ch';
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
      take_drop : forall str n m, take n (drop m str) =s drop m (take (n + m) str)
    }.

  Arguments StringLikeProperties Char {_}.
End StringLike.

End Core.

End StringLike.

End Parsers.

End ADTSynthesis.

End ADTSynthesis_DOT_Parsers_DOT_StringLike_DOT_Core.

Module Export ADTSynthesis.
Module Export Parsers.
Module Export ContextFreeGrammar.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Export ADTSynthesis.Parsers.StringLike.Core.
Import ADTSynthesis.Common.

Local Open Scope string_like_scope.

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

  Section parse.
    Context {HSL : StringLike Char}.
    Variable G : grammar.

    Inductive parse_of (str : String) : productions -> Type :=
    | ParseHead : forall pat pats, parse_of_production str pat
                                   -> parse_of str (pat::pats)
    | ParseTail : forall pat pats, parse_of str pats
                                   -> parse_of str (pat::pats)
    with parse_of_production (str : String) : production -> Type :=
    | ParseProductionNil : length str = 0 -> parse_of_production str nil
    | ParseProductionCons : forall n pat pats,
                              parse_of_item (take n str) pat
                              -> parse_of_production (drop n str) pats
                              -> parse_of_production str (pat::pats)
    with parse_of_item (str : String) : item -> Type :=
    | ParseTerminal : forall ch, str ~= [ ch ] -> parse_of_item str (Terminal ch)
    | ParseNonTerminal : forall nt, parse_of str (Lookup G nt)
                                    -> parse_of_item str (NonTerminal nt).
  End parse.
End cfg.

Arguments item _ : clear implicits.
Arguments production _ : clear implicits.
Arguments productions _ : clear implicits.
Arguments grammar _ : clear implicits.

End ContextFreeGrammar.

Module Export BaseTypes.

Section recursive_descent_parser.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      initial_nonterminals_data : nonterminals_listT;
      is_valid_nonterminal : nonterminals_listT -> String.string -> bool;
      remove_nonterminal : nonterminals_listT -> String.string -> nonterminals_listT;
      nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop;
      remove_nonterminal_dec : forall ls nonterminal,
                                 is_valid_nonterminal ls nonterminal
                                 -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
      ntl_wf : well_founded nonterminals_listT_R }.

  Class parser_removal_dataT' `{predata : parser_computational_predataT} :=
    { remove_nonterminal_1
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps'
          -> is_valid_nonterminal ls ps';
      remove_nonterminal_2
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
          <-> is_valid_nonterminal ls ps' = false \/ ps = ps' }.
End recursive_descent_parser.

End BaseTypes.
Import Coq.Lists.List.
Import ADTSynthesis.Parsers.ContextFreeGrammar.

Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT}
          {rdata' : @parser_removal_dataT' predata}.

  Inductive minimal_parse_of
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      productions Char -> Type :=
  | MinParseHead : forall str0 valid str pat pats,
                     @minimal_parse_of_production str0 valid str pat
                     -> @minimal_parse_of str0 valid str (pat::pats)
  | MinParseTail : forall str0 valid str pat pats,
                     @minimal_parse_of str0 valid str pats
                     -> @minimal_parse_of str0 valid str (pat::pats)
  with minimal_parse_of_production
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      production Char -> Type :=
  | MinParseProductionNil : forall str0 valid str,
                              length str = 0
                              -> @minimal_parse_of_production str0 valid str nil
  | MinParseProductionCons : forall str0 valid str n pat pats,
                               str ≤s str0
                               -> @minimal_parse_of_item str0 valid (take n str) pat
                               -> @minimal_parse_of_production str0 valid (drop n str) pats
                               -> @minimal_parse_of_production str0 valid str (pat::pats)
  with minimal_parse_of_item
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      item Char -> Type :=
  | MinParseTerminal : forall str0 valid str ch,
                         str ~= [ ch ]
                         -> @minimal_parse_of_item str0 valid str (Terminal ch)
  | MinParseNonTerminal
    : forall str0 valid str (nt : String.string),
        @minimal_parse_of_nonterminal str0 valid str nt
        -> @minimal_parse_of_item str0 valid str (NonTerminal nt)
  with minimal_parse_of_nonterminal
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      String.string -> Type :=
  | MinParseNonTerminalStrLt
    : forall str0 valid (nt : String.string) str,
        length str < length str0
        -> is_valid_nonterminal initial_nonterminals_data nt
        -> @minimal_parse_of str initial_nonterminals_data str (Lookup G nt)
        -> @minimal_parse_of_nonterminal str0 valid str nt
  | MinParseNonTerminalStrEq
    : forall str0 str valid nonterminal,
        str =s str0
        -> is_valid_nonterminal initial_nonterminals_data nonterminal
        -> is_valid_nonterminal valid nonterminal
        -> @minimal_parse_of str0 (remove_nonterminal valid nonterminal) str (Lookup G nonterminal)
        -> @minimal_parse_of_nonterminal str0 valid str nonterminal.
End cfg.
Import ADTSynthesis.Common.

Section general.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.

  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_string_for_production
      : item Char -> production Char -> String -> list nat }.

  Global Coercion predata : boolean_parser_dataT >-> parser_computational_predataT.

  Definition split_list_completeT `{data : @parser_computational_predataT}
             {str0 valid}
             (it : item Char) (its : production Char)
             (str : String)
             (pf : str ≤s str0)
             (split_list : list nat)

    := ({ n : nat
              & (minimal_parse_of_item (G := G) (predata := data) str0 valid (take n str) it)
                * (minimal_parse_of_production (G := G) str0 valid (drop n str) its) }%type)
       -> ({ n : nat
                 & (In n split_list)
                   * (minimal_parse_of_item (G := G) str0 valid (take n str) it)
                   * (minimal_parse_of_production (G := G) str0 valid (drop n str) its) }%type).

  Class boolean_parser_completeness_dataT' `{data : boolean_parser_dataT} :=
    { split_string_for_production_complete
      : forall str0 valid str (pf : str ≤s str0) nt,
          is_valid_nonterminal initial_nonterminals_data nt
          -> ForallT
               (Forall_tails
                  (fun prod
                   => match prod return Type with
                        | nil => True
                        | it::its
                          => @split_list_completeT data str0 valid it its str pf (split_string_for_production it its str)
                      end))
               (Lookup G nt) }.
End general.

Module Export BooleanRecognizer.
Import Coq.Numbers.Natural.Peano.NPeano.
Import Coq.Arith.Compare_dec.
Import Coq.Arith.Wf_nat.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}.

  Section bool.
    Section parts.
Definition parse_item
                 (str_matches_nonterminal : String.string -> bool)
                 (str : String)
                 (it : item Char)
      : bool.
Admitted.

      Section production.
        Context {str0}
                (parse_nonterminal
                 : forall (str : String),
                     str ≤s str0
                     -> String.string
                     -> bool).

        Fixpoint parse_production
                 (str : String)
                 (pf : str ≤s str0)
                 (prod : production Char)
        : bool.
        Proof.
          refine
            match prod with
              | nil =>

                Nat.eq_dec (length str) 0
              | it::its
                => let parse_production' := fun str pf => parse_production str pf its in
                   fold_right
                     orb
                     false
                     (map (fun n =>
                             (parse_item
                                (parse_nonterminal (str := take n str) _)
                                (take n str)
                                it)
                               && parse_production' (drop n str) _)%bool
                          (split_string_for_production it its str))
            end;
          revert pf; clear -HSLP; intros; admit.
        Defined.
      End production.

      Section productions.
        Context {str0}
                (parse_nonterminal
                 : forall (str : String)
                          (pf : str ≤s str0),
                     String.string -> bool).
Definition parse_productions
                   (str : String)
                   (pf : str ≤s str0)
                   (prods : productions Char)
        : bool.
exact (fold_right orb
                        false
                        (map (parse_production parse_nonterminal pf)
                             prods)).
Defined.
      End productions.

      Section nonterminals.
        Section step.
          Context {str0 valid}
                  (parse_nonterminal
                   : forall (p : String * nonterminals_listT),
                       prod_relation (ltof _ length) nonterminals_listT_R p (str0, valid)
                       -> forall str : String,
                            str ≤s fst p -> String.string -> bool).

          Definition parse_nonterminal_step
                     (str : String)
                     (pf : str ≤s str0)
                     (nt : String.string)
          : bool.
          Proof.
            refine
              (if lt_dec (length str) (length str0)
               then
                 parse_productions
                   (@parse_nonterminal
                      (str : String, initial_nonterminals_data)
                      (or_introl _))
                   (or_intror (reflexivity _))
                   (Lookup G nt)
               else
                 if Sumbool.sumbool_of_bool (is_valid_nonterminal valid nt)
                 then
                   parse_productions
                     (@parse_nonterminal
                        (str0 : String, remove_nonterminal valid nt)
                        (or_intror (conj eq_refl (remove_nonterminal_dec _ nt _))))
                     (str := str)
                     _
                     (Lookup G nt)
                 else
                   false);
            assumption.
          Defined.
        End step.

        Section wf.
Definition parse_nonterminal_or_abort
          : forall (p : String * nonterminals_listT)
                   (str : String),
              str ≤s fst p
              -> String.string
              -> bool.
exact (Fix3
                 _ _ _
                 (well_founded_prod_relation
                    (well_founded_ltof _ length)
                    ntl_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl))).
Defined.
Definition parse_nonterminal
                     (str : String)
                     (nt : String.string)
          : bool.
exact (@parse_nonterminal_or_abort
                 (str : String, initial_nonterminals_data) str
                 (or_intror (reflexivity _)) nt).
Defined.
        End wf.
      End nonterminals.
    End parts.
  End bool.
End recursive_descent_parser.

Section cfg.
  Context {Char} {HSL : StringLike Char} {HSLP : @StringLikeProperties Char HSL} (G : grammar Char).

  Section definitions.
    Context (P : String -> String.string -> Type).

    Definition Forall_parse_of_item'
               (Forall_parse_of : forall {str pats} (p : parse_of G str pats), Type)
               {str it} (p : parse_of_item G str it)
      := match p return Type with
           | ParseTerminal ch pf => unit
           | ParseNonTerminal nt p'
             => (P str nt * Forall_parse_of p')%type
         end.

    Fixpoint Forall_parse_of {str pats} (p : parse_of G str pats)
      := match p with
           | ParseHead pat pats p'
             => Forall_parse_of_production p'
           | ParseTail _ _ p'
             => Forall_parse_of p'
         end
    with Forall_parse_of_production {str pat} (p : parse_of_production G str pat)
         := match p return Type with
              | ParseProductionNil pf => unit
              | ParseProductionCons pat strs pats p' p''
                => (Forall_parse_of_item' (@Forall_parse_of) p' * Forall_parse_of_production p'')%type
            end.

    Definition Forall_parse_of_item {str it} (p : parse_of_item G str it)
      := @Forall_parse_of_item' (@Forall_parse_of) str it p.
  End definitions.

  End cfg.

Section recursive_descent_parser_list.
  Context {Char} {HSL : StringLike Char} {HLSP : StringLikeProperties Char} {G : grammar Char}.
Definition rdp_list_nonterminals_listT : Type.
exact (list String.string).
Defined.
Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> String.string -> bool.
admit.
Defined.
Definition rdp_list_remove_nonterminal : rdp_list_nonterminals_listT -> String.string -> rdp_list_nonterminals_listT.
admit.
Defined.
Definition rdp_list_nonterminals_listT_R : rdp_list_nonterminals_listT -> rdp_list_nonterminals_listT -> Prop.
exact (ltof _ (@List.length _)).
Defined.
  Lemma rdp_list_remove_nonterminal_dec : forall ls prods,
                                            @rdp_list_is_valid_nonterminal ls prods = true
                                            -> @rdp_list_nonterminals_listT_R (@rdp_list_remove_nonterminal ls prods) ls.
admit.
Defined.
  Lemma rdp_list_ntl_wf : well_founded rdp_list_nonterminals_listT_R.
  Proof.
    unfold rdp_list_nonterminals_listT_R.
    intro.
    apply well_founded_ltof.
  Defined.

  Global Instance rdp_list_predata : parser_computational_predataT
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := Valid_nonterminals G;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_listT_R := rdp_list_nonterminals_listT_R;
         remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;
         ntl_wf := rdp_list_ntl_wf }.
End recursive_descent_parser_list.

Section sound.
  Section general.
    Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} (G : grammar Char).
    Context {data : @boolean_parser_dataT Char _}
            {cdata : @boolean_parser_completeness_dataT' Char _ G data}
            {rdata : @parser_removal_dataT' predata}.

    Section parts.

      Section nonterminals.
        Section wf.

          Lemma parse_nonterminal_sound
                (str : String) (nonterminal : String.string)
          : parse_nonterminal (G := G) str nonterminal
            = true
            -> parse_of_item G str (NonTerminal nonterminal).
admit.
Defined.
        End wf.
      End nonterminals.
    End parts.
  End general.
End sound.

Import Coq.Strings.String.
Import ADTSynthesis.Parsers.ContextFreeGrammar.

Fixpoint list_to_productions {T} (default : T) (ls : list (string * T)) : string -> T
  := match ls with
       | nil => fun _ => default
       | (str, t)::ls' => fun s => if string_dec str s
                                   then t
                                   else list_to_productions default ls' s
     end.

Fixpoint list_to_grammar {T} (default : productions T) (ls : list (string * productions T)) : grammar T
  := {| Start_symbol := hd ""%string (map (@fst _ _) ls);
        Lookup := list_to_productions default ls;
        Valid_nonterminals := map (@fst _ _) ls |}.

Section interface.
  Context {Char} (G : grammar Char).
Definition production_is_reachable (p : production Char) : Prop.
admit.
Defined.
Definition split_list_is_complete `{HSL : StringLike Char} (str : String) (it : item Char) (its : production Char)
             (splits : list nat)
  : Prop.
exact (forall n,
         n <= length str
         -> parse_of_item G (take n str) it
         -> parse_of_production G (drop n str) its
         -> production_is_reachable (it::its)
         -> List.In n splits).
Defined.

  Record Splitter :=
    {
      string_type :> StringLike Char;
      splits_for : String -> item Char -> production Char -> list nat;

      string_type_properties :> StringLikeProperties Char;
      splits_for_complete : forall str it its,
                              split_list_is_complete str it its (splits_for str it its)

    }.
  Global Existing Instance string_type_properties.

  Record Parser (HSL : StringLike Char) :=
    {
      has_parse : @String Char HSL -> bool;

      has_parse_sound : forall str,
                          has_parse str = true
                          -> parse_of_item G str (NonTerminal (Start_symbol G));

      has_parse_complete : forall str (p : parse_of_item G str (NonTerminal (Start_symbol G))),
                             Forall_parse_of_item
                               (fun _ nt => List.In nt (Valid_nonterminals G))
                               p
                             -> has_parse str = true
    }.
End interface.

Module Export ParserImplementation.

Section implementation.
  Context {Char} {G : grammar Char}.
  Context (splitter : Splitter G).

  Local Instance parser_data : @boolean_parser_dataT Char _ :=
    { predata := rdp_list_predata (G := G);
      split_string_for_production it its str
      := splits_for splitter str it its }.

  Program Definition parser : Parser G splitter
    := {| has_parse str := parse_nonterminal (G := G) (data := parser_data) str (Start_symbol G);
          has_parse_sound str Hparse := parse_nonterminal_sound G _ _ Hparse;
          has_parse_complete str p Hp := _ |}.
  Next Obligation.
admit.
Defined.
End implementation.

End ParserImplementation.

Section implementation.
  Context {Char} {ls : list (String.string * productions Char)}.
  Local Notation G := (list_to_grammar (nil::nil) ls) (only parsing).
  Context (splitter : Splitter G).

  Local Instance parser_data : @boolean_parser_dataT Char _ := parser_data splitter.

  Goal forall str : @String Char splitter,
         let G' :=
             @BooleanRecognizer.parse_nonterminal Char splitter splitter G parser_data str G = true in
         G'.
    intros str G'.
    Timeout 1 assert (pf' : G' -> Prop) by abstract admit.
