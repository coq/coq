(** * Test the specs of primitive integers, unsigned and signed, for a sampling of inputs *)
(** This is the integer counterpart of [test-suite/primitive/float/specs.v].
    We enumerate a list of int parameters, a list of specs and a list of
    operators.  Then two things are checked:
    1. Test the specs:
       Each axiom of [Uint63Axioms] and [Sint63Axioms] is empirically
       checked against all instantiations of its arguments from the int
       list.  This is done with vm_compute for the check to be fast.
    2. Test the evaluation mechanisms:
       Again on each int from the list, each primitive operator is
       evaluated in multiple evaluation mechanisms to check that their
       results agree with the one given by vm_compute. *)
From Corelib Require Import ListDef BinNums PosDef IntDef PrimInt63 Uint63Axioms Sint63Axioms.
From Ltac2 Require Import Ltac2 Printf.

Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list_scope.

Open Scope list_scope.
Open Scope uint63_scope.

Module Type T. End T.

(* use empty type to avoid native compiling expanded values  *)
Module Tests : T.
(** *************************************************************************)
(** * Specifying the arguments to test on *)
(** EDIT HERE TO ADD MORE TESTS *)
(** ** List of ints to instantiate spec and operator args *)
(** The same list serves as unsigned and as signed values, as shift
    amounts and as bit indices.  Keep it short: the specs with three
    arguments are instantiated with the cube of its length. *)
Definition tricky_ints : list int
  := Eval cbv in
      [0; 1; 2; 3
       ; 62; 63; 64 (* around the number of digits *)
       ; max_int (* (-1)%sint63 *)
       ; PrimInt63.sub max_int 1 (* (-2)%sint63 *)
       ; min_int (* 2^62 *)
       ; PrimInt63.sub min_int 1 (* largest positive signed *)
       ; PrimInt63.add min_int 1 (* smallest negative signed + 1 *)
       ; PrimInt63.lsr min_int 1 (* 2^61 *)
       ; 0x7ffffffffffff7ca (* (-2102)%sint63 *)
       ; 12887523328 (* 3 * 2^32 + 2^21 + 2^19 *)
       ; 4930380657631323783 (* an odd number with high bits set *)
      ]%uint63.
(** *************************************************************************)

(** * Reflective machinery to instantiate specifications *)
(** ** Variables we know how to instantiate *)
Inductive SPEC_VAR_TYPE := INT.
Coercion denote_SPEC_VAR_TYPE (x : SPEC_VAR_TYPE) : Set
  := match x with INT => int end.

(** ** Fully-instantiated ("bare") specifications *)
(** (Perhaps we want a better name than "bare" meaning "no binders"? *)
(** As we'll see later, we check for [EQ l r] that [l] and [r] are
    [Constr.equal], for [IFF A B] that [A] and [B] have the same truth
    value, and for [PROP P] that [P] holds, where the truth value of a
    fully evaluated proposition is decided syntactically (see
    [decide_prop]). *)
Inductive BARE_SPEC :=
| EQ {T1 T2} (lhs : T1) (rhs : T2)
| IFF {T1 T2} (lhs : T1) (rhs : T2)
| PROP (P : Prop).

(** A [SPEC] is a [BARE_SPEC] prenex-quanified over known variable
    types.  We hold the original proposition here so that we can
    pretty-print it easily *)
Inductive SPEC :=
| BARE
    {U : Prop} (spec : U) (* for printing purposes *)
    (s : BARE_SPEC)
| FORALL (T : SPEC_VAR_TYPE)
    (s : T -> SPEC).

(** An [ANNOTATED_BARE_SPEC] holds the [BARE_SPEC] and also the
    propositional spec for pretty-printing of results. *)
Definition ANNOTATED_BARE_SPEC : Type := BARE_SPEC * {P : Prop | P}.

(* missing list functions *)
Section FlatMap.
Variables (A : Type) (B : Type).
Variable f : A -> list B.
Definition flat_map :=
  fix flat_map (l:list A) : list B :=
    match l with
    | nil => nil
    | cons x t => (f x)++(flat_map t)
    end.
End FlatMap.
Arguments flat_map [_ _].

Section ListPairs.
Variables (A : Type) (B : Type).
Fixpoint combine (l : list A) (l' : list B) : list (A*B) :=
  match l,l' with
  | x::tl, y::tl' => (x,y)::(combine tl tl')
  | _, _ => nil
  end.
End ListPairs.
Arguments combine [_ _].

(** ** Machinery for instantiating specifications with all examples *)
Fixpoint instantiate1_all_ways (s : SPEC) : list ANNOTATED_BARE_SPEC
  := match s with
     | @BARE U spec s => cons (s, exist _ U spec) nil
     | @FORALL T s
       => flat_map
            (fun v => instantiate1_all_ways (s v))
            match T with
            | INT => tricky_ints
            end
     end.

Definition instantiate_all_ways_nored (ls : list SPEC) : list ANNOTATED_BARE_SPEC
  := flat_map instantiate1_all_ways ls.

Definition instantiate_all_ways (ls : list SPEC) : list ANNOTATED_BARE_SPEC
  := Eval cbv in instantiate_all_ways_nored ls.

(** ** Some General Ltac2 Machinery *)
Import Ltac2.Constr.
Import Constr.Unsafe.
Ltac2 Type exn ::= [ PrimInt_Test_InternalError (message) | PrimInt_SpecTest_Failed (message) ].
Ltac2 Type exn ::= [ Reification_error (message) | Reification_unhandled_kind (message, kind) ].

Ltac2 lf () := String.make 1 (Char.of_int 10).

Ltac2 rec count_prod (x : constr) : int :=
  match kind x with
  | Cast x _ _ => count_prod x
  | Prod _ x => Int.add 1 (count_prod x)
  | _ => 0
  end.
Ltac2 mkApp f x := Unsafe.make (App f (Array.of_list x)).
Ltac2 mkRel i := Unsafe.make (Rel i).
Ltac2 mkLambda b body := Unsafe.make (Lambda b body).

(** ** Reification of known variable types *)
Ltac2 reify_var_type (t : constr) : constr
  := match List.assoc_opt Constr.equal t
             [('int, 'INT)]
     with
     | Some v => v
     | None => Control.throw (Reification_error (fprintf "Unhandled type %t" t))
     end.

(** ** Capping powers of two during reification *)
(** The shift specs mention [2 ^ to_Z p], which cannot be computed when
    [p] is large (the result would have up to [2 ^ 63] bits).  When such
    a power is the divisor of a [Z.div], or a factor of the left operand
    of a [Z.modulo] by [wB], the result is unchanged if the exponent is
    capped at 64, because every value involved is below [wB = 2 ^ 63] in
    absolute value.  These two patterns are rewritten during reification,
    so that the checked statement follows the axiom as written.  Any
    other power with a non-constant exponent, except the powers of
    [head0] and [tail0] (which are at most 63), is rejected, so that a
    change in the axioms fails here instead of hanging in [vm_compute]. *)
(* Corelib has no number notation for [positive] or [Z]. *)
Definition one : Z := Zpos xH.
Definition two : Z := Zpos (xO xH).
Definition sixty_four : Z := Zpos (xO (xO (xO (xO (xO (xO xH)))))).

Definition pow2_capped (e : Z) : Z :=
  if Z.leb e sixty_four then Z.pow two e else Z.pow two sixty_four.

Ltac2 is_app2 (f : constr) (c : constr) : (constr * constr) option
  := match kind c with
     | App g args
       => if Bool.and (Constr.equal f g) (Int.equal (Array.length args) 2)
          then Some (Array.get args 0, Array.get args 1)
          else None
     | _ => None
     end.
Ltac2 is_pow2 (c : constr) : constr option
  := match is_app2 'Z.pow c with
     | Some (b, e) => if Constr.equal b '(Zpos (xO xH)) then Some e else None
     | None => None
     end.
Ltac2 rec cap_pow2 (c : constr) : constr
  := let c := Unsafe.map cap_pow2 c in
     match is_app2 'Z.div c with
     | Some (a, d)
       => match is_pow2 d with
          | Some e => mkApp 'Z.div [a; mkApp 'pow2_capped [e]]
          | None => c
          end
     | None
       => match is_app2 'Z.modulo c with
          | Some (a, m)
            => if Constr.equal m 'wB
               then match is_app2 'Z.mul a with
                    | Some (a, d)
                      => match is_pow2 d with
                         | Some e => mkApp 'Z.modulo [mkApp 'Z.mul [a; mkApp 'pow2_capped [e]]; m]
                         | None => c
                         end
                    | None => c
                    end
               else c
          | None => c
          end
     end.
Ltac2 rec check_powers (c : constr) : unit
  := match is_app2 'Z.pow c with
     | Some (_, e)
       => let bounded :=
            lazy_match! e with
            | Uint63Axioms.to_Z (head0 _) => true
            | Uint63Axioms.to_Z (tail0 _) => true
            | _ => Unsafe.is_closed e
            end in
          if bounded then ()
          else Control.throw (Reification_error (fprintf "Power with an unbounded exponent in %t; extend cap_pow2" c))
     | None => ()
     end;
     let _ := Unsafe.map (fun c => check_powers c; c) c in ().

(** ** Reification of specifications after binders have been removed *)
(** Does not run typechecking, and therefore works on open terms (with
    unbound rels).  Equalities and equivalences are split into their
    two sides so that the error messages can display both; anything
    else (implications, conjunctions, ...) is kept as a proposition to
    be decided after evaluation. *)
Ltac2 reify_bare_spec (ty : constr) : constr
  := let ty := cap_pow2 ty in
     check_powers ty;
     match kind ty with
     | App f args
       => if Constr.equal f '@eq
          then Unsafe.make (App (mkApp '@EQ [Array.get args 0]) args)
          else if Constr.equal f '@iff
               then Unsafe.make (App (mkApp '@IFF ['Prop; 'Prop]) args)
               else mkApp 'PROP [ty]
     | _ => mkApp 'PROP [ty]
     end.
(** ** Reification of specs, including binders *)
(** [n] is how many binders are left to remove in [spec], and
    therefore which [Rel] the [spec] should be eventually applied to
    *)
Ltac2 rec reify_spec' (ty : constr) (spec : constr) (n : int) : constr
  := match kind ty with
     | Cast ty _ _ => reify_spec' ty spec n
     | Prod b body
       => if Bool.and (Int.gt n 0) (Constr.equal (Binder.type b) 'int)
          then let ty := reify_var_type (Binder.type b) in
               let body := reify_spec' body (mkApp spec [mkRel n]) (Int.sub n 1) in
               mkApp 'FORALL [ty; mkLambda b body]
          else let r := reify_bare_spec ty in
               mkApp '@BARE [ty; spec; r]
     | _ => let r := reify_bare_spec ty in
            mkApp '@BARE [ty; spec; r]
     end.
(** Only the leading binders over [int] are instantiated; a
    subsequent non-dependent product is an implication and is part of
    the proposition to decide. *)
Ltac2 rec count_int_prod (x : constr) : int :=
  match kind x with
  | Cast x _ _ => count_int_prod x
  | Prod b x => if Constr.equal (Binder.type b) 'int then Int.add 1 (count_int_prod x) else 0
  | _ => 0
  end.
Ltac2 reify_spec (spec : constr) : constr
  := let ty := Constr.type spec in
     reify_spec' ty spec (count_int_prod ty).

Notation "` x" := (ltac2:(let v := reify_spec (pretype x) in exact $v)) (only parsing, at level 10).

(** * Machinery for deciding fully evaluated propositions *)
(** After [vm_compute], a closed proposition built from the specs is
    made of equalities between closed values, [True], [False],
    conjunctions, disjunctions and non-dependent products (implications,
    including [not]).  Anything else means the evaluation was not
    complete, and is an error rather than a failure. *)
Ltac2 rec decide_prop (p : constr) : bool
  := lazy_match! p with
     | True => true
     | False => false
     | ?x = ?y => Constr.equal x y
     | ?a /\ ?b => Bool.and (decide_prop a) (decide_prop b)
     | ?a \/ ?b => Bool.or (decide_prop a) (decide_prop b)
     | _ => match kind p with
            | Prod b body
              => if Unsafe.noccur_between 1 1 body
                 then Bool.or (Bool.neg (decide_prop (Binder.type b)))
                              (decide_prop (Unsafe.substnl ['True] 0 body))
                 else Control.throw (PrimInt_Test_InternalError (fprintf "Cannot decide dependent product %t" p))
            | _ => Control.throw (PrimInt_Test_InternalError (fprintf "Cannot decide %t" p))
            end
     end.

(** * Machinery for reporting results *)
Ltac2 report_result (red : string) (result : constr) (specTy : constr) (spec : constr) : message option
  := let msg :=
       lazy_match! result with
       | EQ ?x ?y
         => if Constr.equal x y
            then None
            else Some (fprintf "%s failed!%sGot: %t%sExpected: %t%sIn %t %t" red (lf ()) x (lf ()) y (lf ()) spec specTy)
       | IFF ?x ?y
         => let b_x := decide_prop x in
            let b_y := decide_prop y in
            if Bool.equal b_x b_y
            then None
            else Some (fprintf "%s failed!%sGot: %t (%s)%sExpected something equivalent to: %t (%s)%sIn %t %t"
                         red (lf ()) x (if b_x then "true" else "false") (lf ()) y (if b_y then "true" else "false") (lf ()) spec specTy)
       | PROP ?p
         => if decide_prop p
            then None
            else Some (fprintf "%s failed!%sGot: %t%swhich does not hold%sIn %t %t" red (lf ()) p (lf ()) (lf ()) spec specTy)
       | _ => Control.throw (PrimInt_Test_InternalError (fprintf "Unhandled result %t (on %t : %t with %s)" result spec specTy red))
       end in
     match msg with
     | Some msg => Message.print (Message.concat (Message.of_string "Test Error: ") msg)
     | None => ()
     end;
     msg.

Ltac2 rec report_results_gen (error_early : bool) (red : string) (results : constr) : unit
  := lazy_match! results with
     | nil => ()
     | cons (?res, exist _ ?specTy ?spec) ?results
       => let err := report_result red res specTy spec in
          let check_rest () := report_results_gen error_early red results in
          let zero_err () := match err with
                             | Some err => Control.zero (PrimInt_SpecTest_Failed err)
                             | None => ()
                             end in
          if error_early
          then (zero_err   (); check_rest ())
          else (check_rest (); zero_err   ())
     | cons ?v _
       => Control.throw (PrimInt_Test_InternalError (fprintf "Invalid result format %t" v))
     | _
       => let results' := Std.eval_hnf results in
          if Constr.equal results results'
          then Control.throw (PrimInt_Test_InternalError (fprintf "Results must be a literal list, not %t" results))
          else report_results_gen error_early red results'
     end.
Ltac2 report_results red results := report_results_gen false red results.
Ltac2 report_results_fast red results := report_results_gen true red results.

(** *************************************************************************)
(** * List of (reified) specifications *)
(** EDIT HERE TO ADD MORE TESTS *)

(** [tail0_spec] is an existential, which the machinery above cannot
    decide; we check the equivalent statement where the witness is
    made explicit, and check that the original statement is still the
    one this was derived from. *)
Check (tail0_spec : forall x, Z.lt Z0 (Uint63Axioms.to_Z x) ->
  exists y, Z.le Z0 y /\ Uint63Axioms.to_Z x
                        = Z.mul (Z.add (Z.mul two y) one) (Z.pow two (Uint63Axioms.to_Z (tail0 x)))).
(* If the [Check] above fails, [tail0_spec] changed: update [tail0_spec']. *)
Axiom tail0_spec' : forall x, Z.lt Z0 (Uint63Axioms.to_Z x) ->
  Uint63Axioms.to_Z x
  = Z.mul (Z.add (Z.mul two (Z.div (Z.div (Uint63Axioms.to_Z x) (Z.pow two (Uint63Axioms.to_Z (tail0 x)))) two)) one)
          (Z.pow two (Uint63Axioms.to_Z (tail0 x))).

Definition spec_list : list SPEC :=
  [ (* unsigned *)
    `of_to_Z

    ; `lsl_spec
    ; `lsr_spec
    ; `land_spec
    ; `lor_spec
    ; `lxor_spec

    ; `add_spec
    ; `sub_spec
    ; `mul_spec
    ; `mulc_spec
    ; `Uint63Axioms.div_spec
    ; `Uint63Axioms.mod_spec

    ; `eqb_correct
    ; `eqb_refl
    ; `Uint63Axioms.ltb_spec
    ; `Uint63Axioms.leb_spec

    ; `compare_def_spec
    ; `head0_spec
    ; `tail0_spec'
    ; `addc_def_spec
    ; `addcarryc_def_spec
    ; `subc_def_spec
    ; `subcarryc_def_spec
    ; `diveucl_def_spec
    ; `diveucl_21_spec
    ; `addmuldiv_def_spec

    (* signed *)
    ; `Sint63Axioms.div_spec
    ; `Sint63Axioms.mod_spec
    ; `Sint63Axioms.ltb_spec
    ; `Sint63Axioms.leb_spec
    ; `Sint63Axioms.compare_spec
    ; `Sint63Axioms.asr_spec
  ].
(* Spec to check that evaluation mechanisms agree for each operator. *)
#[local] Abbreviation reflspec1 f := (fun x => @eq_refl _ (f x)).
#[local] Abbreviation reflspec2 f := (fun x y => @eq_refl _ (f x y)).
#[local] Abbreviation reflspec3 f := (fun x y z => @eq_refl _ (f x y z)).
Definition op_spec_list : list SPEC :=
  [ ` (reflspec2 PrimInt63.lsl)
    ; ` (reflspec2 PrimInt63.lsr)
    ; ` (reflspec2 PrimInt63.land)
    ; ` (reflspec2 PrimInt63.lor)
    ; ` (reflspec2 PrimInt63.lxor)
    ; ` (reflspec2 PrimInt63.asr)
    ; ` (reflspec2 PrimInt63.add)
    ; ` (reflspec2 PrimInt63.sub)
    ; ` (reflspec2 PrimInt63.mul)
    ; ` (reflspec2 PrimInt63.mulc)
    ; ` (reflspec2 PrimInt63.div)
    ; ` (reflspec2 PrimInt63.mod)
    ; ` (reflspec2 PrimInt63.divs)
    ; ` (reflspec2 PrimInt63.mods)
    ; ` (reflspec2 PrimInt63.eqb)
    ; ` (reflspec2 PrimInt63.ltb)
    ; ` (reflspec2 PrimInt63.leb)
    ; ` (reflspec2 PrimInt63.ltsb)
    ; ` (reflspec2 PrimInt63.lesb)
    ; ` (reflspec2 PrimInt63.addc)
    ; ` (reflspec2 PrimInt63.addcarryc)
    ; ` (reflspec2 PrimInt63.subc)
    ; ` (reflspec2 PrimInt63.subcarryc)
    ; ` (reflspec2 PrimInt63.diveucl)
    ; ` (reflspec3 PrimInt63.diveucl_21)
    ; ` (reflspec3 PrimInt63.addmuldiv)
    ; ` (reflspec2 PrimInt63.compare)
    ; ` (reflspec2 PrimInt63.compares)
    ; ` (reflspec1 PrimInt63.head0)
    ; ` (reflspec1 PrimInt63.tail0)
  ].
(** *************************************************************************)

(** * Utility definitions for managing lists specifications *)
(** We unfold standard library constants early to guarantee that we
    won't run afoul of constants that show up in the specs themselves *)
Definition map_fst : list ANNOTATED_BARE_SPEC -> list BARE_SPEC
  := Eval cbv in ListDef.map (@fst _ _).
Definition combine_annotations (orig : list ANNOTATED_BARE_SPEC) (result : list BARE_SPEC) : list ANNOTATED_BARE_SPEC
  := Eval cbv in ListDef.map (fun '((_, anno), v) => (v, anno)) (combine orig result).
(** The native compiler is much slower if we feed it the precomputed
    instantiations of specs, whereas we want to make sure that [simpl]
    and [cbn] have as few places to take the wrong path as possible.
    Reductions like [cbv] and [lazy] and the [vm] are mostly
    indifferent.  So we maintain both [_red] versions for [simpl] and
    [cbn] and non-[_red] versions for [native_compute]. *)
(** We make [_red] definitions [Definition] statements, to work around
    COQBUG(https://github.com/rocq-prover/rocq/issues/4790) and avoid stack
    overflows in COQNATIVE *)

(** * 1. Test the specs *)
Section TestSpecs.

Time Definition specs_red : list ANNOTATED_BARE_SPEC
  := Eval cbv [spec_list instantiate_all_ways] in instantiate_all_ways spec_list.

Definition bare_specs_red : list BARE_SPEC
  := Eval cbv [map_fst specs_red] in map_fst specs_red.

Time Definition bare_specs_vm : list BARE_SPEC
  := Eval vm_compute in bare_specs_red.

(** ** Fuse in the annotations so that we can report errors nicely *)
Time Definition results_vm : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations bare_specs_vm specs_red] in combine_annotations specs_red bare_specs_vm.

(** ** Report results *)
Time Ltac2 Eval report_results "vm" 'results_vm.

End TestSpecs.

(** Check that the machinery indeed fail, providing useful error messages,
    on some purposely-wrong specs, one of each shape. *)
Section NegativeTest.

Axiom wrong_eq_spec : forall x, PrimInt63.sub 0 x = x.
Axiom wrong_iff_spec : forall x, ltb x 1 = true <-> Z.le (Uint63Axioms.to_Z 1) (Uint63Axioms.to_Z x).
Axiom wrong_prop_spec : forall x, ltb x 1 = true -> ltb 1 x = true.

Definition wrong_spec_list : list SPEC := [ `wrong_eq_spec ; `wrong_iff_spec ; `wrong_prop_spec ].

(** A power of two with an unbounded exponent outside the two capped
    patterns must be rejected at reification time. *)
Axiom uncapped_pow_spec : forall p, Z.pow (Zpos (xO xH)) (Uint63Axioms.to_Z p) = Z0.
Fail Check ( `uncapped_pow_spec ).

Definition wrong_specs : list ANNOTATED_BARE_SPEC
  := Eval cbv [wrong_spec_list instantiate_all_ways] in instantiate_all_ways wrong_spec_list.

Definition wrong_bare_specs : list BARE_SPEC
  := Eval cbv [map_fst wrong_specs] in map_fst wrong_specs.

Definition wrong_bare_specs_vm : list BARE_SPEC
  := Eval vm_compute in wrong_bare_specs.

(** ** Fuse in the annotations so that we can report errors nicely *)
Definition wrong_results_vm : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations wrong_bare_specs_vm wrong_specs] in combine_annotations wrong_specs wrong_bare_specs_vm.

(** ** Report results *)
Fail Ltac2 Eval report_results "vm" 'wrong_results_vm.
(*
Test Error: vm failed!
Got: 9223372036854775807
Expected: 1
In
(wrong_eq_spec 1) (sub 0 1 = 1)
...
*)

End NegativeTest.

(** * 2. Test the evaluation mechanisms *)

Definition op_specs : list ANNOTATED_BARE_SPEC
  := instantiate_all_ways_nored op_spec_list.
Time Definition op_specs_red : list ANNOTATED_BARE_SPEC
  := Eval cbv [instantiate_all_ways op_spec_list] in instantiate_all_ways op_spec_list.
Definition op_bare_specs : list BARE_SPEC
  := map fst op_specs.
Definition op_bare_specs_red : list BARE_SPEC
  := Eval cbv [map_fst op_specs_red] in map_fst op_specs_red.

(** Machinery for evaluating independently the LHS of specs *)
(** To check that all evaluation mechanism agree, we will then
    0. evaluate [op_specs] with [vm_compute]
    1. [extract_lhs] of [op_specs]
    2. evaluate LHS with each mechanism
    3. [merge_lhs] with results of 2. and 0. *)
Inductive hlist := hnil | hcons {T} (x : T) (_ : hlist).
Fixpoint extract_lhs (ls : list BARE_SPEC) : hlist
  := match ls with
     | nil => hnil
     | x :: xs
       => let rest := extract_lhs xs in
          match x with EQ v _ | IFF v _ => hcons v rest | PROP p => hcons p rest end
     end.
Fixpoint merge_lhs (ls : list BARE_SPEC) (result : hlist) : list BARE_SPEC
  := match ls, result with
     | nil, _ | _, hnil => nil
     | x :: xs, hcons v vs
       => match x with
          | EQ _ x' => EQ v x'
          | IFF _ x' => IFF v x'
          | PROP p => PROP p
          end :: merge_lhs xs vs
     end.

(** 0. evaluate [op_specs] with [vm_compute] *)
Definition op_bare_specs_vm : list BARE_SPEC
  := Eval vm_compute in op_bare_specs_red.

(** 1. [extract_lhs] of [op_specs] *)
Definition LHS_op : hlist
  := extract_lhs op_bare_specs.
Definition LHS_op_red : hlist
  := Eval cbv [op_bare_specs_red extract_lhs] in extract_lhs op_bare_specs_red.

(** 2. evaluate LHS with each mechanism *)

(** *************************************************************************)
(** * Computing reduced expressions *)
(** EDIT HERE TO ADD MORE REDUCTION STRATEGIES *)
(** ** [vm_compute] is ommited as it is the reference *)
(** ** [native_compute] *)
(** Native is slow at compiling big code, so we start from smaller code *)
Definition LHS_op_native := Eval native_compute in extract_lhs op_bare_specs.

(** ** [hnf] *)
(** recursively applies hnf to all elements of the list *)
Ltac2 rec eval_hnf_hlist (c : constr) : constr
  := lazy_match! c with
     | hcons ?h ?t =>
         let h := Std.eval_hnf h in
         let t := eval_hnf_hlist t in
         '(hcons $h $t)
     | hnil => 'hnil
     end.
Time Definition LHS_op_hnf := ltac2:(let l := Std.eval_hnf 'LHS_op_red in let x := eval_hnf_hlist l in exact $x).

(** ** [cbn] *)
Time Definition LHS_op_cbn := Eval cbn in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l).

(** ** [simpl] *)
Time Definition LHS_op_simpl := Eval simpl in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l).

(** ** [cbv] *)
Time Definition LHS_op_cbv := Eval cbv in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l).

(** ** [lazy] *)
Time Definition LHS_op_lazy := Eval lazy in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l).

(** 3. [merge_lhs] with results of 2. and 0. *)

(** ** fuse the results of vm RHS (vm because it's fast) back into cbn/hnf/simpl LHS for comparison *)
Definition op_bare_specs_native : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_native] in merge_lhs op_bare_specs_vm LHS_op_native.
Definition op_bare_specs_hnf : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_hnf] in merge_lhs op_bare_specs_vm LHS_op_hnf.
Definition op_bare_specs_cbn : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_cbn] in merge_lhs op_bare_specs_vm LHS_op_cbn.
Definition op_bare_specs_simpl : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_simpl] in merge_lhs op_bare_specs_vm LHS_op_simpl.
Definition op_bare_specs_cbv : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_cbv] in merge_lhs op_bare_specs_vm LHS_op_cbv.
Definition op_bare_specs_lazy : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_lazy] in merge_lhs op_bare_specs_vm LHS_op_lazy.

(** ** Fuse in the annotations so that we can report errors nicely *)
Time Definition op_results_native : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_native] in combine_annotations op_specs_red op_bare_specs_native.
Time Definition op_results_hnf : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_hnf] in combine_annotations op_specs_red op_bare_specs_hnf.
Time Definition op_results_cbn : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_cbn] in combine_annotations op_specs_red op_bare_specs_cbn.
Time Definition op_results_simpl : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_simpl] in combine_annotations op_specs_red op_bare_specs_simpl.
Time Definition op_results_cbv : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_cbv] in combine_annotations op_specs_red op_bare_specs_cbv.
Time Definition op_results_lazy : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_lazy] in combine_annotations op_specs_red op_bare_specs_lazy.

(** ** Report results *)
Set Printing Depth 100000000.
Ltac2 Eval report_results "native" 'op_results_native.
Ltac2 Eval report_results "hnf" 'op_results_hnf.
Ltac2 Eval report_results "cbn" 'op_results_cbn.
Ltac2 Eval report_results "simpl" 'op_results_simpl.
Ltac2 Eval report_results "cbv" 'op_results_cbv.
Ltac2 Eval report_results "lazy" 'op_results_lazy.
End Tests.
