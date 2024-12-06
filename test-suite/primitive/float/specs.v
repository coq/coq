(** * Test the various specs of primitive floats for a sampling of inputs *)
(** We enumerate a list of float and int parameters, a list of
    specs and a list of operators. Then two things are checked:
    1. Test the specs:
       Each spec is empirically checked against all
       instantiations of arguments from the float/int lists.
       This is done with vm_compute for the check to be fast.
    2. Test the evaluation mechanisms:
       Again on each float/int from the lists, each operator
       is evaluated in multiple evaluation mechanisms to check
       that their results agree with the one given by vm_compute. *)
From Corelib Require Import ListDef BinNums PrimInt63 Uint63Axioms.
From Corelib Require Import SpecFloat PrimFloat FloatOps FloatAxioms.
From Ltac2 Require Import Ltac2 Printf.

Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..))
  (format "[ '[' x ;  '/' y ;  '/' .. ;  '/' z ']' ]") : list_scope.

Open Scope list_scope.
Open Scope float_scope.

Section __WORK_AROUND_COQBUG_4790.
(** *************************************************************************)
(** * Specifying the arguments to test on *)
(** EDIT HERE TO ADD MORE TESTS *)
(** ** List of floats to instantiate spec and operator args *)
Definition tricky_floats : list float
  := Eval cbv in
         [infinity; neg_infinity; nan; 0; -0
          ; 0x1.fffffffffffffp+1023 (* largest finite value *)
          ; -0x1.fffffffffffffp+1023 (* largest negative finite value *)
          ; 0x0.1p-1070 (* smallest positive value *)
          ; -0x0.1p-1070 (* non-zero negative value closest to zero *)
          ; 1; -1; 0.5; 2; -0.5; -2
          (* numbers from fma tests 264-266 from testsuite/tests/fma/fma.ml,
       cf
       https://github.com/coq/coq/issues/17893#issuecomment-1654794043. These
       tests trigger the broken implementations of Cygwin64, mingw-w64
       (x86_64) and VS2013-2017. *)
          ; 0x3.bd5b7dde5fddap-496
          ; -0xd.fc352bc352bap-992

          ; 0x3.bd5b7dde5fddap-504
          ; -0xd.fc352bc352bap-1008

          ; 0x8p-540
          ; 0x4p-540
          (* ; 0x4p-1076 *) (* same as 0x0.1p-1070 above *)
          (* constants from [add.v] *)
          ; 3
          (* ; Z.ldexp one 1023%Z *) (* same as largest finite (emax-prec) above *)
          ; Z.ldexp one (Zneg (xI (xI (xI (xI (xI (xI (xI (xI (xI xH)))))))))); -Z.ldexp one (Zneg (xI (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))
          (* constants from [classify.v] *)
          ; Z.ldexp one (Zneg (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH))))))))))); -Z.ldexp one (Zneg (xO (xO (xO (xO (xO (xO (xO (xO (xO (xO xH)))))))))))
          (* constants from [div.v] *)
          ; 6
          (* constants from [double_rounding.v] *)
          ; Z.ldexp one (Zpos (xI (xO (xI (xO (xI xH)))))); Z.ldexp one (Zpos (xO (xO (xI (xO (xI xH))))))
          ; 1 + Z.ldexp 1 (Zneg (xO (xO (xI (xO (xI xH))))))
          (* constants from [next_up_down.v] *)
          ; 42; -42
          ; Z.ldexp one (Zneg (xO (xI (xI (xI (xI (xI (xI (xI (xI xH)))))))))); -Z.ldexp one (Zneg (xO (xI (xI (xI (xI (xI (xI (xI (xI xH))))))))))
          ; -0x1.ffffffffffffap+1023
          ; -0x1.fffffffffffff
          ; -0x0.fffffffffffffp-1022
          ; -0x0.01p-1022
          ; 0x0.01p-1022
          ; 0x0.fffffffffffffp-1022
          ; 0x1.fffffffffffff
          ; 0x1.ffffffffffffap+1023
          (* constants from [normfr_mantissa.v] *)
          ; 0.75
          (* constants from [sqrt.v] *)
          ; 9
      ].
Definition tricky_spec_floats :=
  Eval cbv in ListDef.map Prim2SF tricky_floats.
(** ** List of ints to instantiate spec and operator args *)
Definition tricky_ints : list int
  := Eval cbv in
      [0; 1
       ; max_int; PrimInt63.sub max_int 1
       ; Uint63Axioms.of_Z prec
       ; Uint63Axioms.of_Z emax
       ; Uint63Axioms.of_Z emin
       ; 2; PrimInt63.div max_int 2
       ; PrimInt63.sub (PrimInt63.div max_int 2) 1; PrimInt63.add (PrimInt63.div max_int 2) 1
       ; PrimInt63.sub (Uint63Axioms.of_Z prec) 1; PrimInt63.add (Uint63Axioms.of_Z prec) 1
       ; PrimInt63.div (Uint63Axioms.of_Z prec) 2; PrimInt63.sub (PrimInt63.div (Uint63Axioms.of_Z prec) 2) 1; PrimInt63.sub (PrimInt63.div (Uint63Axioms.of_Z prec) 2) 1
       ; PrimInt63.sub (Uint63Axioms.of_Z emax) 1; PrimInt63.add (Uint63Axioms.of_Z emax) 1
       ; PrimInt63.div (Uint63Axioms.of_Z emax) 2; PrimInt63.sub (PrimInt63.div (Uint63Axioms.of_Z emax) 2) 1; PrimInt63.add (PrimInt63.div (Uint63Axioms.of_Z emax) 2) 1
       ; PrimInt63.sub (Uint63Axioms.of_Z emin) 1; PrimInt63.add (Uint63Axioms.of_Z emin) 1
       ; PrimInt63.div (Uint63Axioms.of_Z emin) 2; PrimInt63.sub (PrimInt63.div (Uint63Axioms.of_Z emin) 2) 1; PrimInt63.add (PrimInt63.div (Uint63Axioms.of_Z emin) 2) 1
       (* constants from [ldexp.v] *)
       (* ; 9223372036854775807 *) (* max_int *)
       ; 0x7ffffffffffff7ca%uint63 (* (-2102)%sint63 *)
       ; 0x7ffffffffffffffd%uint63 (* (-3)%sint63 *)
       ; 3
      ]%uint63.
(** *************************************************************************)

(** * Reflective machinery to instantiate specifications *)
(** ** Variables we know how to instantiate *)
Inductive SPEC_VAR_TYPE := INT | FLOAT | SPEC_FLOAT.
Coercion denote_SPEC_VAR_TYPE (x : SPEC_VAR_TYPE) : Set
  := match x with INT => int | FLOAT => float | SPEC_FLOAT => spec_float end.

(** ** Fully-instantiated ("bare") specifications *)
(** (Perhaps we want a better name than "bare" meaning "no binders"? *)
(** As we'll see later, we check for [EQ l r] that [l] and [r] are
    [Constr.equal], and we'll check for [IFF (x = y) (x' = y')] that
    [Constr.equal x y] and [Constr.equal x' y'] are the same.  (We
    don't currently support reporting results about [IFF A B] for [A]
    and [B] not equalities. *)
Inductive BARE_SPEC :=
| EQ {T1 T2} (lhs : T1) (rhs : T2)
| IFF {T1 T2} (lhs : T1) (rhs : T2).

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
            | FLOAT => tricky_floats
            | SPEC_FLOAT => tricky_spec_floats
            end
     end.

Definition instantiate_all_ways_nored (ls : list SPEC) : list ANNOTATED_BARE_SPEC
  := flat_map instantiate1_all_ways ls.

Definition instantiate_all_ways (ls : list SPEC) : list ANNOTATED_BARE_SPEC
  := Eval cbv in instantiate_all_ways_nored ls.

(** ** Some General Ltac2 Machinery *)
Import Ltac2.Constr.
Import Constr.Unsafe.
Ltac2 Type exn ::= [ PrimFloat_Test_InternalError (message) | PrimFloat_SpecTest_Failed (message) ].
Ltac2 Type exn ::= [ Reification_error (message) | Reification_unhandled_kind (message, kind) ].

Ltac2 unify_bool (x : constr) (y : constr) : bool
  := match Control.case (fun () => Std.unify x y) with
     | Val _ => true
     | Err _ => false
     end.

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
             [('spec_float, 'SPEC_FLOAT)
              ; ('float, 'FLOAT)
              ; ('int, 'INT)]
     with
     | Some v => v
     | None => Control.throw (Reification_error (fprintf "Unhandled type %t" t))
     end.

(** ** A kludgy hack we have to do to support some specifications that aren't equalities but have case statements out front *)
(** turns [let '(x, y) := z in w = q] into [(let '(x, y) := z in w) = (let '(x, y) := z in q)] *)
(** Does not run typechecking, and therefore works on open terms (with unbound rels) *)
Ltac2 rec push_case_eq (tag : constr) (mkCase : constr (* retty *) -> constr -> constr) (branch : constr) : constr
  := match kind branch with
     | Lambda b body => push_case_eq tag (fun retty body => mkCase retty (mkLambda b body)) body
     | App f args
       => if Constr.equal f '@eq
          then let ty := Array.get args 0 in
               let x := Array.get args 1 in
               let y := Array.get args 2 in
               mkApp f [ty; mkCase ty x; mkCase ty y]
          else Control.throw (Reification_error (fprintf "Unrecognized under case %t (from %t from %t)" f branch tag))
     | _ => Control.throw (Reification_error (fprintf "Unrecognized kind under case %t (from %t)" branch tag))
     end.
Ltac2 swap_case_eq (x : constr) : constr
  := match kind x with
     | Case c (retty, rel) ci discr branches
       => if Int.equal 1 (Array.length branches)
          then match kind retty with
               | Lambda retty_b rtProp
                 => if Constr.equal rtProp 'Prop
                    then push_case_eq
                           x
                           (fun retty b => Unsafe.make (Case c (mkLambda retty_b (liftn 1 1 retty), rel) ci discr (Array.of_list [b])))
                           (Array.get branches 0)
                    else x
               | _ => x
               end
          else x
     | _ => x
     end.

(** ** Reification of specifications after binders have been removed *)
(** Does not run typechecking, and therefore works on open terms (with unbound rels) *)
Ltac2 reify_bare_spec (ty : constr) : constr
  := let ty := swap_case_eq ty in
     match kind ty with
     | App f args
       => if Constr.equal f '@eq
          then Unsafe.make (App (mkApp '@EQ [Array.get args 0]) args)
          else if Constr.equal f '@iff
               then Unsafe.make (App (mkApp '@IFF ['Prop; 'Prop]) args)
               else Control.throw (Reification_error (fprintf "Unhandled base spec app %t" ty))
     | k => Control.throw (Reification_unhandled_kind (fprintf "Unhandled base spec %t" ty) k)
     end.
(** ** Reification of specs, including binders *)
(** [n] is how many binders are left to remove in [spec], and
    therefore which [Rel] the [spec] should be eventually applied to
    *)
Ltac2 rec reify_spec' (ty : constr) (spec : constr) (n : int) : constr
  := match kind ty with
     | Cast ty _ _ => reify_spec' ty spec n
     | Prod b body
       => let ty := reify_var_type (Binder.type b) in
          let body := reify_spec' body (mkApp spec [mkRel n]) (Int.sub n 1) in
          mkApp 'FORALL [ty; mkLambda b body]
     | _ => let r := reify_bare_spec ty in
            mkApp '@BARE [ty; spec; r]
     end.
Ltac2 reify_spec (spec : constr) : constr
  := let ty := Constr.type spec in
     reify_spec' ty spec (count_prod ty).

Notation "` x" := (ltac2:(let v := reify_spec (pretype x) in exact $v)) (only parsing, at level 10).

(** * Machinery for reporting results *)
Ltac2 report_result (red : string) (result : constr) (specTy : constr) (spec : constr) : message option
  := let msg :=
       lazy_match! result with
       | EQ ?x ?y
         => if Constr.equal x y
            then None
            else (* if unify_bool x y (* commented out because of https://github.com/coq/coq/pull/17899 *)
                 then Some (fprintf "%s failed to fully reduce, leaving over %t (expected: %t), in %t %t" red x y spec specTy)
                 else *) Some (fprintf "%s failed!%sGot: %t%sExpected: %t%sIn %t %t" red (lf ()) x (lf ()) y (lf ()) spec specTy)
       | IFF (?x = ?x') (?y = ?y')
         => let (lhs, rhs) := lazy_match! result with
                              | IFF ?lhs ?rhs => (lhs, rhs)
                              | _ => Control.throw (PrimFloat_Test_InternalError (fprintf "Impossible! Result branch mismatch %t" result))
                              end in
            let descr := if unify_bool y y' then "should" else "should not" in
            if Bool.and (Bool.equal (Constr.equal x x') (Constr.equal y y'))
                 (Bool.equal (unify_bool x x') (unify_bool y y'))
            then None
            else (* if Bool.equal (unify_bool x x') (unify_bool y y') (* commented out because of https://github.com/coq/coq/pull/17899 *)
                 then Some (fprintf "%s failed to fully reduce, leaving over %t (expected something equivalent to: %t), in %t %t" red lhs rhs spec specTy)
                 else *) Some (fprintf "%s failed!%sGot: %t%sExpected something equivalent to: %t%s(both sides %s unify)%sIn %t %t" red (lf ()) lhs (lf ()) rhs (lf ()) descr (lf ()) spec specTy)
       | _ => Control.throw (PrimFloat_Test_InternalError (fprintf "Unhandled result %t (on %t : %t with %s)" result spec specTy red))
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
                             | Some err => Control.zero (PrimFloat_SpecTest_Failed err)
                             | None => ()
                             end in
          if error_early
          then (zero_err   (); check_rest ())
          else (check_rest (); zero_err   ())
     | cons ?v _
       => Control.throw (PrimFloat_Test_InternalError (fprintf "Invalid result format %t" v))
     | _
       => let results' := Std.eval_hnf results in
          if Constr.equal results results'
          then Control.throw (PrimFloat_Test_InternalError (fprintf "Results must be a literal list, not %t" results))
          else report_results_gen error_early red results'
     end.
Ltac2 report_results red results := report_results_gen false red results.
Ltac2 report_results_fast red results := report_results_gen true red results.

(** *************************************************************************)
(** * List of (reified) specifications *)
(** EDIT HERE TO ADD MORE TESTS *)

(* [Prim2SF_SF2Prim] has an hypothesis not handled by the above machinery
   so let's check something stronger in theory but equivalent in practice,
   since all test cases satisfy the hypothesis by construction. *)
Axiom Prim2SF_SF2Prim' : forall x, (* valid_binary x = true -> *) Prim2SF (SF2Prim x) = x.

Definition spec_list : list SPEC :=
  [ `Prim2SF_valid
    ; `SF2Prim_Prim2SF
    ; `Prim2SF_SF2Prim'

    ; `opp_spec
    ; `abs_spec

    ; `eqb_spec
    ; `ltb_spec
    ; `leb_spec

    ; `compare_spec

    ; `Leibniz.eqb_spec

    ; `classify_spec
    ; `mul_spec
    ; `add_spec
    ; `sub_spec
    ; `div_spec
    ; `sqrt_spec

    ; `of_uint63_spec
    ; `normfr_mantissa_spec

    ; `frshiftexp_spec
    ; `ldshiftexp_spec

    ; `next_up_spec
    ; `next_down_spec
  ].
(* Spec to check that evaluation mechanisms agree for each operator. *)
#[local] Notation reflspec1 f := (fun x => @eq_refl _ (f x)).
#[local] Notation reflspec2 f := (fun x y => @eq_refl _ (f x y)).
Definition op_spec_list : list SPEC :=
  [ ` (reflspec1 PrimFloat.classify)
    ; ` (reflspec1 PrimFloat.abs)
    ; ` (reflspec1 PrimFloat.sqrt)
    ; ` (reflspec1 PrimFloat.opp)
    ; ` (reflspec2 PrimFloat.eqb)
    ; ` (reflspec2 PrimFloat.ltb)
    ; ` (reflspec2 PrimFloat.leb)
    ; ` (reflspec2 PrimFloat.compare)
    ; ` (reflspec2 PrimFloat.Leibniz.eqb)
    ; ` (reflspec2 PrimFloat.mul)
    ; ` (reflspec2 PrimFloat.add)
    ; ` (reflspec2 PrimFloat.sub)
    ; ` (reflspec2 PrimFloat.div)
    ; ` (reflspec1 PrimFloat.of_uint63)
    ; ` (reflspec1 PrimFloat.normfr_mantissa)
    ; ` (reflspec1 PrimFloat.frshiftexp)
    ; ` (reflspec2 PrimFloat.ldshiftexp)
    ; ` (reflspec1 PrimFloat.next_up)
    ; ` (reflspec1 PrimFloat.next_down)
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
(** We make [_red] definitions [Let] statements, to work around
    COQBUG(https://github.com/coq/coq/issues/4790) and avoid stack
    overflows in COQNATIVE *)

(** * 1. Test the specs *)
Section TestSpecs.

Time Let specs_red : list ANNOTATED_BARE_SPEC
  := Eval cbv [spec_list instantiate_all_ways] in instantiate_all_ways spec_list. (* 0.911 secs *)

Let bare_specs_red : list BARE_SPEC
  := Eval cbv [map_fst specs_red] in map_fst specs_red.

Time Let bare_specs_vm : list BARE_SPEC
  := Eval vm_compute in bare_specs_red. (* 1.934 secs *)

(** ** Fuse in the annotations so that we can report errors nicely *)
Time Let results_vm : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations bare_specs_vm specs_red] in combine_annotations specs_red bare_specs_vm. (* 1.374 secs *)

(** ** Report results *)
Time Ltac2 Eval report_results "vm" 'results_vm. (* 0.634 secs *)

End TestSpecs.

(** Check that the machinery indeed fail, providing useful error messages,
    on some purposely-wrong spec. *)
Section NegativeTest.

Axiom wrong_spec : forall x, (- x)%float = PrimFloat.abs x.

Definition wrong_spec_list : list SPEC := cons ( `wrong_spec ) nil.

Let wrong_specs : list ANNOTATED_BARE_SPEC
  := Eval cbv [wrong_spec_list instantiate_all_ways] in instantiate_all_ways wrong_spec_list.

Let wrong_bare_specs : list BARE_SPEC
  := Eval cbv [map_fst wrong_specs] in map_fst wrong_specs.

Let wrong_bare_specs_vm : list BARE_SPEC
  := Eval vm_compute in wrong_bare_specs.

(** ** Fuse in the annotations so that we can report errors nicely *)
Let wrong_results_vm : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations wrong_bare_specs_vm wrong_specs] in combine_annotations wrong_specs wrong_bare_specs_vm.

(** ** Report results *)
Fail Ltac2 Eval report_results "vm" 'wrong_results_vm.
(*
Test Error: vm failed!
Got: neg_infinity
Expected: infinity
In (wrong_spec infinity) (- infinity = abs infinity)
...
*)

End NegativeTest.

(** * 2. Test the evaluation mechanisms *)

Definition op_specs : list ANNOTATED_BARE_SPEC
  := instantiate_all_ways_nored op_spec_list.
Time Let op_specs_red : list ANNOTATED_BARE_SPEC
  := Eval cbv [instantiate_all_ways op_spec_list] in instantiate_all_ways op_spec_list. (* 0.883 secs *)
Definition op_bare_specs : list BARE_SPEC
  := map fst op_specs.
Let op_bare_specs_red : list BARE_SPEC
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
          match x with EQ v _ | IFF v _ => hcons v rest end
     end.
Fixpoint merge_lhs (ls : list BARE_SPEC) (result : hlist) : list BARE_SPEC
  := match ls, result with
     | nil, _ | _, hnil => nil
     | x :: xs, hcons v vs
       => match x with
          | EQ _ x' => EQ v x'
          | IFF _ x' => IFF v x'
          end :: merge_lhs xs vs
     end.

(** 0. evaluate [op_specs] with [vm_compute] *)
Let op_bare_specs_vm : list BARE_SPEC
  := Eval vm_compute in op_bare_specs_red.

(** 1. [extract_lhs] of [op_specs] *)
Definition LHS_op : hlist
  := extract_lhs op_bare_specs.
Let LHS_op_red : hlist
  := Eval cbv [op_bare_specs_red extract_lhs] in extract_lhs op_bare_specs_red.

(** 2. evaluate LHS with each mechanism *)

(** *************************************************************************)
(** * Computing reduced expressions *)
(** EDIT HERE TO ADD MORE REDUCTION STRATEGIES *)
(** ** [vm_compute] is ommited as it is the reference *)
(** ** [native_compute] *)
(** Native is slow at compiling big code, so we start from smaller code *)
Let LHS_op_native := Eval native_compute in extract_lhs op_bare_specs.

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
Time Let LHS_op_hnf := ltac2:(let l := Std.eval_hnf 'LHS_op_red in let x := eval_hnf_hlist l in exact $x). (* 16.309 secs *)

(** ** [cbn] *)
Time Let LHS_op_cbn := Eval cbn in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l). (* 0.25 secs *)

(** ** [simpl] *)
Time Let LHS_op_simpl := Eval simpl in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l). (* 0.296 secs *)

(** ** [cbv] *)
Time Let LHS_op_cbv := Eval cbv in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l). (* 0.292 secs *)

(** ** [lazy] *)
Time Let LHS_op_lazy := Eval lazy in ltac2:(let l := Std.eval_hnf 'LHS_op_red in exact $l). (* 0.259 secs *)

(** 3. [merge_lhs] with results of 2. and 0. *)

(** ** fuse the results of vm RHS (vm because it's fast) back into cbn/hnf/simpl LHS for comparison *)
Let op_bare_specs_native : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_native] in merge_lhs op_bare_specs_vm LHS_op_native.
Let op_bare_specs_hnf : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_hnf] in merge_lhs op_bare_specs_vm LHS_op_hnf.
Let op_bare_specs_cbn : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_cbn] in merge_lhs op_bare_specs_vm LHS_op_cbn.
Let op_bare_specs_simpl : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_simpl] in merge_lhs op_bare_specs_vm LHS_op_simpl.
Let op_bare_specs_cbv : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_cbv] in merge_lhs op_bare_specs_vm LHS_op_cbv.
Let op_bare_specs_lazy : list BARE_SPEC
  := Eval cbv [merge_lhs op_bare_specs_vm LHS_op_lazy] in merge_lhs op_bare_specs_vm LHS_op_lazy.

(** ** Fuse in the annotations so that we can report errors nicely *)
Time Let op_results_native : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_native] in combine_annotations op_specs_red op_bare_specs_native. (* 0.826 secs *)
Time Let op_results_hnf : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_hnf] in combine_annotations op_specs_red op_bare_specs_hnf. (* 0.83 secs *)
Time Let op_results_cbn : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_cbn] in combine_annotations op_specs_red op_bare_specs_cbn. (* 0.83 secs *)
Time Let op_results_simpl : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_simpl] in combine_annotations op_specs_red op_bare_specs_simpl. (* 0.865 secs *)
Time Let op_results_cbv : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_cbv] in combine_annotations op_specs_red op_bare_specs_cbv. (* 0.845 secs *)
Time Let op_results_lazy : list ANNOTATED_BARE_SPEC
  := Eval cbv [combine_annotations op_specs_red op_bare_specs_lazy] in combine_annotations op_specs_red op_bare_specs_lazy. (* 0.812 secs *)

(** ** Report results *)
Set Printing Depth 100000000.
Ltac2 Eval report_results "native" 'op_results_native.
Ltac2 Eval report_results "hnf" 'op_results_hnf.
Ltac2 Eval report_results "cbn" 'op_results_cbn.
Ltac2 Eval report_results "simpl" 'op_results_simpl.
Ltac2 Eval report_results "cbv" 'op_results_cbv.
Ltac2 Eval report_results "lazy" 'op_results_lazy.

End __WORK_AROUND_COQBUG_4790.
