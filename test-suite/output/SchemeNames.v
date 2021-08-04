Unset Elimination Schemes.

(** In this file we test the generation and naming of elimination schemes. *)

(** * Schemes for inductive SProp *)

  (** Here is an inductive SProp. *)

  Inductive fooSProp : SProp := aSP | bSP.

  (** ** Try Induction into all Sorts *)

       Scheme Induction for fooSProp Sort SProp. (* fooSProp_inds *)
  Fail Scheme Induction for fooSProp Sort Prop.
  Fail Scheme Induction for fooSProp Sort Set.
  Fail Scheme Induction for fooSProp Sort Type.

  About fooSProp_inds.

  (** ** Try Minimality into all Sorts *)

       Scheme Minimality for fooSProp Sort SProp. (* fooSProp_inds_nodep *)
  Fail Scheme Minimality for fooSProp Sort Prop.
  Fail Scheme Minimality for fooSProp Sort Set.
  Fail Scheme Minimality for fooSProp Sort Type.

  About fooSProp_inds_nodep.

  (** ** Try Elimination into all Sorts *)

       Scheme Elimination for fooSProp Sort SProp. (* fooSProp_cases *)
  Fail Scheme Elimination for fooSProp Sort Prop.
  Fail Scheme Elimination for fooSProp Sort Set.
  Fail Scheme Elimination for fooSProp Sort Type.

  About fooSProp_cases.

  (** ** Try Case into all Sorts *)

       Scheme Case for fooSProp Sort SProp. (* fooSProp_cases_nodep *)
  Fail Scheme Case for fooSProp Sort Prop.
  Fail Scheme Case for fooSProp Sort Set.
  Fail Scheme Case for fooSProp Sort Type.

  About fooSProp_cases_nodep.

  (** ** Scheme Equality *)

  Fail Scheme Equality for fooSProp.

(** * Schemes for inductive Prop *)

  (** Here is an inductive Prop. *)

  Inductive fooProp : Prop := aP | bP.

  (** ** Try Induction into all Sorts *)

       Scheme Induction for fooProp Sort SProp. (* fooProp_inds_dep *)
       Scheme Induction for fooProp Sort Prop.  (* fooProp_ind_dep *)
  Fail Scheme Induction for fooProp Sort Set.
  Fail Scheme Induction for fooProp Sort Type.

  About fooProp_inds_dep.
  About fooProp_ind_dep.

  (** ** Try Minimality into all Sorts *)

       Scheme Minimality for fooProp Sort SProp. (* fooProp_inds *)
       Scheme Minimality for fooProp Sort Prop.  (* fooProp_ind *)
  Fail Scheme Minimality for fooProp Sort Set.
  Fail Scheme Minimality for fooProp Sort Type.

  About fooProp_inds.
  About fooProp_ind.

  (** ** Try Elimination into all Sorts *)

       Scheme Elimination for fooProp Sort SProp. (* fooProp_cases_dep *)
       Scheme Elimination for fooProp Sort Prop.  (* fooProp_case_dep *)
  Fail Scheme Elimination for fooProp Sort Set.
  Fail Scheme Elimination for fooProp Sort Type.

  About fooProp_cases_dep.
  About fooProp_case_dep.

  (** ** Try Case into all Sorts *)

       Scheme Case for fooProp Sort SProp. (* fooProp_cases *)
       Scheme Case for fooProp Sort Prop.  (* fooProp_case *)
  Fail Scheme Case for fooProp Sort Set.
  Fail Scheme Case for fooProp Sort Type.

  About fooProp_cases.
  About fooProp_case.

  (** ** Scheme Equality *)

  Fail Scheme Equality for fooProp.

(** * Schemes for inductive Set *)

  (** Here is an inductive Set. *)

  Inductive fooSet : Set := aS | bS.

  (** ** Try Induction into all Sorts *)

  Scheme Induction for fooSet Sort SProp. (* fooSet_inds *)
  Scheme Induction for fooSet Sort Prop.  (* fooSet_ind *)
  Scheme Induction for fooSet Sort Set.   (* fooSet_rec *)
  Scheme Induction for fooSet Sort Type.  (* fooSet_rect *)

  About fooSet_inds.
  About fooSet_ind.
  About fooSet_rec.
  About fooSet_rect.

  (** ** Try Minimality into all Sorts *)

  Scheme Minimality for fooSet Sort SProp. (* fooSet_inds_nodep *)
  Scheme Minimality for fooSet Sort Prop.  (* fooSet_ind_nodep *)
  Scheme Minimality for fooSet Sort Set.   (* fooSet_rec_nodep *)
  Scheme Minimality for fooSet Sort Type.  (* fooSet_rect_nodep *)

  About fooSet_inds_nodep.
  About fooSet_ind_nodep.
  About fooSet_rec_nodep.
  About fooSet_rect_nodep.

  (** **  Try Elimination into all Sorts *)

  (** Unforunately there is some overlap with names so we need to create a fresh inductive. *)
  Inductive fooSet' : Set := aS' | bS'.

  Scheme Elimination for fooSet Sort SProp. (* fooSet_cases *)
  Scheme Elimination for fooSet Sort Prop.  (* fooSet_case *)
  Scheme Elimination for fooSet' Sort Set.  (* fooSet'_case *)
  Scheme Elimination for fooSet' Sort Type. (* fooSet'_caset *)

  About fooSet_cases.
  About fooSet_case.
  About fooSet'_case.
  About fooSet'_caset.

   (** ** Try Case into all Sorts *)

  Scheme Case for fooSet Sort SProp. (* fooSet_cases_nodep *)
  Scheme Case for fooSet Sort Prop.  (* fooSet_case_nodep *)
  Scheme Case for fooSet' Sort Set.  (* fooSet'_case_nodep *)
  Scheme Case for fooSet' Sort Type. (* fooSet'_caset_nodep *)

  About fooSet_cases_nodep.
  About fooSet_case_nodep.
  About fooSet'_case_nodep.
  About fooSet'_caset_nodep.

  (** ** Scheme Equality *)

  Scheme Equality for fooSet.

  About fooSet_beq.
  About fooSet_eq_dec.
  About internal_fooSet_dec_bl.
  About internal_fooSet_dec_lb.

(** * Schemes for inductive Type *)

  (** Here is an inductive Type. *)

  Inductive fooType : Type := aT | bT.

  (** ** Try Induction into all Sorts *)

  Scheme Induction for fooType Sort SProp. (* fooType_inds *)
  Scheme Induction for fooType Sort Prop.  (* fooType_ind *)
  Scheme Induction for fooType Sort Set.   (* fooType_rec *)
  Scheme Induction for fooType Sort Type.  (* fooType_rect *)

  About fooType_inds.
  About fooType_ind.
  About fooType_rec.
  About fooType_rect.

  (** ** Try Minimality into all Sorts *)

  Scheme Minimality for fooType Sort SProp. (* fooType_inds_nodep *)
  Scheme Minimality for fooType Sort Prop.  (* fooType_ind_nodep *)
  Scheme Minimality for fooType Sort Set.   (* fooType_rec_nodep *)
  Scheme Minimality for fooType Sort Type.  (* fooType_rect_nodep *)

  About fooType_inds_nodep.
  About fooType_ind_nodep.
  About fooType_rec_nodep.
  About fooType_rect_nodep.

  (** ** Try Elimination into all Sorts *)

  (** Unforunately there is some overlap with names so we need to create a fresh inductive. *)
  Inductive fooType' : Type := aT' | bT'.

  Scheme Elimination for fooType Sort SProp. (* fooType_cases *)
  Scheme Elimination for fooType Sort Prop.  (* fooType_case *)
  Scheme Elimination for fooType' Sort Set.  (* fooType'_case *)
  Scheme Elimination for fooType' Sort Type. (* fooType'_caset *)

  About fooType_cases.
  About fooType_case.
  About fooType'_case.
  About fooType'_caset.

  (** ** Try Case into all Sorts *)

  Scheme Case for fooType Sort SProp. (* fooType_cases_nodep *)
  Scheme Case for fooType Sort Prop.  (* fooType_case_nodep *)
  Scheme Case for fooType' Sort Set.  (* fooType'_case_nodep *)
  Scheme Case for fooType' Sort Type. (* fooType'_caset_nodep *)

  About fooType_cases_nodep.
  About fooType_case_nodep.
  About fooType'_case_nodep.
  About fooType'_caset_nodep.

  (** ** Scheme Equality *)

  Scheme Equality for fooType.

  About fooType_beq.
  About fooType_eq_dec.
  About internal_fooType_dec_bl.
  About internal_fooType_dec_lb.
