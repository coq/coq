.. _record-types:

Record types
------------

The :cmd:`Record` command defines types similar to :gdef:`records`
in programming languages. Those types describe tuples whose
components, called :gdef:`fields <field>`, can be accessed with
:gdef:`projections <projection>`. Records can also be used to describe
mathematical structures, such as groups or rings, hence the
synonym :cmd:`Structure`.

Defining record types
~~~~~~~~~~~~~~~~~~~~~

.. _record_grammar:

.. cmd:: {| Record | Structure } @record_definition
   :name: Record; Structure

   .. insertprodn record_definition of_type_inst

   .. prodn::
      record_definition ::= {? > } @ident_decl {* @binder } {? : @sort } {? := {? @ident } %{ {*; @record_field } {? ; } %} {? as @ident } }
      record_field ::= {* #[ {+, @attribute } ] } @name {? @field_spec } {? %| @natural }
      field_spec ::= {* @binder } @of_type_inst
      | {* @binder } := @term
      | {* @binder } @of_type_inst := @term
      of_type_inst ::= {| : | :> | :: | ::> } @type

   Defines a non-recursive record type, creating projections for each field
   that has a name other than `_`. The field body and type can depend on previous
   fields, so the order of fields in the definition may matter.

   Use the :cmd:`Inductive` and :cmd:`CoInductive` commands to define recursive
   (inductive or coinductive) records.  These commands also permit defining
   mutually recursive records provided that all of
   the types in the block are records.  These commands automatically generate
   induction schemes.  Enable the :flag:`Nonrecursive Elimination Schemes` flag
   to enable automatic generation of elimination schemes for :cmd:`Record`.
   See :ref:`proofschemes-induction-principles`.

   The :cmd:`Class` command can be used to define records that are also
   :ref:`typeclasses`, which permit Rocq to automatically infer the inhabitants of
   the record.

   :n:`{? > }`
     If specified, the constructor is declared as
     a coercion from the class of the last field type to the record name.
     See :ref:`coercions`.

   :n:`@ident_decl`
     The :n:`@ident` within is the record name.

   :n:`{* @binder }`
     :n:`@binder`\s may be used to declare the
     :term:`inductive parameters <inductive parameter>` of the record.

   :n:`: @sort`
     The sort the record belongs to.  The default is :n:`Type`.

   :n:`:= {? @ident }`
     :n:`@ident` is the name of the record constructor.  If omitted,
     the name defaults to :n:`Build_@ident` where :n:`@ident` is the record name.

   :n:`as {? @ident}`
     Specifies the name used to refer to the argument corresponding to the
     record in the type of projections.  If not specified, the name is the first
     letter of the record name converted to lowercase (see :ref:`example <record_as_clause>`).
     In constrast, :cmd:`Class` command uses the record name as the default
     (see :ref:`example <class_arg_name>`).

   In :n:`@record_field`:

     :n:`@attribute`, if specified, can only be :attr:`canonical`.

     :n:`@name` is the field name.  Since field names define projections, you can't
     reuse the same field name in two different records in the same module.  This
     :ref:`example <reuse_field_name>` shows how to reuse the same field
     name in multiple records.

     :n:`@field_spec` can be omitted only when the type of the field can be inferred
     from other fields. For example: the type of :n:`n` can be inferred from
     :n:`npos` in :n:`Record positive := { n; npos : 0 < n }`.

     :n:`| @natural`
       Specifies the priority of the field.  It is only allowed in :cmd:`Class` commands.

     :n:`:`
       Specifies the type of the field.

     :n:`:>`
       If specified, the field is declared as a coercion from the record name
       to the class of the field type. See :ref:`coercions`.

     :n:`::`
       If specified, the field is declared a typeclass instance of the class
       of the field type. See :ref:`typeclasses`.

     :n:`::>`
       Acts as a combination of :n:`::` and :n:`:>`.

     - :n:`{+ @binder } : @of_type_inst` is equivalent to
       :n:`: forall {+ @binder } , @of_type_inst`

     - :n:`{+ @binder } := @term` is equivalent to
       :n:`:= fun {+ @binder } => @term`

     - :n:`{+ @binder } @of_type_inst := @term` is equivalent to
       :n:`: forall {+ @binder } , @type := fun {+ @binder } => @term`

     :n:`:= @term`, if present, gives the value of the field, which may depend
     on the fields that appear before it.  Since their values are already defined,
     such fields cannot be specified when constructing a record.

   The :cmd:`Record` command supports the :attr:`universes(polymorphic)`,
   :attr:`universes(template)`, :attr:`universes(cumulative)`,
   :attr:`private(matching)` and :attr:`projections(primitive)` attributes.

   .. example:: Defining a record

      The set of rational numbers may be defined as:

      .. rocqtop:: reset all

         Record Rat : Set := mkRat
          { negative : bool
          ; top : nat
          ; bottom : nat
          ; Rat_bottom_nonzero : 0 <> bottom
          ; Rat_irreducible :
              forall x y z:nat, (x * y) = top /\ (x * z) = bottom -> x = 1
          }.

      The :n:`Rat_*` fields depend on :n:`top` and :n:`bottom`.
      :n:`Rat_bottom_nonzero` is a proof that :n:`bottom` (the denominator)
      is not zero.  :n:`Rat_irreducible` is a proof that the fraction is in
      lowest terms.

.. _reuse_field_name:

   .. example:: Reusing a field name in multiple records

      .. rocqtop:: in

         Module A. Record R := { f : nat }. End A.
         Module B. Record S := { f : nat }. End B.

      .. rocqtop:: all

         Check {| A.f := 0 |}.
         Check {| B.f := 0 |}.

.. _record_as_clause:

   .. example:: Using the "as" clause in a record definition

      .. rocqtop:: all

         Record MyRecord := { myfield : nat } as VarName.
         About myfield. (* observe the MyRecord variable is named "VarName" *)

         (* make "VarName" implicit without having to rename the variable,
            which would be necessary without the "as" clause *)
         Arguments myfield {VarName}.   (* make "VarName" an implicit parameter *)
         Check myfield.
         Check (myfield (VarName:={| myfield := 0 |})).

.. _class_arg_name:

   .. example:: Argument name for a record type created using :cmd:`Class`

      Compare to :cmd:`Record` in the previous example:

      .. rocqtop:: all

         Class MyClass := { myfield2 : nat }.
         About myfield2. (* Argument name defaults to the class name and is marked implicit *)

   .. exn:: Records declared with the keyword Record or Structure cannot be recursive.

      The record name :token:`ident` appears in the type of its fields, but uses
      the :cmd:`Record` command. Use  the :cmd:`Inductive` or
      :cmd:`CoInductive` command instead.

   .. exn:: @ident already exists

      The fieldname :n:`@ident` is already defined as a global.

   .. warn:: @ident__1 cannot be defined because the projection @ident__2 was not defined

      The type of the projection :n:`@ident__1` depends on previous projections which
      themselves could not be defined.

   .. warn:: @ident cannot be defined.

      The projection cannot be defined.  This message is followed by an explanation
      of why it's not possible, such as:

      #. The :term:`body` of :token:`ident` uses an incorrect elimination for
         :token:`ident` (see :cmd:`Fixpoint` and :ref:`Destructors`).

   .. warn:: @ident__field cannot be defined because it is informative and @ident__record is not

      The projection for the named field :n:`@ident__field` can't be defined.
      For example, :n:`Record R:Prop := { f:nat }` generates the message
      "f cannot be defined ... and R is not".  Records of sort :n:`Prop`
      must be non-informative (i.e. indistinguishable).  Since :n:`nat`
      has multiple inhabitants, such as :n:`%{%| f := 0 %|%}` and
      :n:`%{%| f := 1 %|%}`, the record would be informative and therefore the
      projection can't be defined.

   .. seealso:: Coercions and records in section :ref:`coercions-classes-as-records`.

   .. todo below: Need a better description for Variant and primitive projections.
      Hugo says "the model to think about primitive projections is not fully stabilized".

   .. note:: Records exist in two flavors. In the first,
      a record :n:`@ident` with parameters :n:`{* @binder }`,
      constructor :n:`@ident__0`, and fields :n:`{* @name @field_spec }`
      is represented as a variant type with a single
      constructor: :n:`Variant @ident {* @binder } : @sort := @ident__0
      {* ( @name @field_spec ) }` and projections are defined by case analysis.
      In the second implementation, records have
      primitive projections: see :ref:`primitive_projections`.

   During the definition of the one-constructor inductive definition, all
   the errors of inductive definitions, as described in Section
   :ref:`gallina-inductive-definitions`, may also occur.

Constructing records
~~~~~~~~~~~~~~~~~~~~

   .. insertprodn term_record field_val

   .. prodn::
      term_record ::= %{%| {*; @field_val } {? ; } %|%}
      field_val ::= @qualid {* @binder } := @term

   Instances of record types can be constructed using either *record form*
   (:n:`@term_record`, shown here) or *application form* (see :n:`@term_application`)
   using the constructor.  The associated record definition is selected using the
   provided field names or constructor name, both of which are global.

   In the record form, the fields can be given in any order.  Fields that can be
   inferred by unification or by using obligations (see :ref:`programs`) may be omitted.

   In application form, all fields of the record must be passed, in order,
   as arguments to the constructor.

   .. example:: Constructing 1/2 as a record

      Constructing the rational :math:`1/2` using either the record or application syntax:

      .. rocqtop:: in

         Theorem one_two_irred : forall x y z:nat, x * y = 1 /\ x * z = 2 -> x = 1.
         Admitted.

         (* Record form: top and bottom can be inferred from other fields *)
         Definition half :=
           {| negative := false;
              Rat_bottom_nonzero := O_S 1;
              Rat_irreducible := one_two_irred |}.

         (* Application form: use the constructor and provide values for all the fields
            in order.  "mkRat" is defined by the Record command *)
         Definition half' := mkRat true 1 2 (O_S 1) one_two_irred.

Accessing fields (projections)
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   .. insertprodn term_projection term_projection

   .. prodn::
      term_projection ::= @term0 .( @qualid {? @univ_annot } {* @arg } )
      | @term0 .( @ @qualid {? @univ_annot } {* @term1 } )

   The value of a field can be accessed using *projection form* (:n:`@term_projection`,
   shown here) or with *application form* (see :n:`@term_application`) using the
   projection function associated with the field.  Don't forget the parentheses for the
   projection form.
   Glossing over some syntactic details, the two forms are:

   - :n:`@qualid__record.( {? @ } @qualid__field {* @arg })`   (projection) and

   - :n:`{? @ } @qualid__field {* @arg } @qualid__record`   (application)

   where the :n:`@arg`\s are the parameters of the inductive type.  If :n:`@` is
   specified, all implicit arguments must be provided.

   In projection form, since the projected object is part of the notation, it is always
   considered an explicit argument of :token:`qualid`, even if it is
   formally declared as implicit (see :ref:`ImplicitArguments`).

   .. example:: Accessing record fields

      .. rocqtop:: all

         (* projection form *)
         Eval compute in half.(top).

         (* application form *)
         Eval compute in top half.

   .. example:: Matching on records

      .. rocqtop:: all

         Eval compute in (
           match half with
           | {| negative := false; top := n |} => n
           | _ => 0
           end).

   .. example:: Accessing anonymous record fields with match

      .. rocqtop:: in

         Record T := const { _ : nat }.
         Definition gett x := match x with const n => n end.
         Definition inst := const 3.

      .. rocqtop:: all

         Eval compute in gett inst.

Settings for printing records
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The following settings let you control the display format for record types:

.. flag:: Printing Records

   When this :term:`flag` is on (this is the default),
   use the record syntax (shown above) as the default display format.

You can override the display format for specified record types by adding entries to these tables:

.. table:: Printing Record @qualid

   This :term:`table` specifies a set of qualids which are displayed as records.  Use the
   :cmd:`Add` and :cmd:`Remove` commands to update the set of qualids.

.. table:: Printing Constructor @qualid

   This :term:`table` specifies a set of qualids which are displayed as constructors.  Use the
   :cmd:`Add` and :cmd:`Remove` commands to update the set of qualids.

.. flag:: Printing Projections

   Activates the projection form (dot notation) for printing projections (off by default).

   .. example::

      .. rocqtop:: all

         Check top half.  (* off: application form *)
         Set Printing Projections.
         Check top half.  (* on:  projection form *)

.. _primitive_projections:

Primitive Projections
~~~~~~~~~~~~~~~~~~~~~

Note: the design of primitive projections is still evolving.

When the :flag:`Primitive Projections` flag is on or the
:attr:`projections(primitive)` attribute is supplied for a :cmd:`Record` definition, its
:g:`match` construct is disabled. To eliminate the record type, one must
use its defined primitive projections.

For compatibility, the parameters still appear when printing terms
even though they are absent in the actual AST manipulated by the kernel. This
can be changed by unsetting the :flag:`Printing Primitive Projection Parameters`
flag.

There are currently two ways to introduce primitive records types:

#. Through the :cmd:`Record` command, in which case the type has to be
   non-recursive. The defined type enjoys eta-conversion definitionally,
   that is the generalized form of surjective pairing for records:
   `r` ``= Build_``\ `R` ``(``\ `r`\ ``.(``\ |p_1|\ ``) …`` `r`\ ``.(``\ |p_n|\ ``))``.
   Eta-conversion allows to define dependent elimination for these types as well.
#. Through the :cmd:`Inductive` and :cmd:`CoInductive` commands, when
   the :term:`body` of the definition is a record declaration of the form
   ``Build_``\ `R` ``{`` |p_1| ``:`` |t_1|\ ``; … ;`` |p_n| ``:`` |t_n| ``}``.
   In this case the types can be recursive and eta-conversion is disallowed.
   Dependent elimination is not available for such types;
   you must use non-dependent case analysis for these.

For both cases the :flag:`Primitive Projections` :term:`flag` must be set or
the :attr:`projections(primitive)` :term:`attribute`  must be supplied.

.. flag:: Primitive Projections

   This :term:`flag` turns on the use of primitive projections when defining
   subsequent records (even through the :cmd:`Inductive` and :cmd:`CoInductive`
   commands). Primitive projections extend the Calculus of Inductive
   Constructions with a new binary term constructor `r.(p)` representing a
   primitive projection `p` applied to a record object `r` (i.e., primitive
   projections are always applied). Even if the record type has parameters,
   these do not appear in the internal representation of applications of the
   projection, considerably reducing the sizes of terms when manipulating
   parameterized records and type checking time. On the user level, primitive
   projections can be used as a replacement for the usual defined ones, although
   there are a few notable differences.

.. attr:: projections(primitive{? = {| yes | no } })
   :name: projections(primitive)

   This :term:`boolean attribute` can be used to override the value of the
   :flag:`Primitive Projections` :term:`flag` for the record type being
   defined.

.. flag:: Printing Primitive Projection Parameters

   This compatibility :term:`flag` (off by default) reconstructs
   internally omitted parameters at printing time (even though they
   are absent in the actual AST manipulated by the kernel).

Reduction
+++++++++

The basic reduction rule of a primitive projection is
|p_i| ``(Build_``\ `R` |t_1| … |t_n|\ ``)`` :math:`{\rightarrow_{\iota}}` |t_i|.
However, to take the δ flag into account, projections can be in two states:
folded or unfolded. An unfolded primitive projection application obeys the rule
above, while the folded version delta-reduces to the unfolded version. This
allows to precisely mimic the usual unfolding rules of :term:`constants <constant>`.
Projections obey the usual ``simpl`` flags of the :cmd:`Arguments`
command in particular.

Unfolded primitive projections can be built using the compatibility
match syntax for primitive records, or by reducing the compatibility constant.

User-written :g:`match` constructs on primitive records are
desugared using the unfolded primitive projections and `let` bindings.

.. example::

   .. rocqtop:: reset all

      #[projections(primitive)] Record Sigma A B := sigma { p1 : A; p2 : B p1 }.
      Arguments sigma {_ _} _ _.

      Check fun x : Sigma nat (fun _ => nat) =>
        match x with sigma v _ => v + v end.

      Check fun x : Sigma nat (fun x => x = 0) =>
        match x return exists y, y = 0 with
          sigma v e => ex_intro _ v e
        end.

   Matches which are equivalent to just a projection have adhoc handling to avoid generating useless ``let``:

   .. rocqtop:: all

      Arguments p1 {_ _} _.
      Check fun x : Sigma nat (fun x => x = 0) =>
        match x return x.(p1) = 0 with sigma v e => e end.

.. flag:: Printing Unfolded Projection As Match

   By default this flag is off and unfolded primitive projections are
   printed the same as folded primitive projections. By setting this
   flag, unfolded primitive projections are instead printed as
   let-style matches in the form ``let '{| p := p |} := c in p``.

Compatibility Constants for Projections
+++++++++++++++++++++++++++++++++++++++

To ease compatibility with ordinary record types, each primitive projection is
also defined as an ordinary :term:`constant` taking parameters and an object of
the record type as arguments, and whose :term:`body` is an application of the
unfolded primitive projection of the same name. These constants are used when
elaborating partial applications of the projection. One can distinguish them
from applications of the primitive projection if the :flag:`Printing Primitive
Projection Parameters` flag is off: For a primitive projection application,
parameters are printed as underscores while for the compatibility projections
they are printed as usual. They cannot be distinguished if the record has no parameters.
