(* A field may be declared inlinable and renamed at the same time.

   [Ord] declares [t] inlinable, so [S], which declares a module of that type,
   carries an inlining level for [O.t]. The [with Module] clause copies the
   resolver of its target onto [O], and [Tgt] has a field of its own to say
   something about, [Include] having made [Tgt.t] an alias of [MO.t]. Both
   statements then hold of [X.O.t] at once, which is precisely why a resolver
   keeps the two apart in separate maps.

   Applying [F] reads the inlining levels of the parameter's type, and used to
   assume that a field it found there was not also renamed. Drop the [Include]
   and [Tgt] has nothing to say about its own fields, so no name is copied and
   the two never meet. *)

Module Type Ord. Parameter Inline t : Type. End Ord.
Module MO. Definition t := nat. End MO.
Module Tgt. Include MO. End Tgt.
Module Type S. Declare Module O : Ord. End S.
Module F (X : S with Module O := Tgt). End F.
Module A. Module O := Tgt. End A.
Module R := F A.
