Module Syndefs.

#[deprecated(since = "8.9", note = "Do not use.")]
Notation foo := Prop.

Fail
#[deprecated(since = "8.9", note = "Do not use."),
  deprecated(since = "8.10", note = "Duplicated deprecation.")]
Notation foo := Prop.

Check foo.

Set Warnings "+deprecated".

Fail Check foo.

End Syndefs.

Module Notations.

#[deprecated(since = "8.9", note = "Do not use.")]
Notation "!!" := Prop.

Check !!.

Set Warnings "+deprecated".

Fail Check !!.

End Notations.

Module Infix.

#[deprecated(since = "8.9", note = "Do not use.")]
Infix "!!" := plus (at level 1).

Check (_ !! _).

Set Warnings "+deprecated".

Fail Check (_ !! _).

End Infix.
