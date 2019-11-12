Module Syndefs.

#[deprecated(since = "8.9", note = "Do not use.")]
Notation foo := Prop.

Notation bar := Prop (compat "8.9").

Fail
#[deprecated(since = "8.9", note = "Do not use.")]
Notation zar := Prop (compat "8.9").

Check foo.
Check bar.

Set Warnings "+deprecated".

Fail Check foo.
Fail Check bar.

End Syndefs.

Module Notations.

#[deprecated(since = "8.9", note = "Do not use.")]
Notation "!!" := Prop.

Notation "##" := Prop (compat "8.9").

Fail
#[deprecated(since = "8.9", note = "Do not use.")]
Notation "**" := Prop (compat "8.9").

Check !!.
Check ##.

Set Warnings "+deprecated".

Fail Check !!.
Fail Check ##.

End Notations.

Module Infix.

#[deprecated(since = "8.9", note = "Do not use.")]
Infix "!!" := plus (at level 1).

Infix "##" := plus (at level 1, compat "8.9").

Fail
#[deprecated(since = "8.9", note = "Do not use.")]
Infix "**" := plus (at level 1, compat "8.9").

Check (_ !! _).
Check (_ ## _).

Set Warnings "+deprecated".

Fail Check (_ !! _).
Fail Check (_ ## _).

End Infix.
