Set Cumulative StrictProp.
Definition ok(x:SProp) : Type := x. (*SProp is cumulative*)
Definition sp := SProp. (*sp aliases SProp*)
Definition bug(x:sp) : Type := x. (*sp is not cumulative*)
