Class Foo := foo : True.
Instance: Foo := I.
Definition bar (v:=_) (H : @foo v = @foo v) : True := I.
