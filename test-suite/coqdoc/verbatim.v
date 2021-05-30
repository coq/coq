(**

<<
uint32_t shift_right( uint32_t a, uint32_t shift )
{
    return a >> shift;
}
>>

This line and the following shows << verbatim >> text:

<< A stand-alone inline verbatim >>

<< A non-ended inline verbatim to test line location


- item 1
- item 2 is <<verbatim>>
- item 3 is <<verbatim>> too
[[
A coq block : forall n, n = 0
]]
- <<verbatim>> again, and a formula [ True -> False ]
-
<<
multiline
verbatim
>>
- last item

[[[
Γ ⊢ A
----
Γ ⊢ A ∨ B
]]]

<<
A non-ended block verbatim to test line location

*)
