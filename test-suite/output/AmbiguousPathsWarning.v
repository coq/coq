Class A := Ael : unit.
Identity Coercion A_to_unit: A >-> unit.
Identity Coercion A_to_unit': A >-> unit.

Set Warnings "-ambiguous-paths".
Identity Coercion A_to_unit'': A >-> unit.
