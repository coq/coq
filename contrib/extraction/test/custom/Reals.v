Require Reals. 
Extract Inlined Constant R => float.
Extract Inlined Constant R0 => "0.0".
Extract Inlined Constant R1 => "1.0".
Extract Inlined Constant Rplus => "(+.)".
Extract Inlined Constant Rmult => "( *.)".
Extract Inlined Constant Ropp => "(~-.)".
Extract Inlined Constant Rinv => "(fun x -> 1.0 /. x)".
Extract Inlined Constant Rlt => "(<)".
Extract Inlined Constant up => "AddReals.my_ceil".
Extract Inlined Constant total_order_T => "AddReals.total_order_T".
Extract Inlined Constant sqrt => "sqrt".
Extract Inlined Constant sigma => "(fun l h -> sigma_aux l h (Minus.minus h l))".
Extract Inlined Constant PI => "3.141593".
Extract Inlined Constant cos => cos.
Extract Inlined Constant sin => sin.
Extract Inlined Constant derive_pt => "(fun f x -> ((f (x+.1E-5))-.(f x))*.1E5)".
