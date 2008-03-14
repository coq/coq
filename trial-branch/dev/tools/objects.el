(defun add-survive-module nil
  (interactive)
  (query-replace-regexp 
   "
\\([ 	]*\\)\\(Summary\.\\)?survive_section"
   "
\\1\\2survive_module = false;
\\1\\2survive_section")
  )

(global-set-key [f2] 'add-survive-module)

; functions to change old style object declaration to new style

(defun repl-open nil
  (interactive)
  (query-replace-regexp 
   "open_function\\([ 	]*\\)=\\([ 	]*\\)cache_\\([a-zA-Z0-9'_]*\\)\\( *\\);" 
   "open_function\\1=\\2(fun i o -> if i=1 then cache_\\3 o)\\4;") 
  )

(global-set-key [f6] 'repl-open)

(defun repl-load nil
  (interactive)
  (query-replace-regexp 
   "load_function\\([ 	]*\\)=\\([ 	]*\\)cache_\\([a-zA-Z0-9'_]*\\)\\( *\\);" 
   "load_function\\1=\\2(fun _ -> cache_\\3)\\4;") 
  )

(global-set-key [f7] 'repl-load)

(defun repl-decl nil
  (interactive)
  (query-replace-regexp
   "\\(Libobject\.\\)?declare_object[ 
	]*([ 	]*\\(.*\\)[ 
	]*,[ 	]*
\\([ 	]*\\){\\([ 	]*\\)\\([^ ][^}]*\\)}[ 	]*)"

   "\\1declare_object {(\\1default_object \\2) with
\\3 \\4\\5}")
;   "|$1=\\1|$2=\\2|$3=\\3|$4=\\4|")
)

(global-set-key [f9] 'repl-decl)

; eval the above and try f9 f6 f7 on the following:

let (inThing,outThing) =
  declare_object
    ("THING", 
     { load_function = cache_thing;
       cache_function = cache_thing;
       open_function = cache_thing;
       export_function = (function x -> Some x)
     })


;%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
;%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
; functions helping writing non-copying substitutions

(defun make-subst (name)
  (interactive "s")
  (defun f (l)
    (save-excursion
      (query-replace-regexp
       (concat "\\([a-zA-z_0-9]*\\)[ 	]*:[ 	]*" 
	       (car l) 
	       "\\([ 	]*;\\|[ 	
]*\}\\)")
       (concat "let \\1\' = " (cdr l) " " name "\\1 in"))
      )
    )
  (mapcar 'f '(("constr"."subst_mps subst") 
	       ("Coqast.t"."subst_ast subst") 
	       ("Coqast.t list"."list_smartmap (subst_ast subst)") 
	       ("'pat"."subst_pat subst") 
	       ("'pat unparsing_hunk"."subst_hunk subst_pat subst")
	       ("'pat unparsing_hunk list"."list_smartmap (subst_hunk subst_pat subst)") 
	       ("'pat syntax_entry"."subst_syntax_entry subst_pat subst")
	       ("'pat syntax_entry list"."list_smartmap (subst_syntax_entry subst_pat subst)") 
	       ("constr option"."option_smartmap (subst_mps subst)")
	       ("constr list"."list_smartmap (subst_mps subst)")
	       ("constr array"."array_smartmap (subst_mps subst)")
	       ("constr_pattern"."subst_pattern subst")
	       ("constr_pattern option"."option_smartmap (subst_pattern subst)")
	       ("constr_pattern array"."array_smartmap (subst_pattern subst)")
	       ("constr_pattern list"."list_smartmap (subst_pattern subst)")
	       ("global_reference"."subst_global subst")
	       ("extended_global_reference"."subst_ext subst")
	       ("obj_typ"."subst_obj subst")
	       )
	  )
  )


(global-set-key [f2] 'make-subst)

(defun make-if (name)
  (interactive "s")
  (save-excursion
    (query-replace-regexp
     "\\([a-zA-z_0-9]*\\)[ 	]*:[ 	]*['a-zA-z_. ]*\\(;\\|[ 	
]*\}\\)"
     (concat "&& \\1\' == " name "\\1")
     )
    )
  )

(global-set-key [f4] 'make-if)

(defun make-record nil
  (interactive)
  (save-excursion 
    (query-replace-regexp
     "\\([a-zA-z_0-9]*\\)[ 	]*:[ 	]*['a-zA-z_. ]*\\(;\\|[ 	
]*\}\\)"
     (concat "\\1 = \\1\' ;")
     )
    )
  )

(global-set-key [f5] 'make-record)

(defun make-prim nil
  (interactive)
  (save-excursion (query-replace-regexp "\\<[a-zA-Z'_0-9]*\\>" "\\&'"))
  )

(global-set-key [f6] 'make-prim)


; eval the above, yank the text below and do 
; paste f2 morph.
; paste f4 morph.
; paste f5

      lem : constr;
      profil : bool list;
      arg_types : constr list;
      lem2 : constr option                                                      }


; and you almost get   Setoid_replace.subst_morph  :)

; and now f5 on this:

   (ref,(c1,c2))



