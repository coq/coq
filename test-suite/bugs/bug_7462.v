(* Adding an only-printing notation should not override existing
   interpretations for the same notation. *)

Notation "$ x" := (@id nat x) (only parsing, at level 0, right associativity).
Notation "$ x" := (@id bool x) (only printing, at level 0, right associativity).
Check $1. (* Was: Error: Unknown interpretation for notation "$ _". *)

(* Adding an only-printing notation should not let believe
   that a parsing rule has been given *)

Notation "$ x" := (@id bool x) (only printing, at level 0, right associativity).
Notation "$ x" := (@id nat x) (only parsing, at level 0, right associativity).
Check $1. (* Was: Error: Syntax Error: Lexer: Undefined token *)
