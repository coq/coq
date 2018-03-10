##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
from .TacticNotationsLexer import TacticNotationsLexer
from .TacticNotationsParser import TacticNotationsParser

from antlr4 import CommonTokenStream, InputStream

SUBSTITUTIONS = [#("@bindings_list", "{+ (@id := @val) }"),
                 ("@qualid_or_string", "@id|@string")]

def substitute(notation):
    """Perform common substitutions in the notation string.

    Nested notations quickly became unwieldy in the original ‘…’-based format,
    so they were avoided and replaced by pointers to grammar rules.  With the
    new format, it's usually nicer to remove the indirection.
    """
    for (src, dst) in SUBSTITUTIONS:
        notation = notation.replace(src, dst)
    return notation

def parse(notation):
    """Parse a notation string.

    :return: An ANTLR AST. Use one of the supplied visitors (or write your own)
             to turn it into useful output.
    """
    substituted = substitute(notation)
    lexer = TacticNotationsLexer(InputStream(substituted))
    return TacticNotationsParser(CommonTokenStream(lexer)).top()
