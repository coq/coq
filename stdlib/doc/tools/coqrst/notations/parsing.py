##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
from .TacticNotationsLexer import TacticNotationsLexer
from .TacticNotationsParser import TacticNotationsParser

from antlr4 import CommonTokenStream, InputStream
from antlr4.error.ErrorListener import ErrorListener
from antlr4.Recognizer import Recognizer

import os

# Only print ANTLR version warning once
checked_version = False
check_version = Recognizer.checkVersion
def checkVersion_once(*args, **kwargs):
    global checked_version
    if not checked_version and os.getenv ("COQ_DEBUG_REFMAN"):
        # Using "Recognizer.checkVersion" would cause endless recursion
        check_version(*args, **kwargs)
        checked_version = True
Recognizer.checkVersion = checkVersion_once

SUBSTITUTIONS = [#("@bindings_list", "{+ (@id := @val) }"),
                 ("@qualid_or_string", "@id|@string")]

class ParseError(Exception):
    def __init__(self, msg):
        super().__init__()
        self.msg = msg

class ExceptionRaisingErrorListener(ErrorListener):
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        raise ParseError("{}:{}: {}".format(line, column, msg))

ERROR_LISTENER = ExceptionRaisingErrorListener()

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
    """Parse a notation string, optionally reporting errors to `error_listener`.

    :return: An ANTLR AST. Use one of the supplied visitors (or write your own)
             to turn it into useful output.
    """
    substituted = substitute(notation)
    lexer = TacticNotationsLexer(InputStream(substituted))
    parser = TacticNotationsParser(CommonTokenStream(lexer))
    parser.addErrorListener(ERROR_LISTENER)
    return parser.top()
