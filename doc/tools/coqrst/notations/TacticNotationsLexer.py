# Generated from TacticNotations.g by ANTLR 4.7
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\b")
        buf.write("&\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\3\2\3\2\3\2\3\3\3\3\3\4\3\4\3\5\6\5\30\n\5\r\5\16\5\31")
        buf.write("\3\6\3\6\6\6\36\n\6\r\6\16\6\37\3\7\6\7#\n\7\r\7\16\7")
        buf.write("$\2\2\b\3\3\5\4\7\5\t\6\13\7\r\b\3\2\5\4\2,-AA\6\2\"\"")
        buf.write("BB}}\177\177\6\2\62;C\\aac|\2(\2\3\3\2\2\2\2\5\3\2\2\2")
        buf.write("\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\3\17")
        buf.write("\3\2\2\2\5\22\3\2\2\2\7\24\3\2\2\2\t\27\3\2\2\2\13\33")
        buf.write("\3\2\2\2\r\"\3\2\2\2\17\20\7}\2\2\20\21\t\2\2\2\21\4\3")
        buf.write("\2\2\2\22\23\7}\2\2\23\6\3\2\2\2\24\25\7\177\2\2\25\b")
        buf.write("\3\2\2\2\26\30\n\3\2\2\27\26\3\2\2\2\30\31\3\2\2\2\31")
        buf.write("\27\3\2\2\2\31\32\3\2\2\2\32\n\3\2\2\2\33\35\7B\2\2\34")
        buf.write("\36\t\4\2\2\35\34\3\2\2\2\36\37\3\2\2\2\37\35\3\2\2\2")
        buf.write("\37 \3\2\2\2 \f\3\2\2\2!#\7\"\2\2\"!\3\2\2\2#$\3\2\2\2")
        buf.write("$\"\3\2\2\2$%\3\2\2\2%\16\3\2\2\2\6\2\31\37$\2")
        return buf.getvalue()


class TacticNotationsLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    LGROUP = 1
    LBRACE = 2
    RBRACE = 3
    ATOM = 4
    ID = 5
    WHITESPACE = 6

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'{'", "'}'" ]

    symbolicNames = [ "<INVALID>",
            "LGROUP", "LBRACE", "RBRACE", "ATOM", "ID", "WHITESPACE" ]

    ruleNames = [ "LGROUP", "LBRACE", "RBRACE", "ATOM", "ID", "WHITESPACE" ]

    grammarFileName = "TacticNotations.g"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None
