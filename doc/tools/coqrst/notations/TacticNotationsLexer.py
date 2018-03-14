# Generated from TacticNotations.g by ANTLR 4.7
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\t")
        buf.write(".\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\4\b\t\b\3\2\3\2\3\2\3\3\3\3\3\4\3\4\3\5\3\5\3\5\3\6\3")
        buf.write("\6\6\6\36\n\6\r\6\16\6\37\5\6\"\n\6\3\7\3\7\6\7&\n\7\r")
        buf.write("\7\16\7\'\3\b\6\b+\n\b\r\b\16\b,\2\2\t\3\3\5\4\7\5\t\6")
        buf.write("\13\7\r\b\17\t\3\2\6\4\2,-AA\4\2*+~~\6\2\"\"BB}}\177\177")
        buf.write("\6\2\62;C\\aac|\2\61\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2")
        buf.write("\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\3")
        buf.write("\21\3\2\2\2\5\24\3\2\2\2\7\26\3\2\2\2\t\30\3\2\2\2\13")
        buf.write("!\3\2\2\2\r#\3\2\2\2\17*\3\2\2\2\21\22\7}\2\2\22\23\t")
        buf.write("\2\2\2\23\4\3\2\2\2\24\25\7}\2\2\25\6\3\2\2\2\26\27\7")
        buf.write("\177\2\2\27\b\3\2\2\2\30\31\7\'\2\2\31\32\t\3\2\2\32\n")
        buf.write("\3\2\2\2\33\"\7B\2\2\34\36\n\4\2\2\35\34\3\2\2\2\36\37")
        buf.write("\3\2\2\2\37\35\3\2\2\2\37 \3\2\2\2 \"\3\2\2\2!\33\3\2")
        buf.write("\2\2!\35\3\2\2\2\"\f\3\2\2\2#%\7B\2\2$&\t\5\2\2%$\3\2")
        buf.write("\2\2&\'\3\2\2\2\'%\3\2\2\2\'(\3\2\2\2(\16\3\2\2\2)+\7")
        buf.write("\"\2\2*)\3\2\2\2+,\3\2\2\2,*\3\2\2\2,-\3\2\2\2-\20\3\2")
        buf.write("\2\2\7\2\37!\',\2")
        return buf.getvalue()


class TacticNotationsLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    LGROUP = 1
    LBRACE = 2
    RBRACE = 3
    METACHAR = 4
    ATOM = 5
    ID = 6
    WHITESPACE = 7

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'{'", "'}'" ]

    symbolicNames = [ "<INVALID>",
            "LGROUP", "LBRACE", "RBRACE", "METACHAR", "ATOM", "ID", "WHITESPACE" ]

    ruleNames = [ "LGROUP", "LBRACE", "RBRACE", "METACHAR", "ATOM", "ID",
                  "WHITESPACE" ]

    grammarFileName = "TacticNotations.g"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None
