# Generated from TacticNotations.g by ANTLR 4.7
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\n")
        buf.write(":\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\4\b\t\b\4\t\t\t\3\2\3\2\3\2\3\3\3\3\3\4\3\4\3\5\3\5\3")
        buf.write("\5\3\6\3\6\6\6 \n\6\r\6\16\6!\5\6$\n\6\3\7\3\7\5\7(\n")
        buf.write("\7\3\7\6\7+\n\7\r\7\16\7,\3\b\3\b\3\b\6\b\62\n\b\r\b\16")
        buf.write("\b\63\3\t\6\t\67\n\t\r\t\16\t8\2\2\n\3\3\5\4\7\5\t\6\13")
        buf.write("\7\r\b\17\t\21\n\3\2\7\4\2,-AA\4\2*+}\177\4\2BBaa\7\2")
        buf.write("\"\"BBaa}}\177\177\5\2\62;C\\c|\2?\2\3\3\2\2\2\2\5\3\2")
        buf.write("\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2")
        buf.write("\2\17\3\2\2\2\2\21\3\2\2\2\3\23\3\2\2\2\5\26\3\2\2\2\7")
        buf.write("\30\3\2\2\2\t\32\3\2\2\2\13#\3\2\2\2\r%\3\2\2\2\17.\3")
        buf.write("\2\2\2\21\66\3\2\2\2\23\24\7}\2\2\24\25\t\2\2\2\25\4\3")
        buf.write("\2\2\2\26\27\7}\2\2\27\6\3\2\2\2\30\31\7\177\2\2\31\b")
        buf.write("\3\2\2\2\32\33\7\'\2\2\33\34\t\3\2\2\34\n\3\2\2\2\35$")
        buf.write("\t\4\2\2\36 \n\5\2\2\37\36\3\2\2\2 !\3\2\2\2!\37\3\2\2")
        buf.write("\2!\"\3\2\2\2\"$\3\2\2\2#\35\3\2\2\2#\37\3\2\2\2$\f\3")
        buf.write("\2\2\2%*\7B\2\2&(\7a\2\2\'&\3\2\2\2\'(\3\2\2\2()\3\2\2")
        buf.write("\2)+\t\6\2\2*\'\3\2\2\2+,\3\2\2\2,*\3\2\2\2,-\3\2\2\2")
        buf.write("-\16\3\2\2\2./\7a\2\2/\61\7a\2\2\60\62\t\6\2\2\61\60\3")
        buf.write("\2\2\2\62\63\3\2\2\2\63\61\3\2\2\2\63\64\3\2\2\2\64\20")
        buf.write("\3\2\2\2\65\67\7\"\2\2\66\65\3\2\2\2\678\3\2\2\28\66\3")
        buf.write("\2\2\289\3\2\2\29\22\3\2\2\2\t\2!#\',\638\2")
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
    SUB = 7
    WHITESPACE = 8

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'{'", "'}'" ]

    symbolicNames = [ "<INVALID>",
            "LGROUP", "LBRACE", "RBRACE", "METACHAR", "ATOM", "ID", "SUB",
            "WHITESPACE" ]

    ruleNames = [ "LGROUP", "LBRACE", "RBRACE", "METACHAR", "ATOM", "ID",
                  "SUB", "WHITESPACE" ]

    grammarFileName = "TacticNotations.g"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None
