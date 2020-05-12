# Generated from TacticNotations.g by ANTLR 4.7.2
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\f")
        buf.write("U\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\3\2\3\2\3\2\3\3\3\3")
        buf.write("\3\3\3\3\3\3\3\3\5\3!\n\3\3\4\3\4\3\5\3\5\3\6\3\6\3\6")
        buf.write("\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\5\6\65\n")
        buf.write("\6\3\7\3\7\3\b\3\b\6\b;\n\b\r\b\16\b<\5\b?\n\b\3\t\3\t")
        buf.write("\5\tC\n\t\3\t\6\tF\n\t\r\t\16\tG\3\n\3\n\3\n\6\nM\n\n")
        buf.write("\r\n\16\nN\3\13\6\13R\n\13\r\13\16\13S\2\2\f\3\3\5\4\7")
        buf.write("\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\3\2\5\4\2BBaa\6\2")
        buf.write("\"\"BBaa}\177\5\2\62;C\\c|\2a\2\3\3\2\2\2\2\5\3\2\2\2")
        buf.write("\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17")
        buf.write("\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\3\27\3")
        buf.write("\2\2\2\5 \3\2\2\2\7\"\3\2\2\2\t$\3\2\2\2\13\64\3\2\2\2")
        buf.write("\r\66\3\2\2\2\17>\3\2\2\2\21@\3\2\2\2\23I\3\2\2\2\25Q")
        buf.write("\3\2\2\2\27\30\7}\2\2\30\31\7~\2\2\31\4\3\2\2\2\32\33")
        buf.write("\7}\2\2\33!\7-\2\2\34\35\7}\2\2\35!\7,\2\2\36\37\7}\2")
        buf.write("\2\37!\7A\2\2 \32\3\2\2\2 \34\3\2\2\2 \36\3\2\2\2!\6\3")
        buf.write("\2\2\2\"#\7}\2\2#\b\3\2\2\2$%\7\177\2\2%\n\3\2\2\2&\'")
        buf.write("\7\'\2\2\'\65\7}\2\2()\7\'\2\2)\65\7\177\2\2*+\7\'\2\2")
        buf.write("+\65\7~\2\2,-\7\'\2\2-\65\7B\2\2./\7b\2\2/\60\7\'\2\2")
        buf.write("\60\65\7}\2\2\61\62\7B\2\2\62\63\7\'\2\2\63\65\7}\2\2")
        buf.write("\64&\3\2\2\2\64(\3\2\2\2\64*\3\2\2\2\64,\3\2\2\2\64.\3")
        buf.write("\2\2\2\64\61\3\2\2\2\65\f\3\2\2\2\66\67\7~\2\2\67\16\3")
        buf.write("\2\2\28?\t\2\2\29;\n\3\2\2:9\3\2\2\2;<\3\2\2\2<:\3\2\2")
        buf.write("\2<=\3\2\2\2=?\3\2\2\2>8\3\2\2\2>:\3\2\2\2?\20\3\2\2\2")
        buf.write("@E\7B\2\2AC\7a\2\2BA\3\2\2\2BC\3\2\2\2CD\3\2\2\2DF\t\4")
        buf.write("\2\2EB\3\2\2\2FG\3\2\2\2GE\3\2\2\2GH\3\2\2\2H\22\3\2\2")
        buf.write("\2IJ\7a\2\2JL\7a\2\2KM\t\4\2\2LK\3\2\2\2MN\3\2\2\2NL\3")
        buf.write("\2\2\2NO\3\2\2\2O\24\3\2\2\2PR\7\"\2\2QP\3\2\2\2RS\3\2")
        buf.write("\2\2SQ\3\2\2\2ST\3\2\2\2T\26\3\2\2\2\13\2 \64<>BGNS\2")
        return buf.getvalue()


class TacticNotationsLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    LALT = 1
    LGROUP = 2
    LBRACE = 3
    RBRACE = 4
    ESCAPED = 5
    PIPE = 6
    ATOM = 7
    ID = 8
    SUB = 9
    WHITESPACE = 10

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'{|'", "'{'", "'}'", "'|'" ]

    symbolicNames = [ "<INVALID>",
            "LALT", "LGROUP", "LBRACE", "RBRACE", "ESCAPED", "PIPE", "ATOM",
            "ID", "SUB", "WHITESPACE" ]

    ruleNames = [ "LALT", "LGROUP", "LBRACE", "RBRACE", "ESCAPED", "PIPE",
                  "ATOM", "ID", "SUB", "WHITESPACE" ]

    grammarFileName = "TacticNotations.g"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7.2")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None
