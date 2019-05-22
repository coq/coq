# Generated from TacticNotations.g by ANTLR 4.7.2
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\f")
        buf.write("M\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\3\2\3\2\3\2\3\3\3\3")
        buf.write("\3\3\3\3\3\3\3\3\5\3!\n\3\3\4\3\4\3\5\3\5\3\6\3\6\3\6")
        buf.write("\3\6\3\6\3\6\5\6-\n\6\3\7\3\7\3\b\3\b\6\b\63\n\b\r\b\16")
        buf.write("\b\64\5\b\67\n\b\3\t\3\t\5\t;\n\t\3\t\6\t>\n\t\r\t\16")
        buf.write("\t?\3\n\3\n\3\n\6\nE\n\n\r\n\16\nF\3\13\6\13J\n\13\r\13")
        buf.write("\16\13K\2\2\f\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13")
        buf.write("\25\f\3\2\5\4\2BBaa\6\2\"\"BBaa}\177\5\2\62;C\\c|\2V\2")
        buf.write("\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3")
        buf.write("\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2")
        buf.write("\2\2\2\25\3\2\2\2\3\27\3\2\2\2\5 \3\2\2\2\7\"\3\2\2\2")
        buf.write("\t$\3\2\2\2\13,\3\2\2\2\r.\3\2\2\2\17\66\3\2\2\2\218\3")
        buf.write("\2\2\2\23A\3\2\2\2\25I\3\2\2\2\27\30\7}\2\2\30\31\7~\2")
        buf.write("\2\31\4\3\2\2\2\32\33\7}\2\2\33!\7-\2\2\34\35\7}\2\2\35")
        buf.write("!\7,\2\2\36\37\7}\2\2\37!\7A\2\2 \32\3\2\2\2 \34\3\2\2")
        buf.write("\2 \36\3\2\2\2!\6\3\2\2\2\"#\7}\2\2#\b\3\2\2\2$%\7\177")
        buf.write("\2\2%\n\3\2\2\2&\'\7\'\2\2\'-\7}\2\2()\7\'\2\2)-\7\177")
        buf.write("\2\2*+\7\'\2\2+-\7~\2\2,&\3\2\2\2,(\3\2\2\2,*\3\2\2\2")
        buf.write("-\f\3\2\2\2./\7~\2\2/\16\3\2\2\2\60\67\t\2\2\2\61\63\n")
        buf.write("\3\2\2\62\61\3\2\2\2\63\64\3\2\2\2\64\62\3\2\2\2\64\65")
        buf.write("\3\2\2\2\65\67\3\2\2\2\66\60\3\2\2\2\66\62\3\2\2\2\67")
        buf.write("\20\3\2\2\28=\7B\2\29;\7a\2\2:9\3\2\2\2:;\3\2\2\2;<\3")
        buf.write("\2\2\2<>\t\4\2\2=:\3\2\2\2>?\3\2\2\2?=\3\2\2\2?@\3\2\2")
        buf.write("\2@\22\3\2\2\2AB\7a\2\2BD\7a\2\2CE\t\4\2\2DC\3\2\2\2E")
        buf.write("F\3\2\2\2FD\3\2\2\2FG\3\2\2\2G\24\3\2\2\2HJ\7\"\2\2IH")
        buf.write("\3\2\2\2JK\3\2\2\2KI\3\2\2\2KL\3\2\2\2L\26\3\2\2\2\13")
        buf.write("\2 ,\64\66:?FK\2")
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
