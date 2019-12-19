# Generated from TacticNotations.g by ANTLR 4.7.2
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\f")
        buf.write("S\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\3\2\3\2\3\2\3\3\3\3")
        buf.write("\3\3\3\3\3\3\3\3\5\3!\n\3\3\4\3\4\3\5\3\5\3\6\3\6\3\6")
        buf.write("\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\5\6\63\n\6\3\7\3")
        buf.write("\7\3\b\3\b\6\b9\n\b\r\b\16\b:\5\b=\n\b\3\t\3\t\5\tA\n")
        buf.write("\t\3\t\6\tD\n\t\r\t\16\tE\3\n\3\n\3\n\6\nK\n\n\r\n\16")
        buf.write("\nL\3\13\6\13P\n\13\r\13\16\13Q\2\2\f\3\3\5\4\7\5\t\6")
        buf.write("\13\7\r\b\17\t\21\n\23\13\25\f\3\2\5\4\2BBaa\6\2\"\"B")
        buf.write("Baa}\177\5\2\62;C\\c|\2^\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3")
        buf.write("\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2")
        buf.write("\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\3\27\3\2\2\2")
        buf.write("\5 \3\2\2\2\7\"\3\2\2\2\t$\3\2\2\2\13\62\3\2\2\2\r\64")
        buf.write("\3\2\2\2\17<\3\2\2\2\21>\3\2\2\2\23G\3\2\2\2\25O\3\2\2")
        buf.write("\2\27\30\7}\2\2\30\31\7~\2\2\31\4\3\2\2\2\32\33\7}\2\2")
        buf.write("\33!\7-\2\2\34\35\7}\2\2\35!\7,\2\2\36\37\7}\2\2\37!\7")
        buf.write("A\2\2 \32\3\2\2\2 \34\3\2\2\2 \36\3\2\2\2!\6\3\2\2\2\"")
        buf.write("#\7}\2\2#\b\3\2\2\2$%\7\177\2\2%\n\3\2\2\2&\'\7\'\2\2")
        buf.write("\'\63\7}\2\2()\7\'\2\2)\63\7\177\2\2*+\7\'\2\2+\63\7~")
        buf.write("\2\2,-\7b\2\2-.\7\'\2\2.\63\7}\2\2/\60\7B\2\2\60\61\7")
        buf.write("\'\2\2\61\63\7}\2\2\62&\3\2\2\2\62(\3\2\2\2\62*\3\2\2")
        buf.write("\2\62,\3\2\2\2\62/\3\2\2\2\63\f\3\2\2\2\64\65\7~\2\2\65")
        buf.write("\16\3\2\2\2\66=\t\2\2\2\679\n\3\2\28\67\3\2\2\29:\3\2")
        buf.write("\2\2:8\3\2\2\2:;\3\2\2\2;=\3\2\2\2<\66\3\2\2\2<8\3\2\2")
        buf.write("\2=\20\3\2\2\2>C\7B\2\2?A\7a\2\2@?\3\2\2\2@A\3\2\2\2A")
        buf.write("B\3\2\2\2BD\t\4\2\2C@\3\2\2\2DE\3\2\2\2EC\3\2\2\2EF\3")
        buf.write("\2\2\2F\22\3\2\2\2GH\7a\2\2HJ\7a\2\2IK\t\4\2\2JI\3\2\2")
        buf.write("\2KL\3\2\2\2LJ\3\2\2\2LM\3\2\2\2M\24\3\2\2\2NP\7\"\2\2")
        buf.write("ON\3\2\2\2PQ\3\2\2\2QO\3\2\2\2QR\3\2\2\2R\26\3\2\2\2\13")
        buf.write("\2 \62:<@ELQ\2")
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
