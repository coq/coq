# Generated from TacticNotations.g by ANTLR 4.7.2
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys


def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\f")
        buf.write("f\b\1\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7")
        buf.write("\4\b\t\b\4\t\t\t\4\n\t\n\4\13\t\13\3\2\3\2\3\2\3\3\3\3")
        buf.write("\3\3\3\3\3\3\3\3\5\3!\n\3\3\4\3\4\3\5\3\5\3\6\3\6\3\6")
        buf.write("\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3")
        buf.write("\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6")
        buf.write("\3\6\5\6F\n\6\3\7\3\7\3\b\3\b\6\bL\n\b\r\b\16\bM\5\bP")
        buf.write("\n\b\3\t\3\t\5\tT\n\t\3\t\6\tW\n\t\r\t\16\tX\3\n\3\n\3")
        buf.write("\n\6\n^\n\n\r\n\16\n_\3\13\6\13c\n\13\r\13\16\13d\2\2")
        buf.write("\f\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\3\2\5")
        buf.write("\4\2BBaa\6\2\"\"BBaa}\177\5\2\62;C\\c|\2v\2\3\3\2\2\2")
        buf.write("\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r")
        buf.write("\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3")
        buf.write("\2\2\2\3\27\3\2\2\2\5 \3\2\2\2\7\"\3\2\2\2\t$\3\2\2\2")
        buf.write("\13E\3\2\2\2\rG\3\2\2\2\17O\3\2\2\2\21Q\3\2\2\2\23Z\3")
        buf.write("\2\2\2\25b\3\2\2\2\27\30\7}\2\2\30\31\7~\2\2\31\4\3\2")
        buf.write("\2\2\32\33\7}\2\2\33!\7-\2\2\34\35\7}\2\2\35!\7,\2\2\36")
        buf.write("\37\7}\2\2\37!\7A\2\2 \32\3\2\2\2 \34\3\2\2\2 \36\3\2")
        buf.write("\2\2!\6\3\2\2\2\"#\7}\2\2#\b\3\2\2\2$%\7\177\2\2%\n\3")
        buf.write("\2\2\2&\'\7\'\2\2\'F\7}\2\2()\7\'\2\2)F\7\177\2\2*+\7")
        buf.write("\'\2\2+F\7~\2\2,-\7b\2\2-.\7\'\2\2.F\7}\2\2/\60\7B\2\2")
        buf.write("\60\61\7\'\2\2\61F\7}\2\2\62\63\7\'\2\2\63\64\7~\2\2\64")
        buf.write("F\7/\2\2\65\66\7\'\2\2\66\67\7~\2\2\678\7/\2\28F\7@\2")
        buf.write("\29:\7\'\2\2:;\7~\2\2;F\7~\2\2<=\7\'\2\2=>\7~\2\2>?\7")
        buf.write("~\2\2?F\7~\2\2@A\7\'\2\2AB\7~\2\2BC\7~\2\2CD\7~\2\2DF")
        buf.write("\7~\2\2E&\3\2\2\2E(\3\2\2\2E*\3\2\2\2E,\3\2\2\2E/\3\2")
        buf.write("\2\2E\62\3\2\2\2E\65\3\2\2\2E9\3\2\2\2E<\3\2\2\2E@\3\2")
        buf.write("\2\2F\f\3\2\2\2GH\7~\2\2H\16\3\2\2\2IP\t\2\2\2JL\n\3\2")
        buf.write("\2KJ\3\2\2\2LM\3\2\2\2MK\3\2\2\2MN\3\2\2\2NP\3\2\2\2O")
        buf.write("I\3\2\2\2OK\3\2\2\2P\20\3\2\2\2QV\7B\2\2RT\7a\2\2SR\3")
        buf.write("\2\2\2ST\3\2\2\2TU\3\2\2\2UW\t\4\2\2VS\3\2\2\2WX\3\2\2")
        buf.write("\2XV\3\2\2\2XY\3\2\2\2Y\22\3\2\2\2Z[\7a\2\2[]\7a\2\2\\")
        buf.write("^\t\4\2\2]\\\3\2\2\2^_\3\2\2\2_]\3\2\2\2_`\3\2\2\2`\24")
        buf.write("\3\2\2\2ac\7\"\2\2ba\3\2\2\2cd\3\2\2\2db\3\2\2\2de\3\2")
        buf.write("\2\2e\26\3\2\2\2\13\2 EMOSX_d\2")
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
