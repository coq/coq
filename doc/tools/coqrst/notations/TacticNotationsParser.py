# Generated from TacticNotations.g by ANTLR 4.7
# encoding: utf-8
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys

def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\b")
        buf.write("A\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b")
        buf.write("\t\b\4\t\t\t\3\2\3\2\3\2\3\3\3\3\5\3\30\n\3\3\3\7\3\33")
        buf.write("\n\3\f\3\16\3\36\13\3\3\4\3\4\3\4\3\4\5\4$\n\4\3\5\3\5")
        buf.write("\5\5(\n\5\3\5\3\5\3\5\5\5-\n\5\3\5\3\5\3\6\3\6\5\6\63")
        buf.write("\n\6\3\6\3\6\5\6\67\n\6\3\6\3\6\3\7\3\7\3\b\3\b\3\t\3")
        buf.write("\t\3\t\2\2\n\2\4\6\b\n\f\16\20\2\2\2A\2\22\3\2\2\2\4\25")
        buf.write("\3\2\2\2\6#\3\2\2\2\b%\3\2\2\2\n\60\3\2\2\2\f:\3\2\2\2")
        buf.write("\16<\3\2\2\2\20>\3\2\2\2\22\23\5\4\3\2\23\24\7\2\2\3\24")
        buf.write("\3\3\2\2\2\25\34\5\6\4\2\26\30\5\f\7\2\27\26\3\2\2\2\27")
        buf.write("\30\3\2\2\2\30\31\3\2\2\2\31\33\5\6\4\2\32\27\3\2\2\2")
        buf.write("\33\36\3\2\2\2\34\32\3\2\2\2\34\35\3\2\2\2\35\5\3\2\2")
        buf.write("\2\36\34\3\2\2\2\37$\5\16\b\2 $\5\20\t\2!$\5\b\5\2\"$")
        buf.write("\5\n\6\2#\37\3\2\2\2# \3\2\2\2#!\3\2\2\2#\"\3\2\2\2$\7")
        buf.write("\3\2\2\2%\'\7\3\2\2&(\7\6\2\2\'&\3\2\2\2\'(\3\2\2\2()")
        buf.write("\3\2\2\2)*\7\b\2\2*,\5\4\3\2+-\7\b\2\2,+\3\2\2\2,-\3\2")
        buf.write("\2\2-.\3\2\2\2./\7\5\2\2/\t\3\2\2\2\60\62\7\4\2\2\61\63")
        buf.write("\5\f\7\2\62\61\3\2\2\2\62\63\3\2\2\2\63\64\3\2\2\2\64")
        buf.write("\66\5\4\3\2\65\67\5\f\7\2\66\65\3\2\2\2\66\67\3\2\2\2")
        buf.write("\678\3\2\2\289\7\5\2\29\13\3\2\2\2:;\7\b\2\2;\r\3\2\2")
        buf.write("\2<=\7\6\2\2=\17\3\2\2\2>?\7\7\2\2?\21\3\2\2\2\t\27\34")
        buf.write("#\',\62\66")
        return buf.getvalue()


class TacticNotationsParser ( Parser ):

    grammarFileName = "TacticNotations.g"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "<INVALID>", "'{'", "'}'" ]

    symbolicNames = [ "<INVALID>", "LGROUP", "LBRACE", "RBRACE", "ATOM",
                      "ID", "WHITESPACE" ]

    RULE_top = 0
    RULE_blocks = 1
    RULE_block = 2
    RULE_repeat = 3
    RULE_curlies = 4
    RULE_whitespace = 5
    RULE_atomic = 6
    RULE_hole = 7

    ruleNames =  [ "top", "blocks", "block", "repeat", "curlies", "whitespace",
                   "atomic", "hole" ]

    EOF = Token.EOF
    LGROUP=1
    LBRACE=2
    RBRACE=3
    ATOM=4
    ID=5
    WHITESPACE=6

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.7")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None



    class TopContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def blocks(self):
            return self.getTypedRuleContext(TacticNotationsParser.BlocksContext,0)


        def EOF(self):
            return self.getToken(TacticNotationsParser.EOF, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_top

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitTop" ):
                return visitor.visitTop(self)
            else:
                return visitor.visitChildren(self)




    def top(self):

        localctx = TacticNotationsParser.TopContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_top)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 16
            self.blocks()
            self.state = 17
            self.match(TacticNotationsParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class BlocksContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def block(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(TacticNotationsParser.BlockContext)
            else:
                return self.getTypedRuleContext(TacticNotationsParser.BlockContext,i)


        def whitespace(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(TacticNotationsParser.WhitespaceContext)
            else:
                return self.getTypedRuleContext(TacticNotationsParser.WhitespaceContext,i)


        def getRuleIndex(self):
            return TacticNotationsParser.RULE_blocks

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBlocks" ):
                return visitor.visitBlocks(self)
            else:
                return visitor.visitChildren(self)




    def blocks(self):

        localctx = TacticNotationsParser.BlocksContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_blocks)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 19
            self.block()
            self.state = 26
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,1,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 21
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)
                    if _la==TacticNotationsParser.WHITESPACE:
                        self.state = 20
                        self.whitespace()


                    self.state = 23
                    self.block()
                self.state = 28
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,1,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class BlockContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def atomic(self):
            return self.getTypedRuleContext(TacticNotationsParser.AtomicContext,0)


        def hole(self):
            return self.getTypedRuleContext(TacticNotationsParser.HoleContext,0)


        def repeat(self):
            return self.getTypedRuleContext(TacticNotationsParser.RepeatContext,0)


        def curlies(self):
            return self.getTypedRuleContext(TacticNotationsParser.CurliesContext,0)


        def getRuleIndex(self):
            return TacticNotationsParser.RULE_block

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitBlock" ):
                return visitor.visitBlock(self)
            else:
                return visitor.visitChildren(self)




    def block(self):

        localctx = TacticNotationsParser.BlockContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_block)
        try:
            self.state = 33
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [TacticNotationsParser.ATOM]:
                self.enterOuterAlt(localctx, 1)
                self.state = 29
                self.atomic()
                pass
            elif token in [TacticNotationsParser.ID]:
                self.enterOuterAlt(localctx, 2)
                self.state = 30
                self.hole()
                pass
            elif token in [TacticNotationsParser.LGROUP]:
                self.enterOuterAlt(localctx, 3)
                self.state = 31
                self.repeat()
                pass
            elif token in [TacticNotationsParser.LBRACE]:
                self.enterOuterAlt(localctx, 4)
                self.state = 32
                self.curlies()
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class RepeatContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def LGROUP(self):
            return self.getToken(TacticNotationsParser.LGROUP, 0)

        def WHITESPACE(self, i:int=None):
            if i is None:
                return self.getTokens(TacticNotationsParser.WHITESPACE)
            else:
                return self.getToken(TacticNotationsParser.WHITESPACE, i)

        def blocks(self):
            return self.getTypedRuleContext(TacticNotationsParser.BlocksContext,0)


        def RBRACE(self):
            return self.getToken(TacticNotationsParser.RBRACE, 0)

        def ATOM(self):
            return self.getToken(TacticNotationsParser.ATOM, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_repeat

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitRepeat" ):
                return visitor.visitRepeat(self)
            else:
                return visitor.visitChildren(self)




    def repeat(self):

        localctx = TacticNotationsParser.RepeatContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_repeat)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 35
            self.match(TacticNotationsParser.LGROUP)
            self.state = 37
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.ATOM:
                self.state = 36
                self.match(TacticNotationsParser.ATOM)


            self.state = 39
            self.match(TacticNotationsParser.WHITESPACE)
            self.state = 40
            self.blocks()
            self.state = 42
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.WHITESPACE:
                self.state = 41
                self.match(TacticNotationsParser.WHITESPACE)


            self.state = 44
            self.match(TacticNotationsParser.RBRACE)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class CurliesContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def LBRACE(self):
            return self.getToken(TacticNotationsParser.LBRACE, 0)

        def blocks(self):
            return self.getTypedRuleContext(TacticNotationsParser.BlocksContext,0)


        def RBRACE(self):
            return self.getToken(TacticNotationsParser.RBRACE, 0)

        def whitespace(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(TacticNotationsParser.WhitespaceContext)
            else:
                return self.getTypedRuleContext(TacticNotationsParser.WhitespaceContext,i)


        def getRuleIndex(self):
            return TacticNotationsParser.RULE_curlies

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitCurlies" ):
                return visitor.visitCurlies(self)
            else:
                return visitor.visitChildren(self)




    def curlies(self):

        localctx = TacticNotationsParser.CurliesContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_curlies)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 46
            self.match(TacticNotationsParser.LBRACE)
            self.state = 48
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.WHITESPACE:
                self.state = 47
                self.whitespace()


            self.state = 50
            self.blocks()
            self.state = 52
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.WHITESPACE:
                self.state = 51
                self.whitespace()


            self.state = 54
            self.match(TacticNotationsParser.RBRACE)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class WhitespaceContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def WHITESPACE(self):
            return self.getToken(TacticNotationsParser.WHITESPACE, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_whitespace

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitWhitespace" ):
                return visitor.visitWhitespace(self)
            else:
                return visitor.visitChildren(self)




    def whitespace(self):

        localctx = TacticNotationsParser.WhitespaceContext(self, self._ctx, self.state)
        self.enterRule(localctx, 10, self.RULE_whitespace)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 56
            self.match(TacticNotationsParser.WHITESPACE)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class AtomicContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ATOM(self):
            return self.getToken(TacticNotationsParser.ATOM, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_atomic

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAtomic" ):
                return visitor.visitAtomic(self)
            else:
                return visitor.visitChildren(self)




    def atomic(self):

        localctx = TacticNotationsParser.AtomicContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_atomic)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 58
            self.match(TacticNotationsParser.ATOM)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class HoleContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self):
            return self.getToken(TacticNotationsParser.ID, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_hole

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitHole" ):
                return visitor.visitHole(self)
            else:
                return visitor.visitChildren(self)




    def hole(self):

        localctx = TacticNotationsParser.HoleContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_hole)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 60
            self.match(TacticNotationsParser.ID)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx
