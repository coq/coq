# Generated from TacticNotations.g by ANTLR 4.7
# encoding: utf-8
from antlr4 import *
from io import StringIO
from typing.io import TextIO
import sys

def serializedATN():
    with StringIO() as buf:
        buf.write("\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\n")
        buf.write("J\4\2\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b")
        buf.write("\t\b\4\t\t\t\4\n\t\n\3\2\3\2\3\2\3\3\3\3\5\3\32\n\3\3")
        buf.write("\3\7\3\35\n\3\f\3\16\3 \13\3\3\4\3\4\3\4\3\4\3\4\5\4\'")
        buf.write("\n\4\3\5\3\5\5\5+\n\5\3\5\3\5\3\5\5\5\60\n\5\3\5\3\5\3")
        buf.write("\6\3\6\5\6\66\n\6\3\6\3\6\5\6:\n\6\3\6\3\6\3\7\3\7\3\b")
        buf.write("\3\b\3\t\3\t\5\tD\n\t\3\n\3\n\5\nH\n\n\3\n\2\2\13\2\4")
        buf.write("\6\b\n\f\16\20\22\2\2\2L\2\24\3\2\2\2\4\27\3\2\2\2\6&")
        buf.write("\3\2\2\2\b(\3\2\2\2\n\63\3\2\2\2\f=\3\2\2\2\16?\3\2\2")
        buf.write("\2\20A\3\2\2\2\22E\3\2\2\2\24\25\5\4\3\2\25\26\7\2\2\3")
        buf.write("\26\3\3\2\2\2\27\36\5\6\4\2\30\32\5\f\7\2\31\30\3\2\2")
        buf.write("\2\31\32\3\2\2\2\32\33\3\2\2\2\33\35\5\6\4\2\34\31\3\2")
        buf.write("\2\2\35 \3\2\2\2\36\34\3\2\2\2\36\37\3\2\2\2\37\5\3\2")
        buf.write("\2\2 \36\3\2\2\2!\'\5\20\t\2\"\'\5\16\b\2#\'\5\22\n\2")
        buf.write("$\'\5\b\5\2%\'\5\n\6\2&!\3\2\2\2&\"\3\2\2\2&#\3\2\2\2")
        buf.write("&$\3\2\2\2&%\3\2\2\2\'\7\3\2\2\2(*\7\3\2\2)+\7\7\2\2*")
        buf.write(")\3\2\2\2*+\3\2\2\2+,\3\2\2\2,-\7\n\2\2-/\5\4\3\2.\60")
        buf.write("\7\n\2\2/.\3\2\2\2/\60\3\2\2\2\60\61\3\2\2\2\61\62\7\5")
        buf.write("\2\2\62\t\3\2\2\2\63\65\7\4\2\2\64\66\5\f\7\2\65\64\3")
        buf.write("\2\2\2\65\66\3\2\2\2\66\67\3\2\2\2\679\5\4\3\28:\5\f\7")
        buf.write("\298\3\2\2\29:\3\2\2\2:;\3\2\2\2;<\7\5\2\2<\13\3\2\2\2")
        buf.write("=>\7\n\2\2>\r\3\2\2\2?@\7\6\2\2@\17\3\2\2\2AC\7\7\2\2")
        buf.write("BD\7\t\2\2CB\3\2\2\2CD\3\2\2\2D\21\3\2\2\2EG\7\b\2\2F")
        buf.write("H\7\t\2\2GF\3\2\2\2GH\3\2\2\2H\23\3\2\2\2\13\31\36&*/")
        buf.write("\659CG")
        return buf.getvalue()


class TacticNotationsParser ( Parser ):

    grammarFileName = "TacticNotations.g"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "<INVALID>", "'{'", "'}'" ]

    symbolicNames = [ "<INVALID>", "LGROUP", "LBRACE", "RBRACE", "METACHAR",
                      "ATOM", "ID", "SUB", "WHITESPACE" ]

    RULE_top = 0
    RULE_blocks = 1
    RULE_block = 2
    RULE_repeat = 3
    RULE_curlies = 4
    RULE_whitespace = 5
    RULE_meta = 6
    RULE_atomic = 7
    RULE_hole = 8

    ruleNames =  [ "top", "blocks", "block", "repeat", "curlies", "whitespace",
                   "meta", "atomic", "hole" ]

    EOF = Token.EOF
    LGROUP=1
    LBRACE=2
    RBRACE=3
    METACHAR=4
    ATOM=5
    ID=6
    SUB=7
    WHITESPACE=8

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
            self.state = 18
            self.blocks()
            self.state = 19
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
            self.state = 21
            self.block()
            self.state = 28
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,1,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 23
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)
                    if _la==TacticNotationsParser.WHITESPACE:
                        self.state = 22
                        self.whitespace()


                    self.state = 25
                    self.block()
                self.state = 30
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


        def meta(self):
            return self.getTypedRuleContext(TacticNotationsParser.MetaContext,0)


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
            self.state = 36
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [TacticNotationsParser.ATOM]:
                self.enterOuterAlt(localctx, 1)
                self.state = 31
                self.atomic()
                pass
            elif token in [TacticNotationsParser.METACHAR]:
                self.enterOuterAlt(localctx, 2)
                self.state = 32
                self.meta()
                pass
            elif token in [TacticNotationsParser.ID]:
                self.enterOuterAlt(localctx, 3)
                self.state = 33
                self.hole()
                pass
            elif token in [TacticNotationsParser.LGROUP]:
                self.enterOuterAlt(localctx, 4)
                self.state = 34
                self.repeat()
                pass
            elif token in [TacticNotationsParser.LBRACE]:
                self.enterOuterAlt(localctx, 5)
                self.state = 35
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
            self.state = 38
            self.match(TacticNotationsParser.LGROUP)
            self.state = 40
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.ATOM:
                self.state = 39
                self.match(TacticNotationsParser.ATOM)


            self.state = 42
            self.match(TacticNotationsParser.WHITESPACE)
            self.state = 43
            self.blocks()
            self.state = 45
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.WHITESPACE:
                self.state = 44
                self.match(TacticNotationsParser.WHITESPACE)


            self.state = 47
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
            self.state = 49
            self.match(TacticNotationsParser.LBRACE)
            self.state = 51
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.WHITESPACE:
                self.state = 50
                self.whitespace()


            self.state = 53
            self.blocks()
            self.state = 55
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.WHITESPACE:
                self.state = 54
                self.whitespace()


            self.state = 57
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
            self.state = 59
            self.match(TacticNotationsParser.WHITESPACE)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx

    class MetaContext(ParserRuleContext):

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def METACHAR(self):
            return self.getToken(TacticNotationsParser.METACHAR, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_meta

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitMeta" ):
                return visitor.visitMeta(self)
            else:
                return visitor.visitChildren(self)




    def meta(self):

        localctx = TacticNotationsParser.MetaContext(self, self._ctx, self.state)
        self.enterRule(localctx, 12, self.RULE_meta)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 61
            self.match(TacticNotationsParser.METACHAR)
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

        def SUB(self):
            return self.getToken(TacticNotationsParser.SUB, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_atomic

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitAtomic" ):
                return visitor.visitAtomic(self)
            else:
                return visitor.visitChildren(self)




    def atomic(self):

        localctx = TacticNotationsParser.AtomicContext(self, self._ctx, self.state)
        self.enterRule(localctx, 14, self.RULE_atomic)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 63
            self.match(TacticNotationsParser.ATOM)
            self.state = 65
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.SUB:
                self.state = 64
                self.match(TacticNotationsParser.SUB)


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

        def SUB(self):
            return self.getToken(TacticNotationsParser.SUB, 0)

        def getRuleIndex(self):
            return TacticNotationsParser.RULE_hole

        def accept(self, visitor:ParseTreeVisitor):
            if hasattr( visitor, "visitHole" ):
                return visitor.visitHole(self)
            else:
                return visitor.visitChildren(self)




    def hole(self):

        localctx = TacticNotationsParser.HoleContext(self, self._ctx, self.state)
        self.enterRule(localctx, 16, self.RULE_hole)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 67
            self.match(TacticNotationsParser.ID)
            self.state = 69
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==TacticNotationsParser.SUB:
                self.state = 68
                self.match(TacticNotationsParser.SUB)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx
