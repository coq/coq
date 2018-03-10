# Generated from TacticNotations.g by ANTLR 4.7
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .TacticNotationsParser import TacticNotationsParser
else:
    from TacticNotationsParser import TacticNotationsParser

# This class defines a complete generic visitor for a parse tree produced by TacticNotationsParser.

class TacticNotationsVisitor(ParseTreeVisitor):

    # Visit a parse tree produced by TacticNotationsParser#top.
    def visitTop(self, ctx:TacticNotationsParser.TopContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#blocks.
    def visitBlocks(self, ctx:TacticNotationsParser.BlocksContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#block.
    def visitBlock(self, ctx:TacticNotationsParser.BlockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#repeat.
    def visitRepeat(self, ctx:TacticNotationsParser.RepeatContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#curlies.
    def visitCurlies(self, ctx:TacticNotationsParser.CurliesContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#whitespace.
    def visitWhitespace(self, ctx:TacticNotationsParser.WhitespaceContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#meta.
    def visitMeta(self, ctx:TacticNotationsParser.MetaContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#atomic.
    def visitAtomic(self, ctx:TacticNotationsParser.AtomicContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#hole.
    def visitHole(self, ctx:TacticNotationsParser.HoleContext):
        return self.visitChildren(ctx)



del TacticNotationsParser
