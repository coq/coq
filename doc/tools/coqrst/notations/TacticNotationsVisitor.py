# Generated from TacticNotations.g by ANTLR 4.7.2
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


    # Visit a parse tree produced by TacticNotationsParser#nopipeblock.
    def visitNopipeblock(self, ctx:TacticNotationsParser.NopipeblockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#alternative.
    def visitAlternative(self, ctx:TacticNotationsParser.AlternativeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#altblocks.
    def visitAltblocks(self, ctx:TacticNotationsParser.AltblocksContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#altblock.
    def visitAltblock(self, ctx:TacticNotationsParser.AltblockContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#repeat.
    def visitRepeat(self, ctx:TacticNotationsParser.RepeatContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#curlies.
    def visitCurlies(self, ctx:TacticNotationsParser.CurliesContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#pipe.
    def visitPipe(self, ctx:TacticNotationsParser.PipeContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#altsep.
    def visitAltsep(self, ctx:TacticNotationsParser.AltsepContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#whitespace.
    def visitWhitespace(self, ctx:TacticNotationsParser.WhitespaceContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#escaped.
    def visitEscaped(self, ctx:TacticNotationsParser.EscapedContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#atomic.
    def visitAtomic(self, ctx:TacticNotationsParser.AtomicContext):
        return self.visitChildren(ctx)


    # Visit a parse tree produced by TacticNotationsParser#hole.
    def visitHole(self, ctx:TacticNotationsParser.HoleContext):
        return self.visitChildren(ctx)



del TacticNotationsParser
