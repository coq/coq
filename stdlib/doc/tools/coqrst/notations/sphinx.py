##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #         Copyright INRIA, CNRS and contributors             ##
## <O___,, # (see version control and CREDITS file for authors & dates) ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""A visitor for ANTLR notation ASTs, producing Sphinx nodes.

Unlike the HTML visitor, this produces Sphinx-friendly nodes that can be used by
all backends. If you just want HTML output, use the HTML visitor.
"""

from .parsing import parse
from .TacticNotationsParser import TacticNotationsParser
from .TacticNotationsVisitor import TacticNotationsVisitor

from docutils import nodes
from sphinx import addnodes

class TacticNotationsToSphinxVisitor(TacticNotationsVisitor):
    def defaultResult(self):
        return []

    def aggregateResult(self, aggregate, nextResult):
        if nextResult:
            aggregate.extend(nextResult)
        return aggregate

    def visitAlternative(self, ctx:TacticNotationsParser.AlternativeContext):
        return [nodes.inline('', '', *self.visitChildren(ctx), classes=['alternative'])]

    def visitAltblock(self, ctx:TacticNotationsParser.AltblockContext):
        return [nodes.inline('', '', *self.visitChildren(ctx), classes=['alternative-block'])]

    def visitAltsep(self, ctx:TacticNotationsParser.AltsepContext):
        return [nodes.inline('|', '\u200b', classes=['alternative-separator'])]

    @staticmethod
    def is_alternative(node):
        return isinstance(node, nodes.inline) and node['classes'] == ['alternative']

    def visitRepeat(self, ctx:TacticNotationsParser.RepeatContext):
        # Uses inline nodes instead of subscript and superscript to ensure that
        # we get the right customization hooks at the LaTeX level
        separator = ctx.ATOM() or ctx.PIPE()
        # I wanted to have 2 independent classes "repeat-wrapper" and "with-sub" here,
        # but that breaks the latex build (invalid .tex file)
        classes = 'repeat-wrapper-with-sub' if separator  else 'repeat-wrapper'
        wrapper = nodes.inline('', '', classes=[classes])

        children = self.visitChildren(ctx)
        if len(children) == 1 and self.is_alternative(children[0]):
            # Use a custom style if an alternative is nested in a repeat.
            # (We could detect this in CSS, but it's much harder in LaTeX.)

            children[0]['classes'] = ['repeated-alternative']
        wrapper += nodes.inline('', '', *children, classes=["repeat"])

        repeat_marker = ctx.LGROUP().getText()[1]
        wrapper += nodes.inline(repeat_marker, repeat_marker, classes=['notation-sup'])

        if separator:
            sep = separator.getText()
            wrapper += nodes.inline(sep, sep, classes=['notation-sub'])

        return [wrapper]

    def visitCurlies(self, ctx:TacticNotationsParser.CurliesContext):
        sp = nodes.inline('', '', classes=["curlies"])
        sp += nodes.Text("{")
        sp.extend(self.visitChildren(ctx))
        sp += nodes.Text("}")
        return [sp]

    def escape(self, atom):
        node = nodes.inline("","")
        while atom != "":
            if atom[0] == "'":
                node += nodes.raw("\\textquotesingle{}", "\\textquotesingle{}", format="latex")
                node += nodes.raw("'", "'", format="html")
                atom = atom[1:]
            elif atom[0] == "`":
                node += nodes.raw("\\`{}", "\\`{}", format="latex")
                node += nodes.raw("`", "`", format="html")
                atom = atom[1:]
            else:
                index_ap = atom.find("'")
                index_bt = atom.find("`")
                if index_ap == -1:
                    index = index_bt
                elif index_bt == -1:
                    index = index_ap
                else:
                    index = min(index_ap, index_bt)
                lit = atom if index == -1 else atom[:index]
                node += nodes.inline(lit, lit)
                atom = atom[len(lit):]
        return node

    def visitAtomic(self, ctx:TacticNotationsParser.AtomicContext):
        atom = ctx.ATOM().getText()
        sub = ctx.SUB()
        node = self.escape(atom)

        if sub:
            sub_index = sub.getText()[2:]
            node += nodes.subscript(sub_index, sub_index)

        return [node]

    def visitPipe(self, ctx:TacticNotationsParser.PipeContext):
        return [nodes.Text("|")]

    def visitHole(self, ctx:TacticNotationsParser.HoleContext):
        hole = ctx.ID().getText()
        token_name = hole[1:]
        node = nodes.inline(hole, token_name, classes=["hole"])

        sub = ctx.SUB()
        if sub:
            sub_index = sub.getText()[2:]
            node += nodes.subscript(sub_index, sub_index)

        return [addnodes.pending_xref(token_name, node, reftype='token',
                                 refdomain='std', reftarget=token_name)]

    def visitEscaped(self, ctx:TacticNotationsParser.EscapedContext):
        escaped = ctx.ESCAPED().getText()
        return [self.escape(escaped.replace("%", ""))]

    def visitWhitespace(self, ctx:TacticNotationsParser.WhitespaceContext):
        return [nodes.Text(" ")]

def sphinxify(notation):
    """Translate a notation into a Sphinx document tree."""
    vs = TacticNotationsToSphinxVisitor()
    return vs.visit(parse(notation))

def main():
    print(sphinxify("a := {+, b {+ c}}"))

if __name__ == '__main__':
    main()
