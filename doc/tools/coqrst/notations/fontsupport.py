#!/usr/bin/env python2
# -*- coding: utf-8 -*-
##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
"""Transform a font to center each of its characters in square bounding boxes.

See https://stackoverflow.com/questions/37377476/ for background information.
"""

from collections import Counter

try:
    import fontforge
    import psMat
except ImportError:
    print("This program requires FontForge's python bindings:")
    print("  git clone https://github.com/fontforge/fontforge")
    print("  cd fontforge")
    print("  ./bootstrap")
    print("  ./configure")
    print("  make -j8")
    print("  sudo make install")
    raise

def glyph_height(glyph):
    _, ylo, _, yhi = glyph.boundingBox()
    return yhi - ylo

def scale_single_glyph(glyph, width, height):
    """Center glyph in a box of size width*height"""
    # Some glyphs (such as ‘;’) contain references (‘.’ + ‘,’), and moving the
    # referenced glyphs moves them in all glyphs that reference them.
    # Unlinking copies references into this glyph
    glyph.unlinkThisGlyph()
    # Width
    deltaw = width - glyph.width
    glyph.left_side_bearing += deltaw / 2
    glyph.right_side_bearing += deltaw - glyph.left_side_bearing
    glyph.width = width
    # Height
    ylo = glyph.boundingBox()[1]
    deltah = height - glyph_height(glyph)
    glyph.transform(psMat.translate(0, deltah / 2.0 - ylo))

def avg(lst):
    lst = list(lst)
    return sum(lst) / float(len(lst))

def trim_font(fnt):
    """Remove characters codes beyond 191 front fnt"""
    for g in fnt.glyphs():
        if g.unicode >= 191:
            fnt.removeGlyph(g)
    return fnt

def center_glyphs(src_font_path, dst_font_path, dst_name):
    fnt = trim_font(fontforge.open(src_font_path))

    size = max(g.width for g in fnt.glyphs())
    fnt.ascent, fnt.descent = size, 0
    for glyph in fnt.glyphs():
        scale_single_glyph(glyph, size, size)

    fnt.sfnt_names = []
    fnt.fontname = fnt.familyname = fnt.fullname = dst_name
    fnt.generate(dst_font_path)

if __name__ == '__main__':
    from os.path import dirname, join, abspath
    curdir = dirname(abspath(__file__))
    ubuntumono_path = join(curdir, "UbuntuMono-B.ttf")
    ubuntumono_mod_path = join(curdir, "CoqNotations.ttf")
    center_glyphs(ubuntumono_path, ubuntumono_mod_path, "CoqNotations")
