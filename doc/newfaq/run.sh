#/bin/sh
coq-tex -n 72 -v -sl -small main.tex && latex main.v.tex && bibtex main.v && latex main.v.tex && latex main.v.tex && hevea -fix -nosymb main.v.tex

# Commands for installation on pauillac
# scp main.v001.gif interval_discr.v pauillac.inria.fr:/net/pauillac/infosystems/www/coq/doc
# scp main.v.html pauillac.inria.fr:/net/pauillac/infosystems/www/coq/doc/faq.html
