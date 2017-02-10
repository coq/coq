##########################################################################
##         #   The Coq Proof Assistant / The Coq Development Team       ##
##  v      #   INRIA, CNRS and contributors - Copyright 1999-2018       ##
## <O___,, #       (see CREDITS file for the list of authors)           ##
##   \VV/  ###############################################################
##    //   #    This file is distributed under the terms of the         ##
##         #     GNU Lesser General Public License Version 2.1          ##
##         #     (see LICENSE file for the text of the license)         ##
##########################################################################
# Parsing compact tactic notation syntax in

TEST_INPUT="unfold {+, @qualid|@string at {+, num}}"

python:
	antlr4 -Dlanguage=Python3 -visitor -no-listener TacticNotations.g

java:
	antlr4 -Dlanguage=Java TacticNotations.g && javac TacticNotations*.java

test: java
	grun TacticNotations top -tree <<< "$(TEST_INPUT)"

gui: java
	grun TacticNotations top -gui <<< "$(TEST_INPUT)"

sample:
	cd ..; python3 -m coqnotations.driver < ../tests/tactics > ../tests/antlr-notations.html
