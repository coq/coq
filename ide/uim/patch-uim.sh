#!/bin/sh

BASEDIR=`dirname $0`
UIMDIR="/usr/share/uim"

RULES=$BASEDIR/latin-ltx-rules.scm

echo "adding latin_ltx-rules to elatin"
cp $UIMDIR/elatin-rules.scm $UIMDIR/elatin-rules.scm.orig
cat $BASEDIR/latin-ltx-rules.scm >> $UIMDIR/elatin-rules.scm

echo "patching elatin-custom.scm"
cp $UIMDIR/elatin-custom.scm $UIMDIR/elatin-custom.scm.orig
sed -e "/elatin-rules-latvian-keyboard/ \
s/^.*$/\t(list 'elatin-rules-latin-ltx\n\
\t(N_ \"Latin-ltx\")\n\
\t(N_ \"Latex-style input method.\"))\n\
&/" $UIMDIR/elatin-custom.scm.orig > $UIMDIR/elatin-custom.scm

if [ "x$AUTOON" = "xyes" ]; then
	echo "setting elatin to be on by default"
	cp $UIMDIR/elatin.scm $UIMDIR/elatin.scm.orig
	sed -e "/default-widget_elatin_input_mode/ s/action_elatin_off/action_elatin_on/" \
		$UIMDIR/elatin.scm.orig > $UIMDIR/elatin.scm
fi

echo "all done"
