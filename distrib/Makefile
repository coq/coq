# Building the different files of the coq distribution

# Rk: parameterized targets are not accepted on DEC boxes...

# config.distrib defines: VERSION, PREVIOUSVERSION, DISTRIBDIR,
# CVSMODULE, CVSTAG, RELEASENUM and ARCH 
sinclude config.distrib
LOCALARCH=`uname -m`
SYSTEM=`uname -s`

BUILDTARGET=world
INSTTARGET=install
MAKECOQ=make

# We assume we are not on pauillac, so we use ssh and scp
SERVER=pauillac.inria.fr
CP=scp -p
SERVEREXEC=ssh $(SERVER) sh -c
FTPDIR=/net/pauillac/infosystems/ftp/coq/coq
#WWWDIR=/net/pauillac/infosystems/www/coq

FTPVDIR=$(SERVER):$(FTPDIR)/V$(VERSION)

######################

noarguments:
	@echo Please use either
	@echo "make tag          to tag the current archive with the release number"
	@echo "make tar-gz       to build a tar.gz of sources"
	@echo "make arch-tar-gz  to prepare a binary tar.gz for this arch"
	@echo "make rpm          to prepare source and arch rpms"
	@echo "make src-rpm      to prepare source rpms from the tar.gz"
	@echo "make arch-rpm     to prepare binary rpms for the current arch from the src.rpm"
	@echo "make ide-rpm      to build a src.rpm and a rpm for coqide on this arch"
	@echo "make ide-arch-rpm to build a rpm for coqide on this arch from the src.rpm"
	@echo "make pcoq-rpm     to build a src.rpm and a rpm for pcoq on this arch"
	@echo "make deb          to build a debian package"
	@echo "make win          to build a windows package"
	@echo "make macosx       to build a MacOS-X package on a disk image"
	@echo "make contrib-tag     to tag the current contrib state with the release number"
	@echo "make contrib-tar-gz  to build a tar.gz of contrib sources"
	@echo "make ftp-install     to prepare the ftp repository and copy the packages done"
	@echo "make tar-gz-ftp-install         |add the corresponding"
	@echo "make src-rpm-ftp-install        |packages to the ftp"
	@echo "make arch-rpm-ftp-install       |repository supposed"
	@echo "make arch-tar-gz-ftp-install    |to be already"
	@echo "make contrib-ftp-install	       |prepared"
	@echo
	@echo "make clean        to remove temporary files"
	@echo "make cleanall     also removes built packages" 

################## Main targets

COQPACKAGE=coq-$(VERSION)

distrib: tag tar-gz

###################################################################
# Tagging the archive
#

tag:
	echo -n "Tagging the archive with version number $(CVSTAG)...";\
	cvs rtag -F $(CVSTAG) $(CVSMODULE)


## Use make LOCAL=1 to build packages from working directory...
ifeq ($(LOCAL),1)
# export sources of the current work directory
WORKDIR=..
$(COQPACKAGE):
	@echo "Copying sources from work directory"
	@- rm -rf $(COQPACKAGE)
	mkdir $(COQPACKAGE)
	cd $(WORKDIR) ; cp -rf `ls -a | egrep -v 'distrib|^\.$$|^\.\.$$'` $(DISTRIBDIR)/$(COQPACKAGE)/
	cd $(COQPACKAGE)/ ; $(MAKECOQ) clean; \
	  rm -fr CVS */CVS */*/CVS */*/*/CVS */*/*/*/CVS
	find $(COQPACKAGE) -name CVS -type d -exec rm -fr {} \;
else
# export a fresh copy of the tagged CVS version
$(COQPACKAGE):
	@echo -n Exporting a fresh copy of the archive...
	@- rm -rf $(COQPACKAGE)
	@cvs export -d $(COQPACKAGE) -r $(CVSTAG) $(CVSMODULE)
	@echo done
endif

###################################################################
# .tar.gz packages (sources, binaries)
#

TARGZ=$(COQPACKAGE).tar.gz
ARCHTAR=$(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar
ARCHTARGZ=$(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar.gz

tar-gz:
	rm -f $(TARGZ)
	$(MAKE) $(TARGZ)

$(TARGZ): $(COQPACKAGE)
	@rm -rf $(COQPACKAGE)/doc     # doc is implementation doc
	@rm -rf $(COQPACKAGE)/distrib
	@rm -rf $(COQPACKAGE)/KNOWN-BUGS
	@rm -rf $(COQPACKAGE)/{TODO,ANNONCE,PROBLEMES}
	@rm -rf $(COQPACKAGE)/theories/Num
	@rm -rf $(COQPACKAGE)/contrib/graphs
	@rm -rf $(COQPACKAGE)/doc/newsyntax.tex 
	@rm -f $(COQPACKAGE)/make.result
	@rm -rf $(COQPACKAGE)/test-suite/parser   # tests pcoq
	@find $(COQPACKAGE) -name ".cvsignore" -exec rm {} \;
	@echo done
	@echo -n Building the tar.gz source package
	@tar cvf $(COQPACKAGE).tar $(COQPACKAGE)
	@gzip --best --force $(COQPACKAGE).tar
	@chmod g+w $(TARGZ)
	@echo done
	@echo Checking release parameters
	./check-list
	@echo done

test:
	- rm -rf $(COQPACKAGE)
	gunzip -c $(TARGZ) > tmp.tar
	tar xf tmp.tar
	rm -f tmp.tar
	@echo Trying "$(MAKECOQ) $(BUILDTARGET) check"
	(cd $(COQPACKAGE);\
	 ./configure -local -opt -emacs emacs;\
	 $(MAKECOQ) world check >& test.log;\
	 if [ $$? = 0 ];\
	 then echo '"$(MAKECOQ) $(BUILDTARGET) check" succeeded';\
	 else echo '"$(MAKECOQ) $(BUILDTARGET) check" failed'; exit 1;\
	 fi)
	@echo "Compilation succeeded"

# where binaries are compiled
ARCHBUILDROOT=$(DISTRIBDIR)/tar-$(ARCH)
ARCHINSTALL=$(ARCHBUILDROOT)/buildroot

arch-tar-gz:
	$(MAKE) arch-image
	$(MAKE) arch-tar-gz-final

arch-image: $(TARGZ)
	@echo "Building $(ARCHTARGZ) to be installed in /usr/local/"
	@echo "Warning: leading / is removed"
	@-rm -fr $(ARCHINSTALL) $(ARCHBUILDROOT)
	@mkdir -p $(ARCHBUILDROOT) $(ARCHINSTALL)
	@echo "Building binaries... (see arch-image.log)"
	(cd $(ARCHBUILDROOT);\
	 gunzip -c $(DISTRIBDIR)/$(TARGZ) | tar xf -;\
	 cd $(COQPACKAGE);\
	 ./configure -prefix /usr -emacslib /usr/local/lib/emacs/site-lisp -opt -reals all;\
	 $(MAKECOQ) coq check;\
	 $(MAKECOQ) -e COQINSTALLPREFIX=$(ARCHINSTALL) BASETEXDIR=$(ARCHINSTALL) install-coq) > arch-image.log 2>&1
	@echo " .... done"

arch-tar-gz-final:
	(cd $(ARCHBUILDROOT)/buildroot;\
	 tar -cvf $(DISTRIBDIR)/$(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar *)
	gzip --best $(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar
	chmod g+w $(ARCHTARGZ)

clean::
	rm -fr $(ARCHINSTALL) $(ARCHBUILDROOT)

cleanall::
	rm -f $(COQPACKAGE) $(TARGZ) $(ARCHTARGZ) arch-image.log test.log

###################################################################
# RPM (Coq, CoqIde and Pcoq are separated)
#
rpm: src-rpm arch-rpm
src-rpm: coq-src-rpm ide-src-rpm pcoq-src-rpm
arch-rpm: coq-arch-rpm ide-arch-rpm pcoq-arch-rpm

coq-rpm: coq-src-rpm coq-arch-rpm
ide-rpm: ide-src-rpm ide-arch-rpm
pcoq-rpm: pcoq-src-rpm pcoq-arch-rpm

RPMTOPDIR=$(DISTRIBDIR)/RH/src
RPMTMPPATHDIR=$(RPMTOPDIR)/admin
RPMBUILDROOT=$(RPMTOPDIR)/install

# rpm versions 2 and 3: replace rpmbuild by rpm 
RAWRPM=rpmbuild
RPMVERSION=`$(RAWRPM) --version | sed -e "s/RPM version \(.\).*/\1/"`

# option --target avoids problem with i386/i686
RPM=$(RAWRPM) --buildroot $(RPMBUILDROOT) --target $(ARCH) --rcfile RH/rpmrc

# rpm files
RPMEXT=$(VERSION)-$(RELEASENUM)
COQRPMPACKAGE=coq-$(RPMEXT)
COQIDERPMPACKAGE=coqide-$(RPMEXT)
PCOQRPMPACKAGE=coq_ext_for_pcoq-$(RPMEXT)
COQSRCRPM=$(COQRPMPACKAGE).src.rpm
COQRPM=$(COQRPMPACKAGE).$(ARCH).rpm
COQIDESRCRPM=$(COQIDERPMPACKAGE).src.rpm
COQIDERPM=$(COQIDERPMPACKAGE).$(ARCH).rpm
PCOQSRCRPM=$(PCOQRPMPACKAGE).src.rpm
PCOQRPM=$(PCOQRPMPACKAGE).$(ARCH).rpm

RPMLOG=$(DISTRIBDIR)/RH/rpm.log
RPMFILESLOG=$(DISTRIBDIR)/RH/coqfiles.log

coq-src-rpm: $(COQSRCRPM)
coq-arch-rpm: $(COQRPM)

ide-src-rpm: $(COQIDESRCRPM)
ide-arch-rpm: $(COQIDERPM)

pcoq-src-rpm: $(PCOQSRCRPM)
pcoq-arch-rpm: $(PCOQRPM)

$(RPMTOPDIR):
	@mkdir -p $(RPMTOPDIR)/BUILD
	@mkdir -p $(RPMTOPDIR)/RPMS
	@mkdir -p $(RPMTOPDIR)/SOURCES
	@mkdir -p $(RPMTOPDIR)/SPECS
	@mkdir -p $(RPMTOPDIR)/SRPMS
	@mkdir -p $(RPMTMPPATHDIR)
	@mkdir -p $(RPMTOPDIR)/RPMS/$(ARCH)

RH/rpmrc: config.distrib
	(if [ "$(RPMVERSION)" != "2" ];\
	then\
	echo %_topdir $(RPMTOPDIR) > RH/rpmmacros;\
	echo %_tmppath $(RPMTMPPATHDIR) >> RH/rpmmacros;\
	echo %_arch $(ARCH) >> RH/rpmmacros;\
	echo macrofiles:/usr/lib/rpm/macros:RH/rpmmacros > RH/rpmrc;\
	else\
	echo topdir: $(RPMTOPDIR) > RH/rpmrc;\
	echo tmppath: $(RPMTMPPATHDIR) >> RH/rpmrc;\
	fi)

%-$(RPMEXT).src.rpm: RH/%.spec $(TARGZ) RH/rpmrc
	cp -f petit-coq.gif $(RPMTOPDIR)/SOURCES
	cp -f $(TARGZ) $(RPMTOPDIR)/SOURCES
	$(RPM) -bs RH/$*.spec
	mv $(RPMTOPDIR)/SRPMS/$@ .
	chmod g+w $@

%.$(ARCH).rpm: %.src.rpm
	@mkdir -p $(RPMBUILDROOT)
	@echo "Building the $(ARCH) rpm for $*... (see RH/rpm.log)"
	$(RPM) --rebuild $< > $(RPMLOG)
	mv $(RPMTOPDIR)/RPMS/$(ARCH)/$@ .
	chmod g+w $@

clean::
	rm -fr $(RPMTOPDIR) RH/rpmmacros RH/rpmrc

cleanall::
	rm -f *.rpm $(RPMLOG) $(RPMFILESLOG)

###################################################################
# Zip for Windows (package does not contain coqide)
#

COQWINZIP=$(COQPACKAGE)-Win.zip
WINBUILDROOT=$(DISTRIBDIR)/winbuildroot
WININSTALL=$(DISTRIBDIR)/wininstallroot


win: $(COQWINZIP)

$(COQWINZIP): $(TARGZ)
	@echo "Building $(COQWINZIP) to be installed in \coq\bin"
	@echo "Warning: leading / is removed"
	@-rm -fr $(WINBUILDROOT) $(WININSTALL)
	@-mkdir -p $(WINBUILDROOT) $(WININSTALL)
	@echo "Compiling and installing coq... (see win.log)"
	(cd $(WINBUILDROOT);\
	 gunzip -c $(DISTRIBDIR)/$(TARGZ) | tar xf -;\
	 cd $(COQPACKAGE);\
	 ./configure -bindir /coq/bin -libdir /coq/lib -mandir /coq/man -emacslib /coq/emacs -reals all -coqide no;\
	 $(MAKECOQ) coq;\
	 $(MAKECOQ) -e COQINSTALLPREFIX=$(WININSTALL) BASETEXDIR=$(WININSTALL) install-coq) > win.log
	mv $(WINBUILDROOT)/$(COQPACKAGE)/INSTALL.win $(WININSTALL)
	cd $(WININSTALL); zip -A -r $(DISTRIBDIR)/$(COQWINZIP) *

clean::
	rm -fr $(WINBUILDROOT) $(WININSTALL)

cleanall::
	rm -f $(COQWINZIP) win.log

###################################################################
# Debian
#

COQDEBPACKAGE=coq_$(VERSION)-$(RELEASENUM)_i386.deb
COQDEBCHANGES=coq_$(VERSION)-$(RELEASENUM)_*.changes
COQDEBORIG=coq_$(VERSION).orig
COQDEBTARGZ=$(COQDEBORIG).tar.gz
COQIDEDEBPACKAGE=coqide_$(VERSION)-$(RELEASENUM)_i386.deb

DEBIANBUILD=$(DISTRIBDIR)/deb/build
DEBIANLOG=$(DISTRIBDIR)/deb/deb.log
LINTIANLOG=$(DISTRIBDIR)/deb/lintian.log

deb: prep-deb
	cd $(DEBIANBUILD)/$(COQPACKAGE) ;\
	 dpkg-buildpackage -rfakeroot -uc -us 2>&1 | tee $(DEBIANLOG)
	(lintian $(DEBIANBUILD)/$(COQDEBCHANGES) | tee $(LINTIANLOG)) || true

$(COQDEBTARGZ): $(TARGZ)
	tar xzf $(TARGZ)
	mv $(COQPACKAGE) $(COQDEBORIG)
	tar czf $(COQDEBTARGZ) $(COQDEBORIG)	
	rm -rf $(COQDEBORIG)

prep-deb: $(COQDEBTARGZ) $(TARGZ)
	@rm -rf $(DEBIANBUILD)
	@mkdir -p $(DEBIANBUILD)
	cp $(COQDEBTARGZ) $(DEBIANBUILD)
	cd $(DEBIANBUILD) ; tar xzf $(DISTRIBDIR)/$(TARGZ)
	cp -a debian $(DEBIANBUILD)/$(COQPACKAGE)
	rm -rf $(DEBIANBUILD)/$(COQPACKAGE)/debian/CVS
	date > prep-deb

deb-sign: prep-deb
	cd $(DEBIANBUILD)/$(COQPACKAGE) ;\
	 dpkg-buildpackage -rfakeroot 2>&1 | tee $(DEBIANLOG)
	(lintian $(DEBIANBUILD)/$(COQDEBCHANGES) | tee $(LINTIANLOG)) || true


clean::
	rm -fr $(DEBIANBUILD)

cleanall::
	rm -f $(DEBIANLOG) $(LINTIANLOG)

###################################################################
# Mac OS X
#

MACOSXPKG=coq-$(VERSION).pkg
MACOSXDMG=coq-$(VERSION)-macosx.dmg

macosx:
	# Builds the /usr/local/bin image
	$(MAKE) arch-image
	# Builds the pkg file
	$(MAKE) macosx-pkg
	$(MAKE) macosx-dmg

macosx-pkg:
	# Builds the info file
	sed -e "s/VERSION/$(VERSION)/g" MacOS-X/coq.info.template > MacOS-X/coq-$(VERSION).info
	# Builds the resources files
	rm -rf MacOS-X/Resources
	mkdir MacOS-X/Resources
	sed -e "s/VERSION/$(VERSION)/g" MacOS-X/Licence.rtf.template > MacOS-X/Resources/License.rtf
	sed -e "s/VERSION/$(VERSION)/g" MacOS-X/Welcome.rtf.template > MacOS-X/Resources/Welcome.rtf
	cp MacOS-X/ReadMe.rtf.template MacOS-X/Resources/ReadMe.rtf
	# Builds the pkg file
	package $(ARCHINSTALL) MacOS-X/coq-$(VERSION).info -r MacOS-X/Resources


macosx-dmg:
	rm -f $(MACOSXDMG)
	# We successively :
	# - create the dmg file
	# - bind it to a device /dev/diskXs2 (name)
	# - create the file system and name it "Coq X.X"
	# - unbind the device to mount the image on /Volumes
	# - copy the package
	(export size=`du -s $(MACOSXPKG) | cut -dc -f 1`;\
	hdiutil create -sectors `expr $$size + 1000` $(MACOSXDMG);\
	export name=`hdid -nomount $(MACOSXDMG) | tail -1 | cut -d" " -f 1`;\
	newfs_hfs -v "Coq $(VERSION)" $$name;\
	hdiutil eject $$name; hdid $(MACOSXDMG);\
	mkdir "/Volumes/Coq $(VERSION)/coq-$(VERSION).pkg";\
	ditto -rsrcFork -v $(MACOSXPKG) "/Volumes/Coq $(VERSION)/$(MACOSXPKG)")


###################################################################
# contribs and patches
#
contrib-tag:
	echo -n "Tagging the contrib with version number $(CVSTAG)...";\
	cvs rtag -F $(CVSTAG) contrib
	@echo done

contrib-tar-gz:
	- rm -rf contrib-$(VERSION)
	@echo -n Exporting a fresh copy of the contribs...
	cvs export -d contrib-$(VERSION) -r $(CVSTAG) contrib
	@echo -n Removing the maintenance files ...
	@rm -rf contrib-$(VERSION)/*/*/bench.log
	@rm -rf contrib-$(VERSION)/Lyon/PROGRAMS
	@find contrib-$(VERSION) -name ".cvsignore" -exec rm {} \;
	@echo done
	- rm contrib-$(VERSION).tar.gz
	@echo -n Building the tar.gz contrib package
	@tar cvf contrib-$(VERSION).tar contrib-$(VERSION)
	@gzip --best contrib-$(VERSION).tar
	@echo done


patch:
	@echo ******** ATTENTION, plante sur pc-linux, essayez pauillac ******
	$(CP) $(FTPDIR)/V$(PREVIOUSVERSION)/coq-$(PREVIOUSVERSION).tar.gz .
	rm -rf coq-$(PREVIOUSVERSION)
	gunzip -c coq-$(PREVIOUSVERSION).tar.gz | tar x
	rm -rf $(COQPACKAGE)
	gunzip -c $(TARGZ) | tar x
	diff -rc coq-$(PREVIOUSVERSION) $(COQPACKAGE) > patch-$(VERSION)-$(PREVIOUSVERSION)
	gzip --best patch-$(VERSION)-$(PREVIOUSVERSION)

###################################################################
# Installation in the ftp repository
#

ftp-install: prep-ftp-install
	$(CP) $(COQPACKAGE)/CHANGES $(FTPVDIR)/
	$(CP) $(COQPACKAGE)/README $(FTPVDIR)/
	$(CP) $(COQPACKAGE)/README.win $(FTPVDIR)/
	$(CP) $(COQPACKAGE)/README.macosx $(FTVPDIR)/
	$(CP) $(TARGZ) $(FTPVDIR)/
	$(CP) $(COQPACKAGE)-*.tar.gz $(FTPVDIR)/
	$(CP) $(COQRPMPACKAGE).*.rpm $(FTPVDIR)/

# prep-ftp-install: $(FTPDIR)/V$(VERSION)
prep-ftp-install: 
	- $(SERVEREXEC) mkdir -m g+w $(FTPDIR)/V$(VERSION)

final-ftp-install:
	$(SERVEREXEC) "'(cd $(FTPDIR); rm -f current;ln -sf V$(VERSION) current)'"

tar-gz-ftp-install: prep-ftp-install
	chmod g+w $(TARGZ)
	$(CP) $(TARGZ) $(FTPVDIR)/

src-rpm-ftp-install: prep-ftp-install
	chmod g+w $(COQSRCRPM)
	$(CP) *.src.rpm $(FTPVDIR)/

arch-rpm-ftp-install: prep-ftp-install
	chmod g+w $(COQRPM)
	$(CP) *.$(ARCH).rpm $(FTPVDIR)/

arch-tar-gz-ftp-install: prep-ftp-install
	chmod g+w $(ARCHTARGZ)
	$(CP) $(ARCHTARGZ) $(FTPVDIR)/

contrib-ftp-install: prep-ftp-install
	chmod g+w contrib-$(VERSION).tar.gz
	$(CP) contrib-$(VERSION).tar.gz $(FTPVDIR)/

patch-ftp-install: prep-ftp-install
	chmod g+w patch-$(VERSION)-$(PREVIOUSVERSION).gz
	$(CP) patch-$(VERSION)-$(PREVIOUSVERSION).gz $(FTPVDIR)/

###################################################################
# Special targets
#

#clean::

cleanall:: clean
	rm -f config.distrib

