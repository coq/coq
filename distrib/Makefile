# Building the different files of the coq distribution

sinclude config.distrib
LOCALARCH=`uname -m`
ARCH=`uname -m | sed -e 's/i.86/i386/'`
#Pour MacOS X
#ARCH=`uname -m | sed -e 's/Power Macintosh/MacOS-X/'`
SYSTEM=`uname -s`

ARCHBUILDROOT=$(DISTRIBDIR)/${ARCH}
RPMTOPDIR=$(DISTRIBDIR)/redhat
RPMTMPPATHDIR=$(DISTRIBDIR)/redhat/admin

# Parce que le chemin d'installation est cablé en dur dans coqtop, on ne
# peut pas construire les rpm ailleurs que dans / et donc on doit être root
#RPMBUILDROOTOPT=
RPMBUILDROOT=$(DISTRIBDIR)/rpmbuildroot
RPMBUILDROOTOPT=--buildroot ${RPMBUILDROOT}
RAWRPM=rpm
RPMVERSION=`${RAWRPM} --version | sed -e "s/RPM version \(.\).*/\1/"`
RPM=${RAWRPM} ${RPMBUILDROOTOPT} --rcfile rpmrc

FTPDIR=/net/pauillac/infosystems/ftp/coq/coq
WWWDIR=/net/pauillac/infosystems/www/coq

COQPACKAGE=coq-${VERSION}
COQRPMPACKAGE=coq-${VERSION}-${RELEASENUM}

######################

noarguments:
	@echo Please use either
	@echo "make tag          to tag the current archive with the release number"
	@echo "make tar-gz       to build a tar.gz of sources"
	@echo "make rpm          to prepare a src.rpm and a rpm for the current arch"
	@echo "make arch-rpm     to prepare a rpm for the current arch from the src.rpm"
	@echo "make arch-tar-gz  to prepare a binary tar.gz for this arch"
	@echo "make contrib-tag    to tag the current contrib state with the release number"
	@echo "make contrib-tar-gz to build a tar.gz of contrib sources"
	@echo "make ftp-install  to prepare the ftp repository and copy the packages done"
	@echo "make tar-gz-ftp-install         |add the corresponding"
	@echo "make src-rpm-ftp-install        |packages to the ftp"
	@echo "make arch-rpm-ftp-install       |repository supposed"
	@echo "make arch-tar-gz-ftp-install    |to be already"
	@echo "make contrib-ftp-install	       |prepared"
	@echo "make deb		 to build a debian package"
	@echo "make win		 to build a windows package"

################## Main targets

distrib: tag tar-gz
rpm: src-rpm arch-rpm

#################
tag:
	echo -n "Tagging the archive with version number $(DASHEDVERSION)...";\
	cvs rtag -F $(DASHEDVERSION) $(MAJORVERSION)

tar-gz:
	@echo -n Exporting a fresh copy of the archive...
	@- rm -rf ${COQPACKAGE}
	@cvs export -d $(COQPACKAGE) -r $(DASHEDVERSION) $(MAJORVERSION)
	@echo done
	@echo -n Removing the maintenance files and doc...
#	@rm -rf ${COQPACKAGE}/doc     # doc is implementation doc
	@rm -rf ${COQPACKAGE}/distrib
	@rm -rf ${COQPACKAGE}/KNOWN-BUGS
	@rm -rf ${COQPACKAGE}/{TODO,ANNONCE,PROBLEMES}
	@rm -rf ${COQPACKAGE}/theories/Num
	@find ${COQPACKAGE} -name ".cvsignore" -exec rm {} \;
	@echo done
	@echo -n Building the tar.gz source package
	@tar cvf ${COQPACKAGE}.tar ${COQPACKAGE}
	@gzip --best --force ${COQPACKAGE}.tar
	@echo done
	@echo Checking release parameters
	./check-list
	@echo done

src-rpm: ${COQRPMPACKAGE}.src.rpm
arch-rpm: ${COQRPMPACKAGE}.${ARCH}.rpm

test:
	cp ${COQPACKAGE}.tar.gz tmp.tar.gz
	gunzip tmp.tar.gz
	@echo Trying "make world"
	- rm -rf ${COQPACKAGE}
	tar xf tmp.tar
	(cd ${COQPACKAGE};\
	configure -local -opt -emacs emacs;\
	make world >& log.world;\
	if [ $$? = 0 ];\
	then echo make world succeeded;\
	else echo make world failed; exit 1;\
	fi)
	rm tmp.tar
	@echo "Compilation succeeded"

release-bin:
	@echo
	@echo "***************"
	@echo "   attention   "
	@echo "***************"
	@echo
	@echo "   \"make release-bin\" suppose que vous venez de compiler"
	@echo "   ET D'INSTALLER Coq. Tapez <Ctrl-C> pour abandonner"
	@echo "   et <Return> pour continuer."
	@echo
	@read
	tar -cvf $(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar --files-from $(COQLIB)/COQFILES
	gzip --best $(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar

arch-tar-gz-final:
	(cd ${ARCHBUILDROOT}/buildroot;\
	tar -cvf ${DISTRIBDIR}/$(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar *)
	gzip --best $(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar

arch-tar-gz: ${COQPACKAGE}.tar.gz
	@echo "Building $(COQPACKAGE)-$(SYSTEM)-$(ARCH).tar.gz to be installed in /usr/local/"
	@echo "Warning: leading / is removed"
	- mkdir -p ${ARCHBUILDROOT}
	(cd ${ARCHBUILDROOT};\
	rm -rf ${COQPACKAGE} || true;\
	gunzip -c $(DISTRIBDIR)/${COQPACKAGE}.tar.gz | tar xf -;\
	cd ${COQPACKAGE};\
	./configure -bindir /usr/local/bin -libdir /usr/local/lib/coq -mandir /usr/local/man -emacs emacs -emacslib /usr/local/lib/emacs/site-lisp -opt;\
	make world tools;\
	rm -rf ${ARCHBUILDROOT}/buildroot/* || true;\
	make -e COQINSTALLPREFIX=${ARCHBUILDROOT}/buildroot/ install)
	$(MAKE) arch-tar-gz-final

win: ${COQPACKAGE}.tar.gz
	@echo "Building $(COQPACKAGE)-Win.zip to be installed in \coq\bin"
	@echo "Warning: leading / is removed"
	- mkdir -p ${ARCHBUILDROOT}
	(cd ${ARCHBUILDROOT};\
	rm -rf ${COQPACKAGE} || true;\
	gunzip -c $(DISTRIBDIR)/${COQPACKAGE}.tar.gz | tar xf -;\
	cd ${COQPACKAGE};\
	./configure -bindir /coq/bin -libdir /coq/lib -mandir /coq/man -emacslib /coq/emacs;\
	make world;\
	rm -rf ${ARCHBUILDROOT}/buildroot/* || true;\
	make -e COQINSTALLPREFIX=${ARCHBUILDROOT}/buildroot/ install;\
	cd ${ARCHBUILDROOT}/buildroot;\
	zip -A -r $(COQPACKAGE)-win.zip *;\
	mv $(COQPACKAGE)-Win.zip ../..)

rpm-dirs:
	- mkdir ${RPMTOPDIR}
	- mkdir ${RPMTOPDIR}/BUILD
	- mkdir ${RPMTOPDIR}/RPMS
	- mkdir ${RPMTOPDIR}/SOURCES
	- mkdir ${RPMTOPDIR}/SPECS
	- mkdir ${RPMTOPDIR}/SRPMS
	- mkdir ${RPMTMPPATHDIR}
	- mkdir ${RPMBUILDROOT}

rpm-config: rpm-dirs
	- rm rpmrc rpmmacros
	(if [ "${RPMVERSION}" = "3" ];\
	then\
	echo %_topdir ${RPMTOPDIR} > rpmmacros;\
	echo %_tmppath ${RPMTMPPATHDIR} >> rpmmacros;\
	echo %_arch ${ARCH} >> rpmmacros;\
	echo macrofiles:/usr/lib/rpm/macros:rpmmacros > rpmrc;\
	else\
	echo topdir: ${RPMTOPDIR} > rpmrc;\
	echo tmppath: ${RPMTMPPATHDIR} >> rpmrc;\
	fi)

# Les cibles suivantes ne sont pas acceptées sur DEC (car paramétrées)

${COQPACKAGE}.tar.gz:
	${MAKE} tar-gz

# rpm 3.0 met dans LOCALARCH mais rpm 2.5 dans ARCH...
${COQRPMPACKAGE}.src.rpm: ${COQPACKAGE}.tar.gz coq.spec
	${MAKE} rpm-config
	cp -f petit-coq.gif ${RPMTOPDIR}/SOURCES
	cp -f ${COQPACKAGE}.tar.gz ${RPMTOPDIR}/SOURCES
	- mkdir ${RPMTOPDIR}/RPMS/${ARCH}
	- rm ${RPMTOPDIR}/RPMS/${LOCALARCH}
	- ln -s ${RPMTOPDIR}/RPMS/${ARCH} ${RPMTOPDIR}/RPMS/${LOCALARCH}
	${RPM} -ba coq.spec
	mv ${RPMTOPDIR}/SRPMS/${COQRPMPACKAGE}.src.rpm .
	(if [ -f ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${LOCALARCH}.rpm ];\
	then mv ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${LOCALARCH}.rpm ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${ARCH}.rpm;\
	else mv ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${ARCH}.rpm .;\
	fi)

# Sera déjà fait si le src.rpm vient d'être fait
${COQRPMPACKAGE}.${ARCH}.rpm: rpm-config ${COQRPMPACKAGE}.src.rpm
	- mkdir ${RPMTOPDIR}/RPMS/${ARCH}
	- rm ${RPMTOPDIR}/RPMS/${LOCALARCH}
	- ln -s ${RPMTOPDIR}/RPMS/${ARCH} ${RPMTOPDIR}/RPMS/${LOCALARCH}
	${RPM} --rebuild ${COQRPMPACKAGE}.src.rpm
	(if [ -f ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${LOCALARCH}.rpm ];\
	then mv ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${LOCALARCH}.rpm ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${ARCH}.rpm;\
	else mv ${RPMTOPDIR}/RPMS/${ARCH}/${COQRPMPACKAGE}.${ARCH}.rpm .;\
	fi)

RH/coq.list: ${COQPACKAGE}.tar.gz Makefile config.distrib
	rm -rf RH/${COQPACKAGE} RH/build
	cd RH ; tar xzf ../${COQPACKAGE}.tar.gz
	cd RH/${COQPACKAGE} ; sh ../do_build
	cd RH/${COQPACKAGE} ; make COQINSTALLPREFIX=${DISTRIBDIR}/RH/build install
	echo "# This file has been generated" > RH/coq.list
	echo "# Do not edit" >>RH/coq.list
	cd RH/build ; find . '!' -type d | sed -e 's|^\./|/|g'>> ../coq.list

coq.spec: RH/coq.list RH/coq.spec.tpl
	echo "# This file has been generated from RH/coq.spec.tpl" > coq.spec
	echo "# Do not edit" >> coq.spec
	cd RH ; m4 -P coq.spec.tpl >> ../coq.spec

##########
contrib-tag:
	echo -n "Tagging the contrib with version number $(DASHEDVERSION)...";\
	cvs rtag -F $(DASHEDVERSION) contrib
	@echo done

contrib-tar-gz:
	- rm -rf contrib-${VERSION}
	@echo -n Exporting a fresh copy of the contribs...
	cvs export -d contrib-${VERSION} -r $(DASHEDVERSION) contrib
	@echo -n Removing the maintenance files ...
	@rm -rf contrib-${VERSION}/*/*/bench.log
	@rm -rf contrib-${VERSION}/Lyon/PROGRAMS
	@find contrib-${VERSION} -name ".cvsignore" -exec rm {} \;
	@echo done
	- rm contrib-${VERSION}.tar.gz
	@echo -n Building the tar.gz contrib package
	@tar cvf contrib-${VERSION}.tar contrib-${VERSION}
	@gzip --best contrib-${VERSION}.tar
	@echo done

##########
patch:
	@echo ******** ATTENTION, plante sur pc-linux, essayez pauillac ******
	cp $(FTPDIR)/V$(PREVIOUSVERSION)/coq-$(PREVIOUSVERSION).tar.gz .
	rm -rf coq-$(PREVIOUSVERSION)
	gunzip -c coq-$(PREVIOUSVERSION).tar.gz | tar x
	rm -rf ${COQPACKAGE}
	gunzip -c ${COQPACKAGE}.tar.gz | tar x
	diff -rc coq-$(PREVIOUSVERSION) ${COQPACKAGE} > patch-${VERSION}-$(PREVIOUSVERSION)
	gzip --best patch-${VERSION}-$(PREVIOUSVERSION)

##########
clean:
	- rm -rf ${COQPACKAGE} ${RPMTOPDIR} ${ARCHBUILDROOT} ${RPMBUILDROOT}

cleanall:
	- rm -rf ${COQPACKAGE}* ${RPMTOPDIR} ${ARCHBUILDROOT} ${RPMBUILDROOT} 

########## Installation in the ftp repository

ftp-install: prep-ftp-install
	cp ${COQPACKAGE}/CHANGES ${FTPDIR}/V${VERSION}/
	cp ${COQPACKAGE}/README ${FTPDIR}/V${VERSION}/
	cp ${COQPACKAGE}/README.win ${FTPDIR}/V${VERSION}/
	cp ${COQPACKAGE}.tar.gz ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/${COQPACKAGE}.tar.gz
	cp ${COQPACKAGE}-*.tar.gz ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/${COQPACKAGE}-*.tar.gz
	cp ${COQRPMPACKAGE}.*.rpm ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/${COQRPMPACKAGE}.*.rpm

# prep-ftp-install: $(FTPDIR)/V${VERSION}
prep-ftp-install: 
	- mkdir $(FTPDIR)/V${VERSION}
	- chmod g+w ${FTPDIR}/V${VERSION}
	(cd $(FTPDIR); rm -f current;ln -sf V${VERSION} current)

tar-gz-ftp-install: prep-ftp-install
	cp ${COQPACKAGE}.tar.gz ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/${COQPACKAGE}.tar.gz

src-rpm-ftp-install: prep-ftp-install
	cp ${COQRPMPACKAGE}.src.rpm ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/${COQRPMPACKAGE}.src.rpm

arch-rpm-ftp-install: prep-ftp-install
	cp ${COQRPMPACKAGE}.${ARCH}.rpm ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/${COQRPMPACKAGE}.${ARCH}.rpm

arch-tar-gz-ftp-install: prep-ftp-install
	cp ${COQPACKAGE}-$(SYSTEM)-$(ARCH).tar.gz ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/${COQPACKAGE}-$(SYSTEM)-$(ARCH).tar.gz

contrib-ftp-install: prep-ftp-install
	cp contrib-${VERSION}.tar.gz ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/contrib-${VERSION}.tar.gz

patch-ftp-install: prep-ftp-install
	cp patch-${VERSION}-$(PREVIOUSVERSION).gz ${FTPDIR}/V${VERSION}/
	chmod g+w ${FTPDIR}/V${VERSION}/patch-${VERSION}-$(PREVIOUSVERSION).gz

deb: ${COQPACKAGE}.tar.gz
	rm -rf deb_build
	mkdir -p deb_build
	cd deb_build ; tar xzf ../${COQPACKAGE}.tar.gz
	cd deb_build ; mv ${COQPACKAGE} ${COQPACKAGE}.orig
	cd deb_build ; tar xzf ../${COQPACKAGE}.tar.gz
	cp -a debian deb_build/${COQPACKAGE}
	cd deb_build/${COQPACKAGE} ; dpkg-buildpackage -rfakeroot -uc -us
