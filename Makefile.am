ACLOCAL_AMFLAGS = -I m4

# configure for distcheck (need to disable Java since Java build requires writing files and distcheck runs everything read-only 
AM_DISTCHECK_CONFIGURE_FLAGS=--disable-oracle --disable-monetdb --disable-java

# add include dir to C compile flags
AM_CPPFLAGS = -I$(top_srcdir)/include
AM_CFLAGS = -I$(top_srcdir)/include @GPROM_CFLAGS@

# subdirs to build
if JAVABINDING
SUBDIRS = include src test javatest
TESTS = blackboxtests/runtests.sh

ANTUTILS_MODULE=$(top_builddir)/antutils/ant-common.xml

BUILT_SOURCES = $(ANTUTILS_MODULE)

$(ANTUTILS_MODULE):
	if [ ! -f $(ANTUTILS_MODULE) ]; then \
		git submodule init && git submodule update && git submodule status; \
	fi

else
SUBDIRS = include src test
endif

# additional directories to include in a distribution package:
# - maintainer Makefile for running autotools 
# - the header file dir 
# - .y and .l files
# - YACC and FLEX generated files
# - scripts for running executables and scripts
# - java source code and build files (ivy/ant)
EXTRA_DIST = $(top_srcdir)/Makefile.maintainer \
	$(top_srcdir)/ant/dockercross/* \
	$(top_srcdir)/ant/*.xml \
	$(top_srcdir)/ant/*.properties \
	$(top_srcdir)/build.xml \
	$(top_srcdir)/ivy.xml \
	$(top_builddir)/include \
	$(top_builddir)/src/interfaces/jdbc \
	$(top_srcdir)/src/parser/*.y \
	$(top_srcdir)/src/parser/*.l \
	$(top_srcdir)/src/parser/*.lex.c \
	$(top_srcdir)/src/parser/*.tab.c \
	$(top_srcdir)/src/parser/*.tab.h \
	$(top_srcdir)/scripts/*.sh \
	$(top_srcdir)/scripts/dev/*.sh \
	$(top_srcdir)/examples \
	$(top_builddir)/javatest \
	$(top_srcdir)/blackboxtests/build.xml \
	$(top_srcdir)/blackboxtests/testcases/*.xml \
	$(top_srcdir)/blackboxtests/testdb/testDB.sql.in \
	$(top_srcdir)/blackboxtests/TestTemplates/*.stg

# Debian packaging
APP_NAME=pug
TMP_DIR=dpkg
TAR_PACKAGE=$(APP_NAME)-$(VERSION).tar.gz

# Create a deb package
pkg-deb: $(TAR_PACKAGE)
	./packaging/debpackage.sh
