AM_CPPFLAGS = -I$(top_srcdir)/include
AM_CFLAGS = @GPROM_CFLAGS@

SUBDIRS = pi_cs_rewrites transformation_rewrites game_provenance xml_rewrites summarization_rewrites semiring_combiner

noinst_LTLIBRARIES        				= libprovenance_rewriter.la
libprovenance_rewriter_la_SOURCES		= prov_rewriter_main.c prov_utility.c prov_schema.c
libprovenance_rewriter_la_LIBADD      	= pi_cs_rewrites/libpi_cs_rewrites.la \
										transformation_rewrites/libtransformation_rewrites.la \
										game_provenance/libgp.la \
										xml_rewrites/libxml_rewrites.la \
										summarization_rewrites/libsummarization_rewrites.la \
										semiring_combiner/libsc.la