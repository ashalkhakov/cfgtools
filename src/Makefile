#
# A Simple Makefile
#

######

include \
$(PATSHOME)/share/atsmake-pre.mk

######

CFLAGS += -O2

######

LDFLAGS :=

######

PATSCCOMP = $(CC) -D_XOPEN_SOURCE

######

SOURCES_SATS += \
  utils/SATS/fundigraph.sats \
  utils/SATS/ltab.sats \
  utils/SATS/stapool.sats \
  SATS/symbols.sats

SOURCES_DATS += \
  utils/DATS/fundigraph.dats \
  utils/DATS/stapool.dats \
  utils/DATS/ltab.dats \
  DATS/symbols.dats \
  DATS/grm.dats

######

MYTARGET=DATS/grm

######
#
MYPORTDIR=MYPORTDIR
#
#MYPORTCPP=MYPORTCPP
#
######

include $(PATSHOME)/share/atsmake-post.mk

######

testall:: all
testall:: cleanall

######

cleanall:: ; $(RMF) MYPORTDIR/*

######

###### end of [Makefile] ######
