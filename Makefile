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
  utils/fundigraph.sats \
  Grammar.sats \
  LR0Configuration.sats \
  LR0.sats

SOURCES_DATS += \
  utils/fundigraph.dats \
  Grammar.dats \
  Input.dats \
  Automaton.dats \
  LR0Configuration.dats \
  LR0.dats \
  main.dats

######

MYTARGET=main

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
