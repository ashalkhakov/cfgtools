#
# A simple Makefile
#

######

include $(PATSHOME)/share/atsmake-pre.mk

######

SOURCES_SATS += \
  ../utils/SATS/fundigraph.sats \
  ../utils/SATS/ltab.sats \
  ../utils/SATS/stapool.sats \
  ../SATS/symbols.sats \
  ../SATS/grm.sats \
  ../SATS/grmfuncs.sats

SOURCES_DATS += \
  ../utils/DATS/fundigraph.dats \
  ../utils/DATS/stapool.dats \
  ../utils/DATS/ltab.dats \
  ../DATS/symbols.dats \
  ../DATS/grm.dats \
  ../DATS/grmfuncs.dats

######

MYPORTDIR=MYPORTDIR
#MYCCRULE=MYCCRULE

######

TEST00A_SOURCES_SATS = \
  ../utils/SATS/fundigraph.sats \
  ../utils/SATS/ltab.sats \
  ../utils/SATS/stapool.sats \
  ../SATS/symbols.sats \
  ../SATS/grm.sats \
  ../SATS/grmfuncs.sats

TEST00A_SOURCES_DATS = \
  ../utils/DATS/fundigraph.dats \
  ../utils/DATS/stapool.dats \
  ../utils/DATS/ltab.dats \
  ../DATS/symbols.dats \
  ../DATS/grm.dats \
  ../DATS/grmfuncs.dats \
  test00A.dats

test00A_C_O := \
  $(patsubst %.c, %_c.o, $(SOURCES_C))
test00A_SATS_O := \
  $(patsubst %.sats, %_sats.o, $(TEST00A_SOURCES_SATS))
test00A_DATS_O := \
  $(patsubst %.dats, %_dats.o, $(TEST00A_SOURCES_DATS))
all:: test00A.exe
test00A.exe: \
  $(test00A_C_O) \
  $(test00A_SATS_O) \
  $(test00A_DATS_O) ; \
  $(PATSCC) $(INCLUDE) $(MALLOCFLAG) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(EXTRAFLAGS)
regress:: test00A.exe; ./$<
cleanall:: ; $(RMF) test00A.exe

######

TEST00B_SOURCES_SATS += \
  ../utils/SATS/fundigraph.sats \
  ../utils/SATS/ltab.sats \
  ../utils/SATS/stapool.sats \
  ../SATS/symbols.sats \
  ../SATS/grm.sats \
  ../SATS/grmfuncs.sats \
  test00B.dats

TEST00B_SOURCES_DATS += \
  ../utils/DATS/fundigraph.dats \
  ../utils/DATS/stapool.dats \
  ../utils/DATS/ltab.dats \
  ../DATS/symbols.dats \
  ../DATS/grm.dats \
  ../DATS/grmfuncs.dats

test00B_C_O := \
  $(patsubst %.c, %_c.o, $(SOURCES_C))
test00B_SATS_O := \
  $(patsubst %.sats, %_sats.o, $(TEST00B_SOURCES_SATS))
test00B_DATS_O := \
  $(patsubst %.dats, %_dats.o, $(TEST00B_SOURCES_DATS))
all:: test00B.exe
test00B.exe: \
  $(test00B_C_O) \
  $(test00B_SATS_O) \
  $(test00B_DATS_O) ; \
  $(PATSCC) $(INCLUDE) $(CFLAGS) $(MALLOCFLAG) -o $@ $^ $(LDFLAGS) $(EXTRAFLAGS)
regress:: test00B.exe ; ./$<
cleanall:: ; $(RMF) test00B.exe

######

include $(PATSHOME)/share/atsmake-post.mk

######

CPF=cp -f

######

testall:: all
testall:: cleanall

cleanall:: ; $(RMF) *_?ats.c
cleanall:: ; $(RMF) MYPORTDIR/*

testall:: all
testall:: regress
testall:: cleanall

######

###### end of [Makefile] ######
