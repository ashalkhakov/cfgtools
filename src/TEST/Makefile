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
  ../DATS/grmfuncs.dats \

######

MYPORTDIR=MYPORTDIR
#MYCCRULE=MYCCRULE

######

TEST00A_SOURCES_SATS = $(SOURCES_SATS)
TEST00A_SOURCES_DATS = $(SOURCES_DATS) test00A.dats

test00A_C_O := \
  $(patsubst %.c, %_c.o, $(SOURCES_C))
test00A_SATS_O := \
  $(patsubst %.sats, %_sats.o, $(TEST00A_SOURCES_SATS))
test00A_DATS_O := \
  $(patsubst %.dats, %_dats.o, $(TEST00A_SOURCES_DATS))
all:: test00A
test00A: \
  $(test00A_C_O) \
  $(test00A_SATS_O) \
  $(test00A_DATS_O) ; \
  $(PATSCC) $(INCLUDE) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(EXTRAFLAGS)
regress:: test00A; ./$<
cleanall:: ; $(RMF) test00A

######

TEST00B_SOURCES_SATS = $(SOURCES_SATS)
TEST00B_SOURCES_DATS = $(SOURCES_DATS) test00B.dats

test00B_C_O := \
  $(patsubst %.c, %_c.o, $(SOURCES_C))
test00B_SATS_O := \
  $(patsubst %.sats, %_sats.o, $(TEST00B_SOURCES_SATS))
test00B_DATS_O := \
  $(patsubst %.dats, %_dats.o, $(TEST00B_SOURCES_DATS))
all:: test00B
test00B: \
  $(test00B_C_O) \
  $(test00B_SATS_O) \
  $(test00B_DATS_O) ; \
  $(PATSCC) $(INCLUDE) $(CFLAGS) -o $@ $^ $(LDFLAGS) $(EXTRAFLAGS)
regress:: test00B ; ./$<
cleanall:: ; $(RMF) test00B

######

include $(PATSHOME)/share/atsmake-post.mk

######

CPF=cp -f

######

testall:: all
testall:: cleanall

cleanall:: ; $(RMF) MYPORTDIR/*

testall:: all
testall:: regress
testall:: cleanall

######

###### end of [Makefile] ######
