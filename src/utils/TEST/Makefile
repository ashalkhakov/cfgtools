#
# A simple Makefile
#

######

include $(PATSHOME)/share/atsmake-pre.mk

######

MYTARGET=MYTARGET
MYCCRULE=MYCCRULE

######

include $(PATSHOME)/share/atsmake-post.mk

######

all:: \
ltab.exe
ltab.exe: \
ltab.dats ; \
  $(PATSCC2) -cleanaft -DATS_MEMALLOC_LIBC -o $@ $<
regress:: ltab.exe ; ./$<
cleanall:: ; $(RMF) ltab.exe

######

fundigraph_dats.o: ; \
$(PATSCC2) -cleanaft $(INCLUDE) $(INCLUDE_ATS) $(MALLOCFLAG) $(CFLAGS) -o $@ -c ../DATS/fundigraph.dats

test_fundigraph_dats.o: test_fundigraph.dats; \
$(PATSCC2) -cleanaft $(INCLUDE) $(INCLUDE_ATS) $(MALLOCFLAG) $(CFLAGS) -o $@ -c $<

all:: \
test_fundigraph.exe
test_fundigraph.exe: \
test_fundigraph_dats.o fundigraph_dats.o ; \
  $(CC) $(INCLUDE) $(INCLUDE_ATS) $(MALLOCFLAG) $(CFLAGS) -o $@ test_fundigraph_dats.o fundigraph_dats.o
regress:: test_fundigraph.exe ; ./$<
cleanall:: ; $(RMF) test_fundigraph.exe

######

cleanall:: ; $(RMF) *.c

######

CPF=cp -f

######

testall:: all
testall:: regress
testall:: cleanall

######

###### end of [Makefile] ######
