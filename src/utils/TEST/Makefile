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
ltab
ltab: \
ltab.dats ; \
  $(PATSCC2) -cleanaft -DATS_MEMALLOC_LIBC -o $@ $<
regress:: ltab ; ./$<
cleanall:: ; $(RMF) ltab

######

CPF=cp -f

######

testall:: all
testall:: regress
testall:: cleanall

######

###### end of [Makefile] ######
