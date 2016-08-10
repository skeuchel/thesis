current_dir=$(shell pwd)

#-----------------------------------------------------------------------------
# Programs
#-----------------------------------------------------------------------------
LATEXMK     := latexmk
LHS2TEX     := lhs2TeX
PDFLATEX    := pdflatex
LATEX       := pdflatex
BIBTEX      := bibtex

MAIN        := main
MAINTECH    := main_techmemo
SRCDIR      := src

LHSFILES    := $(wildcard $(SRCDIR)/Modularity/*.lhs) $(wildcard $(SRCDIR)/ModularEffects/*.lhs)
TEXFILES    := $(wildcard $(SRCDIR)/Modularity/*.tex) $(wildcard $(SRCDIR)/ModularEffects/*.tex)
LHS2TEX_FLAGS  := --poly -s dvipdfm

# Latexmk is so smart that it does not recompile if a file that is included is
# only touched. You must really edit it.
all: $(MAIN).pdf
	latexmk -pdf main.tex

%.pdf: %.tex lhs
	latexmk -pdf  $<
	./shShowVersion.sh

lhs: $(LHSFILES:.lhs=.tex)

once:
	pdflatex main.tex

open: all
	open main.pdf

clean:
	latexmk -C

force:


%.tex : %.lhs force
	[ $(<) ] && ($(LHS2TEX) $(LHS2TEX_FLAGS) $< > $@ || rm -f $@)




# # Only the answer subsumption chapter (separate file).
# subsum:
#  	latexmk -pdf subsumptionOnly.tex
#
# # Only the conclusion chapter (separate file).
# concl:
#  	latexmk -pdf conclusionOnly.tex
#
# intro:
#  	latexmk -pdf introductionOnly.tex

.PHONY: all once open clean
