#-------------------------------------------------------------------------------
# Programs
#-------------------------------------------------------------------------------
LATEXMK     := latexmk
LHS2TEX     := lhs2TeX
PDFLATEX    := pdflatex
LATEX       := pdflatex
BIBTEX      := bibtex

#-------------------------------------------------------------------------------
# Flags
#-------------------------------------------------------------------------------
LHS2TEX_FLAGS  := --poly -s dvipdfm

#-------------------------------------------------------------------------------
# Dirs
#-------------------------------------------------------------------------------
SRCDIR      := src

#-------------------------------------------------------------------------------
# PDF targets
#-------------------------------------------------------------------------------
all: main
main: main.pdf
mod: mod.pdf
intro: intro.pdf

open: all
	open main.pdf

clean:
	latexmk -C

#-------------------------------------------------------------------------------
# LHS processing
#-------------------------------------------------------------------------------
# List of .lhs files needed to be processed by lhs2tex
LHSFILES    := $(wildcard $(SRCDIR)/*/*.lhs) $(wildcard $(SRCDIR)/*/*/*.lhs)

# List of all texfiles. This includes the generated ones (or maybe they have
# to exist prior to invoking make).
TEXFILES    := $(wildcard $(SRCDIR)/*/*.tex) $(wildcard $(SRCDIR)/*/*/*.tex)

# Targets and make rule
lhs: $(LHSFILES:.lhs=.tex)
%.tex : %.lhs force
	$(LHS2TEX) $(LHS2TEX_FLAGS) $< > $@ || (rm -f $@ && exit 1)

force:

#-------------------------------------------------------------------------------
# PDF processing
#-------------------------------------------------------------------------------
# Latexmk does the dependency tracking for us.
%.pdf: %.tex lhs
	latexmk -pdf  $<

.PHONY: all open clean
