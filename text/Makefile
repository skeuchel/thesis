current_dir=$(shell pwd)

# Latexmk is so smart that it does not recompile if a file that is included is
# only touched. You must really edit it.
all:
	latexmk -pdf main.tex
	./shShowVersion.sh

once:
	pdflatex main.tex

open: all
	open main.pdf

clean:
	latexmk -C


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
