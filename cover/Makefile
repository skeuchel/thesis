.PHONY: all
all: cover.pdf

cover.pdf: cover.tex
	latexmk -pdf cover.tex

.PHONY: open
open : cover.pdf
	open cover.pdf

.PHONY: clean
clean:
	rm cover.pdf cover.aux cover.fdb_latexmk
