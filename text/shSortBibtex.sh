#! /bin/bash

bibtool='/usr/bin/bibtool'
infile='Bibliography.bib'
tempout=$(mktemp sortedBibtexTemp.bib.XXXXX)

echo "Temporary output file is $tempout"
bibtool -sort.format="%N(author)" -i $infile --pass.comments=on --check.double=on -o $tempout

echo "Overwrite input file?"
mv -i $tempout $infile
