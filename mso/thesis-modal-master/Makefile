FILENAME=thesis
SOURCENAME=source
OUTPUTNAME=output

default: preview

compile:
	lhs2TeX -o $(FILENAME).tex $(SOURCENAME).lagda --agda
	pdflatex $(FILENAME).tex
	bibtex $(FILENAME)
	pdflatex $(FILENAME).tex
	pdflatex $(FILENAME).tex
	mv $(FILENAME).pdf $(OUTPUTNAME).pdf

open:
	open $(OUTPUTNAME).pdf

clean:
	rm $(FILENAME).*
	rm symbols/*-converted-to.pdf

preview: compile open clean
