main = kernel-spec

all: full

full: *.tex
	pdflatex -shell-escape $(main).tex $(main).pdf
	bibtex -min-crossrefs=10 $(main)
	pdflatex -shell-escape $(main).tex $(main).pdf
	pdflatex -shell-escape $(main).tex $(main).pdf

bibtex: *.tex
	bibtex -min-crossrefs=10 $(main)

quick: *.tex
	pdflatex -shell-escape $(main).tex $(main).pdf

clean:
	rm -rvf *.aux *.bbl *.blg *.brf *.log *.out *.toc *.synctex *-blx.bib *.bcf *.run.xml *.thm latex.out *.nav *.snm *.idx *fls
	find . -iname "*.log" -print | xargs rm -rvf
