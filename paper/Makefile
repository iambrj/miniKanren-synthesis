all: paper.tex paper.bib
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	bibtex paper
	pdflatex paper.tex
	pdflatex paper.tex

clean:
	rm -rf *.bbl
	rm -rf *.blg
	rm -rf *.aux
