default: pdf

pdf: 
	lhs2TeX --agda paper.lhs > paper.tex
	pdflatex paper
	pdflatex paper
	bibtex paper
	sleep 1
	pdflatex paper
	sleep 1
	pdflatex paper

clean:
	rm -rf paper.aux paper.out paper.ptb paper.bbl paper.blg paper.log paper.pdf paper.spl paper.tex
