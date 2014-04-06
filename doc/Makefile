hott.pdf: hott.tex
	pdflatex -halt-on-error hott.tex
	pdflatex -halt-on-error '\providecommand{\WarningsAreErrors}{true}\input{hott.tex}'

hott.bbl: hott.tex
	pdflatex -halt-on-error hott.tex
	bibtex hott.aux
