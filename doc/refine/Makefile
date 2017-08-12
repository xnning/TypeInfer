MAIN = main

all: $(MAIN).pdf

$(MAIN).pdf: $(wildcard sections/*.tex)
	@latexmk -pdf $(@:.pdf=.tex)

clean:
	@rm -f main.pdf main.bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg
	@rm -Rf auto/

.PHONY: all clean
