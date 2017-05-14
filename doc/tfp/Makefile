all:
	@latexmk -pdf main.tex

esop:
	@latexmk -pdf main-esop.tex

clean:
	@rm -f main.pdf main.bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg
	@rm -Rf auto/

.PHONY: all clean
