MAIN = main

all:
	@latexmk -pdf main.tex

detype:
	@latexmk -pdf detype.tex

systemf:
	@latexmk -pdf systemf.tex

clean:
	@rm -f main.pdf main.bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg
	@rm -f detype.pdf detype.bbl *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg
	@rm -Rf auto/
	@rm -f annotated_reviews.pdf

review:
	xelatex annotated_reviews.tex

submit: all review README_MATERIALS.md
	@latexmk -jobname=paper_full -pdf -pdflatex='pdflatex %O -interaction=nonstopmode -synctex=1 "\newcommand*{\submitoption}{} \input{%S}"' $(MAIN)
	rm -Rf coq && mkdir -p coq
	rsync --relative --files-from submit.txt ../coq coq
	tar zcf bundle.tar.gz paper_full.pdf coq README_MATERIALS.md
	mkdir -p upload
	mv bundle.tar.gz $(MAIN).pdf annotated_reviews.pdf upload/

.PHONY: all clean submit
