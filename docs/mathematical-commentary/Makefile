.PHONY: all check clean

all: check
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=.build main.tex
	mkdir -p ../../output/pdf
	cp .build/main.pdf ../../output/pdf/hypernets-mathematical-commentary.pdf

check:
	python3 check_sources.py

clean:
	latexmk -C -outdir=.build main.tex
