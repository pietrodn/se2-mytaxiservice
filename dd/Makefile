.PHONY: clean all live pdf

all:
	latexmk -pdf -pv main

live:
	latexmk -pdf -pvc -silent main

clean:
	latexmk -C

pdf: all
	cp main.pdf ../Deliveries/DD.pdf
