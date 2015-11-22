all:
	latexmk -pdf -pv main

live:
	latexmk -pdf -pvc main
	
clean:
	latexmk -C

pdf: all
	cp main.pdf ../Deliveries/DD.pdf
