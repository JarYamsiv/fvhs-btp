IP_FILE := $(wildcard latex/*.tex)
I_FILE := $(patsubst latex/%.tex, %.tex, $(IP_FILE))

all: ${I_FILE}
	@echo "Completed !!" $@
	@echo "this is a temporaryfile to hold the output of pdflatex" > temp

%.tex:latex/%.tex
	pdflatex $< > temp
	mv $*.pdf pdf/$*.pdf
	@rm *.log *.aux
	@echo  converted $< "\n"

FORCE:
