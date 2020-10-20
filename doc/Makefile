SOURCES := $(shell find . -type f -and \( -name '*.tex' -or -name '*.bib' \))
MAIN := main.pdf
VIEW := open -a Skim

default: build

.PHONY: build
build: $(MAIN)

.PHONY: watch
watch:
	@fswatch -o $(SOURCES) | xargs -n1 -I{} make

.PHONY: view
view:
	@$(VIEW) $(MAIN)

.PHONY: clean
clean:
	@latexmk -C $(MAIN:.pdf=.tex)

$(MAIN): $(SOURCES)
	@latexmk -pdf $(MAIN:.pdf=.tex) -halt-on-error

