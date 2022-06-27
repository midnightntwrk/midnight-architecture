rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))
pumls=$(call rwildcard,,*.puml)
pngs=$(patsubst %.puml,%.png,$(pumls))
pdfs=$(patsubst %.puml,%.pdf,$(pumls))

$(pngs): %.png: %.puml
	plantuml -p -tpng < $< > $@

$(pdfs): %.pdf: %.puml
	plantuml -tpdf -Sshadowing=false < $< > $@

.DEFAULT_GOAL=default
default: $(pngs) $(pdfs)
.PHONY: default
