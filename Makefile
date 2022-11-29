rwildcard=$(wildcard $1$2) $(foreach d,$(wildcard $1*),$(call rwildcard,$d/,$2))
pumls=$(call rwildcard,,*.puml)
pngs=$(patsubst %.puml,%.png,$(pumls))
svgs=$(patsubst %.puml,%.svg,$(pumls))

$(pngs): %.png: %.puml
	plantuml -p -tpng < $< > $@

$(svgs): %.svg: %.puml
	plantuml -p -tsvg < $< > $@

.DEFAULT_GOAL=default
default: $(pngs) $(svgs)
.PHONY: default
