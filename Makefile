AGDA_FILES := $(shell find . -type f -and -path './src/*' -and -name '*.agda')
AGDAI_FILES := $(subst .agda,.agdai,$(AGDA_FILES))
HTML_FILES := $(addsuffix .html,$(subst ./src/,./docs/,$(basename $(AGDA_FILES))))
AGDA_MODULES := $(subst /,.,$(subst ./src/,,$(basename $(AGDA_FILES))))


default: listings


########################
# Initialise Git hooks #
########################

.PHONY: init
init:
	git config core.hooksPath .githooks


#####################
# Typecheck library #
#####################

.PHONY: test
test: index.agda
	@echo "Checking schmitty.agda-lib..."
	@agda -i. -isrc index.agda


#####################
# Generate listings #
#####################

docs/index.html: index.agda
	@echo "Generating listings..."
	@agda -i. -isrc index.agda --html --html-dir=docs

.PHONY: listings
listings: $(HTML_FILES)

define HTML_template
$(1): docs/index.html
endef
$(foreach html_file,$(HTML_FILES),$(eval $(call HTML_template,$(html_file))))


#######################
# Generate index.agda #
#######################

INDEX_AGDA := "module index where\n\n"
$(foreach agda_module,$(AGDA_MODULES),$(eval INDEX_AGDA := $(INDEX_AGDA)"import $(agda_module)\n"))

index.agda: $(AGDA_FILES)
	@echo $(INDEX_AGDA) > index.agda
