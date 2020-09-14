SOURCES := $(shell find . -type f -and -path './src/*' -and -name '*.agda')
OBJECTS := $(subst .agda,.agdai,$(SOURCES))
DOCS := $(addsuffix .html,$(subst ./src/,./docs/,$(basename $(SOURCES))))
TESTS_FAIL := $(shell find . -type f -and -path './test/Fail/*' -and -name '*.agda')
TESTS_SUCCEED := $(shell find . -type f -and -path './test/Succeed/*' -and -name '*.agda')

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
	@echo "Checking schmitty..."
	@agda -i. -isrc index.agda


#####################
# Generate listings #
#####################

docs/index.html: index.agda
	@echo "Generating listings..."
	@agda -i. -isrc index.agda --html --html-dir=docs

.PHONY: listings
listings: $(DOCS)

define HTML_template
$(1): docs/index.html
endef
$(foreach html_file,$(DOCS),$(eval $(call HTML_template,$(html_file))))


#######################
# Generate index.agda #
#######################

LIBRARY_MODULES := $(subst /,.,$(subst ./src/,,$(basename $(SOURCES))))

TESTS_SUCCEED_MODULES := $(subst /,.,$(subst ./test/,,$(basename $(TESTS_SUCCEED))))

INDEX_AGDA := "module index where\n"
INDEX_AGDA := $(INDEX_AGDA)"\n"
INDEX_AGDA := $(INDEX_AGDA)"-- * Library\n"
INDEX_AGDA := $(INDEX_AGDA)"\n"
$(foreach module_name,$(LIBRARY_MODULES),$(eval INDEX_AGDA := $(INDEX_AGDA)"import $(module_name)\n"))
INDEX_AGDA := $(INDEX_AGDA)"\n"
INDEX_AGDA := $(INDEX_AGDA)"-- * Tests\n"
INDEX_AGDA := $(INDEX_AGDA)"\n"
$(foreach module_name,$(TESTS_SUCCEED_MODULES),$(eval INDEX_AGDA := $(INDEX_AGDA)"import $(module_name)\n"))

index.agda: $(SOURCES)
	@echo $(INDEX_AGDA) > index.agda
